-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0271
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:52:42.777492+00:00
-- url     : https://prove2.me/submissions/8ac3fe80-d50e-4fc4-8774-a902dcda0343

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 48561155 ≤ n < 48741011 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 48562405 1250 48561155 48561187
    0x8121303021c0807060504110109060219210504090606300621060b0a0506030a0209010309060e0307020a06030e0712050f0304060207061106041a070c0605070909050108070803 77
    0x8103403180025400504000300d1031020241404d640b180402250928091401021414810030a5414042406070600a0a40100390b108150543e8110201343e944d242c10051141070355107070941220480502d41d0045035904c81e0040c010354000c00c109005441c0c1d2010101c409031072100ea140881007032000207000b00b030545640c0740003045d0070031404500251650f040154503001c0c49030103002d2901740c41c100300401201d0300078124040c4049429429080ca85008100e05104c02485c0d1700a85500040802c4036a01945c031810b5680c1c3c02100c07c10000c5203040307800b640d82d030061000b039124004027a00050294420300981e8201c00c68070016184181c40c118002d8400c61284804840c1402000c8280c54014403c2018100501d070a07802401c9052a10002420404081c80c0800d082c1c0c00c072008020210700701c44a40340c80207403003990000c51540c4030101191010f00c1e1000007802a8149030034040220761088440065900c03008c0e0030801a6a03410500c1d545074400d102c2d2a805400601c040044041009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 48563655 1250 48562405 48562429
    0x80d0c020d110a0b0409050a05041101050c0f06011710090203070b0d020904050c120a140402010806011b0308010f05030a0b010b03040c0b0703030203160c02030c060a03060905100812130302 83
    0x410701c41184008040000d00f0140725404c03050a01d80081000c0013041003901610350030a45040c020400390529444652400d00c11a08c25814010000740c0c4941900d01049044540450a000da80c100d50b150300a505101d0003000340b0308031601c91754810700801e81103841007000c0c45600600030300c11586090441134072604806010904d4036828841c0010b01c0d1100d008851281d805c130394100e6600c071225075603506901400b42a07612243e103080614400d039061b00c00025001602403e01e0b0080350b9561004032001c14405c0062038105100e0840d240030940c011610034140c2b5181190481015244c0d411715a0720118444058620300310b8000400c02d80804100540d0400d0290305c0301c080c01034980301a90b2050340322080c11030000b0340c00410060030020741c0b0042400307000e0a243c0041c1c280f00580000341c1e2040179556080c4a034400103818410b650003544020000c1c150340c58140907914242008100352000351003642118040c00c0c1256103905641001c0301c50b15402c0040d800c0c42c080c159028030901444034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 48564905 1250 48563655 48563663
    0x5100c03111515030d170c030a0605040f060f0b0f0f0318070806040501050109020c030a12020c1009050c0301060f0b0a17010e041b0f09090807021009030606080d0c020d 74
    0xc4140903029101c00e005510a50035009040d01c070b4055441810705d041143c0c5001c0c410030901982c0c00700c60074010700c080c581040b80c13030b0b1600d038880d20364441d0240103000560255a00a240000e144801d0240340c005d00100c91408075000a4642d96103600b010070710401003013540200c0100305800d07030403503550041d58004001000b03071004aa442070071140740a03017030307004007041c1d51020040004002d02401182d025020407a070030341c01c2418100c00c10350389001d4681c0b0b9000b40140c440c0003a00b068103503410340e40002c000104407102d0350761000444004005c0d454084c0c44d01c0c040c2d0415002181014040e41c407c9601d10030b401d51718185007100414003030700310907102c00400c05040700c80d001261811150038080c140001d426400303402c1914140860b00e20f0003807010320707a020681007000440f24503041034044a40f80c4001284401032803900c1d0120b44a480c40c025801400e0500380c009060b031180c48041030340d01ca5a42006074545130848941e90701d201a0704000000e102005440040c100001903106441c81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 48566155 1250 48564905 48564913
    0x405060a12110c0f12130302060711060d021305040504050601050d031101090b010602100905061b090d0c0602060a0203040b0c09010512010e0709050a0b0a1404080609030a080105100c0311 82
    0x40b414420040e61060003055076591003120540801d035410700200040a1140300d4003841e0154803a48101442d48500c030191207544c4c0862004107100f12000340c2810210002e040c2a0303101d0000f08090025006240a10340207543c04070040b58904041c801c180c000d981040050a980c1c7c0707043c08004044034a100c00302d0800264520500420b44240a1040754610410214015604050000b0300c3c2080001c80034183c141840780070b1020a0300450015040340d402c041c100f8041140780c4082d1400d00c6079800581d0050107070940782c8140704000304800141c030340303560076900316841d941607100c260b00003940c0103480c01204402184500600800900007408103040003414005c44c1c003100b01100109038030010024111000b0803407c0c1c1e03446403040c00030b8007007101c2d5460024180b095142c4c45018149022050011443d00c1c0440b87c00000140d40080001c0701c100c1d202480e1400c1c003291a0341004c5401008101e49030000300e018900190300c464240017954601440e00941c1c4c8044034144a003022030302003801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 48567405 1250 48566155 48566171
    0x20a08030a0504060b03061003060e0307170301050f12120304020f190503100606052502100909051005010c02090c0c150123010f03020f09040915060501050405060a12 73
    0x140000180d8400c1e52240000a8545054141031050710389001c201c40c80780e0030030000c2200c2d400c0d00350041c1c3d050381d40215001450200c1c200c2c144d4a50b00c81d40c40064000600301140c0d003040800d080c011810b0b03480654108a04d10300980334021542c1c0318505140590f001107401d0003628034280051a0701c98002040060032110500c049148440c3c0105c036052001000346c0309000da82001c100b00c0d030020092540420001d0714202c1c004106002d01e0007000c10304419417000c036442c5104049440001600108144400303103000c0341c05450f010b164800c001c142400c050000b149084810410000c0f15010703111004071440c0784d402c00c00c0707008000f071070f0380790328402480043d40710401080303a080300c801c40c0d0b07202103125410804903441c01c1000110390072224041024004c807030b0b40e0042c1081500080341c100561202d20070901c3d44120300851078507035040f81c070300100c05c42400450300000c0704c0110364500802c1515240d07401120507101c0ea01445811181c01c104200c0c4843c484c442d01c95a110781c005001500036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 48568655 1250 48567405 48567413
    0x1003110607240e03180d0c030503030906010609050f0a0608040c0312050a0e062109151006261302190b0a08071e0c0809090712060b040302130c020a 65
    0xd0640b02d803081c0700c08a05010300441d4201e1203283d900981410040d4181401581100a0150405801030196907403440240800c5404d82000d40030b10f0b4070405494486c0b811140c281e0f5101c10921403c0001201c032800000c072800c1411405030b00701c0c40503081c014054206030b416601d01d03801030030848004845010020106020241540d5990480d0341c40036503c84144000070500c41c1c1007440d440c03003207104221100f001c4a00000400c5803500d00300740101d060369602c0032641070031200003204001c1c0d070360501045401c031418804841503d81d03a4031f40101d140c9072103000040022a24515503003d00c1903901003038488510300c00d040105440209035071606800040504030070201648068100d0f0004038405078a580c2103011154040381c80d00d0942580744a4200c40c1c04042504a0305034144110310030944144080c1804885460718040d014881904000030f000305140340d0b038856210320364a46600031820b000c414081380d00b04c07030f0002e001040100380c0094440040440c2c0c55107805612624104000007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 48569905 1250 48568655 48568673
    0x206160e0d0303020d061d2205010507020601061403070212030a09062c0307030801090b010e040c080105031b03101107020a0303090801060b040b030703090c05060705010203100603051003110607 85
    0x1903110f5a009601c40c604402d0b01401d483c46a00040c6213a01c0c00c0e501c90801200059a1940c00a100380c0d4181a0f003501c86038064801c4d59144c1c002d80154203010030060029000501e05049070030550300d00707981ca100c10071a00018001654040c00581010100c2c0c0900c1401e038020750340202d5106400108034a450b9907640480c0c4100e6040c0101d00c1000300740214001010311041461010840618074005071707650010a4240140900c50940f6511500001140d00c286400c0c2001da80107001001400c01c160805840c04100b4883c0341e20a00c00c0000c002600301c005a41e255032220007400400d401c0c10b44e410000c014003688526045900c8090080b0030250740c0f0150000011400f9442e41c0c3c50490608034000e0a4440701d8018281c0340780200020003130103410b0411280c1c004018540002d0050403031038420744075800d0360300251303214001080300c01c140041940150701514007000c405c0f00c040e96458040e002c0d6038044900341123403040e00904001042030ad032100c1034400c40003004240740074281e0f6545608 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 48571155 1250 48569905 48569929
    0x50715021507020f060406110904090506040209060a120305071401060f1a030106050d05061306081b0307080307030c0503040902130311031204090b0103110c0309100801060206160e 79
    0x1039001d04410391021404807aa640c009000c3d1024010b15041d12410940d02c8401400040000d0307036801c102c2948011a0b403e882504100800900000701030341440356640e4411b0710264411050b250105e001450050b00c4a42101d43d03c42c2e0030356036030007252019103158000725000d56420017810022070071200d0a00c00c40e8090002c2d0240c45601038105554001607940400741c07060481400c10046c024244c100007900c202c58895135000c02c040d0b880c20302055004210500d850841814110081100b48010491081e42e042c00805c954080d4668420596249100c0c0b1a84110f60810080c0c0c10200f8030034540003038003078011401c507482c1907690344c6201c0482e44200c0114041e02c591800030300401459034510f202e5218114000c1c00580d52172040349001e03128034461154460f0343d40480f461281d010350130145949850803034075911030140c00d403a5030712580101d0040e44100c3d042a0850b503164012030a141c10b84903503600401d800d40c1d920030100007100e0310325094001d2081c1441d500d51981c2d111250322134 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 48572405 1250 48571155 48571157
    0x30d090b040c08010608032505100c030b060313030e01020319050403020108011d010b180904080d14010608070c140619060b0f220b0d0212010b0c0c0904050715 70
    0x86180034104030070030b51000d0b0492002c1d039050040401001500009603428941401c1c04003c4c0d400018200504030300160000402a011b020b242600d20641a41700b4108101c0315281400410608401c21007103100c22034042d40c01000c480e02d5000800e11440814103200360600440f46400d004180300389810150480850000d140014180119603021700c0e41c6004200004850315400800c651141c40d083d01401102c1d0481170124001c1e403244266103083c8818800235014205504142c1032001140d80030090a18903035051121240aa0884502880c100c842507a903580310ba0b104c41c14101c41082c41003406941c0d4298124a40c22031207418401c40f406140b408000c000c0c807201c1d2007002410703224035a11505e8011020312040240850501c100c41070118010761a983c0c41c0310680c4443d900c2c040a81044400f89804682804a5280d0350b00424005d05da12601d040300780c2c0d80c0c16850144c0d00c548000044540c000d0030310800c1d1424079454075a00144103400384c1c6c900f540c441c10400039014188074000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 48573655 1250 48572405 48572423
    0x209040813030b090c01170702060f0405100c0801080114130807020604031a0a0516090b03040507080d0c051002041206020d0b0405070e01230307051e04030b0105090a06180e030d09 79
    0x5c103181d031f00907144039075003001c881d40783c102c2d03191a100107074580c10014200e1120300200000030782008010301c001186807003a14001c0156040c2030340d004000c0329090207a07484e550700e40302d64880380301c25003c5040d10880c0040c4400b002000e603650740c003200d0f400045040b42c0110f814800800028030306000c10900000c5201010111b140a0803a8801d540014040040004e250b203030001c4d400350b1280c007060a44480d0003486070307a03480783d20703150340350214aa104122070300074802100f40c920742c8602c400301090b01650072100400484c2034820b04a120398400e020007141104080c0000801e5500644010340c210080052201e90110100c0c0a854080b20b06500240c000034420a2a68000a400b075200701000d58904e94034080030803030a108d11024140f8400d0000210310179005a0b80303d100c0c0d2407410314452070340780c07210340d13924025200080a0080d14400c204000008112a8251007804129417084d102e20b500040074142540042103280c0030000980020807200304141d44d1802030700c5520f0701c41c0d4181 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 48574905 1250 48573655 48573673
    0x120908030106120b100f052a0a021002031305010f030b03010c080a140105091f0b040306020d0b010203070507030623040809040b060c07050f0d060507080702070906030209040813030b09 81
    0x904122981c460241d0b05c0781e00c00c04200e102c9180d004529201c2d09080d8244913035134800b1540034546602403003114822801d1101044c4002050100d220300b40c1e184282d440300c40c40c2400000981e241d0040702d817024a204a000010810b642c45204041040c01c1517080015050f40351030301090035915081c002c0c9010900c5481030260b002030600c82d00400c0b20142031101415410b010020f54144806000440308460344000c5a402010b0128402c00a104070f0313040c5550345a803460507002035003200b032402a40c5868800001740720b50010044500056201015242460135940e40d240100103c1c100301c000480008030b601d41c0034001c1c0c2101da000e24003580c00651540b414904100c2075610362041b5602a540c2800341a54030040040c092059650032140f98102c460b0503004155030603503030200a05014204002c2c41030890300100401d001e901e081e82030f01e040f40e840d1a410340c00e40e606444020b4207ca10100080c01080c41180500b84a8030310091034952982d490b260f2000200307060b15030021503080340700f003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 48576155 1250 48574905 48574937
    0x90506130c08030f030406020304020406050607050105190603030203030406090606090c020106080f03040605030a0902240d060b09030a170c0f030a02010c030605060415110303010f0e010e04050d120908030106 91
    0x1d01001010442c0040d03140031000a01c0c0c88590001070801070107590044082400c5540301c1d04004080e01024040310703160031640c24024080c0405803411014821243c5541c40710013407501410041d03c1e09a0001c5146881e503a6428000b0400380c0401e0703070b025640b000046003a03811340c010340c02c01040c20342c00841d01900b4003480a0501c03600044903a8143d1080100300100741d00601900c0d8003005458001903940e03460300100d81804010381e010f00e0340e0902002c00c1304a610042c80541a0031440f12000c02966496104c028614420280f0803a030540c403500c1c1c0500003403a850300040555000607085814450003150152800115883c40800c540000c15000101c82d82440341081038005898180626071501c008980b4510960080500c03629108104102c16401200843c0c4100040001c4964944c0e54800c4600d090800f0701491000342040000081c0d4000003800d2603009076000000b504498a00c081c0680304860040c1b4400000c60311200c992000c00c44000c0510700920301034484900800d03440305 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 48577405 1250 48576155 48576173
    0x11508070f0b04080a120302070c0914090105040206030a150302030f07030516050105041521020a0f030e0706081b040308030604061e21020307030503070201030c02071a0d09050613 79
    0x1100300341007010f120400c0741100c00125034804a03000101c0714503496940c0401c401034031400e0406000c410701d60000080c040115484a0f0340030301e4840042c0b00d0f94844022490aa0b2410344010f503004006002281d1052a20390001c6901e070300141d0050002a0340b940424200b0351000308840da15003001c4801c10a211045c01034002659620084000c424100303800a406030041d401220ba0038200210385010b114001e00b5203503803d001c4c100359508042c1c100407801d4042d51287d1025400a052580c14207001e90081c0200c51340701410001402d512420850110b400c0720f402020b5107500158144503207151a045001403003d9401890520b69078585041800300395007081d03104510000c0d0044e004441c2c01606c1081c1d0007030343d0342c40c6480030150134001d0300080411400f4001a40c14012030400000b0020000000e11855200382c0f01400320051314282130340c407483e0038030540001c209401c050b030023010381e480010072283c8904c2c0d100181c248100d403505480d080c021a0054264444001c840042c818418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 48578655 1250 48577405 48577409
    0x7031a07021b1c06270302030a031104080318040b0a0b0d020706140a020a08010501110604062406030e1203010e0103080705100c02060403020c09090709110c060405030a1b030c02060c011508070f 85
    0x2011740c0340950496400a540c1d1190601d06010140d8802c8491181c0c03075141d0440d001000480100da444018801d26000c084003018031481c032440c9820341004071818241c2d0723804212051492541c0c00d040c04001c20b81c02940c040801294031550300c0c90329034259011420340038028149000010789400410f4006066041e06805c8107041c4141005140c1c40e6140028000c4d030b2150340003030302049005660341c51034bc2c464511001a1850b081210010640e9a4554015001a0106c0044070412200e03540b61030f0381c6210070700454448820300001400071031141c0004010076403040c800c40d01d007103c03460000002c643d010081c1a005030404000d01c000d0503810020410f12150840d030003500ca0038682c1c0803517520815803040041250700c600000045101d040f0540e10900b480742d099654610b01854145d8580d8030501c3c0240c00b01d4482c02a00da1100e080c15541e50040b64141c884404a1185400b00030442d0030171203543e44150340310094005e040a2650100c00148035220003045c0301e0342011202d4100b162070b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 48579905 1250 48578655 48578711
    0x10608040c09020414240307020a05061302210a0803040c26030915040b04080706020d030204150e04090204110903010e0105090c0108090304090203070207031a07021b1c06 75
    0x5220901008000e030040700809070080310850001c40ba802042030301415103040160300d0910100403c48c0441e0003040766a0a00c0c03003403042d15216540d0100302000d64107001006034010001000c00015849400386071180c01c0d1843e81101c85120030703a030f0340410319441210200c40d80344000504101d05102d06804441558143c048100d502a1400c4032581c0c034000c0b40ba078144620b03ca14181d00b2101a404121009008072410041d51662181c0c10756076035010038400c00006108045800d5041c031b01c1313442034506842e885000e034004010443d2080b10826100c040711a40709584458a00069035544200f0704c0c040032928100741c8502245007010708542c6060345e407908990400c4200030b140b680c04141254001402d007040b031000e03116402d6091440c0101e421041029200005000100f500028003400701c0b441012140b200303204c054021211840c2c250380c00d501503401850312100d001c0c000c00500e443e030000901202d1a8140d0124044840c406080742602e5007a502e0226030380740241c0c8548407a0000403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 48581155 1250 48579905 48579907
    0x7021201020304031d06040302061207021e0607030b0418060902010906140d050a090c0806010f06090806130305130308030609090109021804060f0e10050f0c070618020603010608040c0902 82
    0x41a100509802241e002c2c2c1806644000494071051b50350300156400b45070003500040d04d81561229080c070400003038450502510480741d0045941980101c00c1802c104408003408440e241c862081c0d000d040c03084420390f801a00c2c0c03020300c001804118203410107940500300102e000d00c0b0a00000d00150450b4102e0400c00080c41100c40c42c0040c990200c0d9040212a800011981c0d5042460f038000c00780c1080003051040e02c1c00e000903020754001200e90503108800031841e09143d481100b92600c1300c1500c1400040d400c483d001a261001c020b1030a80880e0090034040d2805080c01141c0356041001d41044030540004400d214684c240300000aa000210340001c0080c00d1060300000e40200d10201c402d5282007030400000d042004070380041400d07450140003030107040d0101c0d200644400750241e41040c0d0030729040001e0035a04d0304c203038014040c0708103a10076071400e0040d45581c4090b0070b07004d00242d905142c091541e40143c4a40005500a003515a920311450900c0c1c640100004e00300d40c000650140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 48582405 1250 48581155 48581161
    0x5010501020a0b101e0905060315010e040507090f06090e0f070e0403030e010f020a0318020f06070303110a0207170606010e06030402040f0603030e0102010606090305070501200111070212010203 85
    0x6000180e02d44520340228041c02e06a588030882c0c150b244440e0055402000c0a000880c10344400c454242c0944106804c00c2c0a43d503a0302041c5556920b0703078080d0726640781902d40108641c03007200038882c0c1c00902072802ea412060f01c43c00c50300203488074516503030000c0c1e585d00300c00c101d800c2180c4120950380301010f000d445141d00c895602a900d8800c0d0103100728801040c8040340405019a10625000e43d41800074064503449404100094010018807004681820003802c0740e00e1205003000c0510303a000341001081c4034144180107041e044690224141581e176081542c08a1101e009451008100c5e401080114141513491031040c0c40801c400459910420620601d41c1e04120384e00b070f43c4502034500325280e644900001c0c028101070b4103e80340712440e202c008070a061b40500d5081002c502a00241304082d51000c080b2003054640c071024200e6088600140180c1d8420700f203030388030003241c40c4d500441202e80ca0042800c503108280c051420000016403442141021850107010030841002142103207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 48583655 1250 48582405 48582407
    0xe10060803210c071a041104090b1602010e0307211d01120b1f0801050a030f02060f07170c06010902030c03060f030712060f05060a0503030703050c1f0f05060405010501 74
    0x10602c4500000700704200310001d82440011029102c019400182540c1c0381014410000f502c804182d070240c0341c907a50211451024202130184c14901644440c840100b030b600e000c0120f2a008400500101f1552244000c190160301000903054060050b61083c045184078440042c02c41c450035884018091074081401d804e01285005600a0400782440041c0c3e94140c00010000c0c0040f0010343d5118034848510080700c00e221200b82d800984540b60200566215002c00400010034030000f04071010204101d40141000c0b4060400b12040300700702806e1242c1581e03541301d40e091070030b04540c1803030001c1030341c00c0d42c01d100300415401841d646000f1480c500304161008840c0c480200581d024032214000016070751020070406004001c103181e00c0c40d5103400352514030b015001038030415135418206800705000d0710f0840c0c0710408545000b4000d61500c0495034064400760803030f07040c1d5440f40c003903141800c0c00f09850a8a0410014000c400042d00328100c0c07144e4030894101a140318081c0307107010018440751b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 48584905 1250 48583655 48583687
    0x1b030103060c050909011508091207110609040203040302030a0813020a210819020715051b0a0c0303030209130c0912080409150e0106030b06040b16060e10060803 71
    0x149400460120b002c1441c16016206480384000b00c981149a2000003d107545c03040c0d61003955559903680c1c103110398803005032140d91210881d0003503101d9181008175500154a50349030071a0344202030943c9080c8202a80040d003241c2080f03e0036000f680000905120150b400b010169001a00c6800009207100c150046440c21174140107030040240708003c0301c01c01c40e4003180d00207002580b26032819a2041d00c1e481d074880d02d0795290316081c058441c1140202d1550308955042e40c0d11013440e40c41a00b014150b805140e40c00307852040d9a13000e4050030b8100404102d58481090142d070190300d01596807500001441082402040001c2441c1d24001034610060b6000c440201191102044070b0702c038107030310704103040700d4401c0398065a0702c0d40c079040300b082000c14514518021511298a000c41c240ea07128021b4040e148107000050f803003517040009001e4003d5400241000380b441c03540340c40001d11280c0d00c00d01180c15002110210f0341c408220428420120f00070900a41100c9000c0c604114010860b9051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 48586155 1250 48584905 48584909
    0x30305030603030712110f03040b0d0513050a03020a0c05180105010302030907091505010201061e0504020f0412030305010f1401080604090203160902040602011b0c06111608030105091b0301 83
    0x40040000c08074480350340800503100007941010070202c000d00003000260802c11603000003980b034040c00e415101401d4010040ea02141d12103000703589401032100304000102b0b002000d880080042d4164840414410880c05030881d2094004184503041418092107440c020380c8081d10905034080320000d02c940e4000b0060440f003007803c001d616520380e804201d08000c100d420030710002d40342c10405601d40c0024909031080341d07800c0c1c00070041680c9402c54041e4910100d03000c902d9000c1d105c2010801820154014401c000411110703600707041c0c40d50000c80e1800b10500d41070300002d44400c018020201032080ca00010a5030034056003071122660000782c07140d8401403103944159910100c3c1015918148044951600d4100785609559211a1140001c1d045400f030100150f1900708404d182019070151048460710540710901d0001450352044060042c0030072002c2412414030035822543c44a1820401040c403411200340c5a6040400f48120900003c2c0802d5034065003100100580303142030700300d0741 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 48587405 1250 48586155 48586157
    0x60406140c0c0307030c0309120602090f09060d08030403120e01020904060503010501050310180b090609010c0813200603012904050a170a120804061503080301090e0a021c03090e040506010303 84
    0x5406c54904040e545800da6602c01d800e08551605400200005d984c02403602034811140b20796880e8108051255000d001c44103ea00300c594001c40b080450f207840040d5510521030315020b0014480d003203a42c0c061b18090141034816a4010550302c2e0103251500440018080036002003140f50715010002c1d544a0081d540040e0844c0c0d21100c804071f1218011028245a800c0070301c0260b14113000c5001540c81400f2a01180107510344040d15094a21801440340100780562400c44114165258124812603160710f000d603079203a03100c298065849490180d0300800000c440c00e2501025039904400b811b85403944080d00240401062103140e8a1081c0c0109031282c07200c0401000d02400c0c00e203494501d0607038003d4a10b5202540d044100b41e07104c0f00300c3d446184240300074001c01284100740c2007044100e000041c100e403070510041c05404036550155003002c061008844850780300381c01007680d808001403150000d07808000c4403014180c100c12210010000102060030038a01501d1b0283c4524060000038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 48588655 1250 48587405 48587417
    0x60c010b10110c090f01210203070b040e090106030803040803191406010f051e0705072706050103020a08150301110c030304110a030c030201031a12010b03070501050a02031206010c05060406140c0c030703 89
    0x1050844100ca8030307e1030755405000c071038196480d50840401c9411138425941d012a828002955000e418000d2508580d07101041c0e07415910b60769181d001c1c0d0b420040680010810724000440c03882028002c2030304005080c0b50500541c2407100c00103080801d0b1000319802d00400f0440c5246c80e00c129032a0f81400c003441c111460300e0343d0a614240f0b09044895001403038200d00342d40c620440003034601001c81054482c0c00c04222035903461005605034011005004007003260b1100042d84084e54800c40c0088100003000002d0358142e030103c40b0302a4103e0348088029600210810080007520001076411042c100c0340044640d1455460708001e80341d40c00002d041585401008100c2c00c0d1501d401b0b0300d000001800001d10310800e1840b28000c111180150348030348540040020554081c808903900207007554060340c0307020005011094640000350543d070400420018000c00b01d20309000c1e00c0d028500c294000b1500100c0500401c541c040f0103401201005820070103030b01803600000848102e154542000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 48589905 1250 48588655 48588689
    0x60d020301061805011404050402101202360906030307080c011b020d1205060a03021504050402030c04030b07020304050a0905180115090513050606060c010b10110c090f01 75
    0x30074054001c9038401110310300058552403560f03007560402070603141d041c559403000d481c00034108000d50b074007030351f019410415160291250620900301c0585400421401514212138140901c04040840910010000503035041c00b5581444854020a01e802250b40082da402c2c1800080d031644100c400003400303164005480110320400b900f02075105220500c0741c5241040000010703407914082038041d000140d00b60200e40b11060f241c0303d801d000350f0029155050541c219801e2041180d01107450100e001b006200010702c540d202c1c0010b5100d2042074610940765031441c03616603201540980710301c0035074200b44030611082d1540c808860032102032a0022505840d103034105c40c148004d0900c203407055404c2c404c0f443c00c0340075518100c004403179003403004001940e500c041003190101188001000764002101081aa1820101400f0055000c4000144400050300000c41205030400e2000111388001c0183c52102428407007246010010f681c10429482c10400074000c85d4014040c080d60308110b0205 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 48591155 1250 48589905 48589909
    0x30213091106130503060106171b0f090d02090703020702190311090406140403030e0705010e030705091e1501080606160201180f0305010f0e03040e01050d0204020702030613030f090509060d02 84
    0x40d0200414018055545658540304010900340480c8011124030f50410041400100321030101c000c1107a9550381c7c68100000d0030503007500d8cd44000d0304290b100100042080140e82c904001d035000d00c500341ca00681da10710600c1445a01844104c841d070200d94140d004001003000101c2e58a010001111444034903515843c10800900e004200700c036031911044108000c041e01540032854060007441200d40142e540e000440329904603540d62909600059030420213828004203094002042043c12440c0641002c0c801c00c1ea294101c4d045400c0c2e2a0f4020103140d030b540c100981a030000e4059175528a0041c00c80c410303102d00704001c40002c1c10454000c2044060141c528140c44c0030f4445095444140d075030301e081841c0030b880c11084422207186001c580c91151540041118219041071400d561541e186c03000b0000e5a54184000341e802c203408110303210040c2c0e0140f01041c0701d0b0400c194689408403c504005141c042d40031140c605000001c202404180d2f961011a580824110380b04e018081040c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 48592405 1250 48591155 48591187
    0x80a050a2402120405010501080706091719060b09010b07081603021c0201051e040302070303030b0a0308070f06050a06080304090e01020d05040308040311070b030f15060307020106030213091106 85
    0x303401072400d00c04550807441e440e055414500480c0544000d102c0c99890b100065203801c100d114803404280202410841e280c800c48c08440120300700020f40344c0050140f020030044155508084501e6956124404003e2400000a030b0150250f41270b81800c10300141c0d5910441c1c0b18046484404424407045c00040501c20005800d40d002d0090303210100300007402c13002e806000252811400c01e0140d11904849082c105001032045030590b0040c1699490758800341c0045c03843e181c0306504103ea076200400811005402070914902c02ca40362200301400741809011503101624542c0400d0030f24a003040941b10000c155070030b4a11070a00052035490300d0f0f4101e07009100c0c140c5c550104d141050104018144c000141c0b41c80340d40a611240491000651081e45840d203500401d00b4040041c000b00b00e403000117260865000c03084541144014000f800060200e410132140140141e454001c103000f1410013201030f1319080c00c90b048c1804000d542c0d55440c0b10390301c240ea40d458040c0002240d00300d105c0107150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 48593655 1250 48592405 48592463
    0x503150307210c090b010c02100e061902010506090105100e06040906090605010f03050f13030c0f0506060f0303180d1a010303170f06030a08030703140c030402010306080a050a 77
    0x340440030101200e914101c42c1045510042e180352100d5040054007585a005809046405035980034490101e50308105610034502e4101040040303107044807600e91110402003211389218021813050007201400213094a90090010f0301038040d003c01000300c2d03290041041c046403940d040500010709894045421030060794004500a41132110006401495902c598242d81082e610113106000400b000d4066440c1903466a00802082000641d226800711509060a1191030b1078842c8450b00e48401024100d03400d0103076104e1704004180007031071400217603600c21158107501860502d4040d04030f112484d244200d03110f000b00301c845401820023000f40c0c0c250340900b458071084481e6503101d0a0061012401044500b650342452020480301031440422521524004005125401042d034402c0d1060300094001802d01d41c440344c25848003400070140d984603600341c0000030303242d1500b40001402d03903560b0350289600d5008890310102103400810307101d5059401801c0b20b040554204da11000703d00c0c0b10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 48594905 1250 48593655 48593669
    0x16080c03090c040504080403050d090308030f0a06051002060108072c0a060302030709050402010e0609031009110409060504050c1012020304030c020a060804030e0901050303090d02030c0301090c060305070f0503150307 95
    0x404110411200d44090010348e409141260310420340d1090548a00700a4000509030440c203200144041602c0300185912242d00d07240418042d581e200403650b03803210058182c015800240050100c900e082183c0740060131401c0e84507075004d2040c8544080c4a00c0d02116001c00c42282c400150044e640340c200400550380903045030082c913510703920a001040d05450490004404e81865160340c0b130302d101501c5460b1402000703080000c4a10803420002d12035068110b031540d078282560489582c45110b030101c0c0b01c0c0541c20101d1146064034009040401004556101e50083e2407a40c03071b1554010042c0541514101c2c00607a607840d1820180ca021000080003035001054401c0822150ba00c0302a0034001e0b8401c0c1c44e10200e040c5440b00304200e2207003d014954155005201d070515918082264060850000d410380d01041e80042c0070a00792800c00100781c8404950440070400c4662521a0ba03078445c6051411407041c54001c3c0b00100b0138030018007940700111003030340c0d101920340e8240000340040c03403c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 48596155 1250 48594905 48594911
    0x804020315011211010f200a0c1215020711150f07030302090f0a031e0311060a06030213090201080708420102030405060a14040801140f16080c03090c04 67
    0x99888000c40503050201c04655074044c8540313200300795000d00b8102060720f01da51038a5402544c050620308400400d1007030105144034402404022500c9400703410041e28603d00d5507401c006d410705120041a440720b2507941c0c1d040c03040090300302080c1021248000d44c90200d44559000c442c1d000242c90342d0003107200000c03803000c000803080100341d0141d00400355254103490071034121100d402001540403541c0301c0648900c09418003070300100604e044448100e072003810300a10500d16500240d103884012540524080e07960301044c400e41c5000c880300e014030542d001c8188561030460780001d11054011b4909418450100c006c01c91403250160307000d610304004850000d0180c0d0b00602c40c001180340600d42030b0010407419070945554030100864003a148050810b0f8600b500115003210241c400c003804c06410761081c0004918030400317008102a8071050041186241808100c81159480290082044024181c408484160856050307584151407001194030380d80d6481809003071000c40c09210f0781c0585 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 48597405 1250 48596155 48596159
    0x40b040807061b080601050c120c010e070b0705011d0a1205090618090a02120118020c06091605040506031902040605030a240e06280204030803040b0a020a0f080402031501 75
    0x8580552600394240d21342c2c42c207640d91501d60056070540302c1d42105c0500c86d0080340080226900000090050905581c00052004000d0542c1414001290041c201c600400070f20381302445800d00800d142c52010604059110801402c42a83ca880350b4030300501001403a03c014030305600940a031100c0980190082d9900c2c490040e007030b01c140004c007151764030500382c82000c540280c20034420750301505c0c141d0070b81c040182d00b4600078881c0d8542280451100c20780030814680b25500038440c06008611480091556036949180e13105910403640186000c8e6280c0b80800c480c0366000030b580c2c402c1d900710340006051801e060010401600003608155010700c0fa8005880070491030449004955030307102d490107403414000d42d546040d41d240c5480031086074408404204030900c520b155108001c9010340800c00700c40e02000352801e81c0c01690050300c1d1001c01000300010700440e0300500780e108490507011854210640300c090640312040410000f0050000c000800f1502e0400200e0f28207401010003441d84c3d0307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 48598655 1250 48597405 48597431
    0x1b080a0c080d09031212022b0e030901030509100606090e0610050405010302070609350a090312020a05010f0903030e01060e131401050a0203061c1112030d05150f01050909040b04080706 81
    0xb01c0c05e0231f00211140541042c00c014182c161189000c5220b001c40175601e002c120700c004602403c07015007042058060403030704031030242031441454010b0000340c0358645407501d846440c00d0f000c8001011503000d09503c0d4945540d0f6039000d0111801d5410900b401030311255503040400c01407000000041c48080c111039440701030b40c2030282001002000e60010780c100c0300340b10b40c1c03a60301e13000b07c401c200c0c04540c40c02d81c1400040c0320360f1050f01d1006010f1046500c5400c00e91151070075121444104030300680d135147c00700b0505500d40175020548090000a0104502d012541032568070b0003000310380b00b80b50781da81d694104451550b8041d50b0240c0440248086e0071310140003c025407040d40c0840c45001805d00400800e003201a035020b01030740244a941c2260303800070911400c805a00000c08203070108204100b285e400610a11b13020300000c0f590603405420030014841e05541d401e1140341031140501208169603144e2907100d5209a00c6422190309403103d2404442c1c5014181c0000c100505049004481e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 48599905 1250 48598655 48598687
    0x70509031b0a121106071505010f05011403040309060f050c03070c0e09060c0d1d160602010e0f07050f01020f0d0503150901080d0305041b080a0c080d0903121202 71
    0x80c80c1c12035221000c9640c030207080707152140c2520000c014403102070b0070b02800e107000e81c003130300c07480740075507549045440303603031105002c80c2e10907003000c42c8003203080034180469640301040c5002400c40d207102902c1d505003900d01601c1c41038244614000c110202d42420b424a200d00c2c00d1f81c04410b00042100d0315031603140780c100c064070800d000e10140c2480c00700000f44401c400091082c001c40540070f6141c9400c42c18072102000e48506c000c12164151600060000c20714108442c04a10b41036542140d8401e081180090950b0b80c610061b64480d4050500c80d043d41c540481c580c822540121000b10200d642400183e0030445e004080000b280140340000307492640010055100e64050502604440344074010000c404500b80a0300c0e0301d60b0b114044d0022220b0090b4001c6412a02503800303a900148400d25540e0309100f01e4116041940001e4012001c10882d0200b00d002b504008000d49100510740d513004060990307521004c1c12081c840440c4a6900c1d005603242c0001006600301995942801d901c04041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 48601155 1250 48599905 48599953
    0x81f0803040f090f02040e0c0f090d0501020706050603030c1e070b040605070611030408040504050a0e010c0c060518060f0411060301090603050c010906091401020304050310050402010807020303060607030807050903 94
    0x310f5081c02c4070803808030400c0c07003201c054440443d0050403548030001280075940140741500ea10110404c0b034200e01ba51050180d03050b05108200150b079a460a242a170192200038000e07502a90060000400080300031541d54a84040c1c0303a0031405803d0b03030b050740074a403181a41c8113004619000402160b840e41c42001071802c903006520030300c1602042501034005100c11103001e04001c80510060020f450207420043c3c1052000c07601050803041c02c1000c0d0700f1200c28800c0f030000314030b00590fa481001014040c0350703413003009410360341d10188034034020369190000245640000004900020204528403805010740900a0001600c1e0742c4c403012803400404650209842500c2400071000e00780d0300c182c58803400c0d07034095595260242d151052285000000c0c2c0da00707505500003030001080f6a2410021403095440b020800300b850b05103400050304000d40508843d007103402c2082000a541c03104c1c012540180d03414605000e00c0e580d40e00045030140202d201265040c010540300c0f0030310720386044140003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 48602405 1250 48601155 48601169
    0x4090204090c0608090304030309051003020c07060206070912120302070309030c030c0306110a0903080a03090204140f0f070806010807030905060702060f0c0901090e0a0204121b0e07081f0803040f 86
    0x1340d840344850250346c2c0c05603110050029240400c2801325042106079000102e03c5420094104559903040c0d0342800c401350400801039201d442080569503004080d0300c010040000811006039043e141d990301c001c0d80f0003c0405140e000684002050b1050b1842001140c000403a010440d07103d2514407207161803880161006402d00c09101040e160f100201c800000c030f203071258103200d45035544080203600010104130a141d03079925042d0241c0c51724090185a100c0c19880f0744020301c0d01c1c12142d1032140c00527003407040d040030100400c210503822291058000300700f401d000c0720a41c0c80c0c130b8040300544141c1200400e24041c240c10700880c15000203800e40514901c41d60b02400d41c1c0e1313407641c200942c003c1c90700c494005801c0403810842000c0030402d40d6004105141c0251900e500c401540c080b010307c2a0007110520000f0344040340c40c5500c10000b8014102e801810303925420001001084694041c160840314200c5500016981c80c0200040c0000c080e460196511a55540e0001d2440e410f5445421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 48603655 1250 48602405 48602417
    0x140d0f03050c0c15041502040b04090c0306031a09030f12060306010509150409060e16031a0403050318011d010b0301050609010303051e0903011a0319020604050f04090204090c06 78
    0xd40b0a001c01c0140c520891001c40200740703140700700103050803001000d00f040c3c600c2c4130f0300d868000240e009400100701501d03801c0b40940d5524078000c181011a400403c41c1c03000c1610744502400010801c4038020034451400310700315040d480f004825401c510440c82202618800010950080101c024800784140000c03400d039440c50380c0c0c0b0b4081c0034140f0001c0b28040c0e00882480a8a1814500781c1d0115602034054840010303942c601c215014500402c10318070300380342141100200308000010034030b500c0d4090038900c9280107041c19a0017620600003d004d480c0d101c000c000480c0c1514009511420003d122808801c280005487c0554000e212241da103034029420040083da09090465605040740c2d80364ad9007500d0103540303560081e1442261039072000890b004225802090f03030240100c000b1080c0090644601c048071404040c07404030361411143d1001205c2680c080580d9075182583c0444109443e20034407441030900007002002d1081d8000c0d4080d1a04000106002c2e00d43c2d0543c0c141e52198840d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 48604905 1250 48603655 48603661
    0x904060518070501020d05070302011407080609010803091f030e0105042105030c030705070311120a080a090515060a030609050307020a05011404270207031106010603060602060a09140d0f0305 84
    0x7503611074209001d080d0240e40413000540c16184544001c14042d402440001020b104000c4d03c40308006050303a02c200003400a109004062800d181360740d00600700c0a00071880c0060003004100d60740400c0c0c810760035801d40c060151804c0c50094020036111841c000017045603207054989414104829000d00523400004c1c1402c00d003c81c0a441241d02030510400e0b0141140e8810780304a64543c07000c0300860410250b8007011481c0d000c100540d821031402c041c481616054841c0d0000c00323120340109a044841c0c03c0190040125002180f00c1d12220740c90092080680da4400c0811000301240d4401480f0354689542c0506000000c0050300906100b101c49040c0c440d564001100d85428401c40700344041d108010400001c1003050404443d1045003880c2e10060300d481c1040000ca0300a103d0942c042091500042000c070010300009024203200c1c1800c21603103084c441c00175a250401081801c85981d40c10203030003442514408500340070003d404880c0c411103d1f110003440e40e6800700c00000464240008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 48606155 1250 48604905 48604951
    0x30f0b01020f0303010b03090312070309020102012d05250302040302090a050103021f120212151002030711030a02100f021515010c060b100f0909050c120705040509040605 75
    0x1d200e005000b008500b56420040c0d808820307070024020010900c401c001101240b103202d076003644034a2486d03c0c00940044070b03000282c01e4810410f1050f01425030000d11400e1200000302c0c0808a0880305400a00303952a1200e4202c9800340d48594003078041240100d03140071394150000c1003900d00c00c0e07440b5501c07a02d40d00d442905a40003804020b40c060710342401e840d682e030308188401040d0f50143c503040310310401e2905168101d034040040d00061a00607010066180d10300190031202c0740041c0c45a135051075010f94002d4903802102d4005007a0441038440425560f010408800120340040410469a040044c06001d01d1360640c03601002d030042c1e41c064840e075079044c1c0e25148103034208001e0313090f1501c142e0011034090281100071034403244c0e20760003083e40d5181e201103184107000f07035100c103a24041c0c8900040e080d07103d294070170100b250034003080098070700d000f1041c0d40040c03580800d00f502d95200c007041950302d8002e60300300581000c040f00400c803d000b0f45411240c00381001d50080b1206501c01d290b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 48607405 1250 48606155 48606163
    0x40612060b0a0c03030902061602040c020a05030d0c03140711101a010804020402130902030106030b03190b07020f0a030504140d02100503070309060e150915040803040c0e07030f0b0102 81
    0x10489500720014824411000e0144a0069055200b8500090001c440382d000580e580c00800460315001409035114085082620400701040c0340d6000902d407440507070b603801e540c901c05c03845200100d94581040848a03402600605c511001c1c6c403440c60103078500903200030080350000e000441c0031f214110500001040b94440c500e054240592107404984102d801990034032400f4000700c1c2c02a43c00c00c14800f540d2032400180f0f01600c1e90040c003590703a515040c0c7c02400d8403c0c440c100343c03003500003000240101c90b01000000318668130800c180750710740e10b100050b0b08011851400003c14018440d600003010b07403010080007951021008481c40982600c04e1000350460940d000b07400a48800442c03003480e004901542e4016814070740810801036541d81d16050b2035454044c80030652194007112441401408140d52004160004008040b5180c0b0090320102000e403001e0454940000410140a00d40c03101e01c0c05002940c001181c541030419009004007456060112401d10b0320f00d00602e590701c046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 48608655 1250 48607405 48607409
    0xf060e09030304080703171003060c03060e18010209030a050d1b0b0703110d0905060a0507030b0a0303032003090f060603010c200a0f030203130902030103020a060e0102101104061206 80
    0x40300a6096968650360a5200e0340604816000c0c800340140301102c01e2110b5032002d100d00401700c07803072804a2a501c0c120f01a51086c0c2524400d0606091040c00407001c5040005d600c1468900800800c41c4042c409900904c00c0c7c50105805014401000050002c00119582d015560781d0310360450323030700980c81411718100340c0c84024202d03900132011038060f502c04d4120b00360100400303503918030b00b100e0550761b07004464486a00b00e0b826006101004031480082c81141d030b2094403401c0500050046500003554035840780401401d0550345c408140501510303114591110b0400d40700c0b00e075a0304000050f04d90303413462030001d81c00c40d1140800191941c00c0c180030b5041205620b845200c03000c2c41d80c116998000700c7d41c1340290194032450b94140041203c02e00c840f011203010f600039641d501d400340c409e5800a03940e500301840082c010401000181c1340c0a038060308407010b80c07900302021504000101d003002003a00303860b810386013480300b015104050500207004444194454102402c50014a0000e40e0750034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48609905 1250 48608655 48608671
    0xc02010e19030b15031b060a0215190b0f0a051c0812191e0b01180e06030601090603030906030209121024050312030606190909060909110609180a0f060e 67
    0xb00d006c0007410708044028200300d17481d900544041100d010a40c2c4c0c1116030844509601c0c0700c603e0155030481400c3c3c400c10b090000d081d501e100740780c1604804240074180300d200d001e014801008103840d0401d401440281c0195000c18030f640d580700c2d003c9a403941c5220a0745c400142c500520000041c241aa10420445a42c0b595030071440c003c032942d106c0010f11840c2c2c2050705004a000d00c01e540500040200f002508030030340e4240860801d60141407408005800004a8a01c1e006050002c60742088003334007103a025103005030b601c510071004580d040340c032405002c0311449400420307130301c0d809150403003210420b2002603014049104019201006042d2103103e41541142c080301e6012805200119400300c1c01402d100d11f0304e40c4042c0e49140d5003201e130402e5800101011018010f1160318001d04009158030003090118504030340707603038a01001c4001080d1003000c0010f11703030645444050720080c2c0070002c604c90341c0ba18600440d034038010341390b003100a0002d1403510b0008a1008405504103004401c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 48611155 1250 48609905 48609943
    0x30f1101090b0c0d020702062101080d02060f070504120501060302090705160f06090206030112020306060a0b12150604030308060f0d0308010608060301140403020d03050906070c02010e19030b1503 86
    0xa0b01a40c0f4000d54410202c40c641160204450f20150f1140c0008004040c4140182c1c04001c1c04d50484001020f410b800a034a5600410088a6030650000340540c000540c00c200c40119154820255510b108a030f11440780813041c0740405041c81410350040c41100d0080e03038200b44c66a114441115684182c2e000f42c503906040480d480c01080c14500801030152044200107024481500040d5840d0800d07409401c6041500c3d801b0800c5060030300c4220f0308014161a031401590500700440000d000c0c2401004080c0b880b0f900052403840344a400e41090a40980035645c0d4503140c1c10000c000c254202c0300c1c58052840640c0c00e2550b41480c00742c00036400d0305642ca003506030342001400c59912401038183c0d0361664950820717159003140c040d41745016510a8004210204545002500342d500050500006030043c5d01040f805a801660f00070042e030303091030005a0080e14000042d0201c199088001d41c95206910100030040001c0703140f4000c15182840082c000c44c030300101551001c00041c10300e50481 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 48612405 1250 48611155 48611161
    0x1902061006080907090e030307030b010f08060d0f020a06020f010b060a0f0c03030f0507090608060a080606060906040b03010915090c210f0e0102031501020a02180405070b07030f1101090b 82
    0x40715015503604803143c002610b109940d00c43e52101035803059000b500d46c0343c0000090059540e05441000182c0750203080c4954180e00d40c1c1009400035800504541c0190f00e00c4e01a07104004c41142e000c445598020007042031180c407008001c0d51840e103900400402d42c81c212002e41300e440c100083d100040b070b603661085065813054a01719003c02a20f0002c034181034840b961b41402d0034103405820310680b000d980e100c0d2500d14001c40184803e4000d00041c0c0111a880800c1c440c3e0131000c1581540301a00b51207041c0c0e5029281b01003002842150300003111a07070084000300c2c400e41320b034120550380c2d08031103080000180c8961401c4100d546031943c0c00d010170003010842e0401000c6545e11144191030714030000c0c010031868104c0c3d0a5581030284200282d40c00800c12a28400d80b1454051955080c4014200c0420941c0860050400c3c0c1005030b201a01400004007081410070040000e0081d100f41e258507030b0158640600855a99250500070030780c600001e2010483c14820b80c4207a41d0031044030f0403030303403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 48613655 1250 48612405 48612407
    0x6030c0d18050a08070c0b031005060a0e0a0e0702060702030c100f020909041208090a0206031b07050703082706030a09030e030706050c01050705070f1b030f06021902061006 76
    0x840c060030328190007458a020503002c11420300803074104034007600c059a529030861400c0d28100000d0b07084031840c00c4d814010f06c00d0401d48003071031000740c3d0019640b690740c620103604182c40c0b008407103055507403114800e0070204205080d0700201e8022502502101c480d074584000c141c0c1c8a0103940b05c0e10100d03502404c1000c1a0fa09030340c01500902602000051800c20140c01041c0380da4070895040c0d07014080c4220903d5503681c002c400d5a0700001e940050a11003100c0e0b40020318520001d841140140e418044141080d50050210b07180caa50190445601d15600d203410b03065904248440224841400c2c1c0a943c800a4025109100c101c01450b0621310f40e01d1401035801481c01410640070041a90182800c0d1388041100c18040c24140c1c8a40d910341d4041e51101c1d0944e0f0b0002c240d2810071505006100c0007a810030481e250030341c0d0103070015403403658407000d9060490140d88060070b1280e803440041c0c18001039600070004130342c1186403e03845041010b0700b640e80341745c184e0b1004220300501204210075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 48614905 1250 48613655 48613661
    0xb150a030b150a03050610020102180f040b060a171f06120603050304080718020705030f0f070206070f050d0207060f0f030b0402040f080d0912060504141b0301060506030c0d 76
    0x1200000c00c140b0321407211140000c016000303800b03000e0200c1e035650240202c5141c444480d440701c403130030720081d480c0440000280c0d8a0f5000320760325034020580300820b003140d681c82d03400159000301c001d0301c3c0e103440c2e070400c2000402c00c0320280c450301442c42000c400b0a28419121000107030003503101c8218034030240350420840f641c801c404c3e04015016500c0c02c0110010b50148014001048014020403000d41018072098448602e00399182c00c3c50301c1080300c1000240040300743d91401030401c01e04c41e140e03403003007510202c03034413035002c00070362014001450208200144240c62221070040c001c991456400300c400b6070b910251406103101003a203a84404115503c144100c18119450b881c01142201050740800c05a0300560022540c07900f842d1030600110404101c110784e07055207440c2ca0b0781010325002c100c0359202078510380a0038a548910004080c0300001158030f254401c03282c1140c0c0309110000014208c54a0600440c0c829400c120001410f443c000b03056034040c1d01c803201c489180004461085c002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 48616155 1250 48614905 48614921
    0x6050421020607021f020f0102030f01050d0311010c031a040506010c060b12070f03020114030c0405041d06130606080d081303030b06040801020d050f0103080d09061d010f0b150a03 79
    0x444a4108141d0006880e03540340101c1705044070050114007030021001070700301009054048120781c0705008102c520702c050701c1010f0440308291030b04106c00341c0600702100c400c41c070700280b20b0307d40d82003522102c0843c4d0301d948079140d100040c3d0454000f230542e0200700000c2d1001030b550742d03002038110b04500d40030410581c0304d1290b040000701040303000c038141c0200e2381c141821030b48420310303c0e1700d03059041055580006000d00300f11003095001c0c5c0b56207030640040f00e050042d80912401a80e4900c1c08101203403601c82451a65414502151040d142c88010102c00c0180408101c030303d14140f23080018101800140d8071170781070540d1121032080da14820345480c4110b05010035010903407100b000342c43c00e465200040c00940000000980da9094218a1070191b0b04090400120b9041201c01080880e071180103036560b068507018085104105410b000c0044c00c40a91003500f56801c09600b0382d1112815030045181e40040e48040c81181141c4e020010a818100c3d6003070282d00003044014509403103503200c000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 48617405 1250 48616155 48616159
    0xc0509030a120e03011406030f010513030503060301150e06040621030809031b060403080f100512100c05040501080a090b01050603070c08070f0318060f030c03020412110a0605042102 80
    0x703850f100080c002070940c0c034030301e000c007000d5144001130000c00d04091020554000d03141000380024100010780114011010101078204100440424550360307080d0850b20350015400348954989455840d0703030007000000c1d81d0441c802c1703181010010b801050007007400201e00300c11141c8039003d811920b05803076006001389148290b00003041056000503c290708044440d0810000b00700c3d0f40f0342490050030b1010b01030701100d00042c05008022244945602850135540281c034864080c80200c0303450342c035000c3e01c06103c00000717003084928240954480b0150044403026071f2004001d07280c0100901c200c4100d0040648940c000c1001480241011070003513402c1902403030015602205078076042600d40207540d0031192964108102e00516904c844103091a10b6100c0c01804514030300fa40240034801c04001010615403036021801009009034183c5004006460024000100600d4070040f80c48443c43c0552083c00c0718603000c0b5540344550107850540d018100041054580048200fa140844c05012030f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 48618655 1250 48617405 48617417
    0xf050409020c0105040c17100f0e1b01030f0e030405060f0c060a021803060601080403120603020901080f1c020304050405102c010b09010210090515040b0601030c0509030a12 76
    0x9000c86840c40100146001d690002030981070a1620003685070365580900d140c1800c200b81d0851305940400d0800045c102c446001503442900142400941209181c4c0c5800340149210106841f0707010840c03100901c0240c5c0d0400840500d904a0421585070890034411507005000074801c82c20460001c05015284020142c2450444001d41d03250060444441a00c503402103010780140c60b80218050030b03460110041c08291518000080550f01c004102070100950001c100f1000340d007550015000c4c40e000f500c406400d40c0c5855106a441c041d05446c8101840745a0790414401003008614002080590140d40342601e840300b000007820740584032284100c01e0100025802200e5030740010340382c01322001d24401da0784d0110840d2090405034007a00d12043d080210301d141e0303030f4007089040e1004481d00740000c116046d401e24900d4040c0550707242100f46840c106000520a03c85a12031040c4002d0703030280003480140000302c400c7e0042d290821f4041d403240c031030b44000500484d20380004c00450302e002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 48619905 1250 48618655 48618659
    0xc0324060d0c0f0302030c060901020c01081512010e06010609030305030414011514010f020d0509040504060e060906041403070b01090f0b040c050a17010e0402010c1713061e09060f0504 81
    0x42c1d0102225900c030914440582104004509041c000300c10405403c132032490408040c0d10000c1e4031070800c480c02504100e40342c000591725541c407a101d14020400504458100740034442c51038001e003d8a000c03c0040d110300000011594455a5500700340c1c0e601d41d486034110385859807001044100100c2c084015500c5014040e401c01d400c2000000400d40650354045208500d00050035009204000c0d40854002200104000390032100302c4005aa056030000b695664034180500185081414118540a194288a41040c00091550003107000c1c4620792099010a80c00366035034821100c1c01040005032100402c100c08495000305081c080c88030300802e4044040001404584004c3e051002049000c08c10703513413240c0d220213241d86416040880c1021541400e060301d0b01018000c100904004c0f580782c0c0c5d281005a150130301c2e000344544d02840c1d600c07610049545454800c440c0545000520b00c01480e200080c80d00c038101c6400e805c5600c501345414180881250113800c8200c007030092000c03c000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 48621155 1250 48619905 48619913
    0x1030201090506030a0b1504051e10140c010204030b010503100507080a09140a03120c0315030605060a090509150c0a0905120307020a09050106140a020309060912100e0c0324060d 78
    0x74047d4403441c0c05c003650380701c0c00c0408010000348503088080c1c0c64820900d2180d102d4a420400c201c424030380d0b040880c512007041e0f02103078051085200c4a1410350006c900001003040d9903448606841081b0103840c6250f400780c000000702c1c2c50444044001800a0300402c0407408194030500071603020f0100e20041103074075801d1b649485141c4500f100018090307101e40500d40b01c00d100741d00c0811910b190a00080515103d5045a09071901001d0903080d500d101150659540c030a000c4010b10901a0034403980c81c100007030780c1d2100f0420060ad07952185880014400e5101c0e03078101d0300107010540760300f580b0034100014001d0180101c0c0302a00329100401032800903903501014003006202d03202e400f00d91036042550060030a050f41c0d070002e690010030b12513800e03125008000e41c0c5082900341e84e0a516100484006a0346202e008100f1000c4c0c0a4000d107800c4544603500403480d4401001d0032203e0503844401410f40e2042880340101a458040701000d0001c00d0150f0040e4000d0350060054130700c6111515 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 48622405 1250 48621155 48621169
    0x40608011404060c111c050915070308010b090d1203020d020c010504050d02060105150a0903020402310803040b0304060212070207080d020123060103091506050f060301030201090506030a0b 83
    0x10080309407400c00104010421503000395102a440c1d0328082d960f000c80904140da0b1415168010842803000041c0484c143d481082a1096070384004e00c810000001d80c11030f00611317802808150b000404e060700105d84118484201c03251300e03802411140c0d910500b80c0380c040302c01ca04210b800741099006c0000c1030440509001500c0c0140712071000060b00c3c01d051030f0052030204140c03030701c1e41950014801000940c2e00c0740c80000320003820010140d560002104211948c10003a00005c2d032042c03010850a0351185046490030700d6a43c00400181d014000d00202e04030455144100d0101d03a00c01c000500001c46c0c1c3c007001c0c6400c14407480d0050304201600713424030048141124100d0050348003100420526074104002c2d03e052440f0300007001003007045d0900d01c0680c5644d10681c05444000008581c6592080d848021425000034402d2aa060101641006004184502c49c401c2c030b40d0b40800341980c600501144e04980e416120b039a4203034500f2050104a800040550000c180d55405c0601c254507804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 48623655 1250 48622405 48622421
    0x14030708030307050414040606020604030f020c0616231009050a0b01140306010b0906030105102f0c031b1c0803131401050403090b0d0608010e0a14030703050d0b04060801 75
    0xd213070700752114142154403024403920030f03039a8461070a1140811225030003045854005805281002944001d07050583ca0050200002d40d0401c034000b42144038003203029040005180f040000c0e103205485084000c0c00d002b410760425030304d41c000e18041c25402c80e11394825001306200d5015544641c88a450f0400840c400b40c2c403a544904c81d03114910428501030203a2409052003005171410103040c0d01c0400d030540414080c6600455400e101380c1b100900514440d01c09400d100315482003a424400185141010a1541407252081d03030040c1c10300c0c2c6000300c0c085024450f08000842c1c81f020400400000d81e078100350b0008042040d684460128400030001d5101e10707904c880c01c8210b24110714003130312644283c03061400281d15080038807001079400310b402170407038200090350f07074503481d96159100040407107510505440d0300e007000e884e50003a0301040600301c00d8040d10695591501c082740281d168030909a0080c0090000c012005080c101030b4000344a10002400020f039103900c820000d42110810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 48624905 1250 48623655 48623657
    0x30c11070b0d0e0d1d04020d09030c0627080307030207080c0309010210020403080307030507031509060e090304030b18070306050c030402130b01120f1401030804061e0914030708030307 81
    0x3604880c900b0a50003000b0407141514000c002c203100040c0000c1c107100542d08680b8520010003001079007952180c0540302e8912212104100d106850f00c1c000d407404103180c100f103542601740500b60f1040708024900051030b24441400001c40d00c11542c480382da9034001040344050540c244000e42c0414401d202034940300700440d00550703407070300104006481e080f6090007846019004000c1480029500340a070703034006046060200320341e1903006042d000303040f0640000c02c11001a440005104030a600301c84112030505405d8a22904e606a041e912272145000251840b0340401c08100d421200b28003c10302d0070500b1044d1104241c03a41d4030042581d40503a1a41e4100d0400b00610055241c00e00f418192644001010070000b110900060f0580c0d89440c0e90803503031981e85900341410308842d08030706000c9400c086051410343c0c5901c2c00c0c9001d40c106010b1100002d07000e40040d86800d040213034a00c0d101c015519520451454030000c0c0401c4040181c010703030103028103400001c8019040024500800c1c003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 48626155 1250 48624905 48624907
    0x101508070806090f030715090321090201030e010b03060115022b0807030c0f0c03050c01020708070b09011505150d06061e03150e060a03080d0504060b030606010f030c11070b 76
    0x1129803c14a050010900104d1a41081280c2400988004040b9440c00c1d408a804101400d0341d04054428200d520341c101d000016400f0010f908509550042418034401d80b001c104400c000e07402c180c00c94008a0100c0d415500481c0188200004081d1402c40080e8901c121220134441e4010602103024081c41e605000c01d200d00c200c18215004100d0542c0701540d0b29042094071140c0e60000d00d0030f583d2039409070074804c0d030041402c2414801d10842e80c1d1070380124000c0d59200c0076481c01c82c06072340c4080c80030b03114411aa80455240d40040c026040641c803242c21044801341484100a0700b410b0f26040e0050001040100030011241801400300030b00032519407140f0002e1002010801d44c56a00c40001014900244020300d08202040d1030f0969859124000050381c030300010521070007654202510503d00414812851165030f005035119510411080c8600c41c0c121044c180da51800b0303070f03070107011440382501d94083c94400d60010001c44510b1078118029580c40300d41c242403109a42002410b100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 48627405 1250 48626155 48626161
    0x240f070b0a0501080c01090306020f0f04080601030b131a07030209100804020a05010c0302060c0903031b010609060e01031a2a03100605030903040311040609020d0504050d0809101508070806 83
    0x1c03031441118014020352026201403071440b00002c0401406000c018881c0c4c2c1e001c0f4004c00c402c42c8003010b0301c41c2454180513041c0d603144c9030078055540382e02c00d110440e80ca034200381c00143c0700c5101d6000c000410340d1014900d04600208192101c2005009111008160342440b00400301c1d69140d00c1500d44407425140d402c12420301740184010604a0f0b0480c90501c106004c103540000d84c0064920340c00200c0002c8140c442e40810000b82c2035100b07243c007414080458410048118a0652080d0704650030548100305c6150f0b280226181d08034244030140640d03542d808880b401104109841c1c0d803101003c61407640e8440000704218003100c85071986626900040b04001c042c05203c0e65400c042c1059040950440c074001840590300d101d00c1c00010421a400c0d1b5907005503880b103402200242880c070405540390280540e07001c005207011141912240720748064003c03034900482080b4050490340c0c0280201d42c1ea14105030000e040f4584c03c1c94414056a03000040e140002d01292028082040240405007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 48628655 1250 48627405 48627421
    0xe0c13020a020c0d0f0c0605090307050f0d0c060f02010e0a080f0304020a050613030303050c040e01180e07121b0b0405040905030d020a050a0206090616080c0903010903020c0102011406240f070b 85
    0x8400ba081f0034240304003045804680e560004007082124421141e1032195100140443c480503102000108003c1d441100800c1050308204c020000765103946c020000914061815035568890140207020100100b10402c10b825140c00190340c000d001a00085e0f52a03a140007140f0303241d100c9a42d41504400404051080503454001c5a40040300a0940b0f0700780fa08051203032005c03400600ca003504a0707006030080345601d54517800003280000311006071000d00e03a03903940a44442d40307459000c451400070303d07100c0308450800714402000daa00302d2005604150910091200411404009503554481072007480318400c40e50009045650a40e5034160f118214207001034071303080001d0054403542d0400004c1180811a0020840140c0218540b603000c540311034000341e0742c52041603049905542040d40d80410305800040e40c1c0340f541b2080c0d0007001030081c010b0181101041c240c5078a0f5001c0301200c6034540704804105103050304030b44503d0041c03405040c0d888005166000c82003c81c0c0b20380d800420407071a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 48629905 1250 48628655 48628673
    0x30f22050f011d030307080711010203151005120f0601030906090c0302040b030a0f08090619020f06070f09030f0204061203080103050d0305061f09050a06030603060e0c13020a020c0d0f 81
    0x1407043d15101682da010008019499003c010309071810414000009000380741302c0d42d209030341004014021592401e2080039560a940e0504606014480010082e0007142c443c8044903084030b40341d0034080083d1200c1541085404015040c94101521100c085000c120103100711800c5601c99140c101e001031442c810300094540d82c090452013070300015554400300c1c140b640720742c0c1110341c41640c041d507a820303850004c2c40c54002c140401c80030b0004510f00340c16031a00000c00d03107803041002040f16010703a039401c01114010414140f1030001000080100002001d0240d10030540f4801007020540d03d842c0d00300c4948444008100740e0000d5001801002880014040c14100d8500c81c5003d01c01850b2132804034104540c0d6181c0c040c80e030204500d404ca80b062291555401512000f004000225a0b490000380a010940000d81e02c00307140012941c4610000140c0e5000c40d04003510040c0c180c1c0001d0501c40007500038454100035400340d00311519986d030301c9240d11200d0a1181e064245003e011341040400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 48631155 1250 48629905 48629921
    0x309031501080111041508101505030403110c15090d0822050a0b040311030109060507030207050c0d050d260a0c020f121804060512030c061308030f22050f01 69
    0x44c4250410040c4080d1242c000005032000d0107061084086e203441035200c420360295070090f05405151035400072000c0d4030100a42c0610300a582e800e10040003841c0054880c412240321551010b0511400c0c410702150f0320140c690000f0003402c24800d40f4080e2107140042e4401e00280c0040312500101031100041d054481016007010f440c03030344000c2d0401d10f5a41c042e05c1140806064020030300189403059400b50055940e403648414148000c1c24181c1020b00079400445013140c15025000c16030314503050100303103800d02030340080007040c8041c901441035070060b0390800140000412240f1307604004100c0b0700554014405c1d02d4000030404041100282400306628141a1030740022441112081c0c07104155600d41d07050f08910341b402e08604002400821061780103036000f0400e022260513106002c0060402011660140c0d1416030310161603081008010000034003800c010b00225148000316021903500c48003044c9130340a1202d6400f86410408a050b00486480c2d2295070b03004003511080c000c20392 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 48632405 1250 48631155 48631181
    0x6090506070302130e130c0905060a05060c06070302130806190606050a0f030c0e0a090501080c0102060f04080d090206130f08010204140d0302120c060429041403090315010801 77
    0x800e00e100c44c064000240001c2c030032030543d5440741c408200e42c00300c00c01000d0b0003980e1018094145a80d94140d180180000f101c01a1044620540002c0c1a0800c0300443d843c0302007520140880d5a10114150003d4000c0300718025a010b840d9070206603030700c04214245c00341d00c0050030750494400c400c20342c0d402e0720a5500030004110040c00301a0180b030300b000e00c0a0701c000d03040c2800304a84002d1082190303070b4010703007188980c48100c00000040c104496400319060380c5500c1c3c2500d00d2200c20400580c1e680106840c1c010644480b540001d003c55000406403d0012a42c3c50100c0d5000c02030f000a1860342004a40c1500d803010314000304624444110000c2c01420584000e60406161640403000e140f052038105002d0040c0200c02001c040c0f081c0f1401144d4801642520b07190680c05100c00d56800040342d0880e0468201d080316403801200c0d42800050100106003034030503544039a10031503003070000c5242101e07502c002c3c08071841650301417100e8046248240000001585081040f0342905e10400c0401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 48633655 1250 48632405 48632407
    0x90c07111002061302120d1d04020702210a0804140f041a01051804060308120a021c3902011d0a03140c010911040c030e030307120908040306090506070302 68
    0x9910300e0300402c00c0e66110042c202d02d14140d0b4130f0b0f030010031070009034000c00b0300441c054520b41110340c036003107158800b43c031644c031500c1e20070700460a0611049210760b28010794000300040404149800601d81084012100403ea5103402c1700f03943d80c82c80d1030b0041e0b04004009176444007282118100600082d4400c1000c6405008070100102c2015042d0003588140b410008006038514040d04c440c6030401c6501d202600400c840ca580342016481604805089207030050b0100c0469000034040c0284c4403d0f182c040650142400264030450050481241c0341e041915214018440381c44401412030003003290500e510002c60b004d120007400c65103c5c2c0403600701d0003070041c049443c860b000030707000355001c1d81410907141809045e0526030142c019450710440319800c02e17120100700075002100100540056a081c050051030304000d0b130595403035640482c0d05500c2800040d035003901c6038480020217a284a80002e10002c40c0c1c0702c0c0f0354158010781003654813a40f107650070400c0000030402164410340d280360031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 48634905 1250 48633655 48633679
    0x711070303120c1b0b06100306140f0f10080a06060306030f02040c1803031709010504050c22051807060807020604020d0305090301020d1b0e030705100c02090c0711 72
    0x1501c0b15200b40d50a514060f034983d0f000f0301e1107001e01031000720441e403001030794144002450a8440c0e283c00300d903100e0103001c18440b201e266500038011042a40d5a0341c0e60900400d501c0c905000b2a982d40c1458503a04c150038101c0410151201403014003424240d0740e8041d224900000c00340c06070745c0c26903c200304151500e0020000304e010024038191441c0e040b10080364202024504603032000b10500c420090118020000082582004809901040781c00310004103a440842c82401ca42e400c44000e0030b40c0e080507812202600d800070001745d105004044803240141c1b00c00005045800031992000855100c01202d03c0e4203004108100c01000d1520341b4001601d0001402501c9100241c0004d0090b407904040360304140c06101604d071902c0014000710340314003a46102c0c2c0c0140c1003002c2da50403130703581c0d4084210109115808000c4091000b90080c410b1505c2d201c280440324822000d80000c002181009100580d03807001d00d0b40c0981c1015024a032500320700c0c00d2003c0c1ca240800c440c6845000c2103651 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 48636155 1250 48634905 48634907
    0x2030303010e100f090c020106092c0f030a02010b03060a02070c0e0a02040909030e010f0801080304031112010204030507030308010605032502120c1501050d11060c0307080a0302030711070303 84
    0x212810350310300b41e06010280e111801d83c0465052582c01100701e4840c03001c000315801d01d00340d10011580b01d569000344025681c0e50510780c11a1140003115100d034a60b00c5015160141e40c04800c401c610f500b10440705001d0014030070a080d43c003d54100d0700145d448400d84202480c0801c6015003002040707008525040c12550f60030b889442501c50b610340343c410750740090130b0038411f81d05441c002c1080e1041800b000806240c01803030a01d4141c803031800300b030f6440d081c1c200c154450b084a505035003c00380118035260039601c4504e40d040090440f242d0000900a403107031000070a0024200640c81800202001415460f0241c00b8a505070030420401405104216034901902c600320f41400409040092032200c44904904108000350040d210040004503965600300000d5003481c2000044800320345030340c84004028a040c4110320190072400b0a0424510f00d20703104005200007586031382200d01c0c100c0680d0301ca460a400ca03541803400710390301208004406400134459441050309401500a030780c00c55030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 48637405 1250 48636155 48636157
    0x141807020a0f0507080102040b09090f090c24220e060616110406030818040203040f02011103040f09050115050c06070516080d0c0f0c0308040308060109170d030b0d020303 75
    0x40050b003081c202408030350a001003030040300090030a0000035540c031610b81d610700080f54031901c00c1d00d020ba40c1c064000340e42c01203880a61070141d00b03103602500840085100304034003820131003035075103105800c1a075403030012101c10010651031440c40709000100b0040701c10300f04010020fa01c03189032040590100801c558075042100c000848010000046070640c0c01d0184403840b000c4a00d42d007040c80c100002c0203101507540500602c043c0441540481a010340502c0300f80d00007510018550002140200c00540c050028113201085003000c480c200742c0d5070080c070007010751b86600c000001c541e81c10041c484142a640f0760b910460103801c240c2e18003048d811625540da48020580c0c42000004200030700390740d116107003903210390350000007485e2a0b920241020340105001c1c0c02c0180403c000c1d0540c40b803154011034a0b4203600c2d0301a240e030304603a075868070141d669540c000c002030304014184c203000c101c40741d040507105c0c1d001c81c2107001040d03621071209010341107500c10070019100381140b0245d0401650000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 48638655 1250 48637405 48637423
    0x150115050f0a0509030a05070e0705041a1809071106070806060a030b0a05040c030203100609030f110303070602180f031605130b0303031e0c040f0302010513090614180702 75
    0x4460242c0d6000540d0701182d5a0181000725a8140180c0702c40c40c051003800034000080e203048070a52441c0f52200c48041e00c2a210b180720302c0c400c244034070800d000940c80c240d0180182c1e41c0345c80000c0c5210345d002d100150120b03000b291a030002c50302c40c40550030541c0c2d08221843c0d00941d14201807041e800c01c000011907600465002070105901c1c1c15032a113081c0c54181031030008080240c41804143c030b0344007015000e504215a00325003005c26103000110070381f1985144080302d8020160040551681d00d41400c03403d400c001c4540c0500c410007510380010001e20007441002884900e107106040d40c0010800b40940a08140c1d209521000d0302c0d0ba03030703452040c1581c01200c2d401c645100c41403000b249100090130a030340341240e1500004c401c001241000d80e0380010485101d948034500d95481c2c0d8042d42c103600035405a11916450480d05000650080c801403036020314880103045416071342c00c881d9058949030380000b03202c106001401c0e40581401c030050030030b24000a04007005031a006800a594240407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 48639905 1250 48638655 48638677
    0x50a120b0d0206030a0c0e0301060b0a05070516180c1722020303030a050709150509010c030c0b010303030b10031b05130801020406030b0a080a03020c060913050915011505 75
    0x2203201803515528030302a004010b5000c0d041c0380d01d07032a2070340f80340004012000700034010510b1000c02d64164a01845580706552001003868141010201c040f220781e08045000c642a1082005003000c1c0d104140941004002a20710341d8900300001040300252400034160b6000d1107005598500400001c0c44c41c150b1040d220f03c1c003410f81240980316080c7c01001c011000e9098000042070145564158103d030b80b180310242c0300e16960b1552201c50110010103010444002a41800824290342c8580c4a801f0414060300e4407104820b40c60f00c0300080e40c0002c0e8002c40200e640c800b128079407130a18001c04038007403095040800c2000306101722104100541513003181049000515804039459880190b805400d020008640712070700c441c8042e00030000306046a03c41e10750403600041c0c8541c001840c1c03003071303030307419405010148800400e1110301d8000030f08940e07011240722184290b01000d8818503220f226800010501c9041114401200303001c1a00003c20001d29101d050307800b80e0f00842111414114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 48641155 1250 48639905 48639911
    0xf140d02090c07020915030d0906050a0e0a0b0a170a020708030630072103051207141602120a0b13060204030b0108060601030606110c060c160b0309010b01050a12 71
    0x140c2c0c180701500d00c654600207500804007010300c40200024160030302c08610903811940d6035001c8003030075100003440d40700b00d60020714100f14a022443c0314030800090072001501408030f4a494001c03010064000b8500b010000d90002c00c100d0354110884003483d000b00e00c103141145801855211035455200050405010b01c81c13003400340c101c0c5100009449064002c40d0a0b0400907100704007103944400051050342d0883c111514000100c03040e0040c4824590350640702c96140c814040b0782d441282c20300410150034000380b45095001d6804d0304000303022403030310707403d90715411540c038810002100b004019044150340b041d2241000526400720f410f4000104180b6401031034107601d8044003034400c5400060007000d540c4000518070b24001001c500500098806000726070305d0b0201101c840000c0d400400c03059000950280c0d1a040c0500105181c20721001590f540d04030120006165032441e910900c050b40000041061200f0b0a02c17514101a109183c804d25004010500812149141d6024204d0341d42e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 48642405 1250 48641155 48641161
    0xa1209060c0204020c10050415050a05060604090b010c080f0d0501121e08190504080c1002120d1116030207060c020303090418050d080907060c05030412030216030c0f140d0209 77
    0x1100b00000e800754601d906050200385403174509591000c0c400d6150700d8200e8107000c042600d07994140200341c0700d100060702081c00c05141508400260200c4760703406052218a06140002c500385200601c4010100da50142e80d0b0300c00824a081202c00503130113108010302845903074001a6403095071a18020800c0c044d0018442c05007881150b500c00c5051040313802105010b03c440d07240e00403029008907520002510500d0034140244841000700c3c00c11100142c014060021800f042a0b01806590150040c00180c031741412031074494542c00058000164003000384000d040541c10000380000d070255207040200001d0b1540031984d03a00801c105203209c1c036100c4400103062440d1005c1c011040381c001007224000c030146080504072502c00e0710b8040e03c9000d02c10780420340a0248ac19582c181e42d22034001e600c2e00f072901c1046070740c0c03c4008000318114042c01d07914800c07100d144c00d0442c0141d4064108491041d1411043c0d00e0740740c5c0e11398070600d0118800e840c0750313829076580d02c1c0d051034141c1c044d85c1c00640b83d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 48643655 1250 48642405 48642427
    0x108030301140a080d1e08040c0501030507030f020c0114010b04140d1a042f0a0b0a050702030607020601080105160e010e03010b210601050405091c031503050a1209060c020402 77
    0x392070f40c0c00400c2c40e4445c2d03981e440c43c9654000c2c411084003102c10011208500302e604201d401c540c007120090880400d83c4800c000c1c55219500060340100d00d071500007000d08000d01420180e9001c030b48a4181691a001c5212002c00b81d829000d004001d0b00300050b10706450980020140700e030302d0301c281e072144012030a510140146003900e002c80c10f0140c1c099a049180900c2c010f001a44030500d0b4106001300c00301242081100c42c80d05541601004240e403610a1500340c44802a5103c1e400c40c0d8204842844980c0058404125841c0246007a070054203143d030402e0342081c02c580c001860641c000044005800c44c0c1070f0089202461a0f00c20301e0100c0402e076060000c28050030908014542000355030315021104d441003600e10441005210640305e00e031b41e9540401003611001d641519807900040b84c88103010826809400648483d410301042114000c42c0151110b49540d2003070b580741e040750214808001480da510b20042520707080c406651424000d00804807160654000d00642d80010740841c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 48644905 1250 48643655 48643669
    0xc05070807050f1606020304091e0603030504150206060f0108060a0e0a02130b0301050105030c0706060e010308030405240a0903021501031a09070515030a0b040906051e010803030114 80
    0x9500002866500c203203030324101d03a03190000e854144aa000b000c0b0204c0c03039120044041000c0b40c2c000e5000354207060600180500070900e0f64a04404062206113a800d1819640140c0000750700a403034aa8a8901e4141442124100740d1100d00454020004001d010340e628640c080106c1c50a203000b08981c2e540002060111a00381c0081300000180340070042010110b400034011030503490307445074295988110700b00840c0028021580825001c1c0001888050300c0005003080e1401160086034180e0703240c90b00060501d003a002941c2c1d5100000800061100400040c51603000303d200e261160a0055001400c0c030034090000d01519071104151014180b00b0049914100384220006c12103507980d152002ca0740d1030120403071200c4201c001c0040c00030303030f00490410107e58000e0314008079003000c1380e94844658402428a00f03040d964007803e01e42d50f00c030f03031003034054070381c424680018641044105d43c1c21410782c0c8010807080740000c10041c0310700380020080d20704441d02c620304a000480100005254 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 48646155 1250 48644905 48644917
    0xc021b06160203150a050126070e0403180303050301090b0f01080106080603010902121606050319090807050604110405060321090f061c0516020a030f02101104031e020904060c05 78
    0xb09880102803240c07105c1503600050481c4d00b84021040b12071074500c909440310248038200c1e801500001ca013007000002003e000c50340700303119103401d11401403440c414110b80f07801900b05900284001c00184203108030362292020040381103920410804203080001e044603014002c540c1003060b00800b040b07107134409400c000a507543c024000150303032860610869030303000d0301c0000d8040d02c0b920990002e201d0380100100c1e0b00481040f03140d942e400020a404401400d408003007181c85203010050540811014404e441c0243d11171042c100f400f24400d402c0009a400180c6050300c20b4003c8212030614468800700c0c0f00c2a0300b20310700c0c02900c4408030300024815901120105401c04c200241c0384284c0b400b500c0141030440c0c0198410003013629034850245040e03640ca5410360169000704291000b00e401103003964100040c902c101e811091344040c1d01801d940c02d02440710342d082c40215051040003081304200c80d25450302c54820581403041e4001510000c00644060007455a43c10170140c0240715401f2101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 48647405 1250 48646155 48646183
    0xd021507050109060c090e0c130e0a020309070801020301050609040518030c030a110c060d0e0c0a120302060a020307090314190b06102c031f0c021b06160203 69
    0x910340d240c50601d240a481011000c8807a585070100d0502001e0280900f20140e80c00c40003022810364400c8410b4039260b02c00860111081c2048400286160481441902c01c3c07103400c002503100d082245504d4500246d540080c000d0340d0040c00103100300c0d202d0100f6140e82510454011407203071182044003110f042400d0343d0920a000c006011000001e0000051154861594030301400420080009403280983c1e400303d50f00160030002425000169080300344110004415654401e500000040d050074165004000d2044e504c4022000e040c1c05025080d03003d0451070341989980f03001003005110310124080180300c445c2000d995056050b04100080c4200c900e05440031409825040515240d68110b5209100d03d03040c00c1801c0f000c80c411081070050404411020310f040040503000300c41b07150715140700c2c2d8240c0300d03003d9903c80404c00c038803120004001460002500001c0484c009040a0303132044203c1901d107851a1040c81c80e160a02122203050011380f5000f10080244000f03400d01c01c038012498 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 48648655 1250 48647405 48647407
    0x110d0207050a031101050c0d0c110a050c03070e060d0201051c0203040809040f0b180717160f02120403080306040624091203020303010e1003020306090c0f041a0d0215 73
    0x20304200c4006007a69905020342c90b440079078040c0f00840c038283c0700101c46006000303106104e981d45004064022901c41042e5041c403442d81c0384460300440c90240500070544041d4020109404141414441d40019100100705e401030f51418402180c26030480c408001c2c1004000a00c1c152840480040305150000d00c5c0020341d501c0c1040e00744203d06400c1030548a218501e04101c06140700c2e0240b050b54580710015200f0784001c10039400700140c05200600314001d1002d8070704c5000b0980388000c0c6d140d1040025016181c1c401c0e9040702c000f13205074072411400e001c0d0b500111007000084130850540302100d501c2a00641e40355100340109000d407a45a02c401d40e0f09680300803a2258122035500304012402d95a070308291582d640c1c5e200005002c07441c0b8040d000d40c204200500c04449860324150f480209065191101a0f03a82d0109260540450b80d0500c035401c00c4500410350329010321001c6a040b0f080741d082c0f20640780b155024055207106504030384500c2d0311400110440d101c0b0001e100502402030201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 48649905 1250 48648655 48648667
    0x3020f1201060f050412020f041e020d05060a03030206010b0a1206180506030106050109030b040f0212070905060907171810020408010b090c0301121502030a06051c08030604110d02 79
    0x48800400c20301510010908841c0000e00051248068404442c0e4035046a80901e00d03540138051004042070340d203900242c46811181c05003403030340c00291001d08203d50060f901c40c0c0c1c211344441200c401070502403240c18034410401c086036002401c9415103403070b40d01481d030b186d01080058030480c43c90001a0102c5090140004103000ca207544064581803c02c0d0a0000b541c90000300b608075005402610702180048100b40007182e0700c00e588035070041c030030f43c509200b02a154001440d200c0c51202c800241c1e500a540c107000381040c50140540017942070302d6404060402140151000700000c480181080a5030000b0302d02d42c4848130100c5080b103648090b41c205074516603001c1c5c003170741c41030085818960034407840d0011801d048040307a10a114054165095074200f011402e81054846802c0e0740400c8500c900340b8803a070903031004501503080e01400040d8546040c043c0400e500301e0407528000c0f0800c840104010444160407240c0c802c000301c80c001420012080110441d0140b5000c1200c024804151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 48651155 1250 48649905 48649927
    0x40302030d090501030c0305010e07050903010204050301051003021305010b03041e0b0702010c11070b040501260c03041103010207152c0708010b06040f0312030e031306112b03020f 79
    0x1c2c24166202030342c062007050f42000c000d400703941c2c0c2846038092903030690000902481c0300d40007a2011100090005d0f0bd0541d41f04000b03801c0d45e00948150100c50300d03482d410411450802e0100c01043c00d444810301c515032500880d406071307000041010380160680080c1040750000399801072807107580b2400d0b0b80c00604003148000e0083c9800140d8501282030382c2a20100f0400004401e0226104014144e240034203100046428800180448660011028251102001c41020188289440ca60803074a034681404e1401c0800b07050304070790f4002d903c10003030180420f2402282e205101c0b015080841c0c110540d02500c3c20705001e4840e2200724080a2001d40300c4002c0209a140440b1505002440114201d4040140e00d2099206001038601c8980303007000080e4000d5900841684036080026010801041c81801c43d803001d249014844440c1c2c0c42403100b20b81189812800b016060014469071510343c0c0036410a040b0ba90018601c00740001c41c0c0c00641b03206c3d404841d03144007200c008648588502035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 48652405 1250 48651155 48651167
    0xc03041e03030c080709050f120f060405011406010e0f090402011b0b060306060f0904030f09030c061809020c07030b090111160c0605030c03060d030c0b010b07020f04050603071a040302030d 83
    0xf400001140f240104240c02d1082c0d100c2825200c2c000d08002c0d85c607800c1404c1050458904403a49518042e1402d02c40800c001403100d2481507000701e00210360030800b001c0e41180a00e00416060500c120320740e404056884105d0007035040d01d000c1d142c00d9291345035400161a040c013212241d2007420f02e503200320410071a02c4401c290013840f0a0f000c65005441d4002002480300492040c40e801a5040b00010f001c2841854140d094a1460400080719500d81e154440c4203402500100081500204a02004030106c106840200014942141411400c1c400143c8071025488068901c00c03003000450181c00d801c0d4802075054010101550b65000801901a100481c0360000d5648558040307002030351501410480384030703a01d009892840c6948003402c100c0150751010058080000410b90040081d900e03000c154060240700b00c1e0207866010a1041041590903a60782070301944c140004d1000310f440019001094401c4a002d04044c0310072110203a140e805541e04c080d40c148100e80d2504013640e0412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 48653655 1250 48652405 48652421
    0x5030a021326060c09060316090f0f0608060406080715050912060108071d060d0305070507030b061903080301151803030305060909160611030c070b0d180b0c03041e0303 74
    0x1090f01d040c2c0d91101e400c001c42d402445841a0440d004100240b1582542044180c0040d4103007044030295031101500d042098954001800d00e04500d40207000f41a04260384691040302241e0900c4000e080002e0551074074124070408000c03002800080d404140501e098038001c1c1c801030802d0484498900d001e980e144000c1c403400314180940f04001c180d05030300b50710088c1c103580d8011807844941c0359081445022498004190200321090101400040742408084000e40c0601c0002c03081d42410400c0001c008402599883c0000e0002000c0000030310078000d0301e0440740d94804186011149440070b5401c84103081503040460700b071650120405415078001d50141100f0b64806400c0d50b00c09242c0356581c6100f1f5203083c2032070064442002524406d107502f00d0305c00364640030389080020021859261000c5500408042003002c0781c10203102d4130902ca1110003200c0c0403032000300300c22503455801468401070b042203440600080001c0a104040303a8290400fa1b00a0207900d8000d118140240117284070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 48654905 1250 48653655 48653729
    0x90402030a060524090603041505090a0302060601020d080408030a06030203070e040c06082406090604080604150603080a030f020912011401052209060902030a050307030f030c05030a0213 82
    0x6005149440c00e420130500340c444401d000c50b40e00d403008607410006140c000030400c407004003516410040409503800f40e180101e2001d0001c01c0074290130f03d00030f81000d00c018042c40c1154040280c002425a00501490300150081d00713240e03585d01d9001d2100083c01d8680c00c003075014031500c1d4001400c001481182d9100b1401140007501554880b1011106d0f050181d88075150070740c40c0218245002d54500c0203401c42c4400505481c03800350088046a01a00143d00001590300810208410302c080000300c45031114840c41c0c10003050341569102c92860084900340380c00c055803a011210000c0059040b518100d030010140066000040d24880c06400d55665201140720114000112400c0541801a801a01001440c221041c440c08c0c0c000810f00440c040d10002e40340c128480168070b092040d40c401d00c2c0100c0107517a40303401320304010301a010b0b0060301e00100342c03908895403810b680c460181d0f900036800e081e0269480164168407014002c1c1c035044024079041c10403506041100c182d580f0b106030051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 48656155 1250 48654905 48654919
    0x180605100f0f1e0501050909060a0f0b09030f01111e0c0109060606020c04140718050d05010204031205030702070302010e120f03040f0611060408160503040e1504050921090402030a0605 81
    0x4883c03200300e03440828418140800c1c0180902c200e146400d40c41030740c0c00030001d0800c58009a4440300200080110341c88850304020000f1103100d24141403088202d0841b03128000d02107480400c0c0000300f54800c1300fa80c089032040002c40c49940d135005404980b00c50b48030900900031410b26082c01da0040c01503214100144c80b404111a11030f09150044064401126048104c80d9903a11001d0314025110701c0300d485481404040440c080c1c0c1d0b10a00680458018000140c54600758034101e0b00251018400c001441828070402c4051980020b00c0000d6907420310b0040045000400825614032804070030b108140501ca1800f00100f9002010300308440705c68010f415000d650f090169070a110181c0c0e0180c0b15001a80050003207081c03c401044400300c942100d1400902c00d03160241507400a40050301c0248040051100700e1442140224425408030342c10052424021001555200848078002501d120300301200368284041c4259003a1550142040d5600c2c50030405110040c142801064400c4031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 48657405 1250 48656155 48656189
    0x51203090c0a06020c0102100209010302090d06060504050c030906010302010309030c081204020310020a051204020a080307060203010911030106020a02120c0d0f02120d050a03091104020a03021c180605100f0f 91
    0x1100081c4880401d4040c0c001e001c2e594202140b08c030183d40000c00660526400f048441e005844041c5450255030040c3c00008840d8107080801040c1c0e100a008280500024401d02c00010b0700414070504413982400c0004610400d0700d015281c1426174103001d800d80e1008900034940901d007211aa1050740b080b0309444400c090104d40700201d0080b500c0c05000120144981c01480702e001d64500d0300107000401000c03403a6030761052545103511515046a00ea070300400100404d035094041c6140c0e081c0e2a51540d8115814804003d54400107104080c2c860180c641034004000d405200030400002d0103002842450402c2c205260449481d030f00481c09014074020305201c6140c04104130860b40c0b1155582480c1101038207046001d811410801c0d56842410700e030f00d0f4141c1ea48c61000b8501c241c021b440258403040842088060b0f070f0303904001c0b4249036041405880c02e00945e0000340403101d500c0100080d031501d0307144041290780c1858201103003001d0314480c04070b03010300090100c00498280100404c1502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 48658655 1250 48657405 48657407
    0x1080115022503080304031206050103020f0a050d090606060c0201020609030309120703030e0304090603060b010e1302070503090603010b0310060e0d03030504060e0a08130f0b03060607051203090c0a06 88
    0x41460405005811046460300860325458030342c00c40e101c404110400094484d25180e610394800d031812008181c1448440900111602510005180900f811400d020303024030304000c240300e8241e0400400000140c0051030885c3c0b94810b035010747d08440f0401407241ca4260241940030345030f109034050311884000a201c2100042100d20440404005e070202035004540082d098100381c000f00c0038581c41d0250303102c07007150800c064001002c0400011900900e141031040c01c54015083ca00c0c1081074031701010f009504e032083c11903600301e41040010b0343e13080a82405d50440c000d2119266110200000000b0003e242d00081c0d4060304c44d51054201e41540d69400b07485540d0140141a0480100c07210b0b040428003e5101c0c0c0d600034040d100100711185115111810180b000c0d03011100d280d000316070f00c2c090396000380d982405003407552a504051418480315061902000340814406d0600044040030001c06000c1d404500c8035411408bd264101101210346404000209034040c01460034005092 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 48659905 1250 48658655 48658679
    0x50604030807060207080c0a110108090307030e0111151e060a08060601030c030207050d08100f080309040c031503080304050c0d080a0c0309150908010c0801050117040302150a0b010801 81
    0x407548071085a2030b0480e60359409001e134220301c90070341d0500380a120203080541c0912000490350300c41d20300408550344040014089001c058000e82d8940c0c030030300440f000680c1102000c00452002d003060020991800021880c09004202d40f0480d84200700500004c520f810b59000c020708150341d0b0303d02842d610402407248040107481940141da1041002c2002540640c0c401004141c003440c0152078000251501c515020342c074600480041c6181c0c04000801010195040c050800c188a814036189440394030ba64a014141031244145d0383c450103502e8480c040e5020008004c0790f00c1e03200b421665a4140b2140640080b1070335240c0c1e01400c100c8212030720380741603154112a070240406040c10000c1c80d0480c0c01c1d44400d2001c6083c04507000300460104035120700c5120310b0350550742c2d11500b1401d00101d2070039586290182020300c610ba02c01445640c0e048190f00401c003071144c0c4610465500e1741001c9240546c0405100d40c199450402d22a0800107034000c0d0721054403e03210b2000396640c0320140c400d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 48661155 1250 48659905 48659909
    0xf0b03010e06070807050d0c0c0201020d05040f0e06060705061306060503030310060e030115090b041a010504031205220806100302090109090201020102120907050910030812190e030d06050604 84
    0x1d80c1c00c61000208041d0045418541142103440c1c071134180b54818403035100b01c403c00e00c03415000c140c0489485045690411400c0c2d4418518a49a410185405664400441c035405482032621261000907002d84403802503403045900501246d00c01e01b00088c00801410105409503291810040080b91ba800c00100710b034040c120340009003402900e030134030480c0d400101442c083d42c9035480701850250311203100f0640010b03041f102400a811800d00041104403002e8032409143c084640705050642e0303800c041a10202d90700b240900760804e2611008869901c500030100c902d0000b046550f1140d01c0d4070250300300585104404407005030300c440c0c1c4200e10340c40c1503203c0290f1000007800142300e02056030b081044446e106000150078443c141d0000d070000c0008072102c089961110b04200100d1904540050f003180b480c01100d0200790641d01c0301070062055000d0110400400404038082080000c00304141517024034080010398601040c4544a42c00341c02c40201d5542400e80118552038103000700c0c0e003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 48662405 1250 48661155 48661181
    0x6010602061005011d0a090b1215150105041a0304031106061f030e0601030b0a060506030106020d1b050a0b07090906060c0f02030109081603090b0f07060504080912010f0b0301 77
    0x200303e2a0200440b014030030107603070340e4030f0400190660f006621113a1100c03026007824000481d140c00c05206010345290b4001121140b548234411158142c40b100308865003094522246042030200100166941d1003198843c00b01d9269107035907091040380f600301035401684240c0e26541c0394071030003400c95641e6006132103883c0d208622503200d061003002c05014120140c964280485e031000070000c00c1c1e0a00744242c0c02a01c44c082008100004040c0350b12a03000502000c49005003154107254000399200842e030710010521045d00d801103110140d030104440c04641c004215007015149141004204030141c51010210b070030a400401c5807080c038003450013520300c01e5035041d8044855480c1c0089210040e074040c0d801d5540c80e0742d45004902c80744000d144d24902c40103104000c1180303140040ca169143e51085164540500c401005810014200ca007a150010f402050585850800700b01070310039991940c3d4014812005804c0e5070a064110601c503a6100070100008a106c006050980f1090340a0320 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 48663655 1250 48662405 48662431
    0x7110402030708060d0219060309050c1002030301170a0605040303090605180a0305070611211003080904021c020c0d02070f030b0f09010603061d0120091302070206070b01080601060206 81
    0x60442c03c00d44000b104e4140010900544079075000c7c002d5203440c0d003d801c244000703a250381e554802d00074100000624500d0a40e0040844040080000d4503030206002d40140c2c6090300c0d481080c560390400c20700b00d10340e0304a4020003030b50910341b9010303005001c101801c40764542000b0002d0710f41110411026145c1d850100039007101101c580d070858241e806103100f210f48603031303422030200500d40900c00b1b0015038100e006070a80340307641a074500481e6100100f90100c00c1d01c4202007400047c417071304160307412600e040c2d8000d6100d0942011400006010a6014040c544081038600c00f5140000300700301b41e481140c00350b4410607103c201240001c01d00f07003c0604443c1504000c1707442880c1402103190300c015020b00001e4103a0700c03035581d0010f031144002440035049440055802d0700c6401e102e182d4402a0704141901c0c1003026061495a600030700c40d040c0d00c5441b040707800c1082d00320560101c604550340144520b03502d504510344a04500c4d82802030900c2845080300214044e80001245e82c00b84411624607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 48664905 1250 48663655 48663661
    0x1c05040b0a0c090801050f01080601080106080a080703120f020d0b06030c31030606060f020a02030d050a140301181b020c1009170105060108090706080114040207020904030507110402030708 83
    0xe03001500c1003100d40010040c01120008144d0b400703118550040c407029901036640e5241011103440c01606800919069142c000200401000082e1a031030b8140e016186a866901030b0400f80c1c5d5071100d840302880018101401140f194100390f004290a5441c40d400b041030340d8140d810b109090104440303a034002c00d42000b2030454402d1030799150044418000058640c0e00b000620800c3e1000c2c5540304507005a217421050080d01d41052510b0b00920141c80100800005500040e071341e66000703da003034140040011001e01440c800c819407903124110303a034040c0e0741c0d5039200400b03801052005001c5030098502804040d081c184103002040d510815401006002c50940800a1450348001c2020030300c81d0039900050036403481c040c0e65a2810b070040000038a882c220300050940704004003a42982d40220700c003400342c0c50300315480b281900c2d68502c040206c10080c0c00418024481c2e00720196000c0100c608000805500200038030741d20340b062500d0103041c903904c020321040c0e0009031120004035441d1000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 48666155 1250 48664905 48664921
    0x4180203061b0f0c1006060f0507030f020c040204060c02040c020102030622060e070206070201060506090310020f041a0a02010b0a030b0f07030902120c0f060711120a0510021c05040b 80
    0xa802c02060302c900c2c90052500d00101150780b201c0030520860b00a042608000c1d10746119510007410681803d821b0400400b400034603a12844070000e0502c1007450950f15014820004d03444180f10280003195580c0d200c00b0090580c103280a402c034812030a003003012052070303c18000c0d0703030103250003910580d080030015842c4000f0b0307011064402c003c65501c0b48009544812111190f005013600d40103401c650500d00d00c02801e441098000b10f00403a0b0803c2034004640340040c1400942c0904440141c94500101c8400303074522959001c001d0854100704968001d200c04001441c00345500c1d002003006030311680038041d4460850dc03015240592520000b03a80b488545603441d0700600d2480c00190300030207039001a074940846281149103070700801c0710b0001070500c10b410341c190500855082d0b0800c1015540d03c880403580070301f003c0c010414100d5210005408002540c0550340c0542500c011244440a240007904900342d03410171041d03500c521040400e00340c81024000c0d41c02c1201903c4542d03802d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 48667405 1250 48666155 48666181
    0x80403081c0c12112506020c060403050711030a11060a02070b1209100e030d020913060801020901030b0d02030d11100507030b150a14031305010504050303091612031803051005060418020306 83
    0x2e010355645400f04202e80c8c450b03000b4080300c0c0c46140b00c1c1e118070381c0b81d03103250420841c6110156262030003039001410a50100b1429401e2a0150004a80060380c50303691400c12810840d090f41300180b501404201400c50b0f004c001100c3c0d00c030369a00011161281201400401542c180000c1684290010031044084034281d4009111044001d0420120011141c08000440303003503500001c50741c1d41c04a1281601e691500400301462022245ca00400c4a48e400081d1100f80007441c010511040e54060707008004144114441d070060080100302901d00000702071301070188030202a1107201c00d108600c003146004805d8602510503544d800c907d0640014031400903900240c69901e20102900c03509001440c24006c05104510840203182c503800c0494107545003180010071146011454442400704003210034180d05c0d519098a4000700c0c8a0030030210320011542500050080c1c0980300c04421001d2076500403600443d415141040060541071114811104201c0000d40c0b43d000240883c00b0310030551 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 48668655 1250 48667405 48667477
    0xd08090d06060e09010e07060e060316090e0a05010f1d07030b06160f021003061d250f0207080303070509090a020f12010e0105030604080403081c0c1211 67
    0x600002e400d5111040580d66407000c554035480e5a44640d03000420078024017650008100c4c90500201400b00c01c40056070501004021058011011000d40184c9102c1c1030400000c01c480e0b008205a03060079002172003c2c000901400c8840006a60005110f91140a1b44058082a613035540c95949902d01c007200034002c0640c0e03041d404441480030b03c4602807120198800144100c5030094200352610600914407000e901d03501c180340c03504808002201c03041c0780e46009000d052203490640e45d140210351010143c2e00c0251080a2a40c0319960441754101000050991091702201c08403a03a0760810b0740d0701d20003243e50030300145040c400d2403030505110010703039003100020401600f801c140740512406a00101c01020b0310b45901c000400ca200c0c0885c1800e80503000c02d1f0081c00b0949403503121001540319030705c4001c02a10340001ea801c89020401c0100607645a0104140004084c07528010220710410380c4140c029840c01403021a454a510125850714503042c0d00e001d6050107420703c45150300d0b00e003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 48669905 1250 48668655 48668663
    0x309020a0806090a05010605041b050703140f090102061501020712030207080a080a080c0403030206010b1803070305030a0f050405030d180b0313060e030304020d1113110702010e0d08090d 82
    0x18420104080300240b02242c424990440200f42d403001504015094501c503a003c24059450400c41d0300c0c00c1045440c131000c01d24040d04003980d0341c080c3e0346801c1b110818102c0702c17500626400308000f011203009400a1888800036801c03030b2520380b59280d0300701181004c810010f002d6030002404100701e0395441c0146208900038010b5940705a550200c6504124000500b1590701500140510903240c02440c1d43d50022031403455a130a10381140d801950f20340e411b0092040c1d407030010880c64045048010000c10100b000303000d5841444c1da074030340550340c1d400941e1203001040c0b444400c03820480c410010340c2d04941004005217100c09076120305450303120b007040d80303040e0043e8100c00106204001c40c00031801460245040c1c14661a01d007450021030b203100c2d000380c995400030003d010144e80ca900c1e00c51039058212a000c07940008800005460702c46907801c040c0203074140f120904044180001814241c0d0007a207440010034014000c0140d0540309a00050000006000241440c2407010321001210302c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 48671155 1250 48669905 48669919
    0x3060c030b03100e0d09030f20040f050109050a0b0d080705031603080105010e1e3109021206070c0b0a060509010e07020f010b010507060e1204061815050901030902 72
    0x101c1e40c0401d0030240d50781d002020312500d850a26004210401c101c4805e0405071074000030301d03070440d40e552403100281706029250100f00c1001c10b15100d81c98240c6149004010002c200c3c0365000d00c001c201400b424400c280280c0d24000000341c1c140d51034081e40034011401445c810480b246683c076140b403a0440c24054031030b84404c1c001c41c03607401c125841e0314200300c0c0a41c80b219895858440010220500c0c01c00c070500803205680c00c04c80c0e14000c070f5a601180d1000b11005840003e0501d01c440c1d0031214605040107602d40142d0500342c55400341d2000c9900e600940359082c0e00313130658a1250f614401a9820350003e8404908880403800d0301c00041c1e0040090b04012801c01d5442c000a06040c2003078000702c010071040d00c1445007503501000030300d108003c10340003400001702120000e0068000c01d00060302e00c0d5181c00e100c1044010500c400d140283ca02049140c80b1503c41300002c00da000c0000d1960301504101c5000320369000344d1004445210100d40e12149021040f800441c00345c04186001c9800103d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 48672405 1250 48671155 48671171
    0x3030203041b0b13080109030801060e030f03030a020417070506040e0c040513050a0507081b09010c0c06030b030f0309030601061209050708010c02010605041506111623100903060c03 80
    0x19a000b1088001c0c80071080b01512910801d000c500048030310762118001d40e2400c0403000000c0d401550440c116100e6060050001f40c80d0004641081d4000031402ca50707000c0002003145015041d4007a1007940e220070a8807185c4d084548505550700841c0c041d42da8007240038442040000c0c44507400507401843c8254103070500f43e4400118105580b14005604004c1e15002000007000c06481400da2000322403400800c0350402d070710703460b800c40c00029040d00720120025908031164017a4071420501c80d40034009525a42c1e0351040240200a081c1c40c692080c091500d008154040020035a010900d00401030300300c992030998240da00c0e040c803030160a02c054440c21290302140c0c092089800800c03050f00003155425100900a00f10b81c4a608468443e91034408017a090784090880301c000e1742d203181040c1c0d46581d041c2c001d892030305240704880a110f001c0c0c280013088030141040244550000e980614030054036042c10414561201c484000016240e114104040b50458201150480b030500f40055002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 48673655 1250 48672405 48672443
    0xb0f1902070b0d06030b0f0f0411030115030c080c01050309100906060b310e06060c19151506021b0a1206090507080102040602060c070320150108010b030a0303020304 73
    0x781141054602c8144d54040070014048030071861640003c050450101a1501d0301d0420000c107005000600600f401ca01041100e803403d40c013542d44100466860003a0f10307520310b010400381e1018001c02200d40941e0014100c1d0b54042ca041c4ca0090440a026061802d07041c0d403080300901c40004c040c1c2d041a2280000100682a81d00507e000d0311501d26044c2e03220070f4002c0014100a407128848510003a0101c10005d6251690216801030012500f00342d5519106083c14070b00002e0032004c48422901072040c5081010350106480101c250b03802c2880240a0000007420a0509200d07580141e0040d02c1559102040e004140d03000010040c415002c40c1d0b194945400e11402c2c0d10004c80c0c0da56907510602c018850104003210080a8a2000b540713002d007000c0000b1340f1003c01521004d001040803554508150080074152181124410281b940580c5a04240d40e140b00c14003d0404182d8020300210326a28107018441040384060300070108404103940c210700945c0300802c265441d40d010a8250898 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 48674905 1250 48673655 48673657
    0x14120319050106020705061c02040510020303010305060f010f0e090115060201020403050c030a030c02012a060504060c0c0803011a09030105090d11150103060b03030d090b07090b0f1902070b 83
    0xc4040040300050010040101021141c06802000640d4410740c0704001d180c1d502d200b1940c0c20000b1000d405014026070541e40041d0150744c02c001e40c001001c46e1800c41c11030b40007000e58100e80c0945e0882d4400e40340c0c1c0044002008080c01010100034414809102041c3d4800b02680c2283d0325100000d41168061002060743d034454001c000141d4001804100b40942041800110b0718100c1c090607502c456950050710141c200d5800034140850080525914002d666034204180d115802004600600e031820302e000340811101240c0709480c0c40c0c6110112840303083d10149140d841628289580d0814032428910000e40c01c1c02c11301658100151151900c0a008050140c0e450100500b0024000003010300310001c1184600819440004801daa1084044210f81140d400040000359140200c001c00d045200740405058918204107080d0304200e5485607083c490011540d801840c0f0340c8171010580144904203512816040a1181030b020044400d40c8841000f0707540100d0b000150780d03e80d08052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 48676155 1250 48674905 48674911
    0x1707061b050a0506150a0e0604150e0a0b0924010302130504061502150907050f0f06071506080705130509010912050703140901050a0309032f010c0c080403141203 71
    0x22508030001784003a010300008020351000044504030325960818000b0386642d03000520301d500c07441d103d600c401c980c595141d2280014141d1564445014604210104064644070b49040d004040880020b40844228410030100007020b0104150b0b42032035400440203900125075a0304c030300824400011f090f540307501c80c490007401c8220303039803154400c8480e020703050019840e18100410880002c10103c031001180c19426542c0840d41d140c12040718001141c18003080c110410380007000040e031203042c44240b240c00c0c10750540d600300c148452a210a0142c2c2c85400340d2146940241c03203040300551058880d000581d00842950002030f00c111a0b0311034607030110900700c40f0008141c0000342c1605150b400030b5a03902c090445221340346040307200d0740002c21521803880b42c00c08140d40d448441c3c040611584e0300d01c64041d0300810680120303800c1c003034008150610320040d05080d840c190900c0c8902c1d000d44121554150041007050a013407442c1c40c0ca911141c104403011000e0b00800182c0140c81084c440a540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 48677405 1250 48676155 48676163
    0x609080d060e060f01020f0a0b09010906022205030705030d0c0f050303070c120801050a03060c170c0c06150a050d050c101d03060603120d0605040c0305040c1707061b050a 75
    0x602e410b0020a203d41c0e98501c5040d141150003400d8802010040000c2c02c0e202654000c1c3c009803281d0b10960003900500c0003000c02450b950001030400c000001401000a1281c0000c40340413519988800f05a0b0b81c03011882807903016080700e04443e40e014000c002c8018564003e14603d052903000390b40703203070070f65104a40060101f501c0910620900100000b044a07540c881d041050030795052800240046866100060100340c680c040b08005a203d98402545e81007500c607000c03814280708000380075a41040240300400d00c03e44002803032901d6008411303200080c0c040d0030f120100e401c11060040008900e00140c3c0d9a10904002c00c0503610b850400c969022003c0da11440f030700034024064051302c51501009d0f0300c41d80c0301100380000c55a01181d00807400c20008000c0e40c7c2d6040d103100c900060301450b0300207035103d850104411222030701a084103110300c1c4142c0b151526039403031703d1175030b0b00180c200011003460742d1001d482808018041c01d10b10030b90000d400e6103202c000c0c0e81035907041e2400301002002c40b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 48678655 1250 48677405 48677429
    0x30908030702060106080a02030f040b04150c2003030606040b0901170a05160c030e010305090109140f01060f1406130306021803070614073809060a0b09040609080d06 73
    0x1710300303940508000c0e001511103400f589581448440202c400744060b10103044245014017240403c50000040d00410020342c0007131140c80c0d4030f010701600841d101100307403031405580c802d000c09071000401140e00c20f890003880360303040605000030080b40303810544c503440c1444944c2c01000c00c1000c0d046040c038032900302004085845d24050754180399410070074031400c0034461b039009d040300002d801200301d825214081c64000b030560f80312031fa44ca0140c400d401014000b1010112a520465400300d021038a00d00d8000080c05110b6452500c88140903141c4102c03843c081d0a03c41510759441e0803030007410303030001031003850200545a8071040e00b01d07132025402e224000306402c0c5d8030240d81021b01c42400100003a04107c602c50300d14201c1d2402c1c0e07101d080030080418681c1054808000c0b0180140460036144004000d03100604805065031140d0503107501400348549000501151325900a000540e800034065107075648447d56084003500300c00e00c080f81c000105100841c4101c80d80c0c0f141000400d0226024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 48679905 1250 48678655 48678659
    0x40f0c08030901021002030411010c0501150b030609090604031709010605060d0209180709050d051203090304030308060607020a1701090203030a09060306090204120209130c1202030d02060f0a0207030309080307020601 95
    0xe17162102c0705a24800c803900500403c008070b00540304410700c6420a0a184030f92085920b0100c0c0140380e0f003040c00d078040c01c889001107180c41901018610805082d50603c49644500560682c0c4000855004000031031000c2c4008400c040c1e402e61a8013312103400100e03500d51a40d0010b1202e8000b010014259a4045114082444c00500021032541c0700c04c400d1070107042520004201700424000d6502a0b5000111a41044010030621003e1843c40f0300141c3c590a20003422a100e42c040e00c8264005000c3c1c50100750140340401c11144c42c10760082c003002c0058541864202d44204001c0030a0095503582080c1025890920042c2102401503817641c103080c0c200303140582141e4281d041501c0d82403040c00140000500e0900071881c1c1501100c0100b00c5a551501c0700700351031110071004000d001da182002681642c807101240700c952085003980d001342c0301440102c0e61f42d04101c078042100e000000120b010700241d980200b007064028500412503030304507210043c1541c026102c24006900030001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 48681155 1250 48679905 48679907
    0xf091e0305040515030703050f0108073308100b043b04062301030f030e0a120503030105091e01030b070c0506040c0501080108070305070509060103060512010b010e01050903070e040f0c08030901 85
    0x152a49c401c01c2c2101c826072550502d40c1c45070317079a8241d000300141800c2061313040214040b80100150070051501d034100b03180c40d140400905a40c401c0d40c40805c0b485462170082200c404d407400b9a403d544070350850f40d95003001c041808000c07004004547c21400007168084800b802d41850551040340a200b0100c4c145049000c2c55419102e0082e0321810151201d0041c400a040300740c2506034a60036103488840d6004a500241c0b001c5515400101055481d52a410030044044091812148102d071404107070381c0c5684116251111418014101194401c010303c0010401070714160450010f10b0009200201c51f81c80c103103800010b980540d42030783d40328020002d942c0e10041d0240500070f110064205a861a03440300e90b151800d020f8a0f01c9460b5040000d44140d110760300040061000a01740711140d101109814020481a02980d0008502103000f58155019800312880b210010b401032080074a00540c0107041c1b078010704101c0e6040034610001000c24080980d181c003500801001d0350b541d40941c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 48682405 1250 48681155 48681161
    0xf0b06040c02070b0f090901120201080604090b1f0b0d0603110a0506040e15040207060b040b2d030a020d1a060405010303090501200f030d0f091e0305040515030703 72
    0x800144a142000d0280c258070741c1c046044022248280744003038031152000c103501c14500034031050342c3e00002c4c528000508108050500042d01c0d000b1b0b29030104d41e0710340d00280b00a40b00e001602506042d0210041550440c600c0050141c1340f01e40404211125210410032000364003103000c5540490302d514081c028032403821188080c84d5401c0701c1c2100343c14949000304265000307501c034149000c6414000151051b640440485c41c0d10b0004000715541c0a1030f1402100510491800501640c40d00f103022540d402c000c8a8000000d410318400c085400e10790300d2400d40d24040200098242c00f0f06034503100144c40300550482160b11419a08800140081796600c620b94004d103540c0c0b00398140001000820b40145140040d19000c0c6030101a1852650502c0c035140000d00b00c20b034007403040c8800000c161501101400404e07400040920010f49098103000a6500a40010b020058512800c20030382210007a4402424400d04043c0d0900d0340d10400162010385000c05900c1e082d0001041002c041d50601c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 48683655 1250 48682405 48682411
    0x4090b03070b04120f0c05030d0c030f0e060d090f06020c030301030b0c071509050a0f200409050303010b2107021c031a10120203090102040303020c060301080c060702040209030102070f0b 82
    0x89411400c282c50441c0741c0b03042c00801040507044c0305c400103064017402000c2c0b4200015150140132506208207814008051034044041134001030303410105014024890101030700305000040a47c0c1c00c04030303d000c00c0b0300140b460b014100e450000e5405440001515400500745407541080919200d6155003803441554800030070803226100b08008040001d040910040001001d503030000400f00454509189416000e9001406034060704e40000100310240400c3c4da07140c001a80d40440b508007140a002c2a58110000140240c00520040c00b48a0321132010b06209500005910000c0303445103030304048003106844110046c1c1107800849462448400807140361070051904004880401c80d0513621408900e004611824082080d0003800f88603a070349070341031258004219900c0c10200501d0707000794018401200940102480c40c091131070039009aa04803186031001e0030306010040100011944465000c0341c1c0f15500f48240920b81e18244044e10409115158a42c01d18540741414a5259801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 48684905 1250 48683655 48683669
    0x906030f11180c0304080702090a060302030f030c1e120c010203060405011d07030507030e0d0e21030a050a03021308010f06050604060f0c05030405040c080a050106090b0901121104090b0307 83
    0x129030750000702d8816450079400700c8060711050700c0b602ca030302d0901101d101d200c0b03000c0d5020b00707000e0500020004075800341003281d108a045a0f039900170801c500b07403240180a8944140e80094078103028070700f50111001c0805000380c1c180d9022141c0e403a603000d0741d0381141102c004245c0d8044104482d50611303120f038501501d1908201d544402c0242c904142034500100303a0070415480320302042c0e42034000d4200c41110144036040e98034240c0c02c007038010104090400000d120300702c0c14210200015083c44820646c01c01400a5840c01003004001d540550020745104100342d0300b0403090058911264403140501215000455082c042c03803006c1c81511410340201d807140c28200300400c03041d5002100501d126860b0f090000340c80703072941800342c00c40c055680201d4201e0b040048500300c181c0d126540d18454806220100030a03600c60104507804401401032401c0f00d0000c02200c0c44035070190700c001d4001e90320114082081c3d03070302c1024892560803541c041d840054a51640508500c0c050281c3c070301400c45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 48686155 1250 48684905 48684919
    0x90f03031003020d05010906021603091a0301032a0f08011b120b0103110a050306130903021203040203030c1f0c1809020714010c020d120917030705040906030f11 71
    0x1024a5078140301845110003482085905241c50070414290400c1004a4102c20210b4a40d500000c100042c050080301c2200028002c038408221080d0001140f6210030211100c45c1c1540e00759a03a0180c101c032090301046030b00a5181040a00000040340326001e400e01c85042200daa25210303415003501c49003213420b0081c20340424008121030381300500500805040d00302182840c0c9942c0142e00500540900c0303035442c100002c110651a40000080d4050720050b1500750b00d071321142d010141180d0047c0c400400680001d030f100001901400c01440d0018001001e891400b601700200c0ca241194040141c0c64010b10200390f40f500158030705c540d1103004140d0600840c1c1070a541c5150210b001613025035503e0990114010b010301040c1500b031600c1900090080050f00316255002c1c1d500c4090440b588000381d100d000300d0f1441c00140c0104880d2a07440509550503c4030407407c402c407904020b10420811801f4000024040c030540105030003580107020720111180d440c1003007505900000c403071a02840f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 48687405 1250 48686155 48686161
    0x50406080f091f0e0106080a0309050d05060a110903030d061503060317070305040503061e1b0912190b060901060305070f0e010c080d020319050108030901200303070206090f0303 78
    0x3102054200395076041c620302030024a01d50321020f0003801c0c001d10401d0950320b0400c6c0402c0b50500000d040c0003070340c002d440d408061907540c02040420b00b451a0014003540090000c502c074648160000540303002c1c819038983c1030004a00102c0c0c81e68026112134a40303942c96000800c0800000812003c800a041c50184519070841c2c0312044062040c480748115a03900182d64820f040c4504286d0b409031a00606540d6a4181514010020b4806409403006080c1440103d403800d400e02d600403140d5000d400300da505203807085080020517000d070070300c0310824003400300303007030301000304c1c45420320020380b043e9048025405c050041c030420030700582205045c0b624003c14000101c0e008500203030314814600c2c1c0501841680e8004032089010130344003c1c01d02c0301c007040300c910046c0150007546c07050015051100b4580c0c0600c1842d0160b070700078403421070303680c1082214108075441102011045944404909400c042c043c0865103158002c440e000c005030048800d0005c030000c180201c0b60400201c1c402141941 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 48688655 1250 48687405 48687421
    0x10050c03060d0f080c010e070e010602150406020702180c040303030f02030615030901020f0301170d031415180c031905040209070c0318060207050a05061201090506030307060507050406080f 83
    0x7119000c4003910350580f01c0ba070380f0200103180044076414032801009021140c4000d55003035a07903c00d070144964084a0000214080741700054001c400f690342c0b600340d4a5501d82d6181c0200a50010340182d800c05200c540c000c102020200781140182e18036145a6074aa2442c14010102c403942615a00003a00400030f1082540d22a5001d01103242d409040c035076a51030340e803000c80c020b10840340110201d40000c40000380401c0421610503400f841c8905440302d000c0109000c50443e070603001169905074180b40403030f1040c0c1420b4440820610081c0081c00c070030b1f0003080ca090304c01604690060b0034410004c100050180d03031a64443c81d03e032000d80240700724240303a800554401001001003042003404290030083c58412074404050a010314900341c0410f4407060001e49400380703409218061500e040c000949070810400700c4c0c0800c0741c0c01040c2c20469003011945005401c020f024194944014040d000104200e881014080c201b9a1100c40c0d4851510001034844d5200400d6034a009030b481c81085031003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 48689905 1250 48688655 48688669
    0x10b01050c0a17070609060614180a0e0a0204020c0c0a150f0e0a0e090a050f030a0c060207020d0203030f030105030c010c02030a142d0606030d0212030c071410050c0306 74
    0x19400102400200385003d10880507018044014109605117000300b410310010703500840550b105440c100c2e25400401080c414481c01480500380391802150005110765030301e50203c111004800143c401010043d000101030380c000f0021041d064011074800c1c10b151030001040c0d40204090410441e050b900e141c4080c04003034141d96000c040c840c015100c40e015503201700503e00035142400c6010a1410640407407039880a150000f15101c0c407c100b120001d951002086d01c107420081d542d41e60414180d41d40742d0313000e50046901283c1100c0030000410041e40c0c20f0000d0320000c3c486241003912036161908044c5072920381e4070154148042e10340c4040240c1c034085051035085400c07a135420885054903004500e40109c1400d281d030410880b0202005840d06011803c14140000d0221f81640c1c480000b01600c4140c41d200d40405680a1a50100e80081071006554410400040d86080101c15210001e0112611187c14000d8100c80300000003000f0034424182c1000c04649007500b18500400800c0759 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 48691155 1250 48689905 48689923
    0x30103030311040e0109050621070501270b0703021b0108131a070f02010b03011a090c0408010c0504090c0f120e030405132703020303070e010507140f010b01050c 71
    0x41540b60354002c2e106448150488008000c0e18140185940e90354010000401c820703600c42e44a0500600849400c5a00b110519070280d02070018142071407800005440041e001000c90b00c10742c0101c00d411915000540d404001401414581c0c0d07a40c07403441c54000e081101900d01d041303400c80c00320103a403003a076440100726170312100c810074035900907500341032031900070f2042007480060b480e610042010240d444800e01c1c0b21001e42e50024002c030a4a14101130a0740c4141c0300c1d1171100c228000041c600340c03030103c41190708402c40b800c040345413540301e010751403d41e00c0e00103881000c6040005d00300311180c07061044988804440c6081c0050300c2c00208001c2080e4080481c25000903120b05808a0500c4c00b03000710782c02048000c04004070408001318040140c0b00c0c0320052213102d091025110205548130151040446e895800b07507255969090041c6c0b021400802141e0401409015000015a009a45002c11003c1c0d2000f040c584408100007400d40e81c3d0f0390300181c1003003070500440b040600c0011789000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 48692405 1250 48691155 48691157
    0x203130221060a0902120601060917010204050f01050306010917070509090d080106050a120f09020909060106080f040c030f060501080606010507200301020f16030206060108070c03111f0b040f060302030303010303 93
    0x13503038540e50000404070200c1c41e1381000d86014410001503070307075080800c102c01c41d0340c1180c903004a83c03650701d05603080340502d2041d035401101d003080ca005958800c900650b0300c80814100f01d01c596440d081c030610402241d03481062254410340d0103000510700704624a0740209005c0052900c0c890226000f004d03001d042c843d4078213100f404a4480c11050040315a000b0000d0707008002c1001c00d864080e41d0b00504407006085e8010b44662020440704240403503207074140c54142e01c40070029100c0c800018402100100295100d07891220b011000840b01c6e41604030850041c0d40202c0e0340d5040000709410090050400c038140311040000f600007c054901201c2e002407684100d4002c42503c03000701e40a417190b1841c2c20814000060b0004c0328401650310004001e01a50807142d06990b00c2e001950710010680305c810125007230407001c00020b441051803c0091802c901a101202821603800c0e03103400181f000c0010141c0c98020703540e0103040030321454000b4090110140490f91560300401d48034441804050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 48693655 1250 48692405 48692411
    0x109110301230a0815100e04080711040f050405030a030c0801050f12031317010b0108070c0b09011118010201050c0708070b09030c030a0305011d16030207060f0203130221060a 77
    0x10150b03070fa42d000b22000302003420035504101c1d02c0b8034070200c400300c048407180f2503918200008100c6040d120922840313113901c0101c00745401216165500fa101d4941000c640c440d1325501110a9109640100350050384070300c0c001d40d101c5040540c05004d0b920007610070300c10080d141004120341c0e0750b004c414082c10709c020b40346a200783c04001c0c0d0080c21440383c44015124515440b80000e00f081101440c941c0da01603002c02004174904240c0116440c6c181660380c040016141880140810700b5420055041038103000001002c5900015151207500152210203000c01c50168440503542c0a018455004521102d51454014266260302687c018400040d101943c98070004004032020811034045190040440e91202940200100030301424000d45191072003401d4111313990819a442e86001d202e0404081c200d0400d540740c00c40094000c0401514290380302e0f05058079614084c40103500809000890010b80c944a005121214020080c1280822004443d80d5a0f0140114902d600301c10004004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 48694905 1250 48693655 48693719
    0x10309021801080c101e05090102010902100e0415080d0c020a0305120d0606020607140904090605010e0a0b220c0905030d020706021b030a02060a03230109110301 71
    0x2180c070490000c48440022065800085a00d040006096103d9201144c0104135a0f603008402c03a01c0c08900c0803c0d0300345074440e18041d035009002d100a844030840c180700000b440b080315000203103041d0750242c1d03404c0825a5102a0b5001d81854051813040051400c6c070b001200340782c1084155241d045c40d00c203404001a250042e011903a581e480c440007180c000b0b040340d042160844141d4021740c803a100c503000e86d070f00e00900000d60a001003403551180b061a02c40400e001007010300c41460382d20280c919a40642c3e91f040101c00100144a624042d0003c800c22024914000104000b1941c00800d01407241108001084400540c5540c0001070907443c00041050441404161401c192036001254940980c1603e07000e4590700241d0082103441c294220390300f100b810740b08442d403284003920b040d406030402608507000d824407d004103001121840e0000300d040ca10030442d80600064140780c0c40f803510b01c01c01003003418041e000b10b101e1441090107075403844d450203100ca1003460b41030b1428079102e4508070319 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 48696155 1250 48694905 48694909
    0x11a06041e0509010b03060306060f03190302100e03090307080111030103060b0102120706020a020706090b07082d041805190b030a0b0721090c170f0304030b1504110901030902 77
    0x740a00802015065842950311940f00c0c106a40044412038024405c2c100090704900d403400b40f4803010b440c0a40500b240030b40c0301d40140c2d00711b02208000d60552041c009443c8540c40144550f80d02d40c039000000d1034075141d4010401d82854a250f0128450760b040010603002080708034102c03411268848000102183c5110040c0d06007260700c0080070403000301003492414403409030024050100507609070b03030007180c80e800142c0d0162500c0c0200801050140003040c0007909010050922620100c500d0714a102da40000e111003a0000144010011022800700840481c1200c00841e54200440520013440c1841401142c480b042070949030303090f240c402101e1944c40900454100c0e80c1c200ca641c032050b11b0041c13005840d80b4229015405010f00cad061130555940c60f40c1c4164140a5880340c40f19000e280b62a41134450342101c0304034102140640003132007900c1001000204010341c82104c4020349450440203c000403480caa4103140110300781502110320920410803a0118078090030005488506400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 48697405 1250 48696155 48696209
    0xf0903030c07050a05030f18030a03120b030c150406080106050712030b061e03010f080105130605060102070b03100609081504080d060b0c010603050d0216060804030c050105070c05011a0604 83
    0x14054017074000003582078110380142c0b0081880001d15440d441d4617144030000d0540d20560f00300d000c0c0000303000803040c40380660b040d080918044070041c02c0300d60320681e60000071920b0302d14210040011100060030800c064004040b540100520305101c0c0c10801c0369142d04103521850750441c400c05940d102d1125032565800c1c15111000503200b181c1605c141c2c0581c222025500c03e00903034042003510340c40050b104205005052244010468044d820352507a07480344041d002c0034040750b0540c01011004540c8042000c040c62140328602035082406140c01e1014100c8861900300300380c1c0d0303000588120940d5001801444e04123170310031410b5956046048102c002405150804540340f4000118284c0c2010150006001d8a0055058501c41c00ea5900241c1c0d580c4c11010002540c40150001082014002d50036140e019000742000140b9036004d546271400c45804481c40c101007901c0c00800c00c00e02109100720b0796281084c05046c02410302603000110107004a02c68641c44e410062641ea802001c0c8071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 48698655 1250 48697405 48697423
    0x311040b070606030b0112080702060901020f10020403020405060f031b030c211501080a03120906020304030807021204060509060313050a0b0a0b0301051501050a0c0b070c0204050f0903030c0705 85
    0x40300d40c6450082c5408009070240748401e03038090340b4240011501d405138035003c13203440d54071105082c07800c003960b4240009a0004d03441c0034158003aa140d0a81c14a1003072245e9000c46241910051751175085104020440364050125070042c503011040c0342694400140ca80c4610110b10100c5000b0a18480004d2400000310b680c0f50f0401051000c800310440d101c940111213950784416a0094107402410264000302449144280c1d408401c07010040380c0660001005a9031413000415000016201c800980e40199811000038100c2020442e26030340c1441101151100d4207070b86841c281c500311000b8014020410329920455000000c11580090000d030b0f070102652040640326000c0160405c0c01c1e1082d0100c4040c0b401702d0800790450300e00d00d0306105043c4103044181d03885900445c0703580111811380045014205005501d08a040480c0b54400f0140c807a031519659101480300a106000a0f034401a0050440420344024802c9147c404403d8a6004a601051549035006801e00501e050108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 48699905 1250 48698655 48698669
    0x5030a0213051c03031107030e01050a05040b030103110f010e030607110c030d091806120b0604020c07090614120a08130e0a0504021002031801110a0b010b07030e1c03031104 76
    0xb05846050041d8285030780e03d01501035201000b40840f081040c2180e0312404400030002050b04040aa1560068000c4e1400d4130151074207a040984030001ba049036402a00141c0e00c102c001d01014249141507425228080c400f1b1802410b42c0a021011994030756001c0c00e51018000e900140005c40a800c000c14120583e004048071940711001ba40a0441d42250043c0e00e1143c0d0b0b2051407001100e0309026050480d9441d0208a031181803584075034460700405802e650b032068007004980080ca03010040c00c000b82500c2c0c80002465072801c504222529217070134084d0b005040d07500211902042c0401c5403899550072400d03040da1009048882000c000c02900f01c58517840c00c01003444140e0246500c280e12591095030005140701d88c0300b500f0390f901d0154030f00c2038506040200030402d840d4441e600f070503d08412001103030074100480c1d07542344007094240c1140e01298004208034080c1540010f410701a00000c6d61048d42000b10b4060010b40e0100700742d00902415110f0080c5031807602c1041c2194028504 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 48701155 1250 48699905 48699919
    0x105040203071103130f2108090a0b0d0501050906011803120c120c0308060a0305190618030201090b010b033309090a050f01050108071a04050604120b010801090305030a021305 77
    0x1080c43e10030141010b001703110451035030900c041f500074150a1551a1001c2e80040e180008450b5942c0c0f11181c0d102c2022242c001d1201103001482130b00c20806005030260301c3c0004111036041c40244280b00900422560420807003200c1d90301d0b0780452200d54001d03130790000b0441d49125511310090302c4001c61040010458903c0d07201007449140d00c1054000514440d5a54a542d074840f00108401d5214502020300580c00c000c0c80300e0f180000e02e055600300f00380b0448000c80e8100c0f03114a04262182c200c00e0580c0542d4403041a0010030807403441e401c0c05064140b80841c01d60800c3c00d1658070404101416201515003c80140b82c410184100c0400000000300100c56030300c1d046000d15102d034a9000d0490380e40c417403100003842c03c00c1c042c050941a124403100400003a8035040c40d004003042c02025044543c5010400421103480309c3c0f0081020300705c07201141c2d1284820340b90403e09840305074060a140d0745080c01034800650b01004603504080e1034140582c48208885d150540490180c0c04a548800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 48702405 1250 48701155 48701167
    0x31203010314060603030f1b2514040603080405060307030209060d020d050f0f2706010603020309100605011709010f09060c020706030902030a02040c050c01020a0903060b010c0b0105040203071103 86
    0xc04004195440501c100640301c180c2c698400b81583c80c0038002c1140000700d02404418480350b50115440300100c08081141e94062410a04078402809e920449501140d612024442c900c0200750900240009541c100006442e5807201c0360607010b603001d071038483d400c00008503100030700c00d4055520f42c50f0020051076885030122843c200941c0a071443e4200d040c1040300047c50301c8803601a16128480340c030b801468a659550140024001410318070b00d01e1200c2040c0e130a503c0c0020403250340688541d031001079030703810b00b070700141d107040ca42d10052080c540c2030400600685e603209525410160710080700442d90384510142501600c1c4061700004124900f60a507024040d081c1c1210117915200d40a035150b26071120300407030a5814450011f90103500050780b660042c00c042c1d000149209885c81e001d0300301101041c0b09400e99001103004000034031030003018414082c052003900c0003840242400040d40d103241d503406a5100381403082038851075012000402c00340c050044900c0310038003581900d584103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 48703655 1250 48702405 48702413
    0xc030c0304060806090f04110105090d2108060328060e0a030f140405150d090209041401271103030c12030a0f050403020a06020702030705120109120f1d0312030103 72
    0x103c0b0840b2407a100e481c3d5030380400c1c800248240f942c3c0c043c1e80c003c1c09001e4045282801034030142d000d201480c1d04400c80007941004209503107481d42000d007040840d500514000c2500400f40030001d880184242c0100f40390506031a110003200c0344a12483d4501c00c00f8036414140780c0c004091460185038240242c0903400c0805030b00041035041d61150b515410b8892104607460040760041b030080d01e0700076004550550080420307201070410460b503000040380203212030303000ca00305a0003510216442c50890700103001c200420f001d80e44101601031502100705100380c000b54500e0302114009820310000301c0e10742145803001d000f241c582240c41e50468840c000050090030721a4011100b0700308280c075000c881000d00f030035805014000d507010340c000c061801154032404000e61008000300e070302d84203059001605864030041c014440040f08000140d90869003800b4015140d06401481004800300b106024660800c00e0300e60203d11280c1a8420480c16001007864400f5485c1c0902e50000f021000100704 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 48704905 1250 48703655 48703667
    0x14060403020916090605040f0603090c0305160e0f150f040e0105010f0504110306010906140405150d14070f0f1202030a0b0a1202060f0703020a02040f0e0d05030f0109020c030c030406 80
    0x3c1c0c1550303076a00601c40d50b51201141c25000d90b005003008420110302c10070800380f0940002030080e000741b1141c3e00e400d42e2581c03064902205508044e14500450788100b1070a040c0c5107019900c003103c000040114030f4a6031113014811344014015100c1c2d0010b84180c1700903221603000c149901824002042203503192002079900c1d016901c41c20307210398109803030b98402408005c245c0b40102d078182c50f12030303501d410902c2c1a1140d06a5640c01e81c034040040c880050103907101c814080c680703a15813121075518041061404180c6008008000d200c03044e00c0705029140d81c1c070071103c80302c210040c50911000c1045000c00c40d00b1480040005100c18000300601003210b40990048040c01400c850041d180c40d40e452140e40c01403445035002e54045010300180070b07085514070003454010712904c1903c40700002580010119003c0c0411581c106949030410311941c003080010980322a06820054158601481038590f424014082c500103140c01107428030180804000395288040140d0a44e03031a41e031903103002445 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 48706155 1250 48704905 48704941
    0x50c041a0a081b031c140f040315110c060415061a040f0608101206110706060f0603020702060715150305031312020f12071a031504020c07140604030209 67
    0x401c0d032404524003c1c0c940000d101c403004088500070008082003d02c142d55000c2111100e01201c00c0400c0545a0104500700510281d481031820001034020300300303490100d0300b00720300c3c0c012403050410400140d54000501c40340d00c942d1100d45044114517000301d60010f0711503035100c1310105100c01d401d12069164030000d041072f01c2c450f01c00125440d598a404403030107030b030a403800d40d40c81c03100c00700c02c0c8440a600710344421454016200490311710035410701040705074001074098955680d1604144200d5010740c044100414042c9010340c02e200b0300750001402c500c25540c000304880102108010645a00d8000111100f6541c40090300c50b903503410015241c0e8082e050a1410000f01c640103d0300c1d107002810741e0700c0c40740c0140c0201d030715120303003c284002d940d4141d443d140a846514400a040c00d1009885024010711046e415104c3c242510101210390900c1c0440c0c1c86240140b000300b03005000040d203001124009d00c0a06054110302e00464410701c92600080c0d005900c5004211404501e800400c03a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 48707405 1250 48706155 48706183
    0x51204023a020f040c0c0b06061209100605010206070210090501060b04030803070f020a11010c05160602070f0e130b0a020f030a0b090f0f15030106090c03060509010b0304050c041a0a08 81
    0x1000f04a12010007003210214034294010a64040703004000c12007041d421580b2400c054146840e03c3c1c1191a1589507100803a40381450341c0c001003503004040094000e0303400401c402e000410036410112006500c622803c00711504e80c070703911701a8205100c001d41000008040001e035543d607898403401c001d00c40d9442194010b01003050000203801c0184005a4886044c0d00805220003424410004480b041c0d03a80501f600c0700e00c203982c800d850441c000d03100c0800521003a0020449145412140e03102c4010943c0250500c01d40c2c441040303094051640303140e543c03603809120070307240c1d0783c2d540d0358074000b8040c0c2c0c0d84408410401004000c0000c040758800180780f0011105c84241da5588400404152313404c0b03840024044954011030000302217100d4401d00d801e0014008181c591315407800d030041750b403001400c800094582c082000f40c0d007425103000e40074004192189180d4a0141c5a00c3c0d03072040d443c00018000daa41c1c04140c07201d10040c0c0c11302c184080c2d005004c400c22682e11800e03580c0e1214003c040c54 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 48708655 1250 48707405 48707419
    0x9030e01091508010504020a121401082b0c081e030a060e04050a030f02010b0603040b15010c03210603061805060601030207020a03020f0d0506040305030108060601051204023a02 78
    0x3040c100c6103603080740c0403050389030b4075120f02c0da00f0b01c018403001e5080103007040107100e01c8403020070114455014217124644001070b000c00d00d61410b030f2401d01e00741d003c00c4e02d031503101180000d0003c2c000314080c40c80da074941b0307500700407002e0703c00c03498040030b03502c06c180007047c4402e64140141200c0d04001c0081d405400008020300180d529591264001d070426030b001080c80c0d00600c11540041d0054000b120303000b1450000084a920391804201135600c07c482c11507101643c0010032180310090640c51031450420b1070646481c0c4002d80e40a000d901e5014103a0807a505d0314113080f00c0c4086a0f80000c0c024503840302044c032440c02010031000304840b4415044400f80a00e0700003800c654881d2091301c3c9815002090f042c0403515540a0010010803c202103821004070004200031401c10004140100d1007565516901c1d850980c40d54107004010380500e042041c02c00c40852000d410480064020b070b0110760110940c00084400a6540039280c00286410815800304e407844100c4c16415034118000d83e555 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 48709905 1250 48708655 48708659
    0x10305160b1206060408121c0e0607120f020a020a020307050103021e0906041e0303080906010b0d020d0902040e0c0a0e090a1202100203040b06100c05030f07030c0609030e0109 77
    0x15000d144007405401c5011400780003403800c1980303100885030000c00183c0b0641c0341c19250383c0f440c5d003051201400d00c400f0a000158030102e021654200d511600c4540304200859403135001c0c500c0c4c584034041c080f21b00b00140c880d200002c80109038400059189401421981c4040d69640a5150480402c1c141e00c240500d1100042c1135005e80201c64000300754043c0c650403850101d14100598100c443c41580050080c440400c0030300b40306a541030000e00c511200b14406245290040c02210300501c000010340043c40100519800607040c0e0303c19012018016884145c0150000c1c018002954065030141c2000c44941d9421b0000c6903504280c20f09896407500c0341e40703507003445a031610305940417051580550800c80200c0c1040d844900001094030555100055030f00b031840998206a80a0700d0a400c1a400c0c00300c41d02e807041005081c00c00341d041c295525401c0e40c070703030a40360300030186588001440014210f04041c8583c1c407111600380d00510809c000c5895040041c001d05510030606c1c04980d60240c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 48711155 1250 48709905 48709933
    0x30906170105030606130603050303070302040e2802030a090b0a0c171303050319060306050604060e09070302010807050d290d12030b01120f0506030105150901030b130507080303010305 81
    0x34090589102900401d4591035200c2400800c0308030905000740315a4980000c03000032804d0008602030703030003a0790268569080001d04446000054107180f06941e10f0304400b1012010504440c0c00f41c0744008006882e43d4804d03081101900a030400180392040141c104a03e4582c5070344014a420320503a0340b207600c44d5403006001a0203a05540d9006c2480302110880d0000388140005c0d85d0000460340c003410140b072a21038807401c0d01e50342c0e00201c460540300d07004c1009504007885102e00810700c5000c50b01d009d0a0500072140c840c2c0441c00040c0c100aa103600003001c080c0500210340030209100c10802c458864051039a06119805204410061141520214a140c0a4484d0010581041d447d0b01c8200c80d43d50309030f005150a80d103040c18080007003060304184905100e50003001404141c041140d1402a04150864800070b1a100000220411810580d02c4600c41c0a054030781c014143d060342d40300d46200d140504104280105a1b11504001041040c1c001c000345048910400407a0f1548840c044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 48712405 1250 48711155 48711197
    0xc0a05060f1e06100314011d0703050601080a0c03020412080904060512060106110106050d0503090906010306120305091203070c030312090b220204020d0207140604020102060f070219030906 83
    0x21a048a00c101e082c0415081d2411034181c01c41800c0b030342000228643e00710841000c0020981c0325906460340342d002e0400b01ea01440209600940c0d40c5000c214914200001070030716000070b003003001000d9803a000080081c2c06941128060f08114010760304080c0f481c540100c0300c1d400b1000a42c0078a0800074001114102520022003204106025114682c00c01404642c040028070901041c0d40d29942d0000d01c648403007000107181400ba030042e642d1103151006100c01410f014126604261400fa0704006e160701141011001503410700c0c11599503400800010181c0724a441c58a1240c0400149801004400d24040c02264400d466454040502010340801c56000004c094400b04034100003410803144000c1414400c1d00d00d40c607d03000038140c0d17000304041340c220801d03183c480742c0d0000303a0700c09114552075810380c0c098070354000300003a140c07650000b034075a400039003512400c218141c08650418001d000500e00a600740407191542c1c01d00d414024207902c2140302e000e000c9803400e035500e8000d0004039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 48713655 1250 48712405 48712441
    0x150f0c0c0306010e040209042405070206070801140f03030d050108060717093a0203030910020711060f120708070e0409030206040308060307180906060f0e010501030b04020c0a05060f 80
    0x410101013682d52034085c020f0b1100020802c40e04d02c40c2100c2000204914860201e8141580500c002031503d011036000c0d24000300501036400744208040100203c5040d030380000d10a00064580b00d034144c280c00302180c07450145910800038542010000304402c1d85c000740052288407550f5513620b00007421440c84007008800d69001c405a082516481d80d00814805503481c0926210000600c1290901e091101503146d0841080160000010f015210034100180c039100495903030300b1031604215171307241d03020590843c00c414003d040c0841c1203180070103c00c0c01c0da1010302d241103860801c0d280129004050690854070f41c0302042010301003942c50300705032041407102c9915400504058455440a4507485c000401c480e1b45032140200108581c000c49029014044512401050034813030307480d188080d43c1098001c4071958200c540300b007061160458801d811030381c007800d000580c1d20000b0b0100380a449904010009072041c1c01d4414200980000c0340c52140007441090b20050b00e40e0055044070f03a4000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 48714905 1250 48713655 48713669
    0xc060c0d05010608132301050906070e010e03031902160807080610081b150a02010b0a0501110706110102090907080a0509031306050306040e0105070507060606230702150f0c0c030601 80
    0x10400c000205440b00214a82c2a035800c05078590740540803903030079100d04070341080032a0441d00a1080e901d400c088100010366003400d00302d200807090004640da80c000d0380742054015046108076074030031f8001e02c208140d3c8005290841001d58407a07107010380d2400700340310740320340c911035100001c400810201641c01500c24020140c1850310403844a42038448004080b950b010006135207101d89075102d074000f4a00f44116030004514070750100100070003202c01d07901542c140b150758411300c024144c02044000541e02030b0b06010001c1060392001c54024000c00c00f0300fa4105031440c0900441c40d030054070851144401140c240a299944c2c00d156469020b60101070512481d5600c0a00c080b0380101e0240d0390000300034200044003203500ba01c1d182962400d403110008035400140400500100d0b00941e0040c00290401c0404049190100030000e402d404120000381004203201c000c5507929610560000c0b030203400e0301d484881e42d004101c8180d014000700030907807083d5014032105050104001d4101c2c1c00c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 48716155 1250 48714905 48714931
    0xe01050a03050702100617010617060f070e0406060e0306090a03080112170426010515060304060f0510150311070f080f0d0203040309090504260c060c0d05010608 71
    0x40d059000d4040640b4a0f410341c00f032090162207503ca00e1146100901401e5140b041400100400c2421200c80d500860803120301c1c02030300010b0400010f04281c1000207061001002d07510b102d012076283c2805642d055103e4106900021115440341c00c1ca00a00740c11409ea03075841c1c5034422403558801c1e080e80003e002c1070800d4010002411255440b2403114007a441f02c5401c4100d641078044e2036401600485500807101d203509141003240310f0104101d1546038000c00c03072818541d0000ad0110341042440c3c1c072951700000080c04001d1160091203030008a404280842d0074140303001c01450040d4081d0f101425009428102c03040c2c443c0c001c8101d040840c05015140011640303c0d08050141824240c039151401c001d90058003503000010880e0500c01c000041c0c80e41404d290041c1682141c0c4c0c000d00b8503908180502c0082a003041c50101c01400500302400d68a12814883c0100d00507004010300d94080d4208000800440100801022940e03110803c003c0ea295134090343c88903416594200d203081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 48717405 1250 48716155 48716167
    0x30516020a06050c2104032a0b0402040e010e06060112060e0109020304020604050315010302041802060a0e030c12060907090c050a0509030709090f0203070501020606011d24190e0105 80
    0x20f68401e6400040d130052003894600000001c400d0403002c40401c000c403401810411013415440344040342c41500d0440a11181b00302c2c40c0b01406510002d0502404654500005c902155610360020303607036202c80d000a00064007401e10058443d0011078400d030124110340c0316500580381510038103003980c500100c0b248159080030040d42c02500028400c98204200f0000400e547d901006084144e00410030004215030451052100303440c0d5a1100c42d403a2a03c4200c44001640e885080e5890000e5a141c85e13004120b0010000e842c00001214050700800004141340c504440410300d01d20138000d10085822440d80c917840704003202c0758140c1d1400054030501410b03d11078481d80c01810402d50003802ca5035001c0c1c0364403040c0112a0700700740c100c0307090002009000446c1400c1c0501001000240007519403490032034006004216402e000081c40e0b80c03085100602607a40d03807240c13a203090444882c90780f4401000f46007091540501e506050200c0c469180d00002c0348909c0b031a082e040810703518103040030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 48718655 1250 48717405 48717413
    0x509071b050322080c01090608011421010b12210a03020f0301060903050c03010b100302070215070302060906010e06030c060315040524030c0f060a120504030f030516020a 75
    0x50084008459600042154501459505100215807242c1c048041e0700945071130111440c4c030390b000310094140452500104645500600c84504407414107030300396501c0301040d0000d2040c185540410103d005400700212802c00158081044040299104105420350100707441e40c901c0138444041101c140c080e802403651540c8006480384450505015040442c2030703160500d981c009800c04030000f12520070070010300c041044281e81402003540200704420981020030501c0381500320b5202415000540802103440e00750140d01240da038100003030380f2059981340c002c0d2101000e840c0c1c0c01440c4108000840c590940d101c03030500444008009184c1c0100d164140700103908024001490215402041d20180c0c5071401000d00c02ca1616050741240240c0f0b9220000c88103000d44030307a01903802010000d41503140d8074188a400b103011151a51030744030018084801c4010302c5500710966041c070701800201904071141d400c2410381e07a101070007070f46c0c0c035202081100082d501740e040c01a400b542c0350030081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 48719905 1250 48718655 48718697
    0xf0f03091c08040510020312040501050f0a05100905070e0613050909030301080a0f0f0b1320030a062d0605040b120309040f060f03080c15041a0709030b0a02030f01050907 75
    0x30545c14010f4a00b0b1181c0f0300b0003407800c0c80d001c4505a035941d44a400300441165035a408039800503a064040205051102b81041501800e003e11a5040d03595808514864014902e5144a0100610032552601e004a0b1010450824490702d405040583d01040b00c01c0ba010007a24161003e520040018610640340d0384034a0055102c2900e0b81c1100b40c0400000c1401d1002072071140d0b120007200c3c0d4842d20700740342112540921a00702c0c60a01442001c50a15507000308100030301a07000b10b0301180111041d4140188961440800442c0d90181c1844011318451350304640c04661085404006003255907052245400c0090284400e54008000c105141d1810381d12108078000142400a512510b40d0041003110405402c1528108004241107c41d01d0042001c0214030312058000b0300d450074140c5c0c81140f182681d010120006a282c0b002582862151351604001c0d038020507038240e2414021440c80080d4001c0d02e085605e00c250000204840c00c0c80340c0080e015102c1a40d400d0000881d22003100d0340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 48721155 1250 48719905 48719929
    0x20102120319060303031d0705010905010c080c031c0f09020108040311070305011815060b0301030201050c1f0603140109081e0f070308010f080703050a03030c020f0f03091c080405 79
    0x41d000c54000c07002d09518034403400000e14880d403400909052101d4500c0c9441c525514004e0040c0d00003141446a81d0340000804102c0e035082c03d00481c52191443c203440c4500801c0684009840003141c9040b00d40400c40c028021903c0d41c960410144c0600b400c0c2ca000e0780d0080b98042d0101e00010b02141c00070348101a8102204042c4c0e00380c0c0d84886d00c80d078605094440aa00d110394110101c4d03000414806d052000c280b10405051080250526152181c0d070389000510002e4148100420722a2000e036061103030340a406035840e40860302c8039007a40d01000a2801d4003050710410704084242001a405202d0201c042c0d81141c082818986616000545d00450f00805d480b101c4040c4410036095400350003400070284a611604001e60419070000d0303241c4072a5125054a40c032030031003000401c40c08070302031800719018600440c0c0c00008802c26440c22544580664aa200340c060070941c0350400700250065000c100d41e1440490318945d04950b20544050014050500412007008585404480042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 48722405 1250 48721155 48721171
    0xf0c031e15090a050105150c0a0204180b0108060f160e040e0703020301050c030906072a020f030607020a150b0a090b01021905010e010b1008071404090207081309090201021203 77
    0x111040d140c00810300d06401698144881e44c0c80380010f110f0784c50305043e0480329040020080c0e040102084425560b40300c40031010f030040d83c0e00d224441c03150f0760708001c0180b03080d003001d960481940d4404029998110441d00004281c0b9420f0100d0321280754420035201061603555103034070750807901c4e081100420010304400d500e446603102c0000180c500303010301340c410041c003200c050312454045a1a410030304000c06e41c408006120161000400020072030a10a0000e40b0030311145050314408600800d2950186070b07810301c2240108600c1a0780050703082c140d1072041034003e10300121000488259902c1c203802603030000c55040c003849020020703880038024000c1407040340d00008a0b000c2c0c0030000d03600140b007500c05035110491081c001c0b00900a180f414202518500b030411001c5000a01d03102000c1d1200d0300304884943c082c081015043e00380d902402210a0856440a003403400914a5200c1041142074451214001410310824880e42e2102c60701038001e0329800e01c00e40301805665100400d101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 48723655 1250 48722405 48722431
    0x708101502030c0705030a0503070303050405010f050c07051005060604090f0f1104061404030c031b03140c0406080c03120a1116031a0402031f0908070b0f0c031e 71
    0x300e40d400a46852606091034010310394442c85000c00038240716290300034501950013103e074480010701c0041221400c0d41c15103070010ba19100c40c41e04030b024101c02c240403641503040c03905000809892030010020a44070300308807144044450384120648004440007171f40301109010401c1042c045401402c04400032110004521a094000b141203446a002d803012050010070f042c001160010a240882a1200c0301581080d1440c2d4a0241a0169002c001e004c1c103403106207940101444d1048101440e4000300f0420003d41550100c3e5484844010040c41942401d50001d02d11801044044408d84060081c003000300d090461030642c1d50000e17403124100589440e503081e4020047c0208101365814116001c2c4491031400c15641c0d080b00c82c009a40c98801c100c00340030050341d0010b4100288800f0b0180c0136454045a0146002400220805040d1000c0024801d0030000f05100e0a80b1648582d4910741040e2200251a4500e00003203c2115010b61801030140d090310b0030b8040160311a138000c07696 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 48724905 1250 48723655 48723659
    0x140402030705040b0d17040f06030209030a0f02190603051f08060a0e16080102070308010905061e0609120604140a0b07030b0d05011d0d0c03020705090604021605030d050709030308070810 82
    0xc480c86c200030402c1c03c948407801080a118195090740c402d4000c290500d401d50030701c181803000a032500076107900103243c54080d120020454682684070008003000b0801032800d00c3c0e49460240140500303ea008021700c200d0000c07450000240d40415041d6408007004010700d94451052600800707021364045003d100345400200044071050004010300340405c000b5031151030600d40548075585c1038020000b80b50815041041d20f07120b03091141545401408071170008800c1c440851050f1007814001c54000c101c0c4801c00e5840c0300d00160f5503015038400e400b0340510101c1d03895107a480b2020440000c0907440004c01080710184650822403040c1c1006103021591213003503030ba09084440040d41071240b61030000000641050901c088032440c000f906122958078079681d402515070f4114041c40748904580008502e180c3c90b154140d45450840111114600c1098141180d4a0300200c9411302e01c141044000b60095210340c80341c008480d407644840b407154580a106a90890f0000d1a03030b80190103000d40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 48726155 1250 48724905 48724913
    0x210110f0403151803050d050c090303130e01050306010506071407050414040309080c010504090f11070506090105070e100f0201090b070e01080606040602120d0603050a06060504140402030705040b0d 87
    0x500045200d243d800151448015254082d25010360700d0004a0200000c40408640c0004c21199904410040020341d641e8030440307000f50b4081c11501035018400492008440303c1c0301b81e00901610760903a90300368282e981d0810196241c41c00d006407030700b0040c1030104000184080b2143c69241506e2020f403140e1944602c0030500701d52001001e909180c82000c20b003c241900024034001804c90140074114004807000007904d14131651040b01d141350340d549940c0b0501f009076800300142c541c0d05001c89645000e5410101e40c0c1c0c20095851001c10351030000421340ca0303030041c1215030100002420b0401c8801c00b0345019643c02c0b8014681100390354941380c0c2203002822135030900340300d051070343c88410304005204001400301000030902806100c041101f40140d5400081c160010030542c0b42240c0c0e2403000200450207400b00f6400103280344203640d492400c0114640240c03042d0b48050710200090800c00e0380c182107801c815900a5015008032009010600742508410701414016240c0030500040765a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 48727405 1250 48726155 48726157
    0x813030813030b15031b03012012092b051b07140612061909020c060115030b18130804080a050c010c0519030309061a0f0103020a0210110f 61
    0x8030107a020781203444140100021141c2150300104451180030f1155140e0700426907680c0b002207841c0030991071105490113a80c00b50020b12101d440121800c02300242c904003500140c0025100102802190300010700c01a0300003003071492100c0c0c208140340400c01035046800c2200c41076400c10100701c2c0400c101140d802c01004d18900b000100b03402090f00b14a8030640404001c0d146442d644151000c10400c52140c5004001940008040fa04030043c0301d144050b40c10049002d074000140c0700c0c00801d00c40028040401c2c2e0a04840c01c19006603880040200700300c048426007035015034002d0404031000b11800300141429406141d12222901d041c000c0e49404429030015030003042d0a0b4080c0030f208003004010300240200c4c0500b030808064000141d610300d44c4942003003111a84100c40010694149840f070f422011000c4c0e0230840070441040d4503291280c0080b4030001c01ca000c4c0400d2036005002c0d520a1003108d00980c2103a000c1e105050300c4a400101500a0f6840328414071418000c1c0450802164 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 48728655 1250 48727405 48727417
    0x8040c05121506060a05180a12060504021f0f03110405030109050106050a240806031609090201080606040f0506030604021b030d050a060308070b060307080f030a110105010501090308130308 83
    0x70004241d00029042420704445008201e140119814000d289005401c98181c400d5500c8003010702e14100510408138010030000d074040c484139500105c1c42d41c00d03c00103900c4180220b00980b03101201c540a42c01080c030054070030b00c0384000203080c2c0e05051003040c4a6440240100340d01500c007444c2a584100007404e4a022640c140c7d6940d644103810001ca1030041d08110041c204103990807401c00c82100c1540c050400c8030840f00a01441c0f200040c4180c0d070a12020625031101d10307811420b20b45400c0c2e0180145181c12003240410244000f08a191903e64140e804980c0300540d45800141400188181a0000344c1010307003103602844102c0700030003042292280c0c05d103401c00440e00c40710040e10540030f43e5409058180201c1c035080703060010403507040480d108d4642225401c09987c03916400b00e4500302d12907100c803c050203500d40c24a0f41c60300100042505100310340d6000680503240c540c0030b003203036401e12429000c185100c500300001030444001c2c0480b0807550b04041ca0190741c984403aa150362220b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 48729905 1250 48728655 48728689
    0x30702030c07150906050a05070b010b0d23060f0a03050318091308040510050d06060207080c011b0b091e030901030623010503100807030f0605090f07030308040c05 72
    0x840e800501c001c0c2040180d0060295101160007504202000751a1981500400c81040b5002900310032450290007150020355016244020641e5600c02c3d96056400021500c2015424080e04803170030007248488024500007805450515128030007007001801c42980e20b260808450030b0004041141800a4070b50f401c1502e60001c0f00c0d145100402100c2c80c0b008000b0b4104a96165003403001c5003098040c1c8050318000d031440b0241800350907040d0741034042c2030801c0c264107042c4200400d100340c0c0454004100d503544030803680c2002d04440152010740c1054810009030203a4070b02d0301d0120341100895900524a4030660b0030644642c070041007102ca0481d281159581b00140c104010f50f45071040800500c6011040d5000041e41c1d01440300c800f8801385528100300303012000c00d201052280300840141000c0b0110385440c1c1e0b83e864807010900c01c1d198141d8810b45401e0009034010004039040c2d2661050300003518131182996025240007801601c151100c0d00c2e4004041156100c141007040342d01d0340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 48731155 1250 48729905 48729907
    0xf12060f0403110706090b0f090d030c02011d090f0606130608040c050109081005060102010b1008010e1303021c02011401060203120108010c0207050105090d02090f09010c0e010e0607020d050303070203 88
    0x4181000791400c014685529416406080c08001c5d55900501c42c5040ea1007094070310350307600700c08144015940624020568407a045580c100704040d002104c0c8500790f0300c01c2e29243d4451280003010b440f610550b803c0c00c0d41010030100000e1406010311013080d031103240140b501e410065003100d110301400700c1e40c0002d80440c03507150a0109110002043c40010b010901c0c108615500700307049680c861901c0785058032016202c0c0302090b4541e00039000700002502c060121581c180d1810740081403194288200c0300c000c41d10f20041030300d03010724004c00c0e411660144c000b443d002c6880304808480400120349042195600c40803404400c0c40a40014001c1c5010380c011034886460702c0024241a6040c1e111040d140c0c50301c44105101e54011902e40c0480d5400d0904a803105140303404240900c0c9146002540184030340200201131114010090081c94040700800511403800c0c005c0c0d60000a01d08800d020a04d422801d040610702000108480ca1014000002c2401130350b4038241b81d03410039541203025800c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 48732405 1250 48731155 48731161
    0x40504150b0301031b0509070507060513080a02010f0f11091e031203010302010206060109032111070902190206010302130203090a33061203030504080f0d0c030e0a0c050f12060f 78
    0x203010176a8009424204d52002d81400c04050103043c921662100400e041d8444000071454025504c3c4640044d401c06099542c030034800400034020700c00745001982003864020469040740c41d0744902504480e0b1703c444146809400b804006141c460b5640320b42291102c2c8241c800a13440901015500c105800103094407541180b00280c1403410050800741001002081040401d40c80e104509810215040781d004002a41c0703c2110700221034209410a0f02c0b8030707000018259840e41c010302e009100e0b8408a00b210001050032a00e640b02880082e50155290394075840f9541564000c5400039482001c83e113100c1a1560f9082a170160409581d9907030040c2005c40303012001c0329081030700945241070100803203424406000d150441050b0050209036665001030300300f10100d8204e030507240c140034120762101000d8201101508492a0b5080001d00b418161407001c003002070710300181d55018901d610005d05010904c400010100c0b00789601580d2500b414034071500507c00c50340561703c2903605608901d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 48733655 1250 48732405 48732443
    0x30a170307090504022b18050f0c06030f0c1c0e0c01030e07080307060e0a021207050a0603061202010c0524180705030312070e1c05010e01020f040504150b030103 71
    0x1802d50700c40350142d40100700e07141a07a0f20186200000c050100c002d00c04541030102210002c0085050301d04609825554400a0003000640102d8400c3c540085402e045104400d001031400b06407100c3d03c0c410584408640f054064001412040720035851a254882c0001a00c0080c0c0d0000300c4000710503040012190415681405401b4014001e0002080361900d0510f00a50300d103d0041c0161280740d0304c0d0a040e141003024041440c410360010308054054004503526a00d84105205103845000d0214000902601a00440d000c440d0460718000551846030019510758480380000c540740d004000d5140007405055844542f4210f990305805546c0c600904000e850b03c0052020482560055908008a5070000202c03124030b001048880300d60345031250280d401f1504039040907407048031804007400c01c0d002c451300004164040c0000703120202461100600302d00c1410700b4030310a42403c0000780316030300b03154001c0c05001601e400040b00c883e0b43e80100c501c8a80003a001180c0b041c2002441c03440b86 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 48734905 1250 48733655 48733667
    0x30e0d080307020f01060f03020d0c1511010c020105070f05030405010609020a0e0f0607050717010204180b030c010c05070611030f03011d1021020105070510020408070e0c070b06030a170307 83
    0x81d01e03000700030030075207091111f01d5800086038480240f09101040f03150040183c0c032031502001342a2204021a0102e07440380182c42481980d8500b21950310f40310301e80c00010b10500816014845030340311540340410304102100d40754001081540c2c590348a100000340740d10280300030400c0126695510328201b86102c1005550510f6050031803240c8020f00070000420b00c08149101141c0078110301041c001992400c03180680030743c0e44070741c3d590b40c5181c59400c03a03040305401c8640804422400e46807a000305600555000000da003004d0500d5002400603c051401803030320002000d103880450303040002c01e20f4102c207994001d1304140540040701c08140304407910410074641024900c043c900e00c403818600405019149020700d0890489087c940c6410b40e400b6104440b519a0001700b5101c078401e42c60a1907010394031910524880748a0202d0008401181400c0319000c4d03c5000c410502d0080d0710b403078094030040c000c1c2c182989030050403048000a002a4001d13205003c1e08000151030b440d02c01c1d07015281c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 48736155 1250 48734905 48734923
    0x7021c03031b27180207020d0b010308070b0105220e0f071418070c020103110415030b090601030605010203070b06030c0901080109170304021008041509050c0a0b090604030609030e0d08030702 84
    0x1030003503c0070007401030491201e14403a0000100030010f0b00c078007203400001d0401c1d046d001d0140100344c1000010080c040004002c2140c03074040e568001060340d99400740081c0c00e42c44070304800c20750a25284000850082e0700050408580e02c030031903607e13030702e080310b0242400e40543c0501000705011420b201b00d81002001c1c2240010f01d910050210700e00001c0140a00000b080c00174100745da1860112a024440410b487c0034045c52400300c442a2000d2901800a040c141696031280c41084009485903100380030310001d490b410f0340a036082a50039a0795a000080c0503107441d40c140100b800306020790310746140c5035000704640e1002050300681c1e07060815207850102003e8460450400c10000542c40d12007403404c801400345810003903546d99080c0b084d440305040c020a1861800c1030368000c10700100203260210b070401105c0b5040407035519041c840d203c2c411000100d0b0040d405000400204040c0c0c0d000002880c00307402d05140b941c089900144601050050132160303440d020050020b655810801019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 48737405 1250 48736155 48736217
    0x120d0c050306100e0d0602030705070c080f120304060902100519020604030906050c010b0a0f06090801200304050c0405160806030f070b0a02010e010e0706120207021c03031b 76
    0x114504081000c180e90050f000b07030320702c14440c49041c204140c0e10307042d031213031070395900100119200d043c0004010403d6010303000560305010504004070304280e004c42c20751400341c1e03440c0007401003e43e01c0c0300254a640008000703640c030310340d2080c51401513101c48440e0b914444096440c0b82c1d43e2103c880300101c0400001509208651003001008002500030f00d041c0203a0b88603041003511100a9944c1c1c40c05001140c807038030340000304c0300c80004000d20b80b00076030000d4900303944410b035007a030b1200841402c8829011040b002c1c4940180044040304040008540050150080e58401c1d43c2200100702918403e0754a0141c2c00e2410350a10403040e440841560425011405060b886145144e140e43ea000350f401088000400011551203180c003d6114a000448260080c4542c10080040030b44034940b621580300400d951013810b0b12911298402c54a680303500400c014440d02c5052003454070b0101001084007030554a5880740c40000c1c400007504092001540c03411025049240a049408074441d5441c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 48738655 1250 48737405 48737407
    0x6040b130206030402010305130606030305030a0f021905070503040305010507120506030f122104050a0512040605071101051c051501020f0a0b04020d0b010902040510050c030702010e0f03120d0c05 86
    0x100107a94080861350440d40902c2d012560f900c8003450441204050751004200038036040e000001c00d9004800303948140e0104a00700308482c0303522104801d91080e0381d04490661a640780422049000e80f0241410a0164040b607040648980c1d446084550654000c404218080c25110b02010305001d1654010802d801521202c0c3c0000141035071001481c080900c0c070080418141c160304a0060081c25101d101404200c840c1001d0a020f905c4862451003541d135405600c0300704d20410341660445040700d016075605494044a61101c48203041c001001ca03041150401030303640c50200a01e091108800305a0001480d030400071140b030704079500308090a0654014448900c5100d101048500da80740d0007024100c0b0560311440050300c2500016001000c0149460012405050760b83c0580180c9109495148900365482410b8415015000e00c0307002d1503208011510042d44142e28106410034081c00c200d810000c0c00000030b0400554101c3d4000000000c034481d02c44144c036002c0c048128507141042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 48739905 1250 48738655 48738691
    0x10090c050a020309010e0f03010c0e04050a05010e0a0903030f0606110c03062a0705030a09090605011e0e0d060f0f0f02090a030212030903030a0806090601080f0105100e04050906040b 80
    0x1940b0f900a0a4050b030600005a80403685a142c0388007449075000300500822800c1c1d1081c0c0701404201214443c1c5c2d0082e494000051071800291282c54180d80c0b240c0c07035103c555501c0180c0d42c0041c00243d43c08408040e2104c01014070600d0034003840018107920b03228202009038070b100417407070255007000e80c6e0310951120051220300324024082110010f030800c0400c54510320400445480d12440d0001001c91000054084403580d220b82e84d50150f841d07002051107000d81e600c1c01151802900c045108490300100e4a0501090003022000311021028122900d0706025854070000c4994281e0684a0140c8805000c0b001d8080703407042c911000c0c1c2e00b003400c40c2410701c0e0502207010003000c5d003c000d00469160f1001c841d496000c01c183c55043d00001c084aa85422500004105003c04d882140c054020325011981c150700403456148101000700c0caa1416a10380b404001045130032009080c00d104880207445019126030103070070320509560009000034142468400c820180080c180c1e404030510140ca = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 48741011 1106 48739905 48739907
    0x2040810050610020105091e0a02030709021c09080f0304020109030b010305030406031a1f090b040b0408210f13050909060a0e01090b0103140a050610090c050a 70
    0x31031000c401c3c000f0b0680c261a000d989018207900a20f491030400c801b091020b0724180720302000c5481003c016000301e810080190072003040260001016981c0b02c88600510200d0480c90078100031071032242d1030310700c1c090160030262188483c002010a056a1003665240c003d5900b041031401709503034374540a540d03607001d48240070210342081e101224003400c3c5ca51311002040050014041d800380e2541c01d2000384441088001800f408140c00b040c03244804010b03002411105d02e900e6950340c10040110303d040002070310200d590410f200742c403480240b108140c070003510041011580310044640303c5480c01203d074020780d41080c185e00c100443d0b620f00141e0240918076101d0b0800c00b404040d52070500361812504090040700c4010010400244500380c440c10145000c000c4d185416000d42d1407a05243c425a10701c01410002101448425814461407154070800e00f030031450994030843c = true := by decide +kernel

theorem cover : BRFrame.Cov 48561155 48741011 := by
  have h0 := BRFrame.cov_init 48561155
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48561155 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 48561155 ≤ n) (h2 : n < 48741011) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
