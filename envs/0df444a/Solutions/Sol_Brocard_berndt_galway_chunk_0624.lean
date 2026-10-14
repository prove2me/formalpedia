-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0624
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:47:07.929207+00:00
-- url     : https://prove2.me/submissions/039fb443-5243-42a0-bed7-0a5bc1197755

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 112050359 ≤ n < 112230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 112051609 1250 112050359 112050373
    0x10b031204030201020703170d0510060f08040b0c07060f05040b1e13290702030406020708030f040b0a1407030509011e080a050606040306090f02040b010504080601050d02040b12 78
    0x14601403044408034040d100020703203481c0c07640d070000c0d440b40d40b58403016107040180401c2e610f1414656048545241c40070504001e85c1c540810908814040b1340124000145404808401c3ca409a00d5442c0110f810800f291180e50300d015a0f0099070740140400c58201d13443e60480290a4514080e00d8043d500c281c0040501d464090180d4465984104056030852040c80511041c00060001501d10030b4020a00e20012460255081c602900c2112000c10b204895020040119030200c00380c130984500f130f825941000d035101401c1d6038030301485400c415002c6c0c0800080004207090f00003401d08a00382d050080e1804102000c00d0016081140305078003240001641811130b6901222030714545600030310351400d00c125044d00a01001c8020081054a80d0b10f4011a0307050342c500060b0742c001c40e84480309111070000c40c5000c00c24140260005c9018a091000c0090290300480c01c0c0d03001e40e84e40380024603043e0720705000c00403403241e450001c3ea04103aa0341c24100084d11900380c00040710190000900c0c40d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 112052859 1250 112051609 112051631
    0xb0411071704030c050f0f09090a030816050d0e0c06040f051003050103080a0315081608160b0a0302030604021201080102031006020f03070b1b0a0914010f210f0e01 72
    0x750038034a44100308100c1c401c020030320010b08554a000180d500036240d0035614100140819442c80f941c2802c0c50384040314408008080c24009002c5003c42c3c031070744d6000196100c540000c01d000c1011040319010990030311403002001459403000c1d0810704601c04440e9808041c40214010394440e41095403401d04203c0107110b1424294002d80500034a0f02d010031413580365850792180e80c000c090200080517116451140006c1d01ca100440152031745400b92210005035031400e1f1501e1415120b847c480e070055040d100302030020102050105c0726078800032840d00403800b804074020b40c402049194099424000080074081d04991580038100a4000681ea8202003c844030028001e5024001b10361201c0e104140030800030054491a991000c0c00341c020f6111100740c03c10f81d100018650800c41000324403040032035070041d82c070001c40f0040b6104180d2034691a0044415803d807502c06c202080310128101d16503440d03881c42c03c10119425a0016400122003c50030603106460550981d80e9100d40405c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 112054109 1250 112052859 112052873
    0xa030c020406030c0e0a0b010e100c0c03060501060c05070906261c0302040602010f1104210525141e010203090d1506060507020306070806011704060504112e02010b041107 75
    0x8147c10302401c0401c41c1c140c1120005041000405240b0104850742c100c2c501000704001320381001d16401306040c0a13070342c3c40b42c100a1a8003130b00396041d2140c0c45520800100f000851040e141030714803041001c1d4200c0908800313550980784001400d525032143c0e6003500c4102e004030401c1d03059a40c00d50350150b942c52500788001c0c2540c03459009901d64030704c3c16888122003100f1200b1103044aa0820700000c4c3d055900c159541d0000ca0621302038114014281c0900700030030308030710301e50201080b021088240ea440e01c0008620705240700840344c02c50940318440007084072098402c03d070545d0510403640341c2f0f5110008a41203650b1000119901d45805048ea124200c19001d408050407080ca040c508202d0ba940000740d9a08002d8240000e000341c1078042a000e1b441401c002e4110b2208420700159400d1a103060b4005003000c650946014560101c01e44603071404211940720480c0d001012805032000808103a40c0c070048404c20760566680e08544000d9407524003846c0780d0035018101841e184c060b1418945 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 112055359 1250 112054109 112054121
    0x1112010e060f1509060f060702060d0f1805030d021e0a1206060216140301110c0d030506100c02040b1c080405040b0d030210020f07061b0e0103020307020a030c020406030c0e0a 77
    0x4040742003e40f1074030b805480d540c0005501c03e000700c50f103910180006000c1030039440341c00c1000c0c0d041000040c442a04103000d0700304644078521044d0410101400e202294544040007000a05580080040c000700318810340103450300c0131804420b141c645400b088000419801100000d0203d541240d00c09100a414803564000f001c19002610050481d0044514101414091540c0540421840fa58951425400310482c1e94095200d282e8410a04406580d100b44840c15030000900700070002c0d5072030420700500716525240d5242c140c24140c0541c2040f0150a5002ca6030340c0009220354903c542d212104d51404171035015002a55483d8100000d000541d0600b2044138000d080d1085180d000942c00607200b0303600b00320564010380750f810070b2000c00f985201e001c0c00034060f1030600c6502032070709c048580c40b4208042283c41c5d07121901c08000c0150240d01040300c010002d03800044492020900a24250807094402080094001d440707a4540071000300580007800110042010400016240d01c03402c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 112056609 1250 112055359 112055371
    0x203070f06121b0203121b161e0c030209130506150f0303030103020a060f0536150313020612100e09060103081605030706060303052d071112010e060f 66
    0x48002c10200c80c80a0350fa4400c06c840349990044550018241c0c100156140c0c0f00b14010340342c2c0316500e41c1c489000d0b00c084036490314141c1c1d8200e0b2254024070791701700c1c642000b0352882c4c1c00101600681d04d19020040c00301801088001e070402040800e0300003503010300031248106000200d1140c0c01c2c1015081c0040c00c0020346180740268800c100600240c0d0701d4180000481702c5500d440c140c0010415000c83c3c0710b00440381851800c581d03100054880000501c210000c9040111607030703030121410410070070115412400b80c00400c00c00c0010645a040d45044c4000c1c0c5030000d0901480c000c00720340e510500200c103c5440182d100340c1401032044111200105401181803801440994150f85682e003d501c5188107040b030120110003d042007110a10a6500b0b85030821010480c83d6034070700b03010b404c5501111400d008040c030400000c48468600407060343e9916000b40090509059580d44504808c0611210b64007034002070540c844000240078481412000b80302905060400990120003c4070107032003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 112057859 1250 112056609 112056641
    0x605030907140f060912030d0906110a0f0f230c012009040504030e04051503060603071809020a0e01080c0f09061f09080d0c050c0108040515040203070f0612 69
    0x62050741d030710303e45000361070003c5070781e5a07441c11034500048841100d04902d107214040411074080e810b20950010a00c103004240a010743c4441c041e41144a1107501c44280208800c0001441d20071700c20300c2480103001d1941040400c00042028004801c0c551514010050a0000344010440320a004142070890321034002100400a100d480f0414000c504550b4003859440002506052294910b01000c0001038010800d0303081c1103059400300c14617840000e02a11440000c542c0d14100082c41c1ca00700d0b4822445c840d03000441d04603250240c400041d09070b0f80600382e05404101c3c00084280d0340e000b480760800030008103050318144108480507408080c03141c3c0424007006990340381d00f070324070721243c44600a580b000b04044a0a0b5402c2d103050304482c0c0e15101e501c1c4010074260f00300e1658408039000f80d0840c1c0300c04881c0401110071500894005100740c00403407003806606202c0140d60341240c401800d440215881d08481e00050655a00020016021803503c2c018150903200d5124a0091014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 112059109 1250 112057859 112057889
    0x21050706021207140a06020304050616090609140a050616150902060a03090302011b020d1701060e060c070312030c0e0f01020718141302030f01050702070902160c0605030907 76
    0x510b005a07000d0b1100181490141d108583c20b12135007401094880c55000d4402c64070f0b400c05041540d1f50704011145000802c826420b00240304c3d02880c8014100c074000c0d901e82482c24245900086286900100c040d003144842c3c0001c01e003580c800c000b401a0341810441061410010300740140c422184002d86c906043c98002010050307140c400c2200e0100c40a420040344c06903242c6012801003800f030400350707a071076172042d4812049540031882001100041e03035841c001c282d18440a20ba101428880c0d88046220b03034500306401d007003440240041d6074551050307941c1107545ea250040ca15014007000800240d98010100b10741d50484011090304a041d0703900300c0c0545401340080d60740e049500842c0e00151000c2c0525040e040d141e00700c400410b00c0c0c40068004d44c140010300c1550000c2c0c5990480c802d00900c281c81842c403405100b0303248641c619074010031100e8900385c5000020b61050407600d121032038880009021444c0c1c5248040181800da646543c1d03803030300704503540c1444040e402070090100984 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 112060359 1250 112059109 112059133
    0x306010e041e0203070603090813090606030c030506030d030b19080304060f210f0902450408090a150e03010b03010c02030909060f13050405100b090415062105070602 73
    0x1a2504c1580c481e401c00082c00280d82c280043c0342d02400d03840311000c2c8403198010414610982000043750120b48040c48030444059007038041d00c0e000c98034103408d68885e00040c490580310390005001020050030032051403c01d182d00341d0042c0000c0c0c000c81c0c82940001410000a9400410110601c125281031034520920341c0e4a241d50b00740c03045050034060384500c000102420503502080409500a10300c1e80389000145002e89030044521070044045841441030400c0703c4400130b802d0903050480c41803d990380d11640c0d4001d1a0b0400f40c00e80e50010180368001c12040d103040f543d1401100345841d10300c441c000060405095a0010a50601a90411440f11540d9400000340c8502e01801c407a400410350740d90313001c640e04034401442668028490004440c44040e00c1d071000e40078a00980642d03100c144d10001c8030095900340700080b500038040c1c00c0000c0210742d4106803544031848000000c02c03a50355170341c034015030407210700789464a000c807281007007003000000c102e5000200752074000b800f1900000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 112061609 1250 112060359 112060363
    0x60509060319060902070302101103130303020a020307060212040b0901021e0903010f052404060302010e04051e1513060e0c0f090607060b1017070e0f0306010e041e0203 74
    0x9010b049040d00c0d03549100350400499003001016100801045484146a0600a41e81d0704559070181a8500c0c141c07140c60500304400c110391040e8200824078104901680c1c0071002544119410011404117000c400c000039001c0c0018440c00076940ca2201503820b0a0401500b01d01c4003500c1c1d4441684100900c0c4210142454043c51038004417884c20340b01d20050340440d01405241c0380b07004109143c0f034104070b079141110060303405aa81081c44c040d0706130401c40905c4111001c2c0c4c000a40440e000c5c031009129807070a03800044c0d111010203041c064023449041c114031111130584507400031070401d9181d01000e0803c090450030802001d03200344480e038540124001021000340c4268090000050180351131038510341101c01a400c054656aa20400307400c20304020000410315500c10412551070201c0c030351050216500c0c0724022112001d450300c40100a5a4020001459503013042e95540c00302e409580c20b0002a0003440d8400c1e9401c503900d4039103404801c1c01d80b094072840e049071250310003502603140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 112062859 1250 112061609 112061611
    0xf0f0607030e070b030901150609050f0f04020706060e0114010e0a1505070c061e0305060a05040f09050102030a02030702010608070b0301060827010b03010515092719020a0605090603 80
    0x5a007000504801402c1035942085902d03004100c0c4641c3c000f051054290741540701d111031500c19540c00d00d00a03120001100d00003000d2040550107001203101400c680780c5801d105186d544014401032800065030f58407000d8481d2a400010300d84a9240100a08a000684020145000d01e40b03041d42145200002d0000c51386800b6442c945980c810035052600e005008a60b41d083c5c00c9080050340b10343d246402000c4052000300f032005090354104d5100a54001d01a041c0a2240180070285547c14201400001c01050880c9144952200c41004c0850020b00c01903004444016001d03a9a14203100702909485c2c40f41e2011030aa4840b940400c030001520007601d041d00c003246451000c9403109002142c3d203c000c0c8911541d22040e0300c01544800740150700094134403500307900038092a900c85066203441440306030030a030401c240000084480510180e2480580807401f1102e00e24442d051031146814241510060b1240300d8032005029890301c0b415980061640380b80c004e19144c104000700b051400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 112064109 1250 112062859 112062871
    0xd0f02040f02161101050c030c061911030a090305091302040302040b030f03040e04061d0c0315060a03080904090c0e0f06040606050a0503100302060a020d03140702070605131e0302030f0f06 83
    0x5013404100005a03c034204440e5852000320847e500c41c00322244660f102c1c801554800141513020301008802560b80c02039010860b2030392001401d650ba1481c0600c051314824030114100b10040001404a0351030a89148405900c04001a122404d620500003203031a404207091103580480c03404214801d00000b03c5090701c0781c00948040e151280d1800c000507100031305d108003146426202e255040d039400658045000d100724215030408010b009410070300d600c1a10707143c0d0401150581480407510010081120140190000a4131900c42e21480428819078018107062114030041c040c060321110354068100c0c1040368108103203864460041c3c8a841054500300500c00044000380303006041921030310007140c0260207280da401c05000000c2d103995200a202d40440c1c949224203d0f00082102113078410012780d0020640207060800070744064100c1002c0c101031000080d804906409100c60f10614440d090f00300007440c0341144101810042403910f00545c1c1d5100305414840140001200744d0082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 112065359 1250 112064109 112064123
    0x10f030206071707050601090911010c110607030512130309060e0f01080c0d05090105101d27030c0304030c050d020a03060c0e1206010f061407031206050d0f02040f0216 74
    0x8008103c90500038040c6907070180450045d03000004890b8241d800141c5c00910030158134455a0b12940103498141409002811040c4002003240d05414028010070002e4001c0c14118200080b02140c800324007030468140700d40004413090b200400d07400408180242403c0e05024101c0d044950100c3c2481d01840041c50410030600046142402c0920440e00c5c1003448400a00151500070401c901030700040e03944070f070080d41e141000a035149540301366110f8000e000915464030b450340c603c05c1d52040e151450350f0700d480084203420b80d00070008100800c0102c55001c06507454603d142410101000b00750f010700d00600c11030069200590f110420b0000b581d520540000b40500c2442045500b00748064105402028171184d42b841940d0000d5018106d99005030b85d248100d490340000c85030f017804491200d95803c020702c00500002d0060040441403110b1403000200242d40e04000303402695010000d894210703800c02043c0c15828103004042860072644825454403014010006160440350700180c424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 112066609 1250 112065359 112065383
    0x110c010302090a08060405070e090111030a09020301061d0601030510060f12150b0306030d0c030512040201020a020604060c061b1409030309120f01060603090f0b1003140c0108010f03020607 83
    0x80d64601003e58050302100040303074081e1400745480da41d244240d00442c2190301e40140010400341e03050041c1c0c40d00b007440407845800c40d00d8108586014082700c5000301c0c2c0c15500c414010501c3c5070400b00414581c80300035000c1506080c5400098111a00504081d9220864510034400281c100c100500540400d00e005550b620080c048440200b42581c24844004460720000900c0355048000e180686011030585143d400700110544055800c103000601041c1c0602502c0204100c0c1a000e9901c00e00600503034441003d25400540c05910a402c858081031424171420140b2115110392180600404140d07412050604005040589044500c4800c038000190740103c5480a00645030354480240100718000786448446450340004a40d810390380d8a081800150140310307014203440306070440300700000c0801d144c03260610f10100070000a60002c502c036000000410f4003440e580c044021001034034a107000207000421030113069002e01d608500404d0240701680d90503080342c3d03806502c100d00d0700d04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 112067859 1250 112066609 112066627
    0x30f071713080703120606120e030408060f100810050f0916090f02040506070609030215040309030204090201030e0a05030d0b030601080d03020a0c05100b01270e0a0b0619020607110c010302 83
    0x540982003440000301810031900241481c1c00542c44c8801900740d048c02e01118003041a510303601d004074841c174941d541c01003010640010410600503048a040c00071074032400c2e15000014034010321000502e81240d5a681045204035140c6012500700d0380c840050309000c51480d0410740c8468207406441a09036a504408108040c0e50b03045400400018040549035141c3e401e005d00108007a030b4055000d401800485090500d0600d00b562181d0360640301c03301c41e5401e54013848010301c0464001c074103047d0b45036507801c840d480801280f54005c4c80f030001580d0b41c4980c143ca05060f504c01904480c06980300b80c0061002c180e012035100b100c0c403032078074005840d10f00c001e500302c0303803505600d00c0174100707000300600c00d42c4102c0340380c03c2600c803520280c8038003c0005603200d4224030b505101c00406182c03003190701e05001c0f802007000b0307298110f84170082c08a074100c41500084c030380368060b8101c0d085540c0120000840706805101307041d8890418100203141c40a03640709503845e00c90548115042550010309200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 112069109 1250 112067859 112067867
    0xc0306040b030604080a0908070e01030f03111603020a0f0815041109040302030a0906050306060d050702010b040e150106030207030c1e0804152304120609020303030f071713080703 79
    0x14021074010121511414036040402070740e4841046040000c41e90900801c600b400050150121524494a42d50ba80e00c3c40d00c49030941074048404408105000000038110101004000342c0b450740c3c81c210b1035a16107944100a64000180e010801c2e8800080c01000940700c0803520480c50715844000c401180e42d149484024040c20030003040c1d04c000d0910a110038140e0010250400c14110381304c8414a07522550159250f0108690780e40d03004070b0411061f415440c0b40c4d04099080405030001003404440b040020381501e400d0030b038040381b56001c0d40054401ca1804d07000c82d8010304060404614000031703901c0c000c001803201c3d1805007100d041070442d0309601e1a0f4140d43c0c0b0f103640d080300680341c1312911a11400007207400100b0f510300007155948420100362098150010449031a141c00f85407034a00307100d90390300120880c02038030320541d07890148026131002e200a520030700d007500b5001e0161806a0015000442007a42c0c0302c44140c00904000c01d03030300c48070500106140c220282584070611454111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 112070359 1250 112069109 112069121
    0x90203060301020c030703050d050f0f010302060705070906062102030403141602061603020c03070e070e040f06030c0503060f0c031b1902071809051002070510060308090a0801020a080c030604 84
    0x4c1494440016504103050703001018049880003072005004a8468085000300e088065417a511104401e03c010801841c1020003494014480d90603204041d94401800c0211079540d80078001207042800b82d050310309207038400c0c0d50512120400450550400303480041c1401c4081483c19642c13040014001c07900348204e80c03240e802e15401064282d95001e040c1c02c4c1045041507132411130240c410b1840100b2a8500451201d00b40e885c5041010819a110f003001c443e8100c1e00c030362440c2c20075641e5103c61504401c030300a920265008141101c01c01d450802131601e0034600500b42d808075910403081c4400103030044100d0782c0050741403003441400708012040102511800364007010304506400205206500442c45204581d10b5100079061000c0e144103400030746445000090064124842c078460341c40555025100040c0101e082700c0c0c2041448c0b403900e0440e031060300183d030080c00210741d0388810714020070007001034030014000350b08000c1044d0b00030f000c0c01005808413074242c0c2c0100024000c2c1c1c030b850f07100c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 112071609 1250 112070359 112070377
    0x181b0306020d3c0f0e03070f030e060310090c03062c011703030a0e030906030a05060f010e0102100c2307050c010c020d1202010f05090f0c0a0f09020306030102 70
    0x8540d10810b5080c15802449030030140403428101000d41414102922400544460001007040e802d86840304074900402549480310301d90313942c8407a4130f400c2c5c4204002414002d4030810444110391840c1c100641105000754005100f07880410810a0076002e14040001303d4408000c042105004042c040c1e005d0190b540085106c000c3ca040c000280e42034400c0780320741e102c480301c484000036602c0c1c803007407003000c40c18100345580756002f000483d01c4580d00d540440036095a2509036410001e880b00001c01990050721503010b5142c81d401403003410328000c2c101040000d000d080144917948204c0000c0d41361080b0020080c0560344d036040c140c0c00306010790712109800c081510031003140118052201456007100300b040d1007900c2000300e10206940203611540086d0b4000f4141d25101403203a03281c50205101a41c1c00313046540310719444c810341c1e00d80d01803c4d005031800c002803d40d120001c0c4400c3d1030101c3e00541c9600c03c001d17080c01006881800f07a0180196501501c0c0540d50744e0303503180840e019104001d21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 112072859 1250 112071609 112071611
    0x609040c03030309170d021b0303060105120a06090903020a0302070b03191802040c0201150902180904030203090303130303080f0412050903030c06010b0a1805010f2105010b0a12181b0306 82
    0x55000001c400c1d40c01050304440c8d50750382c54a500703120507240c0c0da81e000403242640414002c1052242c8181d0340d402040e4000d0308400003007829925801d19005856100c0b8041303000d0791101e0180d904154050140300c0c003801072405800e00310720b040383c4140c00c221032032410744c0286a5100c240040000f401d0566044154018005204080031044024004d01c2080303e66000005040301c00304510700c40c1e0003200c80520b00c842880e031000ea4040d040108028001e002181540f000b0000c0d80442d4030b0900242c103c0803911050b60018038a9410050030050000700040040b580940401002814002c0c85810800e2036150540c0c0700d06240e030100b0f145110307202820000d80704900001841154500c020880b25401b80d445000d1061440180c1507003400c2402880d000c182e0b03000204200c1e503c10720b0001c2d41000200c1c0015840d42c1c8801030300c1c040311020703040350401180004450740800c0c1c2007044001c034814405010000103d1010035942103030001c04000780180e002c003540b11240c602101524000d1508044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 112074109 1250 112072859 112072867
    0x903071a040204140106090f080703080708031009240504020a0c14190501020406031b0804030302030c040e04030804020405100501021506010309050601080a030f0c110d020604120503030a050609040c0303030917 92
    0x1b038050411074151041800c640003050010800900210f49007048aa1281c68035081030001e50b00d401260304003c064161000d00c00134005032110060146400c01c1d0700c5030115640c683c0d469021b0f00c100d05819049140120f0040018401181d48902800300050704000601c103100801410701c1d080104800130039100114070b0061308248030042d80144100d880e1500e007000650b5032000c2d4011400c4019401002027600d440000d00424000d80045034003241d270303031049890709440350882d400c1f0200684d01034002448043c200411801c152240b0f580001d043c240e014542440c0c500001c2d5900301c4014003800f07906c4480d020480d60b134083c2d00725040b5180d0007801d541166844a11803582d441d03400c0c41c1900054403800403260340324040c00c1980c402d03a401c1506460340501707030028044641c00c9040c0498000b9020072000070a02e54035010030300c5c1c0c00d100314040c55603801d014072410160340000d0030407841401309072300f4400007800c2d0252000c101ca52504010071404950704200001c01042c000c403da1080c4009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 112075359 1250 112074109 112074119
    0x11030106050415080f0d020a03030b0609060d0509210406120b030d0c17030c0301170a02060a0201090209240d03050c190506090d020304050f040b0a09020306090903071a0402041401 79
    0xa0f48074000d40f060b10044844118022003103a545200e0f111003c2c01503082156010086440f0750801d484504018180f0b80c40d0054040104280d9408070f601c0340c040d242d680c020b020080109201022114001c0c0c0c0880c28042014030b0150800e224030f1007503c06114140d5000800200c0b1600552314690300102903940120890f0380250500d58107000407108004002c10b8070b07603404018000c0c0e03801641c40c1000075081d40c1c2800a03006030035503008d01c101001d109040600300147d40303c1c0010b01107402103078008940010907106011000001410030ba002d00f100c21a0340e01c4410702403101c061080c0b011959240c1404007070405458034400c52451071200d00030010329024028140c1c01c50b11840b03100e101142d003245c0d19000403580303403544800c00c4c0005810810080240f0303e00050504c00d045402440054194490b07800038039003034999400201d40782c3d001300c10000715103004840c980e481a0383e10051840e00a55545120107040c50158515031040c1020124065440f982d201258980b681010300495503107803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 112076609 1250 112075359 112075391
    0x203040609021f050301050f030a050a0c0906080304030f0803100806150f0306040506010b1b010509010b010306050d03050a0c150905060411040606020606090a20130906030f110301060504 82
    0x81e500682c0148800c00c00031a8804550b224206154801d03603500303007540d003484108002140c205001580c94820f8030400c0002c60700c18040784500030f1040c05104440c5d4030305000c0f10241c034500c0e4400c0e101e80e0800e10041011603d81002c040c3d4042d8070010140d03981d503c000801d101003825801c003c1c1d02c0d21444040100743d0010000340751032000102d40c40608a076003a400c02d03907500401c07503009105404c01e000410405402c072000d014800c402951044403412040345c15400c4800c1120030305400e1307440313800c81420365030184207039006000c0941c0c144d288061240c801401600c104400c0b2402c2019286001080c0010416003c0d02100c00000038000403005051a650300c1500f5103042e03511400382074a03112680b13418418074007104c03030f00c0d00600304503580c81040140400c1c00604000900f40c41c2c240c174004080d110103031144001040341610703481d1404940042d07500b003900d400c60222145426000d2011605c158403040e0459800010b00d2038410907070000c0390161203181d102c103800604042c1122051a19 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 112077859 1250 112076609 112076621
    0x30c1006050901050f0d02040f02070f0212060708150f060d050f240607020a050306010e04030f0e060f0702030705040507030902030f0706080f0a060b07140c0108241302030406 77
    0x10410144042500e070410021540400e104195110000007640c150700d0a0078909501d889000501c006049210100583d081c0e81c0000e6084546490310400681140343c4140c46654210440006001d00d1078234402c090300c20720303010744125a8041099520f04165440051245800402400756515400d07014a000050501a16124507041000780061680c80c038503000484220610484100c2c18140f1409100c6160300581d81070b40c1201c0805008200e07900d0030001ca074020918034200b1010f0349480d0400900340383d110b01041c0d040100c007841c40b00056a554040d120f0020410120b07990703071100380c80083c0c502155070340500d800601704401c1014441d0158440c400443c021380640714040e4004610b280c88482e54004c40e4042219100822306030301040381e00c4e941c808c00c52500010706945810301e1501903040303c4000c41d1070420503080306000c82000c4c030001c58090130070b0074040c6050410800d03000c20700d60359000181c07010140400f0726950365114002880b24034280001113549007000e08182010b846 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 112079109 1250 112077859 112077883
    0x903041a040905070e0307051512010b0705150708160c06110405010e1203030403030e030f03010b07060f05070c12021617010b1e040504020402040801020a0c0c060c021809030c030c 79
    0x103d000c0020748a40c2c00384c0303816403c40c2d5008015000180c01c140c00c12900c401000c0d14004204000c0c400084d02100040b80c1d18041c224043c0e0154585d1010316085107072001c0134114401c2809038a003440070a64024202c84e03000341080c080000800c1c0502011500c2c0e510100b405440d95081020012000c1c252070000e0050b038400307036500040c00b041d00c000e02005080061a441440c0d00c1000060301082c443d034807400c8902407180550303140c4529809103400c0d44c0c000781c01c8580d1030040010080c003001514441c40d003401c3c098100900440c603004101801c035070300626018010130b2810650a0302e40c2c1c424030100740d0241f40000e841c00b03440c0e1a21300c011003400c1c0810180354150300c0e04140300b000303141c41402d00d042920750165401c54070309418107000c09401c02420403070b0859000d01c00440c9415081c0080c100030f40c040e50b00c3c8440329089041c11640c0074826409a410b001c2e0003454140540c0f6541c138034006150b03140d28941d80686460408928510801c0c8003401c3d90301001c07074640c51451001c5600700c3c106e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 112080359 1250 112079109 112079111
    0x20d0b090105180c03040602040302060a0302030a0605041413050709110d0c1b080705011407080a062907170304081c150501080714040f170a0203030703080903041a0409 74
    0x30380c032242403050039280303140c0c40e01d4011000c000080a5104c001c3c0110382c442e1040034054141903803070b404201143c2000039030704003003030b0084100815000340348240c0b002050215000e02c0207402080b0319082108020300105003a000c180020f0040c42010441c000041050715820824250071045d40559500900c81151010341000803141000d4490800d00d100c8403a548a08512030205035501192503105840c215025500c50940c14070b9400074066151041105444d010329618060189504685103600940c402c0c0120190040d14818120910a80e80540145003541e418681c244500c4101c1500203102101100004000030003807220302a20066401604031602074031240c00d0070041d40e100000c0c461222961950801c10b07503110b800e0041d00940c00d070803c034600c081881c2c84401541c2c400d03041502070782048032080100c007089014100651640c0300c003810401c5101d0f400a520792203a0b10000d010450308402203840924184211801480010101641140b400c0c3c182444ca0b0480d00c01c0320109 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 112081609 1250 112080359 112080361
    0x309020f030c1f111006060f0f080c09030c060708090a090b091b090a14010f05030408033402010b0907021603060e0c040608011a011103040522020d0b09 67
    0x5414000b40008030208000e06140c601c1245400e02d824002e0500c04000800c001c2030400c801e6404144298444c0309080c080101e0018100701d00030f403528207030040b03241c204141c8002e042c441d06d40c445003154004160702100e80c1d940c02d0f5200000c2c50081d480807840c0c2d21140c0025407004110303180b07000b80311043c026604a4166aa0b440c480340c200c0c2c51100e4031a41100d0303000c0008440315210035032070000043e4004a14207101c0342002140d2100d150350801c00801000c10b05400c0c0968200c0c0c0090189241d910707101c1d04d1860241d40c3c40445d40400781c50541c0340d2049041202c420041001e0100c089002e1502c2d801c1001b5500c10700074080d20000400d40d0017004010046440c1c40d1012511a118002d9048045501441d664410000340036041020266015401c14503c80c1d5032940540d0340204450800801d8034482c007617a2003142c04400c03513400e0600c2a600d040e2041c506021050314221001111070041415054400d41402019600340004003840010040c030711016a038000141d400e01541e1101603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 112082859 1250 112081609 112081639
    0xc03030604110a02120304141b0108011703040504020702060705030a09090609050411090907180f06060801080a060b1519090603020306031e07080601060801060305090d05070807031707030902 84
    0x724824030050f200160007159448002d40e20900056812500c6203901804200002d40d1030782c208071440c0495245030b803000040440c20f691041d055805040c2030401c032200b05043c2d0791419500c2c030035442400c2c01950081114402d40d41e4060941e40041c6c0c02070203480d0303100c0812000605885c11805641c0c5294604040891040075510503144113643c4185443c03200840c107001c00000c1c18000346840105c0c8680d00000c10249132440c61540310b10410600401c0301c004514a1009590041c2c0100003001032070070040080440001c2c0d212030090b003041000541841c0343d004183d814070400c070861010180003c0c3d600b8038070099030040d444410665a4803918035200c501c01c8090344000d884942d40340d0b0000440c85e4482d220f043c0840c0d11407001404031654113030b0300e0324a103050100c01d9000c080401d400600401c500d9405000d0741f90b01c040204047c00c21062080d0010384a07024622000d0700720b0201180e11010180602c0302c0d0307603030b402c610700b400d017145e152445c4020050550800300301d004102d0560f81d005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 112084109 1250 112082859 112082891
    0x80f070902040b030403030513060e03070203060603120702060c07120f02090a110910020a021e150301031709011101060e060103110304080403061112070206010609050108090706080a09080c03030604 87
    0x200743d5642c461580e18540b91900d040300a040c02500040f1140c081e0070424000422500c55150362103a0340000e10344034283e900406003043d40050040f0300940109502d0303110759806500301c8007c2a070490f1503d458556256000d8542041038010708281851a10414148800d00750324030303401c82c8201d42c2c641c000d40c1c0d1885094262640c0305100100d900f0244000e120341d140c000c4440383c1109180c8101d400c100015000603c0c40c0c0380103080e90b068800b00c0007c2400c42d00f00f2140030707150514200c06032455940746a4070008c2c455040b1f0a051280f48010907980c1007a0f1040a001c0f900180c01d00c0240001a00c2e505c480c0307405082500c00c640480d140400c2d115112188030b069074416a0044801c0e82003614507214000079010301542c140100c801040f1001c000d070429080700340078600030b5009003400d40c100341c4043d2000040760401c605008402040004040300080c00340300307480e03140c5442562520791260800180608810042c20a407001c2030492040348000060362148030226000d00c096014510a20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 112085359 1250 112084109 112084117
    0x30c0209070e091501050906030a02030402040b0a060f0302070c051206070305100609090506030313030602040821090409080d1a03012703030519050405060f0708060102150916080f070902 82
    0x6401c14098800104802c0320364130040c5810906040c05441c2c015030a0008556034802c0b500d101000b5408070512056007003510a0002825017a5482101c560800300e014101200006000c020540c000808404000c0740c0c0810b94005c000103058154000701e45800952940c3d4110f07055000207140030700058203184207282c41c40846d100b648aa400d018201003008005e044010080e0360075210400c2201c142c800f9491020004600800d00140c855081c001c1d054142a484d1110304a000720202c0c014415401980440313000c110700700d80000300f0607100d05d0089890f000c0c0c02000c1407010300d030070302002d150212150a100d100300118020401508011444500e11004030307421401c130366007114400002400382d0300c01900006030b10200706003c2007101e91003051701c004903411201d0b03030420780901010b0209000c161350010303142d0510520a02d400340000395504014083c2d0201c06000c071000c6440c0000c244500000c801c01000743c03805440d110241e4503a00d80c88003840c40e5084c1709503900003480c2c9413203200307036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 112086609 1250 112085359 112085387
    0x60b010306061b1e20030309010503060f030a080f0a0e030a030207171c0c030e040e100903050c060f01080f03040b0306010c0515010933260604030c020907 68
    0x9a04050189110348100349042000300c4a86010b41a5910a04209204c0c3ca0207140f107031245c070940c007200d815515030082071241c0b018000d62043c0010102c0703a8229090b2036208030181c0300d1000100306000081e2400ca084e08018141d89000641d80325044900c40080884030402d450703100841402c2402e141d42c880030404040c006800c85e010603c40000020712030400040003404407440307051507894951560811002e19408141400100070425030400a91001e66208071010000c3c4902000d5903925003442d0b03111204071543d42c03440c440416000c2c1042e24048170104d4120340042ca40f00c0c0114451410070b004044480c03103150700d1000200400403c443c140d4082c0c105550864442c40010344c2c660040c0c42c2c00b2100c038000c400b507202005104a0800780203001510002c603140c5801c0301c0030203000100c3d99104c00b1002d5400582e02403903210541f20800c40f01401000c4843c3e801400951601c541402450078550103a00c050105042d40551000b00083c02283e00300101c0e16171143c20303100a0307084000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 112087859 1250 112086609 112086617
    0x609061509080a060b190e0a0509030a0f0e060d02040806090c0904030e011407050a031e03090203070e100308030106020f15010302011b032f100e030403060f060e0c0304060b01030606 80
    0x2000c0002d00160002155400d01509009211594031401210140d8030342115011032510800c0007034401d400d00585810500c048050740c33501c030300701600a00a40001808000f44001c50800c0082d41c1c0324102240c01068100000315281d0351600303034898071150309031400d881602c501d482241c007a103484001c4034080c2d641503c810054070b101c5c800669240102070343c1650440310501c00035021032002d20003400f000c0c1c401d5071160806041d030030003080712a050400c2101014a401202801624002420801c0d941482040e2143d940c4a560081085407240c00043c15500c0101c0001122900083d581c2400e040300c606840c2c91910242c03030504000340c00d2001900243c500c80740011001c500c444d19030b481e02c6c002c1c6402031004280e0106401d0951185110780c00720041612300345190201407040c40e44003230684d202480b9041e2000820ba58034091404043d081035074074200c8150403100d651003d0014059407004c0d00692500b4007050207243c1044400780c500c0781c104035003a0182c1d84288a09401d980064079 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 112089109 1250 112087859 112087873
    0x3140417120f040911071e0201110c1e04110a080457080705090903070b06130213090609050603010630140a15050c0724060906150908 59
    0x30b03440000e4034150201c85c0004408101c0ca0b00401da0001c0c103003558204503103175a407800d0454400180041003241403082e60b500142c1a000d403950320018242d4800302104640f501b00004400094003c0001c035024011880c0c0008001c50540d410541040c07240703000b010b9081c101040c2d010100365524a6a0a40100c0c05000c007202640102d00403284001e0a11030714101c1d40d031050001a20a011a65041020554445d003c100a24580406401d51103030a0030061810541c00d41d45220150f43d0141c60907101d2201241c3c488404000ca5041d00c3c0c5244000d00d007807203016030315800c0c44000c0445003d4a40120704040018465080c14050603048a20300c01c103c10075100995980d0204000d10b0100131141498100488081a41124030244074860300c000340c1600b820390301d040e0001c0d58030200344807034040c03c050810800000c8207041c3c1c1c0701031b904144026903200340c1c07a50012250800381300d4005100d183c03101c08640408241e207c1c100750b96042110014003010050b0940d0801080d124504056000e60 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 112090359 1250 112089109 112089119
    0xc02011e022a2b1403031005010e030d0f050d0203070f03050903160818040f02030105011e020a030c02060f03091f0207081e040b0318010f180b0403140417120f04 71
    0x400404115520f500d9401c14440b003d646076080362010442e0240241e2001c81802440b0441c80300070801090242000390038401224042a140c411803610141408007001c0a0174207035000b0002c4444c018a20b0318115683d01d0a1100942840e80901d80540083c0c6030a00140d401000081100c0d0062003072951910703000704981d21240039a11040d4001c0003002c6110b694145504c5a000703010407101062070150b1250305142c00104207048030104442034003080c0300391030070b43d42c0c002c105c005c5030903010300d4085c0c0300e20000d002081c2c1920401c0c0d01200041400402c100c80c150300400d10780c107544038013480300c00b0440110701c80301c0c140d01a1490182c9081801c01c09055800b0001207501600d0444a00ca03605050f60303105600c030150421251415055171503a403280010b5000c2c4541040b01d04400c4080051106080714502e03080400d80000b010100c0c0140403e003454094a01d08122140f0264450381c0c694072a42074282101c98851011a20301c0303030340e40110402622400b40c0750440c0711100002d050600e42 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 112091609 1250 112090359 112090399
    0x6050711250906030602030103020f01090b070b130804030b180f070608100b0703050307090f0303050a03020c0a0209090304050310051302060a030b0402030c25020906010c02011e022a 80
    0x102040060881ca44600107858000d6000d400019030290400580300d40c0365006202d11040302d8000b46040040c00e01060026800d034070144c510982e04680b01038400e5980031a500440c014000020b002518085000800c1000e030f008518032440401d440540c5042c0150b00f62a620440c080d44072015070131002d03080c81018410346503547c1c0100310b41e400098840c3e61360801d1020b0380c4034510503800180c000040003030140d0001d5001c00200f0304164011440342c6151070080180c054001c3d81803c02d5000650401c1e40780c2c0401400c0303a401d40081800109052014555607641e125118090083c000e0b0380c07000b2581440c130b2060500c1800141c0024844201560801601342c2c801c003410010b01d03a540c81c8000702c80d200c510140d03104106426019640c4c0f900b903118075048402c0c4c8810429183d40708002c01e00183c030b030b120142e0380155007820074402c443d00e90b100580e014651051010481103110740c03c20713800f17a400900300034031480100008440c10003a00402031a0074007201019003003c50031240d03500c06000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 112092859 1250 112091609 112091653
    0x180804051005070204020c070509010b04050901060e0d152c0c01140f030a020703030e06060a06030e030903060a090b060108040f080a11031b0c0f0d02090403020102040302190306050711 81
    0xc0d510b030031450300c911940054200e811400e00309059a11000741440b1318109809210301400e1121045410300307244c50000b41404105008542c1001103580d012403183e00e074640b012900303982c0286140c844002c12030140b40284460503401e500e40c418000b070316040c20070181d5082d900760144000387c4010640800155004010450000c2050b002001080e054030042d1010354040c5408080c050303900c1807281001020303680c1038406520381d60404400e021070b80c3d41e424a50800c0345c0041c140401c00303000c3c142d283c40c1140191040b080d058000c0360701704034007415603034403540030315200f606050040c0e1507001c011039907103d0859000f072001c41d03280c50340c0f404292040040d01d14010580380c02140203101c00d41046c01c540226a880d40300000e106a0710f440003509006a900c000429180b040031800d6140018200703402d003540c064040c881d480042000d0502c01c2d0122005143c019102c040103035038220280b032421300103100c10388200303183c440460000b51007034200b182407134108002807030002d1005c0500d07446502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 112094109 1250 112092859 112092889
    0x2a0b06010e0904030309020306070f02030d05041b090207170415050d0b0a03150f0216020114040e040b0a0c020105010302130b03070519030507080c01021507020109170307020118080405 81
    0x45140701d0212a0b41c80c0e9405500c0b851290b03a002c0340d100c1c62441458504030020b0a40000d10082440121603640e000040e501c1207488404046915101d030f0404080050000841c04c41c041c5442d00c000c1401c20264000f4000c0d0751090b03841d030280c0c9103840f40300c05a5010b6030040f0445131041085c0441c0503849a0041d0692200440c0c0c00601115041c00080d0710804507407040381d214000c00000c88940303850344039907480e0040d0b45000390310341904290200750b00300c03e8602c000d0502c84403002c198119010f000036500a4501200d9580c42800d0609198a18160032102012841d0503e0800d01d283d40c8103000325812207502030440704441d00b00030300302c0000d030006400c1c043d094401e84c4000a00c6945580524940c1580c0940101d9018190f080403800c0c5049508401c4540d0b00180792040d559030300090015100302501c00b035070a140c40342e8a08a0252a02500c064503811038012540945400d140040d80070340d489030002c102140000c0125696880141405414208240020021804e080c2d00703540d0066 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 112095359 1250 112094109 112094117
    0x30e1e0306010f060c1b0801020703080414010614010c0f05071712040b070303050402130c030209030c1c030503071b05031207030c12020a050c01110403020405010b040e0a0b060903010f0c2a0b0601 86
    0x152070f47c9405003242c00105058001880301c10920003400f2000c0c0060b6800c54203d8000d1201d00c2c00c200209180c0d03c0f030391300c0710360401c0300706191a020703ca034940020001c1c03603111050381c0031607030f98143c420075642c440180320403240516295503986d080001e088404440708182240c0c18082c1035103080e0000c2c0720081c030a98020383c0b80041d200e40c00c4010300ca1958440c0300c40c1c800507207850054050520308140d80480c0740c0503191410100095040303102c46603045591514140b5600c0d940d01c0011648540f00c880c940c4070080b599100c072401c110010000d055502000c100041d410303950507104900380c0c5d580680070030101d881000b1400680060750010904d00d007050400c9072529115094040c2181c440780c01d5000f51071400b14082c809c501c0d00f401110300405409404900345800c2c00040003521402500c0c500e141c0380e42e60380400039a10f520060f18888103004008211a02c0b0380001c90b000f9008d107a20703981c0092038203110103605041203260b04400108428001800a025680e000e44040d80070746258144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 112096609 1250 112095359 112095413
    0x1206030204020307020a060510050901030b0c130303121512031d03030d060e010b09030d05030a0917030403020c09130615050406030c030b06031506010c030e1e0306010f060c 76
    0x580c03600c0c001140283c105900501020700242401002c4500c003070014130409d00c0b100f00800c540c3c2c3c0d801d41071506481d049001803640391510010000d00d0f01c01c00340c0021a80302102000414160800f1203032403010400201841128205c09080d03100c2826402490000700e560822480404e2017084205680410010b501d10888800c01c0001e1641d001031040d5549a1b450b035005000707145c031401a040c0104002007000f414811701c1c0300042d84910b043c00c5100208680440051160001d0340c02284015412200151100c1c0c000c0d1420141a07004480c1900544a400c00c015040e003003481d102c61141d1556015805c044400350756403000b50130600402036086011000c041069aa248101c8000f0b511814070b03803503981c1c170718500380d80074200050070188a40c000c21842806952000340c440d51000303003460720500141d80c034601a140800c0306258a500a410141c129a015548115a8801c118103d0407281a60f90340d44030440c0d1042903000d584002020b400b8002c0008008407050600ba04d80d003241c6c0d00c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 112097859 1250 112096609 112096613
    0x3050307020a0c090606120c0207031407090507110114040b060409030e1905010f05040509060409232d101104030f0b040c06081005061c0e060702060709030308010501120603 76
    0xc3c218140c0120784d40903541c1e041004442c1c0c0106c1507000c826440c05d42880780050f0304001946030002444064011002103c15600e1440c0c02d01051002c2c042542c002c004a04107a480200700d071300c2424a83c80190703e4500144c0c1880c0416904620855020414a000b681c908003400040c0090080c11828820300b0760615103190f444481600b0706010349840302c0050307890b00000402c0003800e18555424083c0810060049443d05270f12954890029103001c587d000141c80c182c4150280e150101600012800032500f04082c0465a41c00307d07583c0d0300348111010b0049040b1001d519414110004951011803008603400058000406c41c40d0520a201d0031b140e0b0704c0d250004006034140c81202c904a00e04204000c211110100001500300d520740304040e0f00d80382c0b00100303402c034280c01141c1c802c01002c0f0360340c0201c0012940044241c0c0c00a8801d0256016103a4182c0c1d4030202581d400d80540100b0000032407041c401c603400400c907509035442d102c2c03691900c8015a4411945140407640f5501c5150101c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 112099109 1250 112097859 112097873
    0x120a021501030f03020114660f03040b09071206021c0b1c02042025020d0b090a0c0b03150301061811041505040306050f0601090303050307020a 63
    0x1c0214010501d8103203061031803a00a003180c0000102c406010390990a100f20360a00b2203000c0d02075080000409125080041441c643e00d0312011100c00620b28181c2c4841d419200a0308185c0e2204540902c44034094a40c0400304070307001e100d10340840c4141c01d00c00a008614a0030b2640e802030080000c0e01c3d61503445120b0911b11840c0b4100c06c0c0e42d0982c001903001c400c801c0780d00c41d0020840310010b0400146010034009655001122504400900180400001d5548650045030302074000300088030031000204c60300845030003440c0040382c0d050241f69101c44070700348210040c4071036500610300b81a40929030b8070081046000381c000d460603c124501c500004a4213081800500329020300c040c2c4a00c1c1c004480b1000c850072281d014040d0341081020480f200700c14540f88a42c420548010803d0401c0c48406111030003903a000303501c0c4441c0e030705000307203c0358200c402001560300500051140740d91b018802103900d030080d5001740c001041c8400800100f4445c00c0515000075107881070350f80c080f02c2611022 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 112100359 1250 112099109 112099111
    0x20a0f170a051b070b070609030306150210060b070f150b060d0209040b0307050603070302160f0605010e0a18020111030702030109062c0d0509010207080106080109061805120a0215 79
    0x402049001410840c1c2d00d40c146083c0904604503c028800a4104080f0700410300400c2d000510711a00c501d42d0104150007a08014090b20360070040c1040c03004442c50096455915401614541c0d00d0700d079020440342340c200100e440030790708484803400e860440e5441c4d09440441e0380d01800c1e03181e075a89100c00300381c0d2410014014503c20401c05a1540c01113800c0008480034000b4061207075001c1407081101d0744500c030a482d400300e140d0030700580703943c005000c07a001210813100080c182e0740340c1211076040044543c0402e041e1005048062101da0f0b134841200b080700c98402c868408501c42c0c4040000540c440c48015013040c404509890070711020380c2c080303420340700551811210261600c8a407070340081010014183c220001000c244602085000706845400b1544050100040011001c207240d000b0006140144107a81c0204089562034a8190003020b601e2002c440640c20005c408001403813400012a1150704540a005a070002c03a072560600c0d8845410340c3d0950107407205442d80c10745032704565 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 112101609 1250 112100359 112100377
    0x111815040b0d0501090e0c090a0e030d020c0115030309050f130207060506120a020a0e06120d08060307060e01050306090403030e01060f0e071b080306040207060e011a0102010c020a0f17 81
    0x150b1521102c0c5030000c1903c2d0160410504580b4103041e400c2018030000349101d0300001070720280e000341c03140450300c8040d2202402c208542c0c8800103000f40150390700e900518a646100008000003110300303001d1040660a84009000500300120511042c0707800240721040900041815155011500c0803c05980180701e05840c0199504204191390134010310f88203040ea50130000d0140164160b00007072280d08180074414000f0200b00010f040e50700d80c2080890050450b80c00c41e0104c4200c107074000e0041500f1114030b4060b0080384400243c103401041e2003114150140c49007401c640d11082400a2150018070540416445002030315070a6820300c16803015001001c08500322074100644c0c1180c801d0060264420040354860790101051003055111500d42e000d5400b0f81c0e29100e810000d0084d000c2d60340003403da0307071510503c807200340030540c010300b44841030500da2003020802000680c202c48200111001580011801d24001080c0c0040c1e506424801c1440c81500c9410300d000314401d82100300f130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 112102859 1250 112101609 112101629
    0x80d0605040e1b06030712020306040905010e03071b060f1b060e0304030302060c0c06010b0a1116060f0c11040b040f020a09030209100b250b0708060a0911181504 71
    0x1900800d58490100e803c0b852100b43c07481442c60800c1079004007501c034091001070040d03134040301054603951940c11002ea4241c01000a00054034003415054407980424030849012014040e81c5055041d0a01860304031070541e00c03080044420071a090311718090b82040c0104501c1e04800110014443e1300c42c091540310030600944d1581d08520b03000c0c0c81e1207000780604000c40001c0c003103942d5950300011541e0540d84a0005551101500103090f00c04044d032000c1c0c680076004100341c2c0c40a030080390851307000b240c000b03550740c11600030010000e60311a410048050041034010128026a08003500030201550010704005a841800f401c0c42c0b0890700040038100006507801e03010410752500346046c0e604020341c0c100c0b070704030740e03240040b8400305104110360049103501803c070703401c14490800256001c0d1030b0424101c14403842c10400c001c11501003222503a1103074402c041c000c01c02c10701c80d20031000071260f40981c10b0b150800c8100002e4040b2641050658040c00c5a0707542c18401e103080002d4401400300b025 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 112104109 1250 112102859 112102873
    0x60c0c15010f140a0510030c120f0903031d0d08061302030a02040503010b031501030b0403030b090405010615050405010c140a080c0f0c040504020105090409080c010908070606050306060607080d0605040e 89
    0x911a500c20503103da034580301d800100c600340950350718084111090285030070005411100c4c3c0006440d09005c02110020359454801d42c86200092a0890100c071803081d0b030104408150000e45000d01c85070050000700c0c691051840c0c0c0111400b03919a0360300001d0041810944408624503201681e101301e444056060f0040303010441c070300b000d0040fa081100102d000c1c00b0181c28048441c41034860511018050392500f6011900385070007503200141d01803000d80014403900c0c142c00d00c54080c00843c440d07818a2010140c4840440b03120741c0555041c1c03130050b0355896049103661640c0c042d00c3c0710340400480600034081d01c50001050440201201e040b0711019021085944003620305100301c08810a00a0341032004200060380e02208840721040200c40016441c410340c1484500d9006600c465a81980703001c55130024020004c001e003186070710400003405003030703207a01c145622400281c41e0325402c9542404030400140c4bc00c0c0c0a05405c101c0e074a00059950b541d9070000e419600c00b01c02884503900300b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 112105359 1250 112104109 112104119
    0x50c01090614070e0d081815091009050f060c013e040b0f07060603020301020a030212010f03020a0b0d0b1507020301140c030105100c02040203070503011d09060c0c15010f 75
    0x1c100b1650102c1142049040000e541020440105000c1e600078119840003a0108003003041c0449500d82c3d89024002d011b050390070041d903021540c0080c5865105040b0124105101d920034003031700e0242c5402902821800f6000b9041c80403d13002006da996143d521421085407a120b04095051800404c41011101013005009110f81d40072586081c24154030800060000400450840341011050800207949000605003c001031440341c10082d4554000504c51920a501d90041c140c6221030400e1900e4690340c0d901340c08103d03261844020741200a40c00b08001e00e0041d04050b12507016450004262802c404000841c5031592020b0f03000129000702e88501541400d00c108001241d00e1010a10181010200d004040c081446042d10078254081013008062150000d0110243d0181042d52282045034000e0b0403900240038110024200c00d444e003c0071540114614007802403d00a8039a50315015002801036000c0c81149880d44510342d0314007008040303045154000c103600c462088286e8200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 112106609 1250 112105359 112105391
    0x614090d0c060609020f0901170412080c1308160b0702031203130f03080106030b04090f021309080f03180304030312020702120d03050a051308040504150b0307180504020f090f01050c010906 83
    0x343c0100041c010102741004001281c1002c18030803103c0909048041e81d40b503501c1c06141e8460602c1981a0501031800003030300c3c0c403000444814400130b00f1a1f0404568540c040401140a001d5000e5407650190042d03818000d0108015034114464105502c503540d80d07500c03013207020300d4102c1045001421010041245680c1032040107025203003201d0510503c0b10a0301c600c420180740f1540688900d070319440103000c01c8196403240300c00a9225026070380310101c1456170045a0001c0311070042810180968450250010044809032a450b031664517851082c0e1425200a411040080ba004041e0120b00d226107141000000d049a2541e42c010510b480e25800103c107580000d04000306d045014410070300007030780c1c04e410789040e16000d030303000511081c04c0c981c0030101411960068190304000400d0110843c1d200e0040c1d65002c1c06411000c2c402d0380c0d2502880200c0c480c058120403032980911040e40d8030320303218040007002c10301403400e02e00b8003501e0b02001c0c0c211340042200302e920642c0e40702ea115188032a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 112107859 1250 112106609 112106627
    0x3040803030430030507050904150f060f050a0e2b06060b040506041e0512071502070e070c050705040213090605090609070f1103070605040614090d0c060609020f0901 73
    0xa1061400c00401c90390411030b180d2003e503810b40c00c1c0758848000808807482141914403041c00108180301ca8105084640c030300000d54081c168911807051008034200340a000d540c8904c110710790301c852410b0fa403180c084904184c8a07002950280801746113400d0300001c1c0712030783c2c0150f100c3c85a070340015000d443c01a084500701d80c804201e1000500041001d569603e0981d42100c0c0c54950701c2c09000c010181c0b011408010341c11542d4098503a42c2954203001d1300243c81426500314078120360301000340302c100b681d0b600641c0c4600030b840100c0500040001c2c0c42128840100e0b07100340c040300d035450303150b20004003030360002c108549100100d9082041b45c0704403409941c000b4141555180801d0074201c0c0415a82c1c01d00800500074801049502c4905c28854614042c901c0301080980303445001d10310b0320340c002d00800d40c0c055aa072410900f44585048442007041d0080400c4002050702102500c02a107034000181ca00342d580d5a5607500000d11000c0d240000d02141c041d08050710b0759203403224009441d80d08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 112109109 1250 112107859 112107893
    0x60e010e0a0c020705011803050a03080412020610050f03100c020c030c15090609060c060106051c0e330406021207020a030813080702030313050a05180f09070503030408030304 77
    0x2082c944103007112034000c10700c0c1055a0080c6015080080405070542400000e0342c80185188034141d0b41c6024117600170092405140300b0019081094599201281c1d2401c0550705070544100c803a000700210314103aa030805004c60b01130250352080e10300408460071516400076045c0560050890344a091806014036a80340c030080b100c01100c101190724451050060010807070041d03030001484171042d5121001d5400300314003141251140d40c1c6509004083c0e410070030060f2a060303603450300d03541c0c40c0d079550096151121070400104010702080c110348800000c204400584080c9400660031110074401002d44240c2c0120005603403841d00010070500c644008117012700b19040682000700195000c0011070f00700c1c001e10007030860f650f902d0910310041d01c2900300c0207506200c00104401e011542c508943c0413038a0480344102c4c8291758409100000103e619144c0d864a803000010341c4001e041404140c215040008a52009480d240464035662054000180580c80482080208804d010f0038001d091 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 112110359 1250 112109109 112109111
    0x70c0209010503010c0e0603070207030c03060c0306090c0f0807031b0806030d05030610110c0901120b06030d05340c03060608030703090308090f270a02070804060819060e010e0a 78
    0xb0400c03c004100f44070245c406c40c0305440000c04583c4032442003203c403000d150050200f4800b60740ea0b1a0180003004903615050109080200000380c60740c0a2040e0b5010190548a803020710020400480e01404000c01e031505050756016003c91180480200e050303491140d859000550401d4000c151034030421921400420104000304801510ba4040d0090082c10604082c3c4082420004160500c200884450742001e0501e000217100f0a229240041c0f032806003600c403169450720418140c441030000001804214104040c3c0c50b005040c0d46d2130b80800d85881030520100300ca14420f4a00300074002d4081d00c0c0880324210900c1400703014401c6200400d981d800443c500f920301c1e540907040904610018155890214035441992903080c858003454200400c2911420044501c0321182c14001000149145120000502e806418030842d1450358100d42c403c0d040c103242000c201e84103000281039180c2070140107050b2221546030f0043c1c80c081c00e880c42c1c4d016159810455124142c10300280100340341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 112111609 1250 112110359 112110371
    0x711030a03020c120a06050f04060c230d020f19080901090c03030f020309040c0207140a030c0509040203101b032406030203060d2102070f1a090d0b070c020901050301 73
    0x350000b0705035030201c0099411106034001d5031103075410701c2c107603c1e0f006d40120b09200400042401d85200d080c8504e10035401040180b0100d2021503c2c1006018020408160301542045064505029102102e00201c0140c50910040b00445068220300301c01c01c40700c2c940c1c0034018501ba4111401c658000000b000800c04c103801c41c0c40d41401840c482c8400b4043c0000c080c04c07160401d10034004c8580884018000b403284002e2600020b644035118416605440e006d1303040c501d010310700304c43d250040703a810141001d03c25007403404110a0010242040340d041c031818030203850500e001d0159400a10403041e00040c2d15483c2540a01581c0b0b051304410f24942c0c80341c0442a40c4d500300301c201020303140036240040e1a80d0303450700440d640d030a500c80060003013030042d01007000c03001c040341d00c001802666a0a03038440e90f0346d07003080724040140303801040c0e98000d00d215460010350400020307104070030300142040000070b41515400e004d02c0040d44d100c8002042d8240311001c0d410306e000500e004000a42c020010b0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 112112859 1250 112111609 112111613
    0x1503030f09060f091801030c08010605010903021201020c070f18090f030f02010b0a0b031005010c050d03020a18030614011e0303211103160e06090409030c15020711030a 74
    0x20350320801c2916440341e0b0010411248540c1e03075005440c010700f00900406030052000d5007032072191000b44001c0b80c1130340744994003203111401030050f541242c0042c1c6410500ca070035542040706104040103c4500e41d942408405000c980411502006146031508100414207105103482d041480b04d41c070003042c80c189555074001401c9207440e0801d094240ca021462a40d044408a003d4004107400790351012050001040b5a0321480055014014040d45404d22907070754401969000901d00e00601140c004d081d000c00b006000382c00a205040301450802e4807400e00303151048000500307800130f40e059659200074268895401c1c4409014011901c450156410442d08000040c0040d020050030022056000c0458110000c2d503c0e01e03503c02e070801404407411a19403034251707800407140801c14296106501200c140500051005900054517881c07a2004000901001c0c00550360205d0070001c2c12084040854500c0c0d2610905040f00d000141e55a000d42c2098020040c1d84180345209400904400b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 112114109 1250 112112859 112112887
    0x8010c08070806030a2018070512040c0f0b070212120405040e010f0903020105090d0c05070b0913140105190b04030204090f060f05060a0602030a080a02030c040306090506150303 78
    0x3901598500d00307114a0f07030366000802c2c100f58040c00018621704000500c01a110524a00449070311401e44240c000f410800c0e0780134a22050544884000c03420400008034015071140e01c00782d2041c0111041703410b00d907071110540d40c01c442075400811002008130703144045207001d1228006020020004181e8004401c207506402d104900c280e61007266110305104070380c042074001d1a4a150309003010030030140c450401074041d00003203d2011150140580103c2c1c01400b4002000c0f9460b000002400741505101b0144110b40c00a42c950f03502032141c182420825080c5d000d003140050204840080c15450705080c0902004017455000c0c400500c9942408010500b20913141200d40403540816000003d0616621010078904068003480c10504c06511942c810b4210303a00640301036030451051a03807480e0803030308ca01031811298001806000410355881458004d0b40e00440120b440c289440c0c1c0d01ea842200700e440042045480c4c0c0c012074100030741c400c0710f01040c19507800194003a43c9007410023100b0079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 112115359 1250 112114109 112114111
    0x507150b032503050a0c0939090302030a030f0905030703021309031803050718020a02060402010c0c05180a0b01030c0206010e100b0c1005061e0607060905071e08010c08 74
    0x11041140c1c0301e079840a0981e4002d01c01c0085030808203403652030300e050038649001c03501030046002e180e0514000800f00014000d407161900914400301540c2154400c1b40468524a0510a410004218004130160b42d090104100c500c1c13003074844010010514401800440159120a100383c005400400241e281c9100c14a01a0740c20180050b5200e0303549402c1d6292200c5104c18035012440350000f02c1006000079880042c1c40e400c0d0314040149000070508021ba11541480c40c0043e00840082001940620040c1d52058821442100040d80f00c1c4003203602d8014984031044012400400d01c85a2401031054801d02c0701c0130300e4140004000200003954900c410300c540904421890000b6030389841200102c1c0242c140021841e41e941101c4a0b0950348050358820360200c2440c0401064032490100c900b6125050788811000301c0041000c10056180c002a80c207980c803e80343c03940c940004005110000141407a00b0300b0401e00e0028411414600001d130704986003d80c9000251107405810420302c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 112116609 1250 112115359 112115383
    0x100615030203100e04120e032a040f02030a0b0405011a030c0a02210a0815030712050c0603070908100e031e09090408030106170f04030804050f0d0507150b03 69
    0x942d50b03803243c03048400d428160364001c000081010040c0810411100d2102519020039a54140680000b000300f40e121030b00602c511003000714030060320300c402c0503007a0341c4104143c1c0203000160900310600081c1c1a80d02c112041c5508035514501d0002614051207610701410040c01c074490790b846407070803008040c40050143d12500c0804a15000280d100300714a1413007008044c024000c95000c400c0c3c0700310640003a058000812030003000a004100b01020100c0f400c0c500800400d01240351001c801409160b200d4162154001c0c12404403407911000000c43c001c14895841e0800107182203a003505120310308001c0070f00c807410640d401a2a0400000b079543d40100003045a03890740d440c80c071060552140010f800d81024034802008140601200030b58101d400c20340300c081004a0118512604a10454903803640040c0000482e0100780300300340f030583c018865401c68803d1248220120320705205601d8800000d000000c0d402c0400c1501c0d480308103144051101840340788500c0c80040c0d2100382c50a06 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 112117859 1250 112116609 112116611
    0x5060706150312030603060b0301020901020703110a0519030b0c03131704031a060111010e0a060911190302100e1e0102100e03070c150c06090602071202030c10061503 73
    0x800261501500050070046520078490b20355001c81c408050301801480c44140d80191400340c2c5502181410300071100c6103003059002d05802c0e030542c2e42c2e4002101080a0345a0048448400800e15880380a4214442007105600103030712840c52030000c0c4481d000500d070b008410000c5c810300c0310f032a500390004c0e41c0007039014909140c41540d07051603000d03038042c991024107160050080e00c0c482c1d01301400071501801c020b03600c41071001201080f45090303a95003450400075501400d40c0a0100d03465a010408542c070901d44c0384c1041c5130b10030014222031541c003041c0b002c503201560208114580309003090030341d6002d82881004510728000080d5028810284145440410b071500703103c5a10a100c01e0360f40719604082040061100d40c070950b41d0f60011602168001c203100008600c1307000000c1310003010b070b005039240300c45040c031541e07100302419070903000300d410b10f801b031140c840028201c004c0780c61948070b00d90085442d4414a501549080c070722441d9003401c00e180140a004410749228584000c121901b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 112119109 1250 112117859 112117871
    0xf0e150d08030403140d050907470a091503110307050313051c020601050409080a05071a01030809011701031e0813060207081212010909020105070b04031e0302030105060706 76
    0x1819101c0440e000c02c4d00142c00340024060410700000d40c8000d01a288c0d440844103400d44410350401c045502e410f10700c40f40707500030003581481034002106100d41c490340305581c044604e104208040c130f80c212401c42e43c0491001203043c018030000700ca403148004218030b01071105001c0001020b01c41c0c403020700103004010300080002c600b800f0b540301c0158030b290b0060495025008003000014881407000e211001402007500015152500f40540d140180d0091222072501d004080245c4032a48001d5085400c0e5501e001c8184d021100e00144034001c600440641c3c0e46c454203c2d0005001070382c030003119003107203d11100510220703c02d881480000c0354102407042140b501810121100d005600b5280b0a500300e04801203078150707020403000300711407003c2c040319245c90f801c24604845000d9441c004a052080c071300104414955a00945082c50040c180030349491801c1d00c46141c10002200e058020952920103200445101c904081c2c1c01aa20300e01141554140000101c6078480e041000e80050b481d09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 112120359 1250 112119109 112119113
    0x40305040618052d0d0803071209080a030c090e0103050717011a040f02130f090c091a090612070908101406060309010b1e090105040905151f0f0e150d080304 69
    0x30502c0501490050280455640c81d00d030559069004880c00c41c005520400c002d007a034507044c042e2b40c0065500292681c2048a504000c80050025155002c2006000ba00020300e0840f10b040050286001e1806400501c2c1031144071646c0942055107114580c1c901245031400383c428624107208104100e4010481314103551410010340103440e10980894104d072000901c030401c14440508039140003000f84071043d86103409540c6803040d44100d44a040f0f0502a2440034518080144420940105140d050003402d0b6408201c4550403590f184c08515180c81c203102c00082000005000c0c0c0802da010301120b60490b481c0181d280c0c001e0142030052001101040602c3d00070740024241e0301c809030003100342d04450003428001c1000451410f0103007c44400118090070580217114009030000c0081c10504c0f854501ca0702c440741c0080c000201e5120300600440700000000131807009165200344010300d20300341200010016000344c048100c040c0303d414099026100d00c95940d80303c0750040317403080d100d581d98 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 112121609 1250 112120359 112120429
    0x2010503041704091109030601052407080d090f0b010801050c04060c02040e06090d09150806010c1a0c0a02010501090b010e0d050c04050106030219090303080a2304030504061805 78
    0x55044400000c1c00c1048081d17620100c00050003130b45070114101c65003a41d9503024080c40d140c4000d88055024000e9010035889480c010007003142d14403c1c283c66150000340120403045903903c0318103c8004020074240d80c217005400100f5070140034064001c100354204007071341204603c00d0348a04c2050120700b13007885080d0f540b558040b004c091364190603074880b46024071240b600d458007a0349440c0801d11002000c680805c43c41440c101800b503e071903214803610303040e0040d035040140c450101c80f0700b09487d90315043e0340580c0c20024024504618825100d00410350081d003510b1341604031195062914107002c48a17030780401c0150f1481ea080d00c208d0440302180c1040c3c3c0c1400a0b281200390060b040000001c2c045601d58010510b103c69003800504013000001c08595080303c920000c2c0004a4290102e01c150403030394000d03100306603001e1840b00b8030300780b120501c1602042101e0940c045100031038108112500210350100464500c031400082c58200000540749601c4182c0e0304856501138611840e2803503007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 112122859 1250 112121609 112121617
    0x1218070909020a051801050109060905032d0a0605070e0405060a03021909050f070e010f0206010e0907170309090601260a140a0c0e03070302090a0e0312090d1704020105030417 77
    0x14000391040003402c000d217800794500b88210344c0000d807020130006506104511800541e0740080107011003102445405050703032b04603284032001c103c01ca0f0711550010740c20040c0100c031502c0f414001c89c5502e00346101030301c00111007510600641c104070070840c26a4410f1590400da03030741160001031140d2001081407255100341c01c9044010301c0d06090022003450459800d00c02c0e034030742e07980c5030751010920b004503001a8680f50400242e804040180804100200410362049050080381c01c1c0340c3d40c0d44295091105820500f0f01d103034100044140d01401d152518aa00c14030070308008240d80d07142c0406420b18074400a100c2e20020f502400300d121002c0c0c5400107124803a40310842240303404d21104250003000c074a0300c0c07400814a140382002103814041519022207400404081007a0f40c0d245c24013002d040354210006144c0401c202001b203903452118120302801c110002444041ca818101a20b040303141404042c841c0c840600b044010303030340304080320703440744d8030103450700c3c03082e201ca410700c01240a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 112124109 1250 112122859 112122869
    0x80d0e03030a050609060604031509020619030203010f080a0b07080603070f080c120d1407060204030c0e0109050108010615030f140a0905060a0501030f030503070c080403081218070909020a 83
    0x50100c04002c540200d0b02500013114005401c1d20303100108807080c4140e11004181210b0421000e0711141c040c1d11290360940040c00c40751500d5010102c18420b00f2400c99443c0c0440d5010006101d500302d4050384001500d070050040c0901c0031a61610501800010581c1d0704004c0c0300c0340052407d88082c002c01c030003015813001d8200c0b9561140c1600751500c41c5010345500034502c072000b204814030000f8140b01c4408490322010341d10014900c059000303a000300d46c2948c040b034082200000140c0249000c000608485606070003650401140030141c8106a1011410b41e0402c903050140130365038a40000300075a03e0400150385a002000f0b0406081c02c0b03170b92030340322910980070403c0803103c541055100c1440b032401e441d9156144602e04040b02c400380009040440c0000e8a040000d0041d401141c10203c0c41c20400310728920303641c4241c5150b00a420841c0c9000c0049120701c0401450101c0542012445a50380c3c0010040c0052607a06c008030b2144103a40c0780c403003c2c820259200e0003030b4400030308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 112125359 1250 112124109 112124113
    0x1140d0f0f080301090608060708010e060d03030e101e0e0606010305040203010e06070f0908060c0307050a2d0905030102070b060405130f111009081b010e040c0207140d02090103080d0e 81
    0x91307900e07175060005110174132440500d07000d0500002e80f418031505d4810b0686803140309c510f02d1a226401405541c9444540403824555555401c803121241003200110360754a0190108008000c0d5400745034061960a0201c00541850000c504101002c680998000800c0c07800151350340d41e500000380582903602010b030a50082c00d042c400700380e92004c200000c2c41410f8070382003000341d0399503e000c4c2c0e144c20031504407481c4d8500713101140c407081c8190010f09802145290842c801c0a1080c50640388072a0750a0080f2100c910746d00012491740c00c0415031009040460085041c00050385800c01c0e10380b4020030f8548101d59070000503695842d1500300502c625000807003050a501d00345000362401203a9070703947c0c0c404c01600c58440f004520404465043d10007000103800070320320407400c4a1003003c0c1c050000341072010080b0512031503221445034417102001d550040c02c92910700804c0010b1003c00b0358106016800c1c5160040168030707201302003030460340d10111541d601c0d4030000d1444d0091503154141d08082c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 112126609 1250 112125359 112125361
    0xc16082413080307021b0a050618042301060f03060e0423070603021309020a0c08401a1608040b16050606030a0b0a0b0a051906030501140d0f0f0803 65
    0x1103030300044103014111030215102e014031179802000f07d04e10191041c03e501c4042000381ca04403507079050513070710892009000400c07001300d0124404c12148451420110842c5d5110040001c242e0042d00002c14103050b08041155034182a04c070228180020700203406c03011064945440e07048a1038082400502d40c0c400c1c0c590b03403501e41c6070080c0a0351080300005c01c1d403030b203940c1d02103081c3c6020303c00c485d5141075940b50640e04070085d40e02e20301c154120f200010303e415492404040c0300c02058000c03405400c403030700344c60b4500c10990348200090740d4217400c840328802c14080700700b41089909080307418040303828002c0003919242e0f16240032544190740010246140c003181b08011400a0810165018070403401c2d91030b940d80e40801d03d5560a0140c10280009101502041d110003059002030402040642072520140e203030400314028140303039002802c0c9c82c003040308100701d05a41441410302410041000da43d8030a00c82c40050660003100402404620900c8920401c20541d05c080000b80c6900c0005a84c032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 112127859 1250 112126609 112126621
    0x7080d0c0606050306060f1e0402041203030e0a081b0c06040303020312070f050405040e0f0d08060f0d261303030206070813020a090209150c160824130803 68
    0x3100d14465800c644090810324081210318012854900c035101c0a0203c80c1d01800510400c00740c0e959000369555103003000c4544408a44480c0004e00150507a058103248188261030000d045400784a81c00c040c0e40c104a031140002624601102c0084090b4403500c42d220720050301260406a902550647c02000014000201074011015016407004c602103520295600b01066420750000806c078000290200300c03e00031032415030702608540d900d0001711030302244602c613864542101210500c01080300e8104100c40d80c6000e88071081a00016191651003410958505605081500141e4200140c640d0410040710801041c0c4041c031a4080c0304402050340ca003070103034641c00185e0b000c500180e810740000741810314900007050702070f501921104000b0300c0c1c81001c000a41103c2c040380d91201d0801440085040700b04003402d010038600c4081d104800071020f960112a04542c007011081d0840482c2c0346007c88e6107100503001e01414a100c0c442d603034403014441036800c0d14038401030100d6804424801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 112129109 1250 112127859 112127867
    0x10b0913032607050d020408060708100501020706080f041e0b0f070306030f1104020d020705010b0f010807120504020102120414120c150f070b010b12070305041e020307080d 76
    0x4150340c081d8a414100354400b070705080e030380c5180c01040c6241c009503601203100c040c0300b44002e10149010a00041c2002e441c3c0d031440f400d024040d180310700000c0c100c0c030030b002800c14101d410100078a0309000409a4618020700030341020002010020b24844170781c001b81c10700a0f1018070440358200361561030450580e5291164050609a603540c080d00c0442000500c080c1c001e100740c0d402c1e00c1d081402000c500140d07980f182c42210308400c6564104d50203006d5103c40245500140c5a258403460010505204040500100c1041105a1410843c40c1d0090110f1550003540216400e81e1900340812542d9407400142d16290b4034521140b00d20300c0000d80000c2c0c5050402124440b150300322881700000100381f114542e144044008a60300003140141440d602030400001c01281c80300e080846e041100c0c40c0c841d944120404d030f112800c01e02000511101d54210186180d03401010b608007045581041c1e11203242d60746040303020040c0d407449007803228190750301040204018101c09003124250384180c00010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 112130359 1250 112129109 112129141
    0x21504030803010b0703020613081204060f0606030e0c060304020d080a03060302090a06090e070503030f1803010c02010b0102071a070807030e040e0d020d0206090d0302070f0c140111010207020d03030e010b09 91
    0x41d0050103000b000c18002440c410509c4031164101d100c0c141400051490b4034042d41c40540102d500310f0b6120b40c2c95411103a140220002024251800a4018600d403a10742c1044400a0741a10a003410010440146d44815104030343d15001079110340c85600d11403040d001082c103a0400307944a403040c001c010582d0003075040482a5021140706010a0031690039465568000c1c0c0074860f81500700748010b003000c2c050000941803484030b004e581c2c0300311b00310718000c00c0c00c550043e0f1400d0f0040c0d4440a400d001d070350f0100150001082d9030b908100d1030121500482c1814000e2220081c020340e000108036082c1441070070100c00c071020042003004680079070b1482942d115041d20895025000b50001c0c1c10800b400418090310840a02380030341010001440c4c1100294007020089540d1480003410f100420150f09071007010b07205501408030891604400034140c0c652013035048250380e0041100c0d00050300d9031700d40742c030000e9458100440e0010481081d240507240d96003240c0d401020030810071441840d0f2824803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 112131609 1250 112130359 112130363
    0x30d0c0c12060204090606020109050a02120705060f0301080d020d020a03050906250501050903120115020f0f0609070b0a0f0c022d1002010b0109030f05010618020306010e0a060903021504030803010b07 88
    0xc01411f65180d4050342603e2203071901a006030000040d58000d130402881035072610003540c044c1c5502940f5580092800d0300011602802c120011005101c2c11a04006d42c5103414101c1c00100b11901c8602002540c60090440041c1000f4020507080b0b8070762602e03005e44000850100c0d106d00944a441d803040350f0484a9002030382c15600b0f14020810101010040781c0110a040007078007801d0b82401c040011483c42002c440c0114401d5400b2400b602d4800c0c0314404c440529000034280b07030b00341040c5181c03400c080b5400074803000b074081126032101ca4101d1074441c1c03444034074284841e01c1009400043d02c0030300b00591095100010011020541c4d41002a000d003039801152245c0c00c003481c1400407804c0b180310619050100d24125000c3c804201500000d03141d04d4424000030518644481c00107803005507100040c1c7d81c0d20340100501c001981c1001440000c0030054071400d072450320f0410002c2c1040545c4c4000790143d040b00c180101a41c481104950256810000703c2c2e60707039651922100e005512807001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 112132859 1250 112131609 112131611
    0x1503021012022503080a290604030203030f1801020c0d14010e10230402030d080a0207020d030e01080619060309081204050a0b0109140403080c0c0d0801080d0806030d0c0c1206020409 80
    0x4514003160b108004040e24111030541700707600c4a487d60300b01a084146115840300003070000000680d02000184001500c0c50384007a03d50914103035256001108002c5035065420034803901c0101d40f9203c2c4800903a0390049d40740022820685035107801840c1e801102c000303d00801c0d006101101c0c6075080141040c8208030403440c0d030454883d043c0104c180965000b94103800040860100c0ba128184481e04050005d0005242001301d0b80003a00590101c0005c4011401c9da1100b12f0031503030014001540104282e801041100000d016040d9021160003200181583c4403445400d008909044c0c071002c0701060210b001c10300306410420b036500c04202d022188212100c1c004100350200340115460804080000005a2141d42d806da5031b035030b4024110043d8803014040d08840440c10051030180c0c506c00d031a504000d50629407520308102e05100f0200500c076985040c0181a2800569500004502c0c81d2004d600d12441c6408200c0d0002075010001841003401c110040c000f0a0340207008460035400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 112134109 1250 112132859 112132861
    0x150a020d020a0f060b220c1205070f0305091f0b19230112020a0806040509010b010207050d02010306030b0a0b18041a0a0204050402070b0604150302101202250308 71
    0x120307601c00480b04018404004844460005600ea0f008642104801000c1c0d041c008000d04010144041d80d8a0f01c49203d40c44030740d03105443e504011514601e83c55801d05100614211001909a444000b82142010f5841000501c40d02c4c0a104e8035026810520150b04003240c000c1040380501100400c2d00d120300280d07500044140c600380e000e07004640800703109070324203070404520308003501080c3c1c0d80c14180909030980d065054401d01c000d24902ca8141c807100785c0350800d03405000854100070b107502d00c240e141c0f1880e00b9032a03800240340d0040710320407151400c410b02d480c40120083c0c9901e034001030170b0705000c206021101c231244d00450782d80d040c1500c00582100900900602920007a1000703031251028000d0b1000c0070b840c50115a500000408026161070703a500003003002c80e401114180c1d032030f554003000d01c810307807604e8012015030808201c0048000d80c1160001040409000c0d08501400780703110030004112600d4050b41e101d601040340b14565420030b070646500bc0308101c1d04c103c001410040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 112135359 1250 112134109 112134133
    0x7140105130c06030e030f041d0705091e031212040512040609050906010c02060d1a0907080c0d0f0915150806010915030507060504030b09060c070b04020d02150a02 72
    0x403122900e482d08441c01d4907003a0715001c01030300144500200c408443c04204691402c000c1d01e00014001400c25640103001080030303810604d60b008018000c9420400304000050441d512120390441c0803c0e10000d500e03a510b00301c00040d281020700c110781d03540e980c40403814002c7c0070340b62118540302c0c50040d429241280345c038490941040c402c5008250101d50401e070180114108050701d03a80c001c6060414400350102c5030001515600005254940c054442c04241c21406100825031150081039485091505007010060b2411200500c16400b0341d0010542c65400340c06500718036011085810100528210781c205068022565585003e105041160120841e40c2c4803410030b0480303180c0d002505481e401c0c400300c00d0103050402c0c5c40c0e150315890400c0100125405000a100034900c0383c540641e40c502d90304c1c0c0326071008001048000c5c650490700c20403a611564100300c2d824907502c44101040340c4c2e214800545420311000000c3e400060044208203120900c030001d00c1600e28070340031214000004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 112136609 1250 112135359 112135381
    0x403110102030c1e0c07080304060e0a2102011803060515090621012c070503030301030506130f120810090605030c06070618080409050a060b030f07110307140105 71
    0xa803800c40010b8003c011101844506805000c0e0302c4a50504c09850951060a00c518146580e00059032540000a007004244c2d040603840f904880181d548100c45854440075051490490f4001b61061800749032208c1160301c16402eaa05030410984901c100588a0a042c2d005180841e0002a41c640c0711610000601c1d01e040018820380000f8182d00300700e48500301ca46510389002034a10000e40d01c0e94a405650149800d1f82d0241400c642c04804c03407004d40c0d903aa40d150183c07661100b40250804c20050020035400301e03001780d1200718240d1103031000c03c042c50400202d03100c0f000003520702d041103940074410342d42c0050050b003c0d551013069400702c1d03900d81400508584e140d00c94194542c0c0710300d01030000741c24110003a0440300d00a2200007000c0c0c00850107038100c4070100d842240c8071403000a05020202051242036000b51100704200202c03800d00c001c0903075621002c1e2623040c1c9418040006102c031403088003220140c240280039680c850a0701c0c541481143c00c503143c86c0d4025420500010b0b10b540340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 112137859 1250 112136609 112136611
    0x32a0a05090a0905160324020403080307050a1407030201020304030801080f0a02040b06040306050c1905040609030312090507090608011107080a1d0a06050c061f09020d060302090906040311010203 86
    0x24181c1c0d5450300d50510003801001c1c84036049809014844010042041e41024100118025010258091840c2c0b000509a0010b002401ca25520600c0248041040d078170940764000ca55040c07290b96041807080540744c0d034010441207820601b001842c0401c01d0781c190051406075200341c844011a90b2541c41d56502c030249040c0112860b400780c40c0e08400351500e03420801c01a80c0103401149025100d8443d03000f620300840304900e02d80000202c0c0aa1508480318440032000c0b985032a500f05402c03c80024590086480302070308108880740c803003050903403540c000b4401c00e602c04221441250f80300e41c0c05028000ca84510760b22540b0f440220854072000d01c0861f0200c9a008040c00e02d00011014180c2d0f442d4840c40400d1102102040036441c0c688403510380b880609110380362603440d91b00301c2d00d00900e8220020f00030a510507403c80e241402c0310b4590300d01c8080d43c100e80c03000350300c903802c0044040041c035a6500280d40310031044280103d8910200d001c0d0302941c020740c0d500c42d0140300c100c00303942030b848 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 112139109 1250 112137859 112137869
    0x8071103030c0d020906070606031403030402010e060306190f170705150304140613020405060d050c01030e030f0f070c08030708040504110f13060201180f080f09032a0a 74
    0x820000208003a07000b400400218504060050400b500d07100412034580005008680c42c5d580c4182c24001e201200940d4841c1c0100701c0011886c40c034155000911039666002054042c580110100d034450742e5524400300c01100d403000d003503a600d654034840d0751160b401d4031a200420f03c10303880b0b40942107004150300e13081d14000780401d1000751a2010380f1400c4d9000070415182d94400c01200900000240081406074a80e01007060f000c0c0b4490042000b21240501450300c02c070002000c071000154086000107180300c007403e002030f070301030144105400c6202d00d84514401150004500300300f088040c0c040c1940e2800b98002e8420f258132916043d0f56403040711405840a40c0601c020445071070a80c01c1103458400d030707002e4581810480000645036802280c1402100d15201c441880302d2682403244007114101819105e0855000d034442010a92004070050f04a040c0060741e081d840102ca02105c0d12004080e04072031015401d10b208010050350901505215410003110080c07e140459410090350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 112140359 1250 112139109 112139113
    0x3090314070c26030301060801260c011202091020070810230c07021206010501051b01060b0c150106031b0c170c150a090f020108090307050106060e01080711 69
    0x2800c0c2111000203070201000030104210f84000040c4440d030a101031402004562605109941020190192901d02c101d400500c4c07410020041700702c0400141000e1075007030a0800300c12442e4a042403c0282c412050100c0c1c0110035046400c07100d03030780400c0740324030b04c1c00da05081010b075243c1c054940c3e01c9540a02c605c44140d8807901328038003c03140c0d9a20012822401c1454035101901070b11400c0b030904001c6503030103503200c2c021a440055080090569407800b00c00c80c094005903045c00001f810500480c124940145100011044070303039000d5000030050480345202d162030302100707000d8682c1c80368950700d01246c4250320303000011a14040c1c041c11110401412010f200d2080c540c40480e650711034400c0130782d5040100e002403c03038072520f03400070b1000f60b8018000c0c08503a003d010658030429005400141c9041c5403202c40c0002c140300c0e44107c044d00764246401c403c5034460841e10340ca503004888018105d5482c1c04400112990800801d98004d00223072074404035982e5160080c2e4007913101948048490b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 112141609 1250 112140359 112140383
    0x20402040803311a0c0d05030103140a15020f13090b01092106050a140405010b030c0f090c030907090f0209040506090601121107050a0c08120c0a0201120b0405070309031407 76
    0x4800048013a050071400b081d29600300041d030010a03203004024420080400c2e00040140140016440c0042c40d4900250040803400d100da51035190350440b03e00d08211456000c14034021002c0504220303807143e0030410800c500191a5501600240303000318a1a02185070540006240c811005410200f4071b000300368007030f082c003c51301c1e210054a801803c80121560f540c560f02c7c0340c0c3d09498030041c0070700d002e0b400000c1c0740c200d24000d0524218020584500c96440040c4804c03456441400040c0d01c14001c0382490b4032911251107880c5005d0240d004020000d040c00035400c2c0e4003505030302400c101101100e0a01840c1c44800c1809580181603408030300103a070010011544e0103ca8100c03401e10610411214a881d003d0307241c1c01d04041005400301c6828020503400c1001c0303203041090340420352002500314641209003250a5550545000080c1849420314880c003c203811540311055440e006042480b40d46490308008008140b5100110040b0310803070410300c0d0441141007512445540082c1e50032007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 112142859 1250 112141609 112141619
    0x108060c030103061a1011070b0c032205060d090c05151b1c0512090102040807090b030309060f09120c01090302120f030a0801081002130303180302040204080331 71
    0x3402070390022412450829101500381e8031b80598500c1207001d203960381800380c40d4180882d410003406501045c01240c091102c8840564048100d880040d03d6400c8a46000205180300300a210280d0040d9400b00c00400d4806140c1081d03000350300003c2c0711740b403100c3c1d00c5503d0707001b0020440314180c210307581c0072014070a086082400c1c040382940282d070042110005110a401000914688800344000500c08186c500300d05118900f42070300031a05038002e50601d400e043d070843c1d07114400d101f4000d0864440c2203090380c0e03813402c2c0111105180c02070001c594a20100c0c81854417a807007251880c0c0075642d03481c016201c071000850403a0b04000140d43e050500c6103540c080014000b01c200551100e4040e0f061980c0c0081020402410f5210a50312086a190302d04000181404158089411900c2c01040000c107031022581c0c1c1c2c4010f981d4503041c0180c15422000c10301d81c2402c06070304000c2d0000e200190105800307070004080c01440442c2c0066801c0c0210440c05040032190b12070701030b111241c2840040c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 112144109 1250 112142859 112142861
    0x30705030f1008030309031b010e03070b0a0b030102040b04060e01171f0e130506090a0807030818070b03060a0f08030405040e0f030a031a0105120609061203070c0e0108060c03010306 80
    0x7401003007016011000b10303210000c040c2564010744080d040c5a200040c0001c440171410404102c0800004c002c0010a1172020000d890f84681e0800400d180e64100004041980c01d42c400c0480c000054000c54171030f40c0307070b210070703406e035070082c01500c000c01c2a004161449600c550034800d070104401d000712900d900c9401c20350040f680d19001a40d44001e5000000c80c03444545c10402d88101680c0724280d0170700680b41055070a118028280d6491504100840b02c0030496400464000e40d5252406880503030303503100c1124220010501c0121280600c00340011029007800145006800c101d070708015841e5241624038000c003036846190310310b4100740000c0021b4982580200c00c0ca111840035200042c0e00d16003807609680c400040f5602080d600c0c980c400021880c000017181c5508203080c400d1502c0c1528412043c0f07004020300c19031241c0703800b5001941f03e8451906098a150111040b02c0e11703405c15103800101c484090082d185001944000042c1d46013000402c0f07801180c4074401c0c1e034690703400d54440b84 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 112145359 1250 112144109 112144111
    0x150a0c0f050a0e1c1a0114010513030f0f11120c0f0303040f0e0702010605060a120522200102120a1404031e0b0f07090509130501062405030705030f 65
    0x2905104104841c40f24030f4460144007040581c140b5042c68a0449624000d482010100c000d0320303c101c0c083c40184184100700795039240030780d400d003003081e00c0d40055202e0001109664000401085a440c00c0e203040004180b00d0701012403081640720643d007080d0050204a40b01d0b91403060f580d070300041003440749040c03030501840889005420b6a2405446050703124450300c0d558406020002c0810400c94981d40c20701c1400080e06003110340328902201d03c00c00a00001071541da00100c0ba40e59004241000750600c409100c54020410503070310304d441e505000d032800b40ca000c003503040002d031131403207060a610118075466400036403807540d400c00140c104100c803005030b404e01d003000d144010000400400c141e00c1c400305417001d058803440b410066030b00d00145881009000180c800700714030f09000440b80c00c200028240d540a90340c3c0c07100390383c2c0c5c5090f000a020b0081c501134180d5103010000700b0440d01c000c90b030f010206102e20f9030b590010035441044600784000c0b070750400019401c1c8040781c100004440d9503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 112146609 1250 112145359 112145377
    0x1e09070915050904080403031704080f0309070806070207090e06010b03040b0c090d150c0815011101150e01030b09060709090203090c04060920030f040f15050108150a0c0f05 76
    0x103140442d0b01c2e44081002c0b10015202a180392074045400c00801d075000345103800200c3c540784003010794102940c03045400e00444101c5100d00b03d010000806400042040800500641080700c425051410010751104540d00414002905084c0d0f0300400e10000209241241d41c00024280340d40e54079202c034111040050405901034208116400c41c40e6928401030452901554401c20555a40c80509084581c034207604130078048040d0421451200e0306949020184080c01d14400c8165190340f014014003000c040d25040e08010703207000c298620318945141c140c902c152810700705030f02c803011100d07601c405c1290031200043c0c00340d41c14031201c1656000385030800000c0040b5445018048000703400d5035410b030042c400c0d245e611900040804480200e481c00804061030340da2071402c10b162141d401000081014001e289030710a42410440c21a462807442c2c141e001040100f561900a11601c804100700b0300fa290702844000b140c89850139101e000b07021811034480e10505100c2c6901596280c1020000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 112147859 1250 112146609 112146641
    0x9030c0603090a1202030a110a02030d0f0e12010203040201020f03180f01050d0e0f010606030e03040902031b0a020705030129120708030d0603060606020f07090e0307060e061e090709 80
    0x14a00000384d0800040000300043d4004c0c640721a49048014191003058029440c00e078002c0e020075000d602c01261100342c80083e46040c610846841c45c06440700361800c840c00341c1164032140c02082e640b806601031b5005a100341d0135503640c1c03030704c182c04c096903030044041d002c0c2000c865031f80e12603441c070348054038030380da060103060035402c080310f160819040300c00c0310a030040303241c10a41445400c100c1c284556405894039040c01c000c441401c030f100c5641c0740030318014181240c0d40000466000c2e21420040700c0242c0c0c0d00c0452a41c4c4104445000391110001d00c1128025824a007880445408001003034903080c140da420f100c10b6000030004c12840103031101400440f402824008503a0004c20702c001c0408034032441c00820340615501c0c00030300302c9085921110071900031968482031503801044100c1203900d03030080403c000284500d124214454100004c1c140341c0342c00a2200644000f040e0179205000e06a541d03031001c40c040d5140220004112000e010f40d400480080c080b1100c00e178091610000c004c50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 112149109 1250 112147859 112147873
    0x1b091202040f0509010c020f0d0f0e04090606080d020c04020403080d0c120f23010f0b0c010f020a030f0b03011406121c021c0e0d03050d0b0a06080a1109030c060309 72
    0x4078542c100d07501559040101d0351652403c4840035010000041e03090802130040602e402d00400040817040e183c8504c00802003170b90fa18414640c2c0d140c10038041d054201d13604112003907407610541d59902c008a051f80c050f000786021140e440c5030078801c0d902102d401840a9140c005c0c0c4080e5140204441200d14060002000041484104600c588200384921100001c0d00e00d0840081d440c50900e500d8104a15500030401400034400c086c1ca00c00403035448201481e124040240d00a024000c2e24444084180c40811580c2ca00b0b40c2c15007180c401400c0e81c000410404840c10141400d803080341150003100e81c00e072008240c0b5402d0800ba0f11281024080a0f2251510109800328083e4100d000e04401a4804200c2001a0b040816255102e00c49418200007401c010703004034010a000880140038850041000c81c105640340e04000103400c401012601159211a0003410020003a100e411710b8030b04d40350807030000304181e02c11510b04203002070040c5440c1140d4002c00400307a0004040c51002d020b540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 112150359 1250 112149109 112149131
    0x7060903050706061707080604020a030f03111203060906040b0f011d04060b090909152a120a0b1021180b09210a030903090b04060c061b09120204 64
    0x302c1440042e0144c00f00e0074418503513134104949010442d0700190529002304003400700594916003000e046030740c0242d04540d110842e0805503420269610301004c0d602811540b003603d6440315009510814040f0707840c290b5a1500d4050000f04d480c51901d158100c0d0b282541e041c40d640c002e136100065082401d11020303181704041c0c0030405907656541322941141020a0504580c505400c8050703110200d01d00034408003600009003c60403c02400032f8010041d03c0140075440440e24030064071003602c942c2100d950760400420b4020060080b62401c65032490302a60380d0003480d103038440459884480e96802ea45005c0740002c102001c0c15040003034001562200c81c144d1188a01c142815054002c005100641c50700001c2e45090805640741904511300e003800040080326a4415101814050705c0c2c000f80104240c9001d8807101c0d080d8100010300d101c0441c0c0003540c070341c0c0400c03020205813181c00180032031641d180354411000031000110f00420352201062150840002a030800da5000510120ba05540c034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 112151609 1250 112150359 112150361
    0x2d0402070516090e15090c04060e25020c1306030623060409020a0b031305010612050f07061b03020a06090b06030f0c0105030601030b03152508040807060903050706 72
    0x6200072185500032421050360604014680030080c28144800c0c00048070000c1219120801030140098000810300452481d550402500c55900c401400410086440d10541e41c140c0c6403c6981d18072800c042000c042c0711241c4411104490100c0e50001e007052983c403005c21a41c49464900d620340790307695a40c008041a15401120000400c402042100200340040c24210440c02410a4012800d012100005840d88801c001c101c40c08544c0b21910307034681d40b400274044c800520015101e50f003080da0100301c10b650800d038001c0f20780c8540226204282c449211584030006442020080398211030268040040c948076400c00d207119106035403d115450340c40c1c0301110381c00b52040d203020350703c40e040016a06041200b07100c9500c482004040000f4180002007403844020862410141c81da2044030312910304002004090142030000042031500741d0a02c2e0161680c655002d40120012003003411490244103454007441e082980c0c0c41c685503240c0c54000c090455510218200041040003c0c0440c000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 112152859 1250 112151609 112151617
    0x50d110d05010306021905040f030f060213032306060a030b0402120d020102040302100206040b07110c030a051b01090602060a0510170a06051005090a050702070305030a080609010e04022d0402 84
    0x11130100103032542d4100d4940d40c0c0008030030782d983c01440070800003130009103400c81040c0f0890350f02600c02140201640703002d101034041c1d0015101c4e0508480d2010042021258071640240310340280122620984400b0566842c2c1c140c898a800841d4000300384081000040042d50041c00502840302d4040b0002c00d0a20f42000d000e41703540184d40c040b40a0046180108590242054910081030700c0d00301a1206030705000050040760501034203020141c0c0986007480385102c1840b0080554103403003c1030034880c1e200c204004105589117801120220703030758042c49042c0207592040d030080c101c9944400300310005080190500c0341e2144c501d400064414a90f44142c146850200050003404029140003000e8071800f50a00740441d81d9858203002d152245141242d2100320480c000c60319840e2920241c3c10000c5a41000e000b078000042c2c03500c051504088172500401c1c06031084a0140e0365010a40c4e00d0902c20388009501c4031403c5014032710703081034202c8040e4048015164003541200000001e0490344 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 112154109 1250 112152859 112152863
    0xc0c03060b01090e01030525090213090506091012080d050c09190b0d090c050a03031d10050d021b07080709050108060402101b1712070f050d110d050103 67
    0x41c49120071071081d680041100c00a005607203004001e541140d40c0c0540710402c1e40689101070301c1c03101c205e08840c04070740c481c0801480c144004654480d014803441f4010380c2c9034011207034120700b402c0224040d400c1c1641140d01c0394102c01c80051086043c10704100408554070015a044902402125141070b510303c80c0e54010301110031403990769178003101484a008030b0010b05050b0902e40600070440401104112640701e00022800512000d0928011820b00b80d20b0300450b0304452007100200c105900511700080b20740030f026540b01203000311410030034011860780b10000000c4007400740c4001c03a501c50b006449000c1481402c500e66080003200c0034501011944201c94580c010101003000e030b01c0511403280580001d001500e220318250700410002d0202188030002c00c0071544540740c06c404040400c41c0300d503070701042c407060b44030740303071414007459000240920184846440494080f90081e5610141c81c0d00a4071498101804900e500d4010142a0a0307800030103400c00c4441290390380d600c2100d01941c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 112155359 1250 112154109 112154111
    0x50a11160e070309032a060507020c13060f03080309010e010509030a09061409210118021305070c110109080f030309010c09030308011503021603020a020312091c02010c0c0306 77
    0x3441d154400750348250141100080c180361600c05808260304c110b02c0042c43c000003c00142d00c21180080c0e80e910240b400300078003100d02d40018000b002e640801c00180607002200e036040f4012003111103204640141c4101c813070038400310108000041541c405168021900b10002030118013600c500303425200116510101a0000518051007a0b084415280a420f441c501218008901c601c07142d49840381800684c810207207040c2803003d102c0504149500e84076040d00074040010100300000390f80c802400102e120350720f41d00322485960a0f5214bc81d10500c501e5440c16100c02140e243e203c10508099826810414070341c0c00454140c10401210301504a010300942d0b0300e1a02c031841346c0c02c58036002485010042c4061003000480c0d4020307459419242041e52090b039400d440182580207104001c10040c91041110034101455008a001e42581d8000e90942d903d040c0e1003030340d4000c2481804400c40d030000600f81d01400861503104500d10151060410700c00035003264a83c8010b100c3d070307a4402c503406 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 112156609 1250 112155359 112155403
    0x906021909170a020109090203040816050a02031c0e10030e0d0e1305040201050307080a0b1c05060604060803070308090709060f08011b0804060510090507050903070b07080901050a11 80
    0x140355061a1102842d82d6000e00f405080039400200401414800c5050700c2d40c021000c01d06214010045489140c2d00c41e002c0902001700d46882501c3d400c50902c240e219005103c207a041d507000100c20304502e90842d9581c01c01d800d20200070007851010700b42c1101e04040e51110103a144e21401c00400900101c5911008e0701034031440104140503091241c40e114040c200014400140d800c101a00e402100c142080f440d503a03107038041c10004160740480f240d446003903600b0075000104106a0050154000c00c250781041e511041880309441e0385100740381c1d40d07500030417904001c01e1140801a030020808420303100029039032003403041a01c44542100101c605030942c03c205040d024840d104101d00f2078070b0180e031004056030000c1c06035500180b001d407803540c0350400035401401044104000d420741c80d00400c42810200001040380e040f070b0f80841d009200b51000414203518000039106410707070204241d481c101c0741c280111015080000d104080c001035a20b2801000c500f840361041e0a403595030002a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 112157859 1250 112156609 112156619
    0x609110903120f031b0702031207110307140d08040e01060f0f14070b060f09070503100b03040507090c0507080409020d0f1407080606070c080a05060106050f030a0906021909 76
    0x5184801e81140c1d0360b01c0081160390070a404071415030358840c003100c80b10004c981002160f030301c541c801e4a030001d6240c068201c0080115004c9405003141600900c8e0f10b502c01c0140c842850f075180c3c4640500c0000b0314940080917218588014090342c2a0312030042c4a0801781d551054000e00c01c420307002000031400070001c4681e0582d1041e2a1005000189803842d21588550190303901441000d0020702070803104000600b01da200d00e001e1007007107440504498014a003071a002440c0c1d40050f10700e42400c81c0c4910f40064003000001c1560b001d1a0490302070034145103428580d4000b4590b5036454000c0c400c2c140106400708560001a0000349001da01c00359480310b810003124201d40c9180c07050a8650314001000c40b00007610aa03165214019060110154a4000006505009400f801013420b00d90724404241030b40041400c2800301d101c5c01c2225001e0b601c0300420303070795802994400002030005000180011441d070704200708481c01a1801441d00080d489402c01e442906c09440b000f08110510400c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 112159109 1250 112157859 112157863
    0x504091110090b04050609040603050a031707020c01050f09010c050303190f0203090d0c0507050409081c180b040f121d03010608070b070206160b0114010201060312050309010609110903 81
    0x168101492400c140020f08281032584507000b28000c050040d50086800e40107071b1980d0b0f0044002e15080401c07128007945d5440d0080140700d019507032095508035240460212400001c412290301d0050712543e042505041c0010030301c0d08100021410041542c002c8400305006100660141c1005442460302c0106403c122056800466075140c0702441002080b031010070204130808003c1040c6840707520350145040c210714092164120542c0242790000103070802c40540002d00d14031341c0c002d513030a110007110b51080f0308451441080003801d030100a01400050744840c1c1003a88103120307803100f240301406900c0303c4148020b4000084007140365548040c500c44e440a818004400080380240031841c1030151081d01c820540c81050076410000c11b080d030440d590441035440b2817501c0300480b4640710141c2440c840d040c1c020b1164100455001072880340f2948103001d01c00540c0d4001d07000c0d0810b5510300030102c5199000501250f515503840074089018410381c054281d51061901189031251a9402018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 112160359 1250 112159109 112159129
    0x303080c390607050d050a0f06060c020a050306132910060206060a15030e01110a05030f01090603020d120201090c060f120204030506061203070f080d0b0409030c06110405040911 78
    0x1101d94840b100300940786034040f044500e03d100318800410b064460703c0b0424060501c0341c002568880c18032074045001a482800c11003505d00031034250741c14581c7c0310281506e90b10309a030801101c50a80aa807800f25105484070680988120008480592915010003c43d0b906807424802c4411000c42000317503d07810030886130449400c45800c0d90080c40d10311844002d5110328501001d050700c50303000390b204030001e51020050800d5950255540c028203140100594011640d204c48080c84400118a02c5101d100d00000d40780d000c0c1542c03005000035291401c1c039840303e200c080110343d00c403400840001d60302c60a03140140f01648440448003800d90700031380340c0505010700a04c5030f4410300c000c20100b000001e034990051815580250800780d010700311801c41c0f0404e10042c20100150150004000c00c08008100459000ca020045900540e040006541030148040c00040c4083c1440c80450034540c4540140c54840020500d4569124080b402f030b03410b0201c00f503808203404801d084031303801c1c4000e480c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 112161609 1250 112160359 112160467
    0x1050a05060309060612121207080702030703020307082a010b01080c0909130f020315010e0105010306031104051909060218040216110102010f1b110c01090303080c 72
    0x750842c5000d46100307580360402003100e403080c05003c031003102c0c4c3c1700140803044280062002055030f6015541d5040a503403401c2e6042d07030018051400040e64548084280c500c100e0345603018516002294607500001d41102c0211180d04e58140d016041180520000c41140d03500e0300c0000c034200c84044009030415100810705400944104a01c0140d60754501000394004110904000030b0100741c200384001c031910880007034151050a0b6066149288007103101e04990b0707981c01e070103c80d0703803900b0044050380c1c05032000074a15904d0900d019964074050b001594003161104a20302080102c40030801525502403050312810350000d00d8440000810807860203050082d18154903180b03007101c540046062081c805000e901c1421072080c8a40c0c402e4000e000506485c403024441c0b00d0050a1189005641d00b501a01003483e04805044521010540595418050f103030354584030301d5510140c600120040c81c02d22000800c22900741d500400144c228000100c1400c07007043c1c12011014900c6e1807048000c9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 112162859 1250 112161609 112161619
    0x305180a06030f14060109090504111207080705030309064602150108060408030c0c030a08090c040501030b16020c0402040608010e010801090c17010b030607050a0f050408250b07030801050a05 84
    0x5c000003a60041201c00032148444400200d5540768240104100401d0840c140d2216003028158816040011040c2c1960b1a600503078502e03c0d40c8500305552486194821900326900340b20300d41c02550b00220115100f14040a890828000b491032240240146246d80c20380c000c80b5070303848290550410002e0342034840040b1030140c40d41029806955070400a000515480c000000101c503da5130794180c4512007810307c222030b180d90b10400301600f58a022201d0703124038842c004812902e4035080c02014102c94000c000703442d003034171000840480c11000903400d80c158411036000c1c03209a00c4520007040109425a03440e40c5039410028480c2d02d50304181d115410300d0f8141035210300840d1107105040201c40c403100b08802e2803c50704080902501585440381c0e8980290300c100311225400500070310819180d5510a1032410644c0750603209800b07140a400b03d20b80c480d4030a000c03c84414558000800c8500294805080c2c1d60503520911b03601181081700040d01c8030004000f075003841d15a1202800040360 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 112164109 1250 112162859 112162861
    0x4050102041a090a12080f030103060606030b06090d03030b0612010b0a0206010f03050d0c06060b031801240302090a1b0c060b060a2c131e0603030c0305180a06030f14 73
    0x13840d0070894010f116640c240d00c882e00e000c10010b001110f80c01d640ba0142981c61b580c0d603042c00001400680308160100f810b10b80491a185855402c540066000400071303007600e442c0d03840490080c1206400c207034012804100c11140d005808038070f94002c2031040c4185980e2000755900908080041e44040194200a1030500005202040c0d445a40d4510300e0302c2c00c054810703414100c001e0051540003001d03c810000901c031102d1020003903c0c013210b82d00c10090211070b003d016229013130b05030451b0054088081c1c810610044c83d0000c6090b4000c814504041840901c5c080405981c603418080340000c500c0803c419010045240176040018004480d25030505240d41000f4206000082c0b1b040c03240104502e100301c00c01c42d02d900f500c01d40c07000500404001117648520100814801182108228000e6050807446216006980683c0c0d4940d90344440f10ba03042e0340c1a52903400071404d0701804c004c0544c02160315110034025200030629980c002c69170385031b5003c10500300d8a20003001035070708031410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 112165359 1250 112164109 112164127
    0xf11041e0b030f0a08090105040308040311150f0f0304060207050327060a0503070c0f0507090f140402010c0305131508070f0207080d0e1f030603120201020403020f010e1804050102041a 81
    0x104400c110107400c2401c1755a141000c00040340c80b4800e6070001095441c01103008010310285a00281070107906441420305103d403090491558003800008525003107041201680441c01d80002c0d54006200d40b03805401c00b101991600c3c216004070010200d9465440c82150b9445103050030400b445106840517403034800d20840080540c0b100500c150184010f0001c0380c01000306035020181141d0b08001954862901c075448070b0081c023111594690180d0812480501d50001107600d01d0040e80d058480c070780680c4c4559415203003500041d1b04801c24030202d03800003903a010f0402141c06c050038560388949851429440290415681c0320044086610403a0288081c01000403003021410150626840c0840c000f00020040540041c0d0109101a04480c82990300d40581211041e60b109403079200185072001c3c070817400c0740600d00c0069072020f11074a294405d9401000405c805400c09000364041206090290703c4070711054400300e94680d8000380409c2115600d0100c004151b02c3d00c0707500c42c9000250 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 112166609 1250 112165359 112165363
    0x102100507020c010e01020c0d03020c010216051021050411010f0507020d080d0228020d02061902070c030204050411090604090302030316021e0d03050c04050d0f11041e0b030f 77
    0x203003c42410b03c0803100142c10305038000c1103400d07144c40c0010500b03070810090b403038020b4480491444040c09445995110002c850700300e114001501e40c0603045884203114440103c5940c81203595184035003841c2c045a02c0030400500400d8803850003182d0403030308400c6050004000c0c910210000d802c000c2e06215400059542070f44690509401c50030070f50319004440d240400911a0900d04c1c02d000410b00041c43d803503d0780a90700030000c00c0030b800703980c4241c1070310714183d840c1d00c7c1c21160081340c503000c010600030810f029400303840002d00a03102e40d0f424075200d41c0820b00721801074074251002540380120000310f10f80842c485610900680c0c090000700080d41d8080d540b0f00010709040345a03160304482080c061f108004422134500c01829207038150b03400e5050280c544a101c1110300000e82400300290b04c0b100000c007150116440603010b11500c240c991a5004580003610040f00c581010020307a81103542ca9000710003c602680756040d1031001846803084c00c646e80c03404124060f410021240301c4050700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 112167859 1250 112166609 112166623
    0x80405030304171902070510090b120714040e040b181504080706111e0306010509040209010225090b090603060f071b0305070b15060412020406090e0606010210050702 73
    0x10100080483c0b590b500f255046900408014035100c41c15034034140e441d1540051404100c800540790001c8442110780201d82182c46402000701109003003040c03105074405d03005800e0b070201c920326207651580d01030101e02050ba440303540140c5511030300c44140020311822426280d0130000640d0360801210791403101949880c08417600c00f000740441c2000605100440040710407060f44040d0421605103040645074144e00500740443d40b4003150001788000a2a040131280a84030585800d401c01b10044200000f0354440c0800c94114000c2d02d524445900d045403000d41c44002004859501d1410114a0400c40c2c40f10081944146586030512015440110f502500174100700b00c11803051f0b43d410001d54500c0d800c1c8440c0c0b107100f009094010305250340400503000040c4070385030206598071307001100e00980f09010415684100d0030001000b081301c1d218001d0b8500c2e80f000c1c20110301c0300e940c3c1902c07004840c14a0248101e603042007003008401d42c1d052012070b080b030f625124104020700f070400d8000d641300a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 112169109 1250 112167859 112167863
    0xc010e0106051507030e0402040e0708070329180708180604020a05060c0a0803090604030f020a0302060708100b030118230105040b010e041b030b1c150605030d02010207030f080405030304 82
    0xf0b00140750400c1c140714017100402c0d1000a08207540e40c075510109010086000c440c480000785c001d83c00b00703210070b2181c000c1551b0011008048440c040c009001002c1080c0b18207a5143c1c0400e10002100c211070000c08140c0c030030790300b0780c545104600e050301c0d40c099017000851215815400c280200300060f90b410004c1d0041d25420740d282520340380124080c51404c1003285d4044c01100000c01000305003c0e0010340544114170035911180300481c151003c0e6a1606030f8800240560400400550a680f08241c1c2a61114a03150a00c1a560313813420143c1135580280c00040700742e1280c3c041607805402030b0082c00c5901845403807005400b0484540802c80440600070306101d03988510b22852160f12840003583d046400810420003280c9491050a01c803113015141c1c2c010a080c21400e01c554600001c07003444403a2049041004010690f50b500d404039128141d00c2c031010342d5078102140c142c4040241d040800b075990001a69074040d030901418120880386a1003c01c00100c040200048007c825070360415 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 112170359 1250 112169109 112169149
    0x605090105100503310b040606050904030e191a030610080f01060507110a0e06030105070e0d0605060307030f03020d020c0d020a03060209011215090f050708160e0301050c0c010e010605 81
    0x121044a060718616031901505040c01c0040c217842090140425409018902c01c02d0100a041e50795414050488800c98001d0f0114106440d1a50315080151001590340f610b1005184101c0c2c8034209000282a80711201e10206800b10812296080200c0d011400c8009800d005030649416034150401e040140a12000c200340881c3c04030800541c0212502c1c1508010450200d082c0c0303608203c0042d03070b0110b800074429070034070000c21100760040b1219200301038060803d0307240c040d8a4031000c0c0070b800040d210b80d0f0103120328034000001c5500c225450700c0d030340d1103540a00f00301d0400d0f00c3c0007454030001020035481132a00c981c81500507601d001c0160101ca038001c1e40541c0b10000c440c0140c800d4641201e1282042c5d0620b41765013600810541070005480058208000c00c544286602c42291411116603000c04c1405020035170798480c91240404600305032a00326400b401910120b07094030015640081c0b010804100f50380306c580c0a0203140345940c0d41c100200b00701c030301d003400103802d03401040788841c001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 112171609 1250 112170359 112170391
    0x5191d0c190306050c0703020118080417030c0303010303050712090501020709050901020c0607020715020313090b03030c0a03030603060e0a0302070e06040e010603080403050705011706090a090b0a0605090105100503 94
    0x140079040039480085030004000c110314502080e07081040d80c82620114019440c01c41e15948071056032500d900b4154114140a060500309503988025400c12801070f0114070040c00303003555446080004502840c030903600c003a164203451506040024a0800103414007c0445003840142da000414100700e801d40072000c10540c8a00702e24034024440d1840300040760290008005086400243d00b000300c8100388030f04440c941440b40d04a85a000b48210300e40d01d1101039800700020f28042d0080c136200344009082d40e192041038110705240c095580e40450100c1d840c0c0100300180801c0384102002190144050400f0142d60b54009446901d240607100d44010703040040358040c4c0392607204022040d00d0a0080000c80e03201c1c1041e0095800920003100e540c4a01c910118542d4400d00c000c90485280144410886c1c80c1c408c10409484d400070548034030156140c05401c0420000495103004540c0a01c0000740c1ca801c15081c08103114050304410b020304040c0382580c0110741c0c00003c50790b201c620030491442c1d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 112172859 1250 112171609 112171639
    0x307200619030b01171501180506070213110313021003020a05121b0c01090c05040603020307060f0e0409110103140c0d050c130b041e03020f01050d0f05191d0c 70
    0x140e06170740040d0380e900c00d00d048100040380c000b9402400300c050090301c403c42248410030384205407480b030b40281c81d00207000740000401400d0007204104010825400441e1038080050f6100d0b144e00101c1b450304410310300030240015410041c540c40903032030440c0350070752074200a448060120320030001c81444e50100b0310b0004580d1003009020041d90380e00703008110307a80c03803301c1840784c068006110709070f480350900b66001500b403602d40714103000c070f81d400780103010705c2460083c01381c40c02c014040210051040c41042d96503a581c1c1c074819401e4151145002c000858940030004080741c0d82000384002c55810001445400c000c07110544203000450000840c1b1790b40c81c80c1e0b5040d2903000354400f091000c00b5651001c1800900781c009041035403000c003030b8814410714040030030092001610019401c031006590007a503e51088005050b080012007001c5104990306030024100c070401c44415401d00d1109502c503a03000044d015680e0001110409040503d02140c0415143c040030420540310f000340d0341107804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 112174109 1250 112172859 112172867
    0x40c12050a020406090b010306080a0209010303080a020c0109080403060c0206040c15090e0703020702012a151d010e01060504150905060112060e1608040c0501080a0b030307200619030b01 82
    0x90701c954003a00a020580d900c08498018040740780e000c5000c681454004156094001420b45103150018110b5502e80d1030340e04e090345c800d00094503041540390204014070340c0e0701007401000403076442425156039403459410814100c8400803402d804541040042c4404600090200d0302500d0502c41210307401d0001c51030503900c0c5070896010a9104240004005841750994040c00045000b0b0301c034040c10006140d160841030b42070060304034150201007045c0e0042098400c1d004002900310400003418560b0002030f01016080e0a1740c504a0380d118a0841c2d107050007805400003e11050f14207009800001101001c000c00c14000ea002c007940d0341e40085c40507031041011250b181d406000400c101d0313890319070031111a08121000c0c80340d403049180d101050351040c03510324892500b142c181c510080c01c0000440701e03080003a11582c030b040d84900c11950580d80910041c0111031062400c000410284461700c480700d80710320b03080382c800c030707c1408003881c02503c602444940d20a54580020400c8001d401030b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 112175359 1250 112174109 112174123
    0x60f0207030213060e0a021b06010b0a08060409151a03010207110f150c031806311706010f0602010c02060c1e1902010b0a06020a0212030d020a0507030e09040c1205 72
    0x115656088000740214180140d00900021400c0b21500280f4042828230968a090a2144088024040040380d908600c601001038000c00300030b0001c81c00320029103031100242071815440b000c00765110228030000303142400010910710700b41c00a608040c1161180030340d2404040c480c03401405074000f0a146603403901c090000300821000aa41c40781d003003050584d40c2e03800401c00c101210081c8000608203103864402d4030506481160030002c03260f00c9080b0300706034181c2240b04031216000c0c40303004118480010008554040d41e00010181585001040038800308260722075010342e4500039010002c1a03010580302c0d0f001c00d010f007009941d8241d14480780928560f0340c07001e0b581104085811081d603441c2c010740c0e42c003804035a8020310200803200204a069440c034462000944d100c10132850040c100f60812140201280e0166824501145551000c0c0d910400941000a10000301c001c10141c1081c0f81e44103010b420355030262245440d075a03c0c0c84200246c040d5222044080b050403042180402541c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 112176609 1250 112175359 112175369
    0xf090914070b180603010e060607060608031815040b03160e0607060c1d0a1a07080403030f17040c0603020f07060e0d03180f02010e01020312090604060501060f020703021306 76
    0x701c00c03071a56030405207903c1e00100c1000c180e844248014445500d01102600e050b107901119146054813410100607495003c900304031400743e125000010103c0052024003a91418024106496010b100402c0101d5044c441c008030b9814041c4002d20080103050b060b2907002d250450703a40a86912001d0559150740515015035210400050380e00404c10030750062461a086a2214600d20480070b00e022516481c0403601e94201880740010043c020f0104002c18070718059185061070070301c40342c0301e05c2e0cd280e005400c250041800c80c80d40380b224aa0100c421b00131002e240c8100300303807420315a03651041c50740380e44105020150045180540701403103504486810b5403200041080d221120035403502c88603840d54200200c0e150012050042a01192484d401ca60000c654100c615003640191901c00c40607001a0452105200e8507501e4449298114050540c20000705801d141514000e0140c03203058000e03800301700a000320341c4034060300014410183c0381c0c1100c400d038003600300c030380c0c801e0080c8555400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 112177859 1250 112176609 112176613
    0x5060a080d0c06111e21090d08011208040302150c0a26070b0109090309120b04060c050c061503011e0222060906140d090305120f010f090914 62
    0x20044499801c040b5040510b403203654103011000c010b25030003090303000b0a904115114019000c0c3c1d594074903076800401e00400e0f0003c1d12040f00480a45800703000a08648090b85a84540301c1c2d0000c1c107402a0001e80104858800c6a1640c0348542c0c1e002480d0145210083c01441e00c040400c008090a40a440c201c52151b4200d41c11005281040203210611640b440c02c0d00681001a040092090b800c45200d00c1d0890a07203211a40703000d100f035008098004e0240c04200d03100d40d0109030300c01c40d6840d52107202d001d890000303c50306090605004485829108005210341001308030985600440c480303070300080304409000c1091040c0c01080c090000d4030032001d0543c1d1040c12504d81c65041707074041e20300c800c410961804002c0e07482c1112a0340100f10b004802c0031981c4070b5400c020051254480103041d420a2004c6030900d909024a0801c1c0c403c0e03110120b0100d5004105052108c004500c0c0d264850900711000c18a5490911007603410002030003103101007a01c41c8540818403a241012440b41455141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 112179109 1250 112177859 112177873
    0x6030f0501051806070504170109060c0f1701050907030504020d060e011d030f16061806060504051005090c070302030403120e090c1206040216061416020102030112030305060a08 78
    0x140440c0240300455000f4403000c0845801200740300300007111072040d1400d44032145450700303010f441c042c1800c901d03c0c140015901d81c220200068401e0142e010b0001e01c0d500c8001e083c2001d490040c068215403d8000003d00860700104050307920b101d5007680040321810002a15222800400c0344510a9200680400c0c102590403140050550001607003000c03000301a0440d03d146132040e0749a00c601d009144a4407814028445c04001440c2c81030038982c4510f0000403603c2c2d0003208000440e0900c401940e40c9992107400300300d2030405003c0d903a4800c0307a0400f9481c0450074a000601114405031040003100c00c00308ea0017040600810803640a5500310070f1100700d032160520020100100c0702599401140034a02241041180400f580c00c9022000c01454a81e6a410103100003034100d4401c101720380c1c5c161240356010610501c9154800404074148404614040c044910301282c18540242160f1042004103d0849809018070040382d05140c0070405895a0703001568a1000d90010101c60203004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 112180359 1250 112179109 112179113
    0x91006140a05040b06040e060118081605060703080c030c0c100209100206010e04020613030614070906020a11131b030b01020c010c030f0804080c010e1e010203040218070306030f 78
    0x482a684000c0c4112080e4001d592100180b00c1900d580c140c13000c3d00100d05000a016403c40da902c61039001038185440080000c04a291940000069100078083d4200c64192000c01910408040140400b0344041340341070800d82d40240700c0c1070000d000602c4503100ac03000c03560034400d0408950248013814200c4001c6038564040200075444440303480e126681071510752031050b0001c95064101c600106800c91181e4403030b02400000ea100800d80301d801210000701100258592103014002040000304403114940080701070001504e6400c8401954450750217080001e8106041c3c190031801902d61a81144040d030142c00035024500e4030074504200c1d0301e08002c0507a4035510150543d9400d0b42166071142594006407150a40d0a1014000a851141d0404a03030300402c06c590704144180103181c07030007030140302c42401c507200c030721039000180c00a0202280020031030344c540c2121207690380210300d9410683d00180c081d0146810b08402416440c0004003142e00a511050003590000320760001d00d1268 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 112181609 1250 112180359 112180379
    0x804300809160e22050d050a020c0603010303020d200d0c140303040b0406060902040b0403030c0c09060807030c0b0426030705010603080c060709060f0507060b0d0302010203070f020f03070308091006 87
    0x4c9460b064104e01c1440110440034074010035240e41034022000d0120388100d40c2d07044403958059078400d020341c4103515500c1d9891301c403040114021400782d40684080085244000c007009003a04600e6074041d050400c5848c0504041222014943c00342400031161505140c482d450500c50f010050603070001004020a00540080c4984a54494070341000000c0d200c8504100b00e0049014612803c48140001e00000c2d000b0404801501e010355000713000350303a81c0d000c508140d42413034201d0070301d5801c240d00810801c844000081d0140c00b101640500b814206035005000d8111404852031030903581c09050402a424001c840706103800000a001a68680c1003a108aa002c42c40c3c0302403c1c03080e5400254058800d00c1c400341512360580c0c400d0f0b0040054001140c4036000f42c80161512541d50300d20312929651000507000c83e034400d8001680303916103458058420042000f210f800e40d0884042959410408000ca03000030368103060200300d54032134070030300340c0f504a403203c0c1c0994443c50890003084032210303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 112182859 1250 112181609 112181611
    0x910180605030f01060c03080c09010e030f0c100201181b08030c06100909020a05130e06041401060501020604050c10210f0501080c0901090b0d120804300809160e 71
    0x8030850f840b0040c1da03141000c40300f01c212500c1c041c00050304034011800684c5030100030654010145031a1140c60f22640000e801e20410b003680b20480d43c07240c800d9610031304080081c550040c2c4240001c02c2003884c041c503030b40003ca5201c0802400c40c05420800e081215002c1c403150013801c4410704807a10364415003031007030307545205a44415040c200500e0000b007507440c6000310801c0f1035016116808a928040c02d20000e243c0d150044c0c10407035118002500c0341d0004001c028400c0d07002e02d00001c88041c00400d01c600312895604060304541000c000c10000c0b9500040507001400256001c1208444420088030102006030340b405220110404103500d51a8a4000004009071180b003000ba0380d0782c174014569540c0c4542c3c0300c240c20525060041110f6621503001d9980300070b0140402c94007150a80d00d00c0e1403076449110320f0001c14806030511051004078540f0746907a101f5180b0113a20401c00341c0442c18060300c1d03281083d040140749800121801018414902e55070015241000c4103500d43d011450701d514 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 112184109 1250 112182859 112182871
    0x30b040f08070c061806120525020309120c03030f070804090c02030c0114011206150b031008071d04080c16260601060903080a03110301030f030e0f0105091018060503 73
    0x841c0c0b00e03480c20016800045e1000b1100c55842c0c2c800f415601840480280400502c40c050071403821080c20044c03140b4428850a1842c2c0b070f4003461350744900000708191461421400101540300141000b100c1e00c0000441e00d40100c10620307580c44102c00e15001d42e07a48201d40120781c440d800c00101c210100c2e0008041e201ea404410024400a403800e41e0f0240d94030402d04c59010400d642813035203008192558080b201c0751038840c2c040021507480e0400315585500580341001c903da400030341040f640d9024800040640400496107140140740151988000005840034101820009101309800e904000141001018044251620350b0710070003d051030880300301d003c0c04044039075245c0c408402c0200d0140c0c10b9802d47d45a000c900350940d1110326250704070212220501d40d032020002860403400d0f01940c000e610a501c110341140c3d940c0740060000c20030f191000d02030b084007003600c40340d85e801400380d401c3c40380241d400c01d204200c43c910440c1c402c144100c0d047da0000e403c84d40407030469030060003188200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 112185359 1250 112184109 112184117
    0x30040f1e110907030b010e100c050304060e01090e01050102030703030b130e01050702010b0a2114010e010f180201090302060a0302070609110307050607080a08061f02010f0b010507050601030b040f08070c06 90
    0x20f5103040781a401ea604032011a800600c00c08410100d43c500083d140300303000d00c1403170007125030455552550300d541c1c003940290000c40c4400010411540c1d0007021040a44030b40070000440c0d52510001070340e40d02400780c00038281601d070000d40600e80c80310031740f8114800060390306003e8401d0301c0c0800c500910040d00c001006500b00900d500603400e00740035942c00c5803d03038040400c074230212007041c03201c1400007441114002024248591482001d0090f491102d401c13000018102000340450350464101200b030700c100101260742000540e800c445004e00701c82c0c0503640255079000080084000788525a0300803e480c1c980700b070380c070140114050003102c440000d6003129603950b151000c01c2040c1c0600c01d00103081400c00c01646100500c43d481143d0800c4029089a03400b230500b108a00e82d80c00d0007130b0240c005070742d502031200c581d000b00c2c003885000034002e0a04c4c6142c11140c1d2070303582e11420305020191071600d112002c1810040050800d046282d00040042e071511280d01e05000108e40c2481010006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 112186609 1250 112185359 112185361
    0x110d03050a0f02040509010504090f0f050328020d0e040e01020f04050f01090b1803070b12090d030204060906080c07080f03010303080a14010e07140c010230040f1e1109 74
    0x6021500c04c03a01941c070001c0004000d40c0c600070811000d4600b50004986080842c421180081c00c40002000d0302d5200c1c0019548500000d0701070031482c600145c150209006a8012030007064001c0751030240b02c801480c00e0890401c180c0c01290107414880340000e110340c800500e1000440e44603029105440081f680d021142c650304004544040c842e0086100244c4208080b12014142c0400340611384c0010f000d6507201d90350f0301c0c1400c5c001d4110102032425840c0003400c108036070606204d00f0261100380d00341141450f04020b8028103848150081500f4480f41401144e01041c46005aa01c10341e44050490f030b40e141034a43d1190250400e100840205007682d022480040c1302d4050110880035030402c0e00d02e103038a003070400c040790f010180030a000e00120750400e00030a842c04005000740c4030100000f40e0381da14010540c2055052842c01d44041d0121568407840e03040034080f40d5908581c10007840c0c8a5980c40b0b0400641013017010344584442c0003040c40100400240200026070180216240304031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 112187859 1250 112186609 112186631
    0x106050903120702060f070507030215070b1b09060c1207030906090602060c03040b0a18030810060516030e060f0c0c100c0b0f13020603041407080a0305041401110d03050a 75
    0x78018020005e6004d102441560f000260030300240254901030302c01c541c0c0c0385589070042240c11000b06c2d408034011900042d81800d00501b201c03096082031548000e0017103a820484200424000c43c54190f102c3d5500042d890011a400c00c141e440440c07035641c2d51a030314903603454007501c45c0c0302ca403203260007260706018001100c50000c50300ea84a002040181131071691107a65001305000000c0050001b00c3d91104102d049900440001303221a100c0d072101c0740c940c24041c81d9082d83c41c895074070100030864100024488064609100302c40079500d8200891803203603280001700507000c0c252007001d03011004129a00d90400004e51083c10360310035510040d405d9508001100c1c100d10606018207480e41e0b43c400b04a0117480f10001c079a02119541c000b00c1d03d003001e5800542540d106640545044510905c0c3c100c9442c4240b02d000d005000d408028483c120313050750091b201d4000c81c480c1d01c4000e205210117900c140d005401e03401103024040107903840c44452a402a00a1201ba194042401e10780360400d14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 112189109 1250 112187859 112187893
    0x300203030c0d020a050408060a050a06120503250b0a0f060504020315090405100608060103020a0608090615060910050a08060319020d0224300609040302150106050903 73
    0x405903020030981c034500a0080003620195108000c0e0408211041200041c07407039083c00058050180c603640400c0d6070038031425540a4420303940202103542c1c04140403a0008800100710b9840c04440c90016880454906452040c4c80b40c1030000f8003a10911000c0081462443e0b01c1075012246108003081001c1d2100180b0040340800c448504840c220354048a00a15040d01e000307501502c80c4080301d4400d8a00d0401d442035070085d038085032465006c00f005008500d030070881000039040503d0318000328075100c0c11840d81c510014050044441000700e18020783e840b407000b1540b0211014140c50441c210325400145180c1c081500c0350001040080030a50510340420045d07003618500c061038011a10030380800030741000c072502c100d0703000c0314140f09501c1e5031900d030f00b100c410031500b2810152916460f680c10001c200342c83c5c0441c403520480c121180d940382d00115166400c10005c1c2c1c3c8075a81c9541c0c2c0d290580c980903420003170410000d40b545c000034000b0b41c403078001c2c40180815400d0302d1003a40f068102403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 112190359 1250 112189109 112189111
    0x4030201060e010e130c09020a020a0302010f051e070e04020a05091207050102100b0d15090210050306030d050705101b11120d0c051908011d1303080604020730020303 73
    0x42c130f00c5401404584100544c011020040d8000d00101c040559549107900882c0d000d046000003603003003d081c13030f401e1640a100d82c4003c40310b90340040c03095151005442c1500421420b081c2011486080403503034030342c4900ca02c0c14880f18044c108560303845d8010303030141440c1c01c509450742c032558446a41c0c0141e0503000c03c854040340d0040c2c004050400c07240c40d125018241c9803243c1034215040442c5e08011680182510502600f241c40c001200d130128010f100c0707484800070009060060400078442c00392000a1504540c80b458903205444e8852403038050306090078524507140440c10f020300c4d403201c4050040b4205070305400751150300100c000ca043c40c9490350085404c281450006011074145105030b600400078000041c64807514144c098981c1080780d80b40c0920403000180744000600421000d20b1000f01e0040d403000c000c02c510320f070254610000010032744005080014410229200392516015204940e92000030040300c4080c40400c0030200ca02c43d04d110255421400034030350301034004000c507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 112191609 1250 112190359 112190369
    0x22106031902010302030601020c0d0f03020c0603100e13150608010501050f010903060c0203070f0b06130b060304020d060b03030703030218090106090303111005190606030e0316020301140f04030201060e01 90
    0x10308195003030350b00150002c2d08010442410b6010304d008054070f40c4d8425004200c26489000b1403a240103650400a1414907107468040c020322042043c000342c00514501003048460008070041c0682c1c0d81105400040b03800040141070500740c100c070a900c02c0c10740e041407042e40e04090080040b41e990304200070441500541e024049201c00c01c1c10700200d18690400300d00c83d5950300407646025070656aa005032208940165440700c90031042c0a010700d00851014400e502401c400d01c000da00e600002036140c400640002c6c896040515540d081124a8005d8074004200400307481c0c44050f20b003000780295102c08001c0c00b450200710a04030051034403a810350306a600d6070f03841d0350290b4111381e003d41c2c4651020b0904c1c103440c444c200315626446418040d9500c03400d0307241d261407207440c580b16050040e03804c2c0750850010702d414015046007680b400000d0310300f0321155102000c4007624038000b1034014030f46c051030304080c10890020403149000d58500789004030710031742c020417115540354031302e074901c000070b000b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 112192859 1250 112191609 112191643
    0x30405012f0f03040606080d020d030e0d0801090b19090b031203130201110f0601030606050f03390301020403050123100b03070201021207080117010605090a0c05070602210603 77
    0xd580007000340c200156921505c0364000207602e6403101c2815142500b01c084400041e03101d5000400d805501d40120080810604010014449000300181079800b050048014242d80ca418001d510344c1c4001e041d01002203041021550561112002d0025207401c800b428003038030620158666075584d0f8011a4807504003d800f1602440c940d07401115032029148950303c49210302e0f020151f4081041c007489008611402000a8062a00007402400f00502600351311030380110510041950051708030040074a07001e01c1c10040f42c805440c000c0001803030b11590316015071000c00c0100030803405501c45000d14581d80f14107034100b504400301d00e1181e60200c0303556080e0800c040e0200071460131100515003003440c5000141c200021903041040304c2c241121100009944071004022050100f81c0b101c921041e00c100074000903041202103a200300e009028681d90a0f660b54100055510403400d495155074018002e40d903400c40e41c02004086001c0c02c0162400403a00c4001c40c0341c500d00080c14100301088a60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 112194109 1250 112192859 112192867
    0x1060609050a0512070b0f030a110310030204110705030d0c09050d03050406180503030c0d0e030f0615120f0d0f0c0b060d0204020408010c02030c07080607050301090c03020f030405012f 81
    0x2091149901120301307000c0b8184500600030a03140d0b029000703010099081c00c0001c0e100d1500e0644174007611220418840c20010410034001c0254001c059a01034a40644020403810403100c0500524422841d001c2e100b0300005c0b1303040c0d034500900c0d00294080d89440d42c400e001c0d55202c000b046034419140c20024045103040100f085202e000c2c880101c8100828003800c00d0b0355646130080390075684184161003035030b00700310001001d0a40040141099034010780040004d20304840d10075a61f40d00180038110900c0c00c50b5840b141e607a4658502c1031199a002c8140c8000303004414a09540308210244003000c51800401c42a0140c868412030010a81140380d15020b0745a40060003146a080300f030a0760425000c000c04030303e0543c01d014854040109034021507450705500f62080c20607074250040c080d160410003d002c0300381e0b800310a0b02c1c159180c1030300002d806041c01e80103400a1040f160310030f5544c2804401c000c00e1200640c045116003250380842094040311078080c00c001d191520a0b03c0031000188 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 112195359 1250 112194109 112194119
    0x60c0703080703090206040303020109120503010b2502030703120e0312030105010c02040902060f0d060f05150d090c0f080f010e06010603020c0a15020301240806060705010912090801060609050a 85
    0x4681c20303000002d40c01c00150044d290340204e001684242c1056001d42c0d1150000001c000e10000050050b09461070914155414140d0285240c03044000480c04001880d02402d55a010020702071f0f402c55004046800060f924178000c000c0402104104010400c0c2311440b01d01c900b0082044103092000056940c6580e00700801982d8150854005030b80040c1d41d4520700c401a00c0b05002814440a0108907544400e800300c40101501d141c2d4000580c140200c0c00d04000da61140c421228004e078000c1003441d00d50000f040c3d500e008102d95040500560400c2c00002402005160054151240f81064941d03250f10300b9005400d1301e0007000c1c00400703944024010030125200746d000e030400d42c80045c19103400920b144c86d21003805000e000c01c03803a2103500000400c2403a141c0c4043d030b880c0003070403a11342c03102411041010b4021076005008600880d400191281044020351207400c071290b200c0128118030003d100300a040360680d0003030514640c070b400c00c0418203e0040c017298048590040c2464a114109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 112196609 1250 112195359 112195367
    0x302120f04030c1203061a070206030a0207150504030504050103050a0506030615060c0f0c0109080a080301050d140d1e030b06040306091a0106050a0305010e040209040212100f020403060e060c0703 86
    0xc0040c1d08000c40c0719008400904c05150311003102a141e030b000b2600f80e09150002d000e07603039a440e440440300130803c0451300584031725023540c2c1c2c401d000345801600d0f42c040d030a00c20003100c0c3c912140040c807031511007008201500003000c3c2065403401c1c1c0c2c0c10440e41d82c804c100e02d02140c0c800c0c2d545942c56480840081c03100801c44034800005000600800c0c14010820300c40342c0342c02106881182300c1d802ca01140f82c16540c1c0b1820002c02030141000a040640c110b884042542c44180540c600070b08a00c013103041485100108001030b901204100d510124000400424421007902c903843c0940c5406c40403424248640191012a4802082c881c50545190b40d0321005005140d0200c42040c61021203491f921400c1202d50b008100c00d480b50b66442c600900000d040345e20582107009200880014000542c84841e041648141d0644600100c0744610707000703914080840c00d10399072407804d00022305500240c940140048902c40c020074480160102d201645546080340c038407080c1c0d103050040b0008603104d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 112197859 1250 112196609 112196611
    0xb060f011404030c0e0f0c03070f0903020a0b030403030506040506030309042408030406030e0312070c0f0206030c0c1006030f1203060506030420040c050d0b0a090e06160302120f 78
    0x5040841d030031400503415030300c20b07001944291340c0011946410449181a03c01c0554848440002090107142100e0808154017000e0400400c105060000301c42c4540581c0c0c00c02d015640040c62181456900c449480c4035070701c100c1e01240040c0c00e2002003a4241424083c05004510041c007540c140050b00003800010000182000780840d00303d45042040060100000094800500655076440c00c0c490702505444090b81c000030030364401c00180040d414a0340a46420a02c10b107003440304010b10b0f05114424034204a40650700103c00400d12001010400c02041c6a54540c0e00b51008010702280100441d000b0340f00c003178016410000b0550016210304c0c0c40d10f0f0364200324100040c1d500d41b40c81c0032400a40045a0449049814000d42c0c05e082d02141c150003150b1030b0464092181e6013210b40c005200c0d01604407541500c47e02c0e041c140e810341c0d607507112803006411494410042c01c0d40303244a0350b5842d1415621030401003410729120035094844d00071a5500000034076461460340302c004401c0380a9030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 112199109 1250 112197859 112197889
    0x30b04020904020d20070215090102030d0606020d090b030112030e06041a070614060114030915040804050406060504270e06070e030d0f140901091a0c0d030204030b06 73
    0x15003004482155691031000d0259a84080800641700c0994130030000c0001003403a81c0c40c00154140400d038016640c12041d0708100344c8241c01c45407a03c0d080d40043c0d2940c040c480100e1a002d05100d400f02e501d07a4006490340c02e6485650710504481d5580d038120741144803c0c09905c00100e05174042e100849e0040c40c210428880203000c441c903055440740b400841030401882851382e03000005958007841154014250341381c2c03000f81141c1c1f040c01d140b400039003140c0d540404a40d00302004000940c020505001c4c080c400d4450f0b01b07480d00580303441c1c9085d40700d540c000e00445100d98544840825070b64070503415a415185107482c080640c98500114001c0285140d00035404142c581d410400d000704c0c140320301c50242c1459180c503149500e003007080605102d10740ca02e80040101a054252902d5880402c13541e00310302924000c1d0750b03403144a0049442010741d0708181130346500c244e400100c03221914024554205900d044e10120405410110140e02c00c9200250850080300c000c68100c0c03030f005019000300c00d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 112200359 1250 112199109 112199111
    0x15040320101107080412060f020a1b050f0a030c060c03050f0c07050a150f0b031c0e191205060105010c0f03030c12060f0e09122d04170c030715030b04 66
    0x102544c40014a0344103400c000c03008030208406108012840c003a242a48520031001d60400341d00410003420202150050600c40025010030020710405000e01c10350b014030002921400186420007030075114a440c0c0480341c691400d15036030030a920a1151034010040f08000001030744809c0e00c5c0b00a66001210103556500a00160000044000c50154100d00c0f030000003240400c10040b2000842d003024101398007a400c000d92890311100c41144416000d0020f082840f44489202c5c080b4242c004003243c18600c05a03441d1010441c0c0100700003001d140d9225100304c603170030303a04d480044501000c1010018200c042004100c00041c1c0a500007010f5808a480d01180501c0c50303503583e00aa0340303d680030b003590482c904c80030302c011900b00020b60740c010403050007061070400320010315069218030740d100c4101c908004152040b00a40c1030142607020301c2e0382e076142c2e150f5840b402100e06810001500407000e104141d039519480c2404100f240884260041c054184c1c0030303c08083c1c001d005801e10040d449 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 112201609 1250 112200359 112200367
    0x150f0a06021507020f03120411100801050402071e0506061c050703030c060b0406090e25090902011106090606040e0c0307061206081b19031e0201050c150403201011 72
    0x105c45c2000605400c150101e003200c0141054140790600001031000c690140582643c10050b0540108400341194019039005a40e6002c60803d40d04401007540183c1030f460824a4203824450002503240c042c503412616070503202d00a0300c10005c1303070310b910100800c5a002a942000464060307400d041c0310078080c0c600403864040110011f000c0742c540303030401d030f0b042a0f4035400d02d0300071002040150ad806001d203910402e20b48403d5940e406c0a0f88074400c0044540c6c46151b01c60441e445801c407070703801000c240110750180c1045003d0750740f60801140d034a07008600c0c0502c889802c10001440401310b94002d4080e0245038141801103d5070181c40310442c3d49a03486640020352042c080000e03914084030080808459003103102040800040d100303041c881c28217000f9042c170100d400612400f045000d040c40c110240c0705e030351005a4841c0103d2121518034040c1460400d05240500503140c420b5100b65244020002d210728041c0c0d038900c05072004001d5030f1001c00300c1c2542024030b501c03200c440000c4034482410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 112202859 1250 112201609 112201633
    0x30203040c05041b0f11120a031103010603090203010f051e0702071806030506060a0803041203021516030b040225080d060f0603050901060e070521150f0a0602150702 73
    0x41c2da40c0c040000700c400b0f81c108080c4404c0342c5d1011320825811071a1524411000d00012526a100150070540790200c03000501d11200502990048200500d44d000b455165030f5581b0703016005080c83c03480bd0780a035081069011450280c2d1141e1441004218040c0d0303040c1c6a0443c490090041c020040410f5208503c0c02145540003070541c0001c01e40581400310303113142541341c00c0d030411030080d1400380140090340003400041c4000c41920252000814104110510790030100c0c03031700010702e800b10411424141400512000c1520701880030362183c4040c0800314000382480102d1040070000754a0394010104030b0715141c00340000e00c0ca5140960701e170380e003003080e07040113041151010340c01100c0041c80c0c1142040340c1c0f81c0602a456100f0402e0000f00a542d2070042000300c80540140894100603000038004101c40d011010740c9580b00140c280480c2a15000314001c40980e0364411891203030f085998141031514140484030181d52455020300030504c440386440f02e40500c003400d5481940101240000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 112204109 1250 112202859 112202861
    0x180c040204080a060b030705150a0e0913060513110d0201021c0201090209090c060d0203070c0c0f08150c160503071202070f060221031302090a0903110a1101030203040c0504 76
    0x1020b00b5066002d0440a082481d00c4e5080b182c0100c0050b0181d00114805c2041e40c0c0e41082d400002d2801d40301e42039179281250750480301d4211551140da404542001802128004a40595006881038404108c0394944405000c3d8105902c20000c01041c0803460300c0303009041c00711380d1b508481c0c810300450b03a44945c500b003901040700d01142c0c80d1340181c2d500d210407405d501d440d1310300b10781226118001d40302d40122440070800510030907000b9a040c4c6d07000408104c0d076134800c1000d00c2040b60084502c1000948802d405130705880e444c41002e030700344506c3c59010500e000313206125004001012190380340c00300385a074006000070b003c003003900c10740410700c001030115030416451616500290301401e481c0d410180c58a0326518541c02500c1194020801c81500c0442c0c000b5107882c554540b5800d603200da64200410b4006400070343c2c020740010603041805503941c042c2d0040369019101362180607101108a001982d01c40107002d0140c14484106245041c7d94001e900850300300d8012500540b205480e1400f0170 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 112205359 1250 112204109 112204117
    0x1080a0e2d011d0607080c030c091203070516150903020f01020c06040f0501030c0302070210180924090b090109020304060b040207030c05120a02070e0a020403050d021c030204030803180c0402 84
    0x150f1814000c500d00504200c0500000b58480c0c2c036814268101c1c24122968035007400000e21103684600b00150f084215540d0101180d8540f80f41c2c0c0c1140d07918030b02450301c80d803031784618901c018120400000104040c184415036920390001683c40e042c003a851502000038080740c1110890550003140c541130381d1034884e44000e00180c18070444468585160400050031650400110000c05205000c481c2c0103903641c14903004c2461081c03520020260440f5025080c000d4a58068000246482102da915800141c00001101461503031078039919900e00d2036409540496440c281c0c0046004014030805800364051904680140d000117003404400d0041012a4007080040d030104a14022345410450304001049001c0492541c5a0501004040103907031003080e4060003400e4070060001900d009881c3e0305440046130040d08070381c0000411003020352030b42c0740300710003410384072544000d40b40c80c41c080d000b03d800f00c0368404400c1d8a0b650300d41d010080406074410001050780585c0d00510341540d2540081c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 112206609 1250 112205359 112205381
    0x180c0903160f05030303060d060902150a020a0203070b03040b04080a0315030b0619030809040f0e03070303150603020301081005070c06060b04050111010603020603040f08041505070201080a0e2d01 86
    0x5019182d09041d201e640252040d440103110780e00c104104442c0d0349076400800302d01da17030100010600e50300a20010305040386444d0051304180340441c007504d204d540020035001c91030095042d81c0b215916041400322130b110481d0090011082c0a020a0014040000900351866503103000244039240c0340a101c0c42040903441a5803040c41441405a0ad2030800d800160144000c0000c1c030503a403540d070301c1c1d14543c0500807100380300303640d41c0d030418018450681042450040c01001d480d582c1049181c003400604c014105400e00385002c010101d2594060b1007164161101000100a0007042c0001a8042c00f070080240303080004841080c1c0000b500c44c001c80340903002d481e01e56516a400e040c0014074441522801c0d402583c1004000c00c0903844180c1142e801c9a000381400241080504256015208a078018600c2140151494242c194000c01501800703100340e840282e02e440322a001c600b99071582c9a000042d40100381c030320032601d01068500040180e00c404030900c008000500508460140780c0b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 112207859 1250 112206609 112206643
    0x30c0606010f14071505010b18060d060f0e010e07020607050d1505120d02060604020a05041a040b030c0301030203010f050105033d09022403040303051003120315050f180c0903 77
    0xe08500d40420b8024640901280c12100b8108111270030002d0116850640e03060203950700040300480d120340b07501311002820101910000d150355030b0460b5503004009200f0821000300520202c1c10b403920104003107008501681d03c490602645140f03080040c0301000124100345004c060002c1c0d0382c4c0301c90403081244003010003e403d48410a01000e418500000d0034640305500c100110710840c0d030030100307860541e00e90340c060310380c40d03070b0314000c41400c5110302e070415440e214000c010814220f04400007541604d20030b500070305c9050030300b191132000d8450038040d0540c0741e00190f1a25840490803a0398042d01c1c2d168218109040d0403034050003502941c0034401d002503584403400726081d41446030901c0c0141c0c0c500136a18243c0d00340b0420890007808042e00c000c040584510111b07060281200721100a941c0240034902100500e40001e0b006021400100c4080d03605000f00180710325240d0701e00f03409084058400c0420140d038883d0642e08480c0108070030010282800349541039201046007540d44e11907006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 112209109 1250 112207859 112207883
    0x90905010c030606050a0f0509030703050304170c04090c170c090117060f0f010b07080f0f12130201020705010e030a171308011e090204020d05190e030c0606010f1407 73
    0x1c40141918810340084d01400000c2004c101e040758000b140c01880080761901c191118800705c006414800b076580b0103085da00c00801c0204921403000da4505030110078004407801c401c8802d05000982e8040c8002411041900a0400041040340d013101c81903a00b101c103490922085c0760004070100c44c03e81107400901c108080c5800641c100304425500081510074a024600e400151110444014003440c60118000b10354582040007420559503e520110b04c0d250320380982c400202ca181c0c04c2400741000074003624010560200461011002d080e4042e40900200c5080100544003003051601c2150180710b03410f901e9012900081c01d8507800d002c2294a03036130703078010004000c1c4890f11582204c07685034504100e44840401024070403038035101d08580030070403140e07600001c0c1c024040c1c10080c1201908000c1040344805680d04c207040c5d03114590504018050300c1404569490140c014441004d610180c0803a413158060700e40d034bd64107441850001e2225200e5224042c042d04040f8040b03480104901d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 112210359 1250 112209109 112209131
    0xc03150702190c090b010305040f0f020d0b011d06040c020a02060a050c030d020a020f070609140d1a190b06180a081f050609040506070f050903010c05040504050615030a110409090501 80
    0xb0040c00031507039003443c06002d2828275850b950445c860702840200591100a501d90842d201c801c14032160540040381c01859680d00c030700b00d501007200000c580108807100380025401e03150034858043c038000070743c0c020310200c000c0d6030a001550780310898000a01030103000360000e12404000800c2080c400003005a00c4031402000a894812a150440032942000000f0b100340c652101242d000c0b02c1004055101406098000c20b000514014000d0f082c007410040304143c09002040443c001c00003501c1440d945000611000f08403854039a40701c2e806881003046da070706034080040c40710150780e0043c6481022542c8650007850407400710800300410320303880500313003142080e4840c841d408041556002c50380c0c9002d55403191908402465002800500c004640ca450320034815108101405070003000784080c920805801c540140c403510b80301d01c0c109000540c0c182010078903181002001403102c1c2c02c45d01c859a070319000c3c0c44181ea000340b481c01d09100019403001780d8054446400e000d800000343c1d080c0c1c52 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 112211609 1250 112210359 112210361
    0x6030e010f0608100f09020901120b0c040b0a0e18041b0b030610120608390d12020109020d03031a0d08030a0905010b0904080415020c03150702190c09 66
    0xc800d60003907803071401c641002408030100700564006050b0100140e0f0021000c8104010208040081c2d000101e550002c00d642e001200c0400505008011003101c1c1ea031f0700d40c01401c45100b540a02c1091010a01170710000c079018101808910341c00074101824890040c0c08201542c90440d42a20000241d0b0640e042104040150802510300491950300e503180030030100308501d80241d00a01001080c045208055080b940030401a00c0018190390088224030f603401f080d0814440c1c40c035009108140e80c0d203210b9041038072600d402200903000c074403142d083d5103a80180da0b25036800c00c000e65403a28600d4005a45400301402c00d94402c0c0c9002a1034846010001502102d440c80c0034010241c40ea643c001140340c0c401607942c42030030640c000c11042c4032807500a0140510084140c0c204200e041448100300042d4090400d039800654181d21002688508a84d208461540203400d5007180010032052010842d4140c0d00160b14011154503000f000c00074084034140100030744000c20140700a02080d506 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 112212859 1250 112211609 112211621
    0x31709010f020109030e0f1f030219020313030305090a0306020307020616020d0207092004080c030d0801061e030e240705040609260d050c060c070f060b010e0301020406030e01 77
    0x602c001c01030641c150b030340034000b013030030039650742c842c3d03040403008049981d446104404003070300000c1c0c40e44022303015400500650411714200c0c0d044144260704a801d40d2000050b100c0c0c81c02a43d403880507151564800780c03010f520112040341c1010781c1c4400070000c00c001d80029070080304e05a004014528050104407419514405203004640008000949555000a01d00d082e0340705900c0010315170107113500c2d020f074400003c03045900910b00404c0005426101003500c0700e07080e6040c0d0a4074030300f0040c1c0000301d503540000d000e607401003281040c0c009907000b030b0345290012060103801d0028180b4616158189001d0440500d0101482030a01681c00c0d4003d14106580092190500e241050f05148018000fa4102d010700300030036200d4261250100050080c1c0801c460b218416611000701da0f41e0000d140340d0100c082210b4501c00d00d00413030480d0220a044800194000341490b40310001c0d580d907800500180d0f4122410001c8402103002c1a0350284010f000408160710006400d100c1a6500340c29901 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 112214109 1250 112212859 112212887
    0x1080a050c011412180d080615070302100b06071a0603010f050c070f020a050406060507170324040b030f0102040303080105150a08101e060314040309140a03170901 72
    0x10f424035405034101c40103001d6848203403544000c1a101d43d2a0070b0301100304180c910040040f813040e044000c030300940200ca1280505815a03c0700380e145407814513114144134030840100103a1103540d0819100505a0017144220002000c40e40740c501c440d101e120520803400d00c0c16140d903440780140303c007901e030900c1911000010b0150500480c540080c44507098040d00c48090b064146d101e050704115510311000f070f4068500144104001a260b00008015030404041203855a0011022102240000d0141c81c443c3c2190b0041c4089541c00c01b03880340341421100c000b103400607115010840e0a54043c007912480044c124001070310f4614605000b030000f40306030710442c00703501d0f0781c001d41007001e04980441e500c401c0c031030802e030006845c5d4103802c290100d460f40c811000c003901401c002e20900358520301e03c1d04980d0181d906110302e144000742030f80ca2107401d80c0d0041c04102d40c450100300d4100c091540c0b0102ca0401010312112a59075120f00380c0c503001e80c1a068610307034000500100a5a000341c00948000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 112215359 1250 112214109 112214117
    0x30b0106031b0306031e06060b030a02091509060406050f070f210311030408030c1309150815041205091c03140a0203040e060a0504091b0902090d06111201080a050c01 73
    0x1502c2c46e1a03110740ca509a0300d00d0481e1884c004003580138001541c00c100b0007003401c205001e5881c540b598004000f500031170540c038414005000070a2100303a20009846000703600420113890302d03142580641e0755901010004041705414800480401c455a0002e88501d006145000303510202c1051254103a01c41c8868000b4149800b0003400d00c07050442c25280d01a600c01401c95494850a40f492068080c010030020314402c51070000c109541e481d00281840058032074a0245141c5a0413820740303890108032002940d41522000401045103446a0f96528116083c042e01d403003401c401003003005400740784404845035003410500030154041800101003440f452864105801000c00039104d00c20352045401020300100030504035905c81c1d00800042600030300400202c40c983c504116070001e5a240e45894a40c401000110b20b0a81d00071030b800300728010304c201d1000c4190f649a400500030081075140340c0000340002031503d5200c0088901a1800c54000c0552410b07610b407151030070003446a464100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 112216609 1250 112215359 112215371
    0x61a0405090d08040f03170903040510030c050307030b2404030b06060702061207031103040f0308010e0105030304060513050a0e0103150b0a0e070c0204061805010f03020603040b0a06030b0106031b03 87
    0xc3d440800e01d90000d0388210002c070346102c46d09003154a0400d10710007e550040c64014800001c4000005200712501940c49203094240780364160225510683d10030701182c01000044c50081c8260300181c99040010b00c010400503940c0114190322254241580c41000c00140c103005101d00601a0340d07100100311415417400d5841c0c0c0c0801c0007809070846804c4500fa460000c9405103000f038000c003009e817112052003030300c910b0141000303e0700140d20241a00455001000841c8100c86c1d0b8a00340d068070800703001549014030b000800c84607640408502404440035040100e51030355507400c4100205603070451400c455055080000301d200340c00003008a100e16148000d200d5440d4401d4510468071000e6108905580c2c2034001c0c1c40e01d00c045a0020740c058074042c0702003000e0300e0f00c003c0d9001c03d60181c04100034681e04d0f50428402d40307045000c080e40c0714009200080004401c10491603200c00300741400300e00e5a07680c1e0b907001900320003078220401198031044c156096601581626507140e800307150602c51 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 112217859 1250 112216609 112216633
    0x10213090b0303040302210a060f0b0f01030e07060c110a090b0102100207030e0607020102010b0d080d1a130507140c03070314070218090a0203030d0501030c080a0b07081003061a040509 81
    0x86c1f43c4c040e081082c0b220000c002d910303014500f17020784041a40c2241047c040b09904d06110001410710008080c45000c1101d1784540d254403038424000c0d058241c100801c0a9801c00c10151000c1d82030810880c0c007201f441c40d0341031460f02e40940c600d0080c207141201048e00340e4805e0019040040e02c0c10900c1501c0d02c144028808070390310a0050b0b03142c4005070b840030750315107031400100e002d4070b0b0307071701d00e454104e2810641c5c3c00c204000791008003050320340448204007000d061004070b94142484130b060765110100550008001c2c0c200e030700054100c061401e04004004001c00c07000312507000b40c1c42110017904007285080c14503801c1003d03040946407900b0700c0340c98081c40b40e0000b1504900f004048619085102c001050381401300902841142c000701160f44a20000700614050642400100c038004e0018100003142e400000340b03400456072102e940701c0c81e607891803006c030b500003401489040600d001480000102d0207500c504400c4940200c4010999254801848142e54001d4441c641c80e910500400301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 112219109 1250 112217859 112217869
    0xf1112061506090409080304030c0501050a02090102030f03072601151e0c0503041703031005010206241305040b0604060510050702040209041b0207170303040209060f040e010213090b0303040302 85
    0x748101210800d4550f09030801040041282c01030082101100000788014903410031307000c0d681d0a210701c00078802560b880480a050740102e00d8401d025078401d12213000c983e41110007541c0c4c0800c80780ba089001070030079131075841844002d00ca5005941070640040c024500003405202141d0303140e0400c525000051010b100f000862a202ca10400c106151401d08002050003241c00802c1c003c0e02541041d0300300c3e81640e4880d802030f00d4a081c22010120006080c1d40041101e520441c8250070900780c00d102100b5081d80c44401c2d41120ba070140b0090b118144200240c800c142c01760303008111119103480c009080c0001c41c1c00603002036101d2010780150351130f00e903840000c942032694151000751301c42c80c0c020b02043c05400316100c041018002890b220003110740c0014144202e6407011814000c1c2403074144401d4482c0310540b00a5082031034000011b61a040c551501d402c8140c005c2d00014070400c115928500320303009402c0b1010828080581001000c0060003075111504c1c040b8099850702c0d14680c0020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 112220359 1250 112219109 112219141
    0x10b04091a220206070c081006090f2304030509040903030603060b0139352701020a0b100501120501140f010c0f05030918090703020603060604030f111206 68
    0x280b06013000280d00b030801ca4021a04002410918222803081e0801d29002d8003810b014083c9101c410314005540301c10341540d0041d00c291064401040001c00e01e0843d00304100400100141c081c004c04101c1104192900c0c0704030b0b0704940c041c0e070307001480a0441c0380c0081034400840b503460400100e403030301500d2050303c651000060a00c10703091500b05510b4032212006840e034a03d0180c4803412945c911258100742950241305002da4621043e12103402801c000d0150140d00e0002c4044820244090514190700f91801d1503408140103d602418a5a890408041c4201c40f88180058403000400031560841c0040a03003850541c01402950704080401c200d240c11403100718030410000301401c81c00c2e4060200c8100990b007203d800c070300781c03911400c00d550ba983c0100800c50044060360041150306040c40c1c1c0340341c054440100a030444034515001c011781030300050f00c441c0e444241000000700080200b00d04618043c4141078150f00c00080c07104000d802485244005c02d280c01c0481006a04071180c00d943c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 112221609 1250 112220359 112220363
    0xf080406031d01021c05100b0310090617030f091305181c05030a1109030a1202061630140411031615020709050106030506030d1b0212010b04091a22 65
    0x1b4103a642d4000300c405d100302588540d8140c00008144205545222115820740d00031600030b2020a07925090640300c0303100340000c412603070410301440d1742048124000305200d100c02000c0f0050725031000c1100046900640c1c1c150401900e00040e9001400140b01c0088a040c0501800052810900c80900345100081c003003211326941f2a0401e5036041d1080c1695840c5001408407803034520b0f1450042404100d4031600c5000d0704c80d000000e150448a071031840c1c1109055034401c016643c0e800180c0d4880d00c40303c0c00b4150b41600b00014003c000750144a4419110700c49040e652803820301d801c06840c0c0303d00e0050a1030181e0043c061007400e032041250f0b040121205e02112402c01202240d04904040054000d1181340c0c0c01c2c000002191a8550000e07405a00102c0558a92400021007519059001c648099000d240345641102501d04100500310b003004940012039904201400501200c403903010071036000d107845018014043c0029400c1e64800300441325025484a2808000300c0210b0324880 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 112222859 1250 112221609 112221611
    0xf060a0506011409040f02120901050c0301030812060102010b03010c0507020f060c0c0d14061302030c0409050607200303130c0f05031009030309060e030406181208070f080406031d01021c 82
    0x261343d07a26581c0c00309101e056400021034403800d09850706180301c04240d4818903e5800c100108174140402005c60b0b0480754405078580c540f080e2808a00b5000400804840c1595038884115940ba1800c1c0a81520402c0319614036a80341810700c10031251003520a203460051509001411100c90700141004170300100326087c814240591a006c800480c0d152500381103030141c0002d02600086460369505203c3c402c806681020035883c041c0301c2160074032000030b00f00341d1144003c00e60321809521120b1a60a524210200048510011230314680c4280c49084102c2028104141400f00c07001441000e0008105241001881d00d0006959070510240c460700c0aa596405c4d40105402607120350000c41e0300101c1070200c0350103c07040e00d03100e0304940b080314041102280328444c814410003a850648440f5010b460007040c55451f4a045030300b00c0c80f011500c08841000344008180d080c1c2c0580010400d1384c1e0082544a10f15201000c4404543e8403123542c4da00603c000f20206021584012511100c0e8078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 112224109 1250 112222859 112222867
    0x3020405090a15140f250504230f06120718030212010b0108070906080c0f070b0c030916061706040f02041d0105010c0302070e0a06050604080f060a05060114 69
    0x55050800400039001807100868003071103c0458219040203150f001c10344a01c0c00181e9035516014071043c130440318107885e12000703102180030b500c403c0c90081a00c2064680030b42407940368590072a2607202403400c594501da80981c002280d00e0641c08031102004241d44040c1404842c0c0c800c01080203003d00618107002900c030a0001c00c0801904c4c200003141c00601000740700c8014401d41d8002c00e1880c15160014400c80001050203000c1d81c51501122000c4d5500303000e0750349841c103030038490304a0b001103e00310a08004503004611508d030030500030f120140310300d59242840300c81c0c0c80c80c102c0640500499040001c90401c071464000f0103003003420107841001c148941c0c3c4c1c0c40c00640104204a40d440f0700c10b1010802082e03c2c0c2c503019401c021042e200303105000c640d03290001941c10503000c002c01001a4020b0805100c0c0074404240c00da001890342c0300100f44d00b52280c00052160700940c010307002c1c81d80041a207020b00d400c104512500f14540040421060400c038000038030304402582910240340b4001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 112225359 1250 112224109 112224121
    0x6040515060d11280320120c090301050702061906150302160206040b04060305011a0f0c010902100c060c211e090c031b060c0201032301080706030608070f03020405 72
    0x600f1110354441001d1000036018090704102c00c0e40c42c084d002c2400003490000d607940f080c1c600e0000020080b6002d01d0302402c04540000300b1184400007022030070680018030000c44591401d001e113502a14060300a000c4a1514440d8482c00740c2c1c8070710710038000500703000c8108a0402c00d118100030741090f914016945040c1000c1c040030242c106c0e040250880c600041c0040c01407040400b400540c0c01507034042c0020799071140c200c540301442c002e4150755407008204003051140d842e0010500c44064000210703000000c1c0e0001113001c086040940042000d5601040030014140301d600200c00346e50038048900e86131345e0300c0b003055500c41074105940d00ea61004a04001d02d00c01e810007101c40b000187c248100d40175071900b08050741e228401100c100700381845003010343c001001040300740c4500c1c0d500c41c3c519508540044020340741c0003501082030175000d10a20441d44040c445140a44034440040102d54500f50008040311601e40c090102504465011b200428003590f400080f42e404680c0803c1c02e032684 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 112226609 1250 112225359 112225391
    0x3060d080c060403081605040e0a0914150601031b0c080a0c08040b0703141206040207061107060e07081b040e010204080d0f020d0903081219021206040515060d 70
    0xd50004100e510942c410030040551000c0c1040c85460a810481104000040242c2e4540500d00442141080071000508004c1c0b040d402048060300a00141e404401e12402160a2039849052034200080c8c800070132120b96014024120001c4158203074102040419000508256a40c90000c044071400240800040d101d80c0180c501c094020340c146076034954a03d20300350b1585c4900411404186482045112918210140c0340100c008106640040e510002044001e41c00b2000403a1819580e44c4e1038041428104054030301540305007400a45880074210b51850a00c0d240d00406140d40560201c50343c01c0d15030341105150174019038020440250003210507000e170082d44c010346070f244500b038000090641d0043c00e03a18250269001c0d1428030b202003c08448d050faa600024103540340400c842099800440a81d40e03202c48160f03469100021041600b030142d86c0001c3c3d0480300d0181d624140500c0d4a420b00c5140d07040444282e190b0020fa1007103010501074001e03482c0041b0307230b95036031061050030804c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 112227859 1250 112226609 112226617
    0x1410030507140d0504020a0b0301031a04030201090b0109140f0c07200d0803100806160e010905040c030b0f030a03020a02280e01170c1f020a060e0106081c0503060d08 73
    0x30b500160340c480c2c4414152034028031085805a11805000c5c4000031001c1ba11411039060700e0700100c1000c1c4503c0c40c00c1034807154041c0030b44114215941d42190401240c3e0349014503001e020320702c0000c03c0c0c2e048101da500741001005801c50210018503414004d0500d81d007000c0b104040c2d800001c10391030103110764442581240c03100a01d500801e444040c1000c100c0341360000c5101c5d9600d5001348000a40320031480743d403075034101c81000c1149004a815a80c042c0640c00e0300b051200c0501d4000c0f440d50b2100301181c1039030030000030301004c6510350310800d03400e00c0c041c1d50140085405070010a8500b6050320000c2d900e180c0c8004c0a4000d10303000000c00c04e40030660349400c6065014a05400342d96503641c40525840c2c1c000d114138811030192484c0521104408500ea0851300c00090203640c503448288602c40c0c100d40310b0a80704040d03104080c072000004102d80a0b0640d00c00f0941d00000e00c0c180380100182c01c04030310320b503000042c0d4071460ac0c0c20302481e004015241c010381d0550300c030004200140780030451071003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 112229109 1250 112227859 112227887
    0x405030102040b030403081503060606070f140706030c0c0209060906030a06110315010c0f030f11010608010b030c092206020c0f0109060c05090d060b06070c060504030201091410030507 81
    0x100015010070243c07029030046004a109030785c0c02550350f555500c8911100300010000754141c000340c000c1021032a1903c00350840f280102d214410000284c0e440708404080d801c220074a580066204001042d050b2040c1c0b509440c060400b0f05140d451a0700044416000402c124402c001880102d030ba1038408110390101c096000e03008000c1c5140500d15008284c0007150303c521507030000c040741011548254460041c490348140c40c000c0510040d50203880382c071888413019040154498256006440034080c1d00b004159a200025100c3c10072800e050074180020a6203028040302003d100001001c19203040b1600850355441c0e045901c1c80c640a000381c071424510260a00ca016105070031501c0641c030a14506100e80750030440312618034011b5802c0c1c010100390715400f0720500c0e112804681150804031442e080104028545802980d03202490641c9410080000c2c501150600441d6040f40400000c0c10207840c42900d11008480011202500340a40d0030426454802041c12540201101d000c044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 112230215 1106 112229109 112229111
    0x110a03060f050a0e040b18150103051006050d06090c0302060414030d0f0f081806070519020102072a0504110d1109010e1002030405030106062028020604050301 70
    0x245004182e20218058807030f0800840005120718400f1201c003441c1248d5a50640c2861450441310300d4080c0840340c6080010f0015540d80e61310300b40c1c51603020701c02191000c02440d1183c21001c2c41d40c8001d410580101d0b0210343d0410041010310005000da0485089100c00c0345d084905050b4035042c40d0101d06541c00c0789032214807480110381d00044205040e17029000e54135510b40b8121088a07080001040401c004800c1351341144410007880081c4025410032000d6203070019a40c41e59000034143d440501440b600070095004140300501c0d0060041103911034500d40e810040d440141c0c2200c03001d1800c5000d01140c200c84090b2289078406039a8080000e03000c2c02400080c1030301d80b40345001e42c8014400056261f80900414002e0012030744c8080b5401c4d000424400c0048050a00c81e8880d04460701602e8001000b0401c5007030502c0080b01c81440b14843d0001c10140d1066401480d095 = true := by decide +kernel

theorem cover : BRFrame.Cov 112050359 112230215 := by
  have h0 := BRFrame.cov_init 112050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 112050359 ≤ n) (h2 : n < 112230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
