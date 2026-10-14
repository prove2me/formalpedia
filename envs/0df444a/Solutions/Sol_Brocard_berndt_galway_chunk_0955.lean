-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0955
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:28:59.702766+00:00
-- url     : https://prove2.me/submissions/73b7f646-73c5-4fa0-a293-a6e50e4fb876

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 171582733 ≤ n < 171762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 171583983 1250 171582733 171582757
    0x10b0906131805030706050708010303140d0f0e0601031106251a1006020c040603230c0d05100f06060c080703020c0a12020103050703290a0308040e0907080105060105 73
    0x12104114441850344402d10540c400c80d21024406003c0c1000740c3e070382e04841821102c1e54034100201c5c88880c06440c11138101c0358540d2740d8004544055240b0030007608440c1203a5002c0d07440da812403140042c2e40c0140075500761040c0c0140320030b40c9103080081d80d00c504901d04a000d80c200f0840b903240c0705004410000c81d00b144140c2c1d154001720519202c440c805002a020305204090420302c03091200e240025401c0365020307821508605e40ea00304010403143d4a00c0010000c00c10341480d4001d0072031001c00c42600007807540135100c01100140204504041000e812103480e04000d5400405540034441d1540810340d003201000a1820400c011308200040c4001408001001c210941094070030401e02d02c10010191101d100c2903038690040112130300402d41240443e0070f01000a8071107102c1e1180400d0300d28045400078001c20341c0d51f0603503c9800740d50b04044d00603860400100104103088010b000404140780c45084a141c10865181040c41329000011140d0400050086917a07024055480c0c02c6050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 171585233 1250 171583983 171583999
    0x1e140604090b031219080109052401020709020a0314181915020d140a0507080606090315070c0218070206040b1f060806011209080f07030516080a11010b0906 69
    0x10b00000740707414040880e0072a114000035021818035402e00701c507504003100d51544d062507621120280296001150242c0030107440944c50715100c0000c135440c1c0c43d08101030050300c50310380d142e10101083e0791100f002403020940f16204089411254000c103544199800d106060207048404c0786a1600407243d0251600260512040103000601da5420f80000c01da080455541d00e100a48502400b180380040c4446200600060040d408901800c0d10403c07941d070381c1c0480c0355680320412800d9000100101d426201d52503010312325090b01c035241801106141c550140b00320403841027022900350700180402c1c0b65010803d202c0d0464002600f19007040d0f00000c038a6440c1d981a01e6008200c0071080b0580e44a00e01c49400a4030036003040750103000c1d0304280e82d0a0034002e40d0101007419103030590401000c41c01c0400a4908a844034000350048500c64640740f403804400881003070a554503500d041e0381d40700000508801c00d54101e0302c08030340002040024001c000c42c950009107501402050f481c01603403c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 171586483 1250 171585233 171585251
    0x702190f080901020f010603060f06050d0f12020309040e1b010c0b06100c0b072d050304020402030a020c070321090e04141c0309020306060f090403030b0a030c1e14060409 75
    0x2031000b45c5800b005840200442682c2c0d0800402a10b0740500c001100344ca4140d01082e1401c10000f66180e840d04a80300880040140c0d81305002c1001c8031503010708500051062214943d1a0702506128060b488002e0108140341d489622a042449440300d040c84a504142000290000c40d40360313202c3c1046414000d06200144180c1c5c0228881a0090007a2007140c10002d80360b0308282c0702111100c12140550704071040c02ca2000c0114448000c0901080d0305000060040c40c20f90000c41d400f0700c403802c0c00f5041030745111040d0302e04560758200b250f400c0503001511014540360200004941294035010f01c4030380c503210203641913640c0607101403d801403109160356401002c014601050041864409a0b1841d035071004008098101d401c92290058101003269490000e4000b03800e07c1c001412941c807921299003d030001c016038641e071500a02c040000101052200c04080010060000c0388421078402200580360501d05800c007078600c0305107542c044c40310780703034a0b0549058070340d03019001405611b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 171587733 1250 171586483 171586487
    0x3204140703180804172a0409080c030f07060e060f040221101d15060d0618030305060f03011b030e0f03030109021b07180b180702060702190f080901 65
    0x56442c03024018400c006070004101c4400b0684015504080040e40e0240d00c1070309148103c00c0020145480910303400c083e5000030301d0140c2c02100514032400c586482d09005909560541c0c1000c20496105d4002103026014000c0074060720900704950301c0075100c1480d2081940011040180c8064014100808595181c4848180392400340b003140013100c061500355040b0034046c104100b04054514406541c1400c1d40400268892500d0500c1f034491645988090074402c02c0d9445400a8400944400c65142c42545224080801328001d9401080f20315068041c0711420860790b4101c0d0007a032400108010000e80c201d00002000d50921b404141c1d00910b1051070300d003004050500100303000c000000980328100d54010580c031940c40070140f01800044040c9a00d62040b885480c0007036103803012f1169400e180b0303400b4400600c002000c1e561180400000c0c8000c0010071100304025a20107800c1c803021540402469002c00d070200d45c5161040c0b00d0395990900340b00c08180052000b240405c07a00c182c4c1e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 171588983 1250 171587733 171587771
    0x11b0f0e1e030a0f11010f0201141602070b070f021206090703110303040504060e01090c05030723041814011401020c0f0a030b041a07050c15040206043204140703 71
    0x20f600049140018642d5050202840d58001e03005d0f4040342200b030501e000c9500601903065001014542103e442c0c0c1e6100d0300c0b01d00c00010740000d4045004007640401c100c9095800703004424003621725603507404228414440350440c01d200e0b4060340d501540810460002c00513110054070b178040d0200300a20b8004000c20301d1405150040c651043c20f2542c0410400a0390015030f0403141308000a00c104040d10310300303651a22042d69140f000407074000401d017007821101c11207031549584141d80d500e4141d440b0000032211404030011000309890303e00b00c80310b6480000c0705a0241101420007031012a0356400030390350700600003120f8040c00d03001c42c03d400f080d607031021104001c640010240b1540e20b407a290208030242c0000c82d4244000800021070041071180c001d817490450054001d00c040c1e496510002d411000040049a02c11810031010402019100750044c040c0d882c0a901700003000e510021240740000205c00c9401140b511880745544d0740000d140d590410020b042c001000300324144901015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 171590233 1250 171588983 171589003
    0x41b0e01111b100f08070c02060d060b130b031e0603010b030a080c1b0109062010090302120901140309010912080a14040512090a0305011b0f0e1e03 65
    0xc0c095100d641e4010240c0d4014004030070300c00c42c3c200c04500f150201c142d844850310000b0780c0000f02410005200a0701407400c00e20410b00003490f90742840c655404180648400342c000303e2402d2008602221030040d4001b400c405029601229400d520b00380c0300c1e602000f02e0303010764800441580004140c2a0b14203510980390200d015066504105c4941001010350740000d0584040340708903183d02c5100034a503244c0049464050b96540320f41458207208030380210104010244015a40ca03140c2c41e80e080410400604a20400d0080341070300c1ca90070041d0800102c01c0f00421541410020850380d40c2c0d20504126001901c1c07202c0c96200e03241d001e0b04c18010002010020201b0300301e01103480031303160015034282c0f0903191484180001e8510411550510074240c0c1c0041c40c80c0d00042d107812401d43d0700005410000c10207000b200d400c96a0307440b036500b500c504000e0802c40c81c405440a2100d83e83c81803080c50383d4603ca05000782004055004101070004d00f5060300d50f482d03840400f0091640d82482181d805e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 171591483 1250 171590233 171590267
    0x803032202030a0309030c080a050606040c17011e06081302120a081303020f061801050d0902060409020c010605090c07060506041103100e01080a0507030b06150c01020414041b0e01 79
    0x200f42c5091030040c003808030500064606002c0c40c0b0300010000b034001044040309a000c0c002e00300d503844c0c510510000e00500307281e84040c00317a081c0340040b09501d0014514020b05503108400305214444101606141a5800a0041103405820080090b082c001c00f1074040303a05440f011900302d4030909903400c1c085103040c002c0c0780e040000b807942c54021000c24418240c1c3e000300e80450703800030394400b00042d0f03108491440c00e400001c4880d550b001d6004a000d440102c082c5a404242a01d40344c2c0050501d134440e41201c0f0311a6400b00d44101042d41c00d03c0380130081c0c50240d604d0002c40c01c11030040c0741c450050110007040c050b220343c002101602e9640003020180b402900701c41d2a410800d0010901401c0c074045c0311408003481c8000600300c3d400085070700c80103401102070840743d801c50f01c8a01210304000c000c16040184001c06400ca00d0010300148000e0b0004d0000680361800c0c2404807280740b85030f04034144150b00b0b10301c5d40030341e41404566030340c0444524203121182d90740050061f02d011a44452700e00c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 171592733 1250 171591483 171591493
    0xf0705060f040201030b22110f0a0206090c030a0b0c0d06090f020919180203130503130f0b07020105030114220c020709060b040302220c0309020f01020106080303220203 74
    0x3a41c0c120614800e8050382c402d0b00e01780503041a0754140b00004084040c200c0c0c40303048032580781e484003e036544031100314850360a5581c5080d801d2004d800351540007100001c010b91007401000740c4d10000348140703280c00c601140038004180042d141c5800012024101c4c41c0c00e1900010390742c4098440f588400300400c840c04003400b200007950a513800039045198014007400b9036005500c850091614080265210200000c030040c00f1428040001d400c010504124840011125804074074200044c04000441c03503c054250341c140004010701495a030f0000740340750b405100590051303801c03205481c1540d60700302820342112140800116508102c800e80420315056451541000c1c440390468200345644d42c0807956159503c080b0b60f01208d09a21804000c0305040c0b1040c801840c001c154000010302040d40c0014010385000c079101224007080e02d400100c0d5540340d074041103080403100000440d00900007001028503003070400341c880c400104442074250b000075541040d001c81642c40c200c032035009403c0360 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 171593983 1250 171592733 171592741
    0xf01050111150403050408060f010810020d0e070e010f0602030910080601020a170c0d05030402030c01080405161203030515010e0906151207030b0a060903060902060721030c0516080f070506 83
    0x3a010b42c6c85409100e03040c2c000d010024500240b00301c0014100d03a903100050502683c4284c2e4140250480e400c02000c0a40320611034401c1042000381d41c0c090f1101e030304211060f515110001c0240c1d02039901c150150340050120351181d5541c0520b62120340240e0510201c2c0b80d552600403401e00c24075102c0108514508000e01c11411881d401604004e45050211103003504401d0041c0d80d40c0c003040b10000d601d076101c0420000d15500c200b0394590000d100b08101c619442c0e1582c0b038080304002a0b005000d0014202d0000713400c4c907525000310be401207040d00caa040c01030040c400081448104e00343c074a0007021f04101042c074648961405680340c0001c2d0100a8581825010003540848107448440000e410100c0090b024a8248a11004c42d866503c8058031a450b540d40d080140191041c140c0c0e0110b420310000d03020800710411003404c5180030300070780c4021080e03807406411500061610800c01009009400c00b0143c400a42004e541c0c01810035500d4503600005a4058031032501c000b04a8041c5a041c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 171595233 1250 171593983 171593987
    0xf0f030c0303050a060b030a0f0216110a0f140405090f1e0d08090a11150d09031205090c120c0612092506120608010219030b090f01050111150403 64
    0x10459181c482d030b41c240f01d151144886a81524203500420fa01c48501704041b0b0351184a60380600c0e0491000f02025040040c8c0c401c81440d60b60b00e08005072541d03030b005070180d0b2442c0f80880002024144103035103120340e241000303020543d081860f500140901d40c0d403030110710060301c104007030301741d01900070110307007040920440708c40c02c030390501d00c08091b240700d684048421a400b40c03110604c56000c001c002c0400a41c6501c1d40c0d0440c5040c0703a5029000b95058620107001c0710324500a00140d005507201240100c524500101400310005d22041e58a01d0882800b040034004036080313034103c00031110f000d40b0031004c0e401242464100f812299004800084102ea000041c481a51040d8030b242c003541d1040f1512108841c94504440c1903c000301c030010f1003441258001d01c1e080c0e00c00c0d158003c00017400c0d6281c00c10715089911240c04101503000c0908819501380c3e0500503940c82440035905c41e840b41c2800c40115004800600070981404903070a0380000b07181c010400c2115100070081c024a6a0400f4140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 171596483 1250 171595233 171595247
    0x204060b1c0605030f151003170a080a09050304090f1508010b090a0c0e1002101a1e0d0f021201050c1e030702060f0c0f040f170d020303130f0f03 64
    0xc1074079902c0c10594005010302d000b181d4030956000c400050070100440b0a00400007160050049442c03071500803010000c1054280400c0800104c5070301d00c2d94803058000c0181803c0001403420700c582c0e060510700000110301100755000c4452720030300400c0c4506143c1c01c1c0d101038429007407000c1c030075141410300146003001504801001c600a551340a1b26032101c0310039100b81d50301c0080a00120b64040e1b03841c6424149005080e1582a46205464507004940e29010555004541c940c1501c40560507246080c035254440f03451000818030350108002d0a180400e603011549140606204d50441c6030a0a54030388441c01403508140c3c40007003041d031030000540e10b02034000842135409852555060003880400d00e0403680200a00e030018803c0390b1700c440b51300002080007440f40d42070407000c1c07144005c444680b00140025001a0f410810381030301b40640d81015201c0300c1403000b40c1c0c0d407018150b45a40303034003c07007180d8001800d4400035100c06440c0c1016400441c0103040180a03c003040d00301001d05520501c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 171597733 1250 171596483 171596527
    0x504050309010e0a0e010e15190509010b0c07030b0601020307050703120f030e0303060904080c0d2a150203040c05060d02030601170907061b050604080301180510120204060b 76
    0x281d0b21075055919003880f40000c40390003a52010101e000050240c209a00c00569020f591641040c1314801c5480c04141c0105101415804050380d902c0302b4041031618000c07260142c0b032000081410641801041da50320321007880044c12096181c8045440c592003032040781e9005410604543c0c0b8a070f92480d01004824180c40c0300c0380020078003180546118464002c01c2e500104540080d800c40d1121010000010809401101c44801c20004014410428000304054549540b5150400415080d5034000c04003008402d54909054140c0e48002400b503400c3c40082203005c450068803942c1c1c0b031070400f66104c01500040d074818000304100d4065601c540046210340000eaa440015940d11000000d501d001034070390030041d4000c0324080c00701620804070010200342d0791607517801e02c01d0b50340c0340c10341031000c10740b4144e0305000000300500c90038503013201038450003150103810089450410804042d091350360040143c460901d05921045d95a190450030103442842945640c52a40d220303041d8214244503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 171598983 1250 171597733 171597737
    0x31805060724050115080601030b04050a1d01051312050f0301030c050f04140106050f0d0e06061503092806060f05011701050d030c02120607170105220c090801050405030901 76
    0x1034100707882d2404038010b5504076001c0d0050110540303800b01003591810801440f480c1010754a12120300259264064240600103036440080c4104c1e03004d452003d00748110500e04110380c100000d002020114403001c0080c540c00c010203508480803c0b604032500c0c0310b00c060003041c0c198080008414400c5504c1410308480040740c40700132810003003040c002510500303540700340441840001005207034000c600405500c491181090300c0c2001c01c00034981183d20b46241004207500071030421043c4c0c00e004030301c400c0303034190851980e0840c5801c2405a070360700b16902a400003400c043c81c48250f0b50b2803400050303c03115803040003448859103585846038904400c0c880c4d80d0003d0b014820b84640c0e04911314003181a1180134000742c9140e5403a842c10b45100e450391800302c4c0c01118644802a9040b0309200300340c01800d00383c0e60f8000d201c6032541c81c040714030340603006584035003100c507142880e00552609000c6618460000418007014000e000d482040c0036900400c03480d400c0c0006c2004005003c03008002c00c120036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 171600233 1250 171598983 171599033
    0x70c06150906080a0309090b0a0503070306020d05070c080f070f060e0105040203210d1a0a0b090a0906050904110301021603020c0a080c01080403030b060f0a0314180a0318050607 78
    0xe0207029030701c04c0407000280104904240a11810711140c00c40740300e149010309140c51803913949020a2401a0a0340300383c4055a000c58a903c03040418091a83c221041b450b03c0b05c04417032540c443c80c03000d20640a112041820000c0c00f0020080c00d1507080c0760050300640c0820100e100f000000b80038003c01c490403840f9010340c1420420780c290001c10300f1081036036840350a00740716203040403c00600406040c070414002c403280079469503a0790645c1c800942840c820a540b04c0c5c40341010f0003480180d940000c1042402c294080c0016100c150386c142c0c0c000c3c0c0002e0300f034030b80c80d01c000d0210740240b0400c8200d00c100c4400c520300c00d05041d00007420301581c6130140c46280303000d5a01c5c00b80549504030601880d0000d00d43c0710200707001c41e119401c210006400145a01d152007100100f48041d40d0120790a14003080c1ca40c8201c2c2000304003010510ba00c00100b00c0c180c801c0692040c0c00326118000d00c240102400342200c40d004c4a90a103410910240c40c02410403666050b507810055104118200e07141080c01c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 171601483 1250 171600233 171600239
    0x20a0206010501110d140721020601050a0e0a050604060308040f0503160f03080a0908030d060501110a081605101406190303050a0c080c0115090b0303030f0103060203070c06150906 79
    0x100d030501060329040b04c0058540c1035140001183c5180b9400010704005606001c0c03c0045032910142121565028448a20030100028081e0400d030b0140d1001e4460900d2100400008812030b40d15540420000d00010301c60392050300080040403581c10141c40751801240c089040c040c149014002e03100c3c100c0440d0784010b00004840d17540ca000f805442d200401082c1d0410000c3c04110150140640360700380207102c2502c401525185800110b2101c081540340ca074100115600220310390541440300c3d0142c0180c1840e0345401140748a01945151401c11450703944003881014000da21486034809c070b050080c0f400c0d00203104d0415506a5001c1c1c8600c0e200e1031400206c0c0b18501c40541200e40c90348906041c200001c1050b9a803841150050755100401c101114402000384140300107002c1e8035040c2038203c0d09001110b8220b03505240c40d0380c041d50080040c003074003001181609044a83c81400035a13030f41d688805c11218844500d200800281c1880c41d0402c0b010030115203071060310400300007000059a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 171602733 1250 171601483 171601487
    0x708010609140613021e0a08010f09050f0105120a14030d0612112106040b1603020a0207090216050a1a100303050a0804110d0b0103060c020c06040603020a090506030901020a0206010501 81
    0x10341a0b030075560110391346a0003d0380111640140c183e08403400a441c854100a40c0340c1805640080c08030000107c602006224000c8900c0500d00940b140c080c00b085203281400010300c4201c0c060007507500c24a030f01600c88015410030440300100950107806c00748244403000c60f0665130341240001041040c1004000310703010001c4041e070a1101e401084003409003150f4000d1040d0b031141a4034540480317030034419840d940b182c200725203030050344640f40f0b0440d0741c980341901000000760789403408105401001107003411070b80000d840d420360f600341100690302c40c2c05015100600601d000f00030a54000c40c00c4c3c01d000c0c061950703101c901c90b4510680342443c6a13a095000c501050a0b40001808507500b44402180c00d80320316200d55110740300d850300c960074085000010740d5128005070100c90480c50707240180100042e0307025100038505070380010003000703020400188085c01140108010140d021418042080c41000800018940600000c0d138a0402044071030103548a2522003016200d00000058154 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 171603983 1250 171602733 171602771
    0xd060605130b0f070204110d0f0b0a050609060d1803020d081b13080616180506120c1606060905070c02011413030b07050a02061e0106200708010609 65
    0x144605101c480784906140d80d42466400c6440c40701024a03061101400580301c5203e501e160303a00482010717498000152001007a90303200e080100f112030420301c44002c10b8a030400d4101c141c80017110300a0b00c8178450400300700540180c0070495219402e20360121913514000c515914018002c0d03082d039031500c51850f0140c3d41400207445071202291000b5003440c4000003c0701800158410042c2c03107021590301c0a525240c10000c4c1e441d15500c10040440010003500407040c204201c80b066000c2c13100624000c0082c0883c0146240005c00b40720000010f505c100901040707071f001c40511140083c0782c50700c83c101080240101e004040c01d00c0d00d0031000c100400e0103210032001e0613a050f511104a00030000600b00185c2140e85c000030410030035000800020f4031040300520494103561100c0d103c15042c075009240002c003a1071801101007005441d104a405c409449041d9a01810600024219101540f1100c0408034030502580240ca902103201081034004000f100c000035024400070610f05c85000000f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 171605233 1250 171603983 171603997
    0xe0f0906010807270e010f0f051003020114120c0901090602010212041103280c1a0307360f0911090405070504050a1202040f1b0c05030f0403080d060605 67
    0xd40d0000b44208240d002c0d00e0300d00e9103181d0944042413210f000340420300050b101540c1030040076944a400c00d480302045031003074201e040d010001c03e220506086908000c45d80071404040c0c1001484c0d102c800b0f42c4080c0808550607040d020380c0b400000d151400214203960004508540000c245090002c0c01501c140241d41e4001181c84a45000e80c480c1e03960706c404ca0506c10042901405a485528035130300680300c1c4091071185640038403220707842510700390807070520a800c104200041d00d40d82941e01002103064943c8140d560400b00750242030246110048980c3d1900c0c944524201c0c04c051079000140c44020045403c0303d1030000c140b50f1982d0000c0c0a031455004070005c0c0d010203018002042c03401d40c03c03c0380c02c40d845061180c034082c0c5901c081105c2c182c0c1c42e0041c4403610641d007002003c60400744281820304000030000c025441e803120b01d034407620907540d01c05002c00510400744000e0003020300403603d110041000c696038699980c50241c003990400c40d1000c04181c41d000340000c44901580854041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 171606483 1250 171605233 171605249
    0x302030105131a010f031b030b1005030c0417030d02042711070f0c08060c0a0e030601030c0e180d090302040e0d0207150905030a0803150f03061315060e0f090601 71
    0x140b41e4443c001183c160850b450054205620740503d002c210491120b19003c25000daa0007050b808024001d002e8000003031011241080b208108010601544800380c900755540c015030000207801d598621840d41c06005a1740495910010b80040d41780300a40441096580000d111090403107111720312801c42e96880c0b48010700d5801040b203000015502c01000c0702ca44e1042040e40007042c1c44070759040c41d0078012110242c1e030740c10014440b031a10303030420f4504066a41c101c004090311340c1503075550005405140300c0d13501046a9030011601c0c800122407a01100301320308080710050f0703400724002000c0e5401c1d40700c1a80a103103020000941c0741c4011170034002210320b039001421854503050200c44075031107106c150001c12030307c40d101040c2582c4c14000c09880740d0103000aa5203e0070100400b0100321800e01406100f00d000b0040b003166900d000c00c440d5804031800b40b40041d015040d08060112011100707040300401d207005008030b042c424088801e4041e603036480511809035908012103540f00c1081c007503490307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 171607733 1250 171606483 171606521
    0x3020c1c17070f0302090a26070e070e0d022202040f09020909060f01020a120507030906080412081e0c0703030c08040807200405070806040c09030803160c12030203010513 75
    0x503c0c9802a00100b2605102820250011303649100e0590b9145002d80510043c1c1ca0031303495204904810001400500110034455400d070034014006800311480d44030050180301c4890110065580302564100382000340d1f0700e2703003035980402840003000790721074051204480c400708404181d51240d0310079290340507006010100d841e1203150400038040481840f503030441c403030f80c0b5030100058003055100384405142d841c1c9079101c0384145000f40c4018403640000d801c10410400308000301d011a21030340a04141c0b4200315425403143d41400d000241103400300300744c981c020300900c81e01e6459000208100c9019a904100f81022023004481048c41510301a2011106000c560046000150400d445003d02c0382107000c00032003400400e01742c82086941d1400700b40208208a103c0c00e06000d0744400301810701d03000c03140c41d08543d114811800090b08001e00d940c8140340e143d48140c000c20b00200d43c581c00400c072410744444000d006010750300c2401818002e003080b071b414904084d401d010700c4880040e080b914038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 171608983 1250 171607733 171607757
    0xc030c1c030b0f0603060303091503040204050a0b010c2003191a06060301140f040912080106052d09030a050a061a090c0304050a200f0d0302030405090703020c1c1707 73
    0x4c155500050001036040c042000702d112255a0300103c0c03070000c000f442d07505e42c591a180c01000215600107250036407a60504103d10003680c1d0081c104070a05901c010205590b80445401c06801c411142580b5014807894003410010417400c000646180e00c01e001c20228454055245651104251911034000e0008d02c01400303100c513041f0181840410150860280c001c0074000901075408050007500d100072600c4243c1526540700d180b0300d02404603810403903c1d19143d04d50715440600860b141d0b5642665a01003444521004011240802c2000341118036520182c10b010303440b500e4502080312441c1c6001100d0140d100c40441311b039600080102800c015a42d2404031a9290340001c0080710396006ea4540b050008801c004184040c1d09880700c5840034440000900011b08000485540720304200101140002e0340001242c05540c000e070b40303801070747d161154150003a020b694107110301c500482011012142c40c00450001480856aa180007010480701114030b5000030741c1c82e83c0005400f04429 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 171610233 1250 171608983 171608989
    0x102032505030304030e030c01021f09060608100e1903020a02040903020a060609021902030f0322052a04020909010306050601090308030f0a141e07050c030c1c030b0f 73
    0x415498500c1180d40000400940d40d071a04652007150100e0106170000f8651072070341020007d1401e05102170000b030404018503028442d1081540240242080c0c40302d14200401400f500200b00900041044480362000030095502418214001003100e03c5940c600c4540881080c0b00401f9843e010340190101601070b400b0f00010745040401a03081d4420b2035803050000d60644900030041807440e0005850b0003200c10800d48500707040d0951011580244018200041c80700e0440b6000410340e5101e08901d44102c080c40c2c0070103440704010b40765000d14040000b1034040616031043c1140014007a000007007030343d81000124081c051459030080300c03610051000503a03a5004a03040441418600c01c0e0300c1d0740780e841d85026842190100740d0030080d40f05000301c02e803041c042d4589070244810383c0c5209281450a40b114240607104010481180002141020b80200110340d1204403440c292a5528a8800c4807a07450705e26282a500e00134124050004c0a41300f40700300c6801c0103004110b00c0383d03010000c0070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 171611483 1250 171610233 171610267
    0x402030c09071215052805061315031107051014011212030b030a050109050c04110f0315040c0201140603060106050a050702031e06040312090b010e1905070905040515010203 76
    0xe01d4180703c0f4080c0c0041744507590718a140f9012903104d141d0b40c407102c000880442d2049455805240510418030440d48188824030100003980d0240c41c1900226481c03100c11006000840500c00d5100350009050741405000314444400c003054001c10310417034905400704d10306120b09100c0c0030900000490b44100291704281442d481c14070a203000f133081c150040c002030501943e000220780c1c0d0b039942d082400410409001e9500c2c1c80c40100e8041203800b0904440e01d580d0300c2540c82c560800c1c100080021092107207016000c10a00c00500100510f030b80710803001c1c0c003d0071114003d8501e031801d5000a00c580c42c00140311410b0314280d5840c2414140203031801d40b400d400c8548101d038507005001c0c018030302c514124020070030412500000c00c4641820f05014080c1000300101c000310300d003098503181c00725098002541c1100c1092000e85000ea0362154150550717203c03044c0d5400302d2400c2c60b00b0300c44800d030b10180c04019642d08a27402c0100f0703140c01c8040490848504076090143e0000d0150002192a01030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 171612733 1250 171611483 171611501
    0xf15020f07060c082716060207090f020915130e0c0403030e03060613180203011103010f060309080702012f030c0c0102010614010c030c060507120f020a081504020c06040b0402030c090712 82
    0x10403140707010f0704202e071201106d90b250804001a07000450030070001e83d5601564030b08000e051411468044028041480b5000f218038889800d400080d20914416607070f0b014000910780010b8840850400000d1130156500c144802d03000a042c00e01d0904451802180480c0a000001c11445420999202140c060320302543c1e04640d01900891002c00f6850a028103441d1b03030030000c0e1250741c940c1040d009801c00c1c86250081c908061030f0100c05800541818121040f00e602420404001d000d0300700304148030b07001d00184402115028441803050080000645805559101a00c04680030400128200c8003148145101c41400050102441d4040c50030315089500915100b0030b410308540314442a5002540d1100010707141344044c0d82500f545215003a0301c0126080300758640008000002e05840300542903c00714a0000040c0f80140d90356811905c5505410080e01d049250900740340702400c3d000c9130184d001e4014018400c9080c030f054600309100703c43e252106e05c50100c5c107002d80001421641 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 171613983 1250 171612733 171612811
    0x3060108011710050903041e180b041b030c020c010e091801141008060601030912030b01050c1212010e010609031e0c0308030a061e030f15020f07060c08 67
    0x30180110042c06000341c0c1d2090740051700440c2d480b880d051901c41e00144030700301c003141441a0101800501c0010a52550480c4109008155141c040c0d0000700101f0301305682c00404079800c40c003885a42d8254009452421464080d41c2148580c0300c0103507050140401003030381c04002d040c00180e03030b50138115542e030364040e8080001400e0400b03c02e0050fa0550242c41d1032800328098401000350b01010461654424030030b19090166503c20366401c40f09664000000060640707400c410341d01fa91185007a2010300f1301c0201111440d800c100c0110802c2c0c2c2c8003488610120a8160010a2668406500a048612540d18050030502d140c031201e054121a2042c9030580900c540c1e500d01043c03a4a40300c4010350702801c01c440d40da080c01c201c0c85007122070079400380348250908001d00700804802d0031407000b00c1c1d8108034403882e51701c01490700d0001c2d4138010044200b510710216a00703072042000b402134140a8401c0d40c0401c40000131084c00e4451500c2124080150520000e4000042900010320b0012144d04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 171615233 1250 171613983 171613993
    0x80a06050405150f0a050a1a0108072c011101090809090c0409021308060709031e020105071208011d0408030714090d0602030604060f081c1e02070e06010302030601080117 75
    0xd52821500e040281c415003e034a071384030300b0f202d0503a90512407603400c610000340801c1821409440307084001013a0000c2410b00110400150b0910700856650308203030341002415011000300920f43d6000041004030900146488000f040c52100511408071001e40042410342480800d100304082030ac001040c021030a4414070002070341d0443e900181c94550a0303030a01d0303a4001c0c2001800380c90030600800aa041016a2a042000c940201d080400b51440d150140320340110b0b81c001680c0522503800e000b018040d0790081da0301c80030fa00c002124142c8007202c41e030540608803081403100e035600c103540c05041c500c0c0400204640c00c1c042c040a810303024140211500b015a481d000130304111140000740da00d02c0e00002006680d107098887c0c4d90107080c0c403211007132000e4140207189940728100c903524620702c04801c001d810340b01e0269a010415142001d40d4099820b400300c002900c498507403103a44038440401d00031801c1c0d0740c003d0094a01c42c0006945501c020780c80c050964005189113403d0302018054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 171616483 1250 171615233 171615253
    0x30706021e04030f1e0c0e1e011410050403050312060a08010e1f0e06180708060c12010e190903140d02090f030102030c0703030209041409011b0207080a06050405 71
    0x15070030161004500450408080c039109007004000c99429143c0031200d076844030608400209803108180c191005041c0c0d0590319520610611a080d101c601042c280c02c010384000542e0100d1a0207030140c100e0150348284080020403810b40c2c55004501000b4400c1c0c00034003801c1141000d21440030b51100000342019611503480d5419804c40d511165a000113070042c080d000202d448c021410350120b44d5820007009001d41c08100c2603101c41000e010503811081f100e10b035100c111800c0160b82d0181444c1d03010343d140c500f0400c40406441d800248214000b180c1100005000140e03907903168070800b048204031205020071061780d0700030202c40500700c040c0990300d000d160705041d8040c0502804031106400580d60003d640c10090305201005c41144203070700400400881103007400589500c581c2c14200540c030b84a28000080103030800c8240440100480002c00c0190201500b00c1850303400c52465006d084101c10104a0311410a4000c4245a5120644100000f5019030215a0043c098026900e6900e9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 171617733 1250 171616483 171616537
    0x408121b0f1e03070f1d040e010203090f071401030b040f050c030702010f090201090303051e03090c0f0a0b0403020915031209040b2e02070b07140f0303040209011205100903030c030b090903070602 86
    0x123180d80c048100380c0d808010400000d108001d2054038450b844000e048880c600000c00b500070184a04a904040d2201110011502c036500070590a1100c40300600107031914038100030481c1c20485136080117600b004d40c6040e00c00920701c40e44103600e80603518a444107003141c4003078410342e1003440000d000328000e002c805454423250003c0d50240c40c101d4007034000002440100440b0b2010b10400902c12501007104001c5510343c001103d08580d0b064415002c80e80d60781c5080b05070419034204241d0103004803c801340084c89600300829041600320307000c00159001d10140055000801d805843d00f030085000c580700200c940058500300941481100c0d542d580723900700c540145c0c0212204503080340902101d810000014020050796821f520025429441c00fa000550500418800d40054041941c0c1c510140682401401107101142000344020f44007860004c0083c0307040503507000040e10700b455003a01460200c81140c0510102c030011810642c403621103000a603c81041c108000b03050440d1205036103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 171618983 1250 171617733 171617741
    0x140a050c0309030a05010c020d03141605130815130201020a110a0f030f05070b0307020a0219050402120a050c160809180106020d170408121b0f1e03070f1d04 69
    0x117208200118802064201c040e01c0c10820317400c034030145800e2071407030307082004005c40b03090b804085442c041c803009401031001d4072940314003484030f1030001e1503d40101d02c1207000a04000b2004903500f052210342c2d212342a4582034180003600a00507086071084002040b03c4c4620800f030000000e05102c4841d540341882c40b202146c0380d00071901c2c0c0721080e14031000d100003072004400030140d8406076071542c80c001c10003d48440380444000e2203003280c840341c004039517103403007030080603040c054411540c0d40d02c252240c0003164001c0341d180404a0500f80040d0b01103000c003080d25a85403140a1000c00b0150300d42e900e5203290098842c464100d01400c1c40504586a101c0640e402810070380c000c0d10042000d600010100041c921a01e002c255401d01400001814102101d50038000140d00258940381c0c2414108001c1a8503a4000191404141e001c14818818010607460341908114810000b64184410b007c3c081141c0002c0450540b800011030789014403000300c040340034400c140b80740daa1100001012a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 171620233 1250 171618983 171619003
    0x121f05030d020606090f060a0e19050c07060b032e15031202010b030c13020a02070504050c0a0e0306040c1206060e130b06010e0a1a090301020d09030f140a050c030903 73
    0x41c1c0c0503c00740b000500304418510340280480c0c0c10702100f03203800c0b408184c036600d0501c612503c0c0c0210b580000c0080214540c004010b42d1035510505c1303030342017220644103190888001954402c1ca0458420440c0c90000780400d102c2a01c0016000042c40b07070074040e40c45082034800b01c1045611450b851100c01642840d002c09540306444030420820010b00090848200042542c000d03031100d01c00c0d03541a5500c18900c000f180d040007004d039440d19801000c074200650765001980103402c04e001e000d034100c43d01002d0008126a0340e102100c12280744200355407581c05807006000d11107a00c00a200300e47c0c0040005d00024054100400c5043e5140c001440a00d001c0b074403041d00840000d018410072000030303000c40d0006000d01e80006c040302c010001079100c410502c140180741428108445212810400340d03a034841c001002151580703054200000074100c032900490011b500b00750481901d5000d5141503810102c0c040304142081c400030010744240d440713003c1115103440706020020b00d59900b04020a09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 171621483 1250 171620233 171620237
    0x60603080a090e0a0204212307090e010605090103080915040b1c090b0a0f0603050304170c0306010f090b0616050709180506150a080d0201060614121f05030d 69
    0x1a4507099150f180d00102800c01c032266401080100a80b4803016400b8054405080c8000e50316621807810380d141252000304c950020f40807869440340c0d0300020500d1030840e80025001d22038042d100602900700c13800e0f4011168840044001032010540d070340c000e40400c0201074000c82041d18550318030030742500640d00c80400150009141002c5e0040440b01110f418182c0500b40880001641c9141c403900c00182607a447c15035a240c0082035500c560050001560085c041da666181c5415508074030703400e80b000d13211152081500343c909904000070110304940803800d500e15003d0524540602401c01c10b5419580104103000502001400b1120454018401c4e0001d01c525440c1941c1c400650b0b007101c024544180800c4003e01c085840480e181d035121007003d010300c403428601070000e6207101c87c3e90815059881103504039006a030f015444034007952165118907038001094400c845081c07150a1221000541b004085200c00110140c0d00c400c540000612049503074481005c81d240120303010320200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 171622733 1250 171621483 171621497
    0x180915090a0204180f03120b0a0315050108060108071a091c0c050402090117180303070804050609030703090303030209010905190617040203060c03090319080402130621060603080a 79
    0x2c501d403500c00c1e0f95018200402005018041c3d8032605130751002007002800780302c0440c0c014070900b600d80c0d00c445660380000702114542622814811503501e40a520340807128a040c00100300c400001500d10704a44944004010482c101012400070300d400604e802c2c500503060000c0044d0340d64000e9462900c0310040e00f104804111ba060000c40c0c00c880b680820702551041018655599000031a04000005001c40b0401503d0f41401654260440380880041c0d0001000f800650390388500e555000318020000c982c4692240b030069500c0b440703501c10041c04100300f400202f0020780660007604055005043c071100503030f990004940a99404d000c0115028400b10b0140700e215080b40d6686074060500006503020b141035030119540e80c40c003a01e036554054010000810a00c810406c40b13540b6001c9881660403640c10310800342c01003d0a9074101c0c03107a19089d210045401c207074801c4000301e503046100fa4840e1056103080c008440440503003580e4890705c0304008804103404900404003268113035505c00e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 171623983 1250 171622733 171622753
    0xc06021e0c010c0905030d0e0a0807060305100603140406050604090b0406060810050108120f07060218040b010804030e01080705070818010905060a090b0a2001091401060518091509 79
    0x1600f12400e0800316030511036810010321207620005a20303580041c0a00b040341801466034005501c50080d5400200280320305040815044d6150300490b004400c4070342c0d2640d1158607180f040e4151100008100600242c0320700250100d510ba401403a0415001f03440042e44615030313111440c04500807141603c20503100c5d00c0401c108041040201807050188004100c030794182000f0603141d00c00b448413440001c1003c80c000250070b801d07500702c03004254440400c40d9241e41c01c1c8054850a2002c80315544100d240244501c0154014040140b0456251760741d6080803c10600643c3e500b14003401040410038140310f10400184180b0007001c021000220700c00410780b003500014000105a000b10f406032005000c40c4148940140000d0292104481881c0d11900203810880794000309840d55101c1c01145500408419410f501440c0c00a0050a00c0140e000d042d62000d82610194441d00350040c5548080000041098010b00e4100340c1210a85000340c020b1400170346034940581c1c031200190402c0b1140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 171625233 1250 171623983 171624007
    0xf0d0803040f0b100b03040b07110f0106080c0d030c061a13020415050c03040b09032d06012304020906130323120a030506130f020403060f050402030606010c06021e 72
    0x80c42e80813a55483d03000965081010700b19203800003420042503048181e001c610220b01030001782e02c0d04c181da142216802454109120302030718580c1700c2d0017031500443d52003034807500b4065990009a9010340f0f4090780b03070030907545040080c1140140c040c3c42a0310090010040d5440c450b81c0b03400a0141c44001d41c03114103001c114252803400320141001e0050803c4440d421380c4011013640c0841c1d40b041d050b9502c5400510200e418038040c44c5840341c24907000301c000c080c00d040004403e103440d00c030202101c03a1070782c86041043c519031441d03204011324107801c004c010051030a40c0042c00ba010010700458113002e0300e040400c5003140c85810407a044500d002e5001c28000c0d00282c0032880f41c00d11801800d4624403031404188503c03824a1060805842e0000100e0580394400344010000640c00100842990b02c02d01100035081400121040e60512980140d8810f460080e140140e0b00200640080c0d00e030900159003c4488c000d080b03d41e0f5401380580d211002013400c5071681c503d107a521060b550690800c0e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 171626483 1250 171625233 171625253
    0x160b0409050a02191209020306040803010305010c0801080319171e07030c090306230106080a06080f060601030213080709020301060e01110a030f030f0f060602070509040308060f0d0803040f 83
    0xe00030709841888070f00b13526044080030b114894000e0502c0005100320100c120041d0241c140c010350035104070003e020030440c041d4021412680280002c1114840f02442290080428411181554002e00c00b41d4405a10100451070301040d60600020341088884240e001600440b02103a810110124490b54280403034000b80c0e010781146800c00007440f040704040e02072180f40c00080c21a51f48d400d8108546003055120782429104451800010360755003100425a43c03086075011445814900000b8040c00006144002c1440d51405420550368000c0110002c0d0072080e40c282031004120000911008180403080242401f00d502594940c100300e009480507050280e00c50420403a001032411a07000401c03a241d04561618002c001801c00e048100c015145201a07494102d242080194240d50076903c16011603182e50250360141d80d60303400300003000c813041328040e01203110580090398620306000b0008099000408540d1405038a4444102e690400c540407940d01c4802c09080e02030150004c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 171627733 1250 171626483 171626491
    0x1050402030a27062f070f0203030304060b031b03030714010908220e04210e28080a0c0e0901020712080414011b05070f141c03050c03060d05160b040905 67
    0x1208100c5410700d441741241403a03580801c40100e004030f040e03010000802d403a2440f49800800700c0381c41c0e0506e81400001402e8040c0468882d1007915004074401d01000d40c070307500002c0000c01442c142401038031520789101c0d9140050602e55a42d008a10008002c0f1004d03021101c580702c500f00e40c0089030034a50311032030119002880c02d43c18540030040022904200f030f4a00c0b0200c6100c41d120244421030030780d205072840090b0b130f074001007c182d84030321411422083d402035190070341c4541c080c590783c1c0c0c080341d11110070701009000c40c1c1111605010072804110840d80062401000502d0010300b1f80791880c203c0c54140500f400621100244410b00500500843d04201e02c80c0c0200b000500202d00e0000640259403110144103010444a0a00404000c940b40154100b5030300c860030800300103015260380c0319460750100440119000174480744648034403803056128442580c03850300d4a800704411034007112000c44081c80b6040d01d40002c90240c00c603e4004207442400a0340316820009a42c040d590010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 171628983 1250 171627733 171627761
    0x41118091501030c060e0d06180c120210080403050903010c051b0f0c01030b060d06060206040209180c060906070614010f06020f0604020f03030d0603120813050601050402030a2706 79
    0x140041038100f0741c00005c07034015003040740c0c420503858003103400d510100b0005000c061600c0d0780c1d100a80c04140d0794120542c4103100d4400b03a0307a1580c1006416032000c40c0041e4000b0741d5281c2404071076004040440d0002d0003030410908140c04400001d007501c40c01504000012030215104209031228902c0d070f0008200d2001400480d81c100034400e941e203e000303610a04247c2c075581c0e5006e044d204c13281140d01d070625100c410302c100b903120900030755241d00c15641280607035078000000341a0401240c0c1c2601c40340e0280090b00080100c3d0040105a400211950303500041c03c20042d40061090f11666005400d801c0490f0500e626254805441d070320594055406c1d50004074680e1400c61001c0707580c40d4442c0d81100d0380d46145174040042440c41c01401c60a070603461a1600c040103219040c019104240e00e15070322040c1e00d594901c41121080f51940000301190300c45c0d00182300078030341a0082c540c8242120380c000f0300c104400d1001008030048004580001030742100703070380906c080c2c0c1c02001e200c031001ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 171630233 1250 171628983 171629023
    0x60d050901021801230913020c0106030b0601090f180e01050405060405300f0f030106030213051804060c111608011a010503011203140a0809070e060d060504111809 72
    0x3040854685c001055040281d000001a280e55039550381c544041c1c0070b0490711011500c41c202104041d008144600003030320100611800950341c2d621407803141090385d600f000151b40540c0707030044040006040712a00c1c058192950f031490040442482650703c03550141c001044141002d040143c00d0410103020078001080c08614a44119a2441980e801c0011018080d079100c5000200759076501404000d0640030000100018600ba8150060228032041038004d1400c10b944408100c103d241c4585002d45003041e800014020174010f030b100440d068440c1c10141c00c04a0a1441141003880c4a1002010f44025a80c24441d0101c248548044c0341803032200b06110510400010300907000501c2034222410b2032110b41d4082501ca40642800c00b5800100d00d038580b52420409400400c04036404541c40c42011000104018a80d942900a800150044141d0041c43c0c0f03500c006010b00800980319484c2c220140600390700c41e504101c50700e4001c1600c1d1003550030080e4165003400300154a40d0300c0d107904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 171631483 1250 171630233 171630257
    0x10c0507030e030309030303090f1b0d0b180616080903210709030804060c1b030c090b040608030d0c090f030201080c0c15070504092018060d050901021801 68
    0x10804590000e50581000020396551400181c514481c0480860f0540804014080248000a40c0001100341a4280c80000b020740414404525020500e40ea004026105d43d00c045010340400380e420001d07401c842c030491003658021924144080d07410100b040040a2101411584582c070b6540004828010754507200c0b0304070042000e0040502ca009800c64010042888180201a844000c541c820705482d01e903650b80c03002401002081030141e0b0710300d800782e601040c4802d41075006c10549070b0050f1012256410408044004e0003440d0300c007504941da1316004507014504001600407074101e00e1004c50042c681440c010700c1072409602100180c42c1c0d000f400d00050303802001490707001059210068984c401c40c0307511890305007400034550307103422040d0034411200c0d404002401502e610010505c03940a101000d000001044a04120640c2d8140514103519481400883c400900144001e0401e14801001c0341294030a540d00c28030751b9800140e00da014041e1390380b2490144000d00304900000da03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 171632733 1250 171631483 171631487
    0x601200a030f18080106060e0909100e01150b13120314090a150903031103042306070203150402090a061809020a12030c0c08010c09030303051e090109030f02010c 71
    0x201440101401080350400b80c040e4410521240003d07281c0000c91001c6544002c0726008003483d0054000007101c0181185032030828032819401841104010b24070309040c5c0c21140700424041c80755201c29500c03a0303006130325100b400c10380101825120390041c0e5100d001d01d8460781003810340c0d8002124240c20781d2001e401300390010b4000304200c1182400030f07502c0c490100064500465500007030442103285040f80866503001b418001903038860b80f101d034030300f6610581c2c06039030380214401c40300d0b001203181400102d00080b00a00407001c40181800e07041804660000341031540d4008014201000c90082005610701001a10f401412010381001910308007422011141c240454a40b0302584480c0c810046450700c6407108028902c06400c42512042e52600034800d0b41b904005031440340c50400c01180c0803006100340440c04483c0d450baa01074601d1a6410340103450000c0c402c0003e403040b14956540c40e00d5803803c1d640300c1c1403524000510008a450050122040d180310681168585516508659 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 171633983 1250 171632733 171632743
    0x409090b01210305160c0306050901050a0507020606150c030c06070804030f03020301140f0307080d030c0e04060806060d05070e190f0501210f020d0605070906050c060f1302031203060120 82
    0x11039070b0850580004801c0c1045046c0c290280c0c402007025181204000c03c0100651195009280403d42400f454888400482e134848041c0d5440b540089003c4000718079000800c001c00b620410340701564140304580800e41e00b04081100c030400400c582408210405501070081d004126030b50038118119410a003000d050101b500803124024156012460055a800c006400083c00004200d4001c0d50381c4800040103801401c10750800f28200203900a481e20b403601031801562600c1005007a2f0385d480703c0402c07148410a2800f900c0c24003c1c05008100c0b51030690307803103109199110b85d410341040b4080c0400102d40759020188102440d0000511004078080c0209000000a00c140301c0500c0503800d02c001e40c0d031a200f0000350310608102e42c6504212035500143d00c15200c54030f8104070f10350b0750358003a1000d12811320100030541003013001442d1080e004048941000c400c8440400c5d001e0580e0120349030000d84410b0030f803406008000c01c1195a4809050812502c6140718164141c10402101360781d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 171635233 1250 171633983 171633997
    0x10603030f050c1f0f0501030606140d05340602070f0608090c040e01021c0516090803090d1118040b130c05060a0525021005070809150409090b01210305 67
    0x54200741c4c000d0b989a0f80640c110041c2840003250410695070340345044001008180701d40b1040c41c40001440c1c0040c074000d101408101c2d040405008040b40d401e40654104406c80d450181c00c000400000502c1036060582c5000340c04250000d01c40107003400f911110303000c80c1c1e074440410070040004210102e503001c030b280a03e041c0169000700d001150146124064010480c402c50711038012045008400e4007031b041640120000a80100d001da071603e021a42c01489000c5c625040e842000031484030b0078076040c10408103000700b402c8203100d0038a20004800001503094a044640d00d001071009002c0c038840d00b113800805400307844a0004842d641c0102400e8203100c2c591281c200424500d48050041d0700b2680703800c50041c8040d41c5424405042d103045042c00000340d00a801c0e903c202180c05008000b200d0616820503140d60031b01c2154400c201c80200310030080508417a0600000401c80b102d801107582a603c542d100203441c3d0b0400c1400400450480c07418038601d82c5408000d00441d4000049a0032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 171636483 1250 171635233 171635263
    0xf09120f03021e03011a0f04060806060d02030a0906240501032403050d0801080304050a0b090406080f010b150a09150e0307030308091015050d05120a02010603030f050c 74
    0x94030110440541c0240240210906807044551201c00300812010003141030301c0f04200d41e240c0c42c0c40585464140c0c1c2c0210450340f40074040803c814040075004802d140c0c0e001c1c0008084910786a11043c001050340c01c1900c2484546856060040410134603000320002c1d11411100300c0702c0c5012011070207050403c00c0c0b14040c10b1640d41d45d006041c0c00c1c65072a045040019406c21100d803560340340f4005580d4012a4001000039141000108130b20001004079402c540c002480c1d281c03414280100f0440d281c1c000140d01d0350090780c48800044400c81842020100e0740b90400004580038110140041c000e9101d4407500b81d40000c000c1c071000103420a241506071040100a40a00301510034150744816800c40801d40c0361041050002c10540d011050324410000e080a45400c2c1c0c484808440640c0c03034203092803e10600101e014006803c0c80c84501015a00640440d401074114001d01c0a595200520f0741d07006075183c1d1414130506130041034000000c0101d02e003c0d4075010f15611001e840308490341130104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 171637733 1250 171636483 171636497
    0x12140c19020109140a031404240c02090c032403100c170f010f06080403090510050f12070201050603060f04020103090212010c120b180408070f05070303120f0912 71
    0x1403414400d40c0000d000c0342d440000b02008800f5950304c240daa00e40040128000380d01001c00007040e90511080d10304440342911a0001c50320b03100444c80c01c4060348200c0400b0481d5000c0358001682d42c141d0346a0140c010000c04540d40c1c14100b141c03900d0040c40a0105468044071096203a054600041c210740010711450300160f080303e010380444014036040c064405840f4030a00f8406407804981401c1c0c1202c40000340010009c0c0ea580d005d0303d203150304403009004515030650422080c1812040116028007500d042450301903040100b90054029007041d42040940c4001c2144264091049030b4010104070010142490540b082c4030f42c140700140f0090406446335038200843d00c50f4000c82e040380b11000c0092100300d1b594080200340000005100003558146600e000481c10450081d08102c1040ca12280701a0f450340c607920b4480c0c1c400c1e001200c2c03055001d000a030201c3c03400e00c1718001452003641e0782c180090800c04440150362030101d050f00110300d03088246000130b46c0d000e40801d2031502400c16503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 171638983 1250 171637733 171637777
    0x1b07050c040f060512030a0e0f0f040e0f0d031a09061309081e0c0d050310030803090307020d050708010522020f03010b0307080a210206061c06060612140c 68
    0x242c0301079403100303810140e01c40b105d60007090048042c050303800c030175980c0303615044078182049065440407544a8104041e10f2603103c071800d06e0340200b01c0240901d4112043d40350303903035103071458080d0b83c9866100290b40d40c0045410f43c2011401c01003502000c5915003000d0400030001140008003141004010f80e82d41103100800000d00305886034504440c804002e40b00034008102c3c02030744140c4800c86180a0307800282c5900e4001c00503240110f1603403605003c05403d5a0f1604025400030382019041c2c40244030ba400165540d04860b004184501c0140c160386141600844c2900c0c000b0300002070410b04144129a070032100b0041000a0760129500c0246001c10f42c0800c0c010301d4802c0b581d9405008140c000309807a04001750315880b0b1480f4241050710310320003445000712108120f11b03050041e04100701061003890818444038420302030441c25030709500c09540700c4003265120741c441000300b10504039803078140500d1b100324080070082d06142001c034500807400c140240310b540c48041280c1b42e101e00301 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 171640233 1250 171638983 171639011
    0x50a050702030316111603021f1e1713050f0f0d0c032c1503100603050612010c020106060813020904061107020d150c05160308060d1203051b07050c04 66
    0xc5ca980c9500d000c01e591095801c201003258860441c0800e0740a50345104c100b2241c14074064920303641c011555512002244418490711180c00c250560604105440601c5000103101c0c1c0103a0707000702407101003103d2000d128900340b42840c16074010621240c100001c03103c10850003144028103080c040c41c10190500c002d19050740c0e44038185405019a8002c0c40070a021ba9200c404c403c44d4440c81100d031030b0031411441d8144030041c4030881d11007079100000f9100b0400c05000c0c0c0c004c103800c01c4000b45421054100c60310070600310740c001900000141c1d120441001070070f030442c008a030410900003000205044d5900402c4401d0b00180000b400c296075003081042d000701480c1a42c10096008240340c0120180d4104150504820b114403541140b40001e80041c89029004030b86000203d080701c85245482c0e41c90903121400d000304060742051040c03621400150340d081220045034443d8a001510381400180d041d41848030755058062007600300078460100c1d0700003c46c034008d401c04850100b402c2d4444218 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 171641483 1250 171640233 171640247
    0xc0216062f03070c080106090209010504050603070c08070c0306051524091e04060501031404080a0e041b080603011112040809040c02060a0e01020f030a0c1106010f050301050a050702030316 83
    0x180200d804041101020420044c2c100d0046403c0c080c000d020050322644c0c0d21080307200320300c0003d0124a040004220a0901001647d88008035050070360071306405440341c2c0030940c4040000c603049144094180304100c1c0c4c5106e10f03504089a91200c0f40b03010081d0003c514110f0078101c1d540981c031002c078054144a143e0404031009000c003e8500c0c0d5040003500c8031000710309446448540300f6810840b01041075442071103111024040c101c031070b60302610b89889a4200e640603202c038204108001114071000d4a590041d1443c94111840141402810714001001e40320081c200b64821390510400140490400c0281c1c1c1c0e00c130b02499041645601c4901d040203a038880c001078140c0003130030203800414076600070410500c183d1180d0028030034a03101090301c0c0d00b04d110b104041c0041d6a0b007803000c111240403031b60041712030569a0414100d0081d0300307406c3c0c6180c25002d0340300524044d0018400e2025007000e000d590b4120b020b01c101070007a41040c0701d000e9100d000090410801c4c14130400600300ba644910300c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 171642733 1250 171641483 171641567
    0x503090a020a0602010f0509060c0f1303060516081303020309010f05120103060e07090603050a06020d0e01060e0105030c04091e0804030b010b0d1d150901110301090c021606 76
    0x2d160741141d4031540a8083e02d07003480520041c0c1d15101c006400c010700490041d1080c0c0c0c0c020b104918111010416850f0382e0041180020300820380c05010000511310b00c160303400342002000c01c040b203540902c40142100320083c2140c4001c4a8002e8400000350004262100d60b00242042031180c24001411207481c01026010484070a004000200384100360748404d04060b994004d8542403503c0e40b07506815606240303c01030455101000b90300108126901810700351400d554041410208081c03444e00f501c1180d040000140200300040003107180802c24801116010340f802e005040ca140c40300d04626440e641006241281da4006008003c3c1c0881100c01030f69020a402d41c007941c440303601015a4001150741032240b841c0c0801e00e100040c1c85080d120344400c0c1100144120a581d4415038034000c00500300005030340d240e41d907025203242c003000035502800f0308007070018a0300950b040007450001c9401102c40d500c0d5490609018144e8044441809401010011941c510070101c0210609540381 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 171643983 1250 171642733 171642739
    0xb0402120111030a02130f0b18011b1a1b07060902010203121005150304110f04020c030a0c0b0c0c06040f110d05030d140c16050a051509060708010b0a0503090a02 71
    0x4002c0804429030241c0040c2c3c00c41d03407950040f147c40d1381e0794051544581c000d95442840a2100350b00d41c5840c20b150610810f010726003805a11207e114030400c20720f034004115400c1c2400700079141c201e6141d2a0944d80f1400c078080224454500191040551007044009004a61a0fa4400301564003c0040741e000340c640d0059615145004100649024000c4c004c992040031007202408401c8460800e9900823600040080c841d40500c100300560740c48000d0110780c0140e001d00c002c00da804401e0010b40a48044c94840740101801d9291004040d00002c041a691440c1800320302c51491000030b0050340039500000b541814003560800070010002c584d4065071112000e01c1c0c10040003404806045400c207030390307401d0103061454442065041401c9a000c8101c000601003544003003081c85080c400c80c1d001d20155021a01d16845490408004101020703c000ba02000d0200c035000800030558024140d00c1d112005504100c80c902c0035105602c14102001404008984840d6080c010000000d40c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 171645233 1250 171643983 171643987
    0x80604090b1305060108010504021f0c050102040b0d06090c1e0905150c10050105011b03140427020c0a03051b07081006080f0303010302100504080d180b070b0402120111 74
    0x41d0301c200b9880c8001c1c4401ca42e2401020000545040140543c43c0034540c018020809004800341c2e411601400e00c0514080017945c004a102240080c402000604858800b42e075903143d107400110151030081e841056018540070748040815440010001c02690602d5154040c0c455204101c4468100f60012507000601b0b82c0046d181d40048802081c1ca010700c0380c1030312a1a00c80c6200241280c100b440307078501007440b616a03001c95070300c03140e900c00450b44280ad0241d440c8580c4916052070f6081a0011050156a0000b0814102c62813410311a1140090002d40c500182c0c00061500c9071804074006052140218900c0ea40d0040040c40036500d5005a04945c00203585100007a5910b02014100c64961b19021001c135400c100803c3c0da4a04840302401545945d182d58240081c49501c0c6607004100078081c040421213550901c8603800d100046e03034030300203103001085084906800790361007000c0342030041241d040041d44443e02d007940f040d0112110304170b42d440f445840340035159441150221443c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 171646483 1250 171645233 171645241
    0x237060203030703061205120a050706050109050633090d0f0f140f0a080904060812030f0f060123160f06060501030501051806010e1008071202030610080604090b 71
    0xc004003842c4204040d69090024942e00d04200005a041c0c0308080e050f40c0040c181c038080c1e0440d600c01000f40c516a440c107245000303441c3e1129021560701ba0000c0722159100ca050052a280c05090000c8200d000d003419844081c1d550003044004229164840c11208003003255403003666004107001c1e01d04c2d00510035119040d42072500c9184501c2d100701c2110360b0444018154529180021500f010b0144d260040030304096640b21440309400c10107456510030b86589000c030321107800380300032000000394940c1541ca0b030800d00d03480c0e8512103004011203450f030b484408002040e81d000510b1175030300e641802a40303101c00d000815540c4604c902c100745060350105002003002c2140919005081d82d016a20401c0025202e000441c196a020b00c580e60f031100040c1c075114170003100c80100c1e6812680c14104813694130308003030110301181c48074295400825012420460318503000f0200c8569003124035401c42c80c519000e800243c05074481344a182c01c0001c0180051108e454643c0000300c03107500094103054500d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 171647733 1250 171646483 171646487
    0x40e04080913020306100302041a070204020705030a111209150304060603050f0f0f0c090601080c1314010f0201050115030e07170c15070b0105040902010302071a0709080a023706 78
    0x1000380d07285d0340100c0010700c49a00c1d081c0f1910070341d8255907401c20000d200380c410a4401c0c1c595001207406a03400390b820004000064001c000038100281c5030b407524940c0074081c103560740c1402100e02e1004c0f440e60040080c0d041da07544103044803208800b00b0b11800d84036151824003200800046e04020014440c6002d05180e4a000140404140308200d0880d540c003664090b21980311881e820301c1681007840d19021450640c02102002e42c0400036001c894100300510202a1181c4100c0e842505140c201e004015120359110000c68007660340c0f80002d00065142429869042c403001c8070038030403d691a60030301c030f1390300061181c007004101803a0280c0d29001004265070b01c5400782e680152040d481d95070f184216110318402e0320a104c2c0c1119141c03600307a20701020b0001a00c2800000c9042560820400001406041c9103c0315500070b120f42e8400c1d071030078900c06004048140c1012515500010040006940710050700d45051002a4a0903001c036050350f05017138001c0300380d071260049807100e900800c0d229 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 171648983 1250 171647733 171647737
    0x100320071e1b12050601050d0f0503070803040c05120601031b050306010803131d0a091103010c09050a05012d031503081c05190b22020310140303040e0408091302 71
    0x942c6501e6004450351003031480d02c10b4158540003003094002c2c10041113149454041c05807014041d40c20402000d000d40d84890a503444028106c0b4410703004001e10060200c4001c506010f800f0590794008110500032120f0f80d21441407000601c2c5038003001c01c90545104030000351000f800d02800b12038080d61a01c020b0707a01c0307800c0301c2003501d854404500700284030b0300d490144a400c568120414185a00c90100460103010341d00425941080c1644851605440911070502c0fa42d0350303540c2d0315617140d080c8400c02204880c1c0c0e92020741005410311141741190701c1540c06140300112000d9940b00001e6441c010740181a5658210300c90b410010b0000080c480c0c040018043c0e0103030f44c940400d514440c140039604540c001c2d0380c9400060740310300501410201d650312800304d4070b0300146580e01e0400c0039003100c0b00d0420000301c0790032403035004018001414080e05c0ca010160034220500c000c0e4844007004030365a40600d02c503900c054890000481c0078010b00b101211401000917102c61070741e51101800a002e5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 171650233 1250 171648983 171649013
    0x1803020703050f01020301030215130b181003060f092301060c0b070207030308040b0a140903041e0b120712090807050c010c02030607030f0216050a02100320071e 71
    0x1c0c040e0120340a20f0010601c200c9041c0e990007002c20038490200241690690000365408a2145032914003143c40c1e150840034107101242c010841c505107082c01c040c4148810018602028507003021000d1042c0ca42105200041d503110000000720711404002200423110051114841000e0703040010030300c19070200d40b400340e081c02044c0c6403149480f0344034226541e1a06100140001e040100414005055024041e412100022002c00e0240c41716a604c0b400000c2a1411080e03584000f07410085952550901e2004001404000381080c1c42c7c00711051180c4680b4015245e240b00000006070014001c00c4010240c09241004210140f041d280094941e40410340a8a0034070849050900c50340c4100c3c8000c100941c090058581c98079441002c3d4007600c01705041d07070303040d50f0244005419421142c0e46407100c00d004c0c000400310440b180c014490f02020901c5454101400c08010b2401b18030814101500d030b40b60f004540c0d680d640d06040c8480009014085030350b90303802201f00c0c81705102d00c20307003981c40e2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 171651483 1250 171650233 171650243
    0x30902010315080a030801080705130e03090405070e0a060806030606010c0305070615050f030309030a060c030603020607060603061d0d0e0609061b1b011205040c120b1510020c0906041803020703 85
    0x10752340c0b00c4100c3c07a641c40c521b1050b03943c171000c442403411071007504c0d8109003142600c41c01100d0521250f100014140c41e0f044690f00000390340b581a061082c640071607190000c0800342882c4c1c1480c10010003190310f40e0001000107050001a110f81d004040c86030085800c1513401ca4002c0141d4001d600950307241c9401885000d100c3c071001a82c2078240e140102c12038582100c0100100050b00a956402001c0c03c1d06910700401d155403808000b000d6180c003802008420301c22000040d5540c158a40801128504504c0060f074500d41d1090301108a000507040ea80c015180c1007044c1d032105880c00081c0f0511500078441d410010210390300c0407801002040d4400303004010160b410345500c09050741040029001254000780003a9584840801d00d648003541040c09290200701603030f00c902d0540441d8003244c504035070307801396203080001002c50f203412007a905000b102c4001c0700b1020300000950f40e003801401c441c4102c113080d02090b0306603541e03402940410200206241c801140f401e010b074070f5094900c0103480d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 171652733 1250 171651483 171651497
    0x209030709060506030703111b0102030a14010503030a0507051006060f1d0f04021b060405030304060c090609170c040614030c04090528060f1a010c12030902010315080a03 75
    0xd6048071030040b0819544058a082d0942d550540124007a282c106401080d000d810030504201c0c081814060101c205440d002503a41d0401c4003040c8100c030240c00d8441500580c0c4001401203a50100c02c50f80307041031078504107071112100d0a025081c6403a0100050320303180707000d0001038201c0e04000c56012401c0b2a4881010041c5c4620b501442c9902d074154013544075002c401205d06c14602607014000c0e00300d000c0120b101e501c1c40f10758160b2518101782d4003a5000c2c0d001100300020441240140c2d950b0112034076064140b0340c607004010700700039540c0c01014951000b40d110980d00300801c00c009080f01c0700003442481419a20f204040c015000d40260900a004080f841c1c152410103014600903964001d000b800131054880c800340c4041c4c414901d041190009038007030004651140a5002a040b103180700043c0b00328444943c1c044030a41c2c81c1c00030b0602c0400390211000c42e40740e841036003a485580c1000b080e500c1041c0300490050060514150b03001004031000f1030480000036541c2d0340d83d842500e800c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 171653983 1250 171652733 171652739
    0x5030a080f090415031b05010206070c03030b04020a0818070302010503070509040b031203100605030907090207030c1a0106084c080c01020607110c19150305060f0d0512070c08070902090307 83
    0x1b400c0810140250750160f8030802c08038400c3c4e4450040c20b40014060300c1d0000d5a820220001001d030f9201c42c19281c00100e40005101001000c00351400400c031035000200a500d00c0c55001030b06c103000c010002c00c240b05011404140c3c9403501e0b009010340100c01400d445e03000c59044191159908261240ca0f00c580714280c000c51100e001e101101e005500041c02010201d1626a803807020b9070244008808100c50a017100c000100420038000024a101e8502c62542d810440000c1030148002c03d60450340754880d4054078001e10b44159190112000055480c08141c10210022010103100c2d86821450040100148074800450210b0951400360b09036a481c0e11011022584074030141050300c0560082440c40f0014501540c40f40342080b103081030301d024a80c1d5281030007400080da81074800405c0d15001000310324601000d062400c110100c806868a050039141c4559500711408422003646002a0403c207124403448960000c0103030307504485001e502c807070140300a5009070f1503003030007840392800c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 171655233 1250 171653983 171654023
    0xf0718090c2c0108120301050d030e03240f0c0d0f1107030e10090b0a030b040b060a0f08010906180e16060c0b1308030c090a15031e0605030a080f09041503 68
    0x150210280d0111651b041d42d007001c040110f194003003481113081c0019422a5101d60b14240a400101c01049200d0042401d410380c118003582c000030300c2250750f00208410842200d400005642014030040400264244120b00040c001d11545010074144c0b0000300e028820075a04c50301c1c0303102803c01902c0210100610311019500c0103104e0143d0807004400384800c003603481c03081e4040d44d50300400074404501c03021000c0100b0000d038008044d410005101c400701d000d034a604040000c5c01056076a80811181c0c0c58101c81c2455015050072015807d6101c5004651480040115021541c0c081c0c114656440d550308000c2c1143c1c0c0100e908441d00310300c040000e141440444203c1c510700e508680d1503031840d03846e032000d007001e80e000030403540c0c0c0030007424030215a0750060508104004602d0b10700085154090398041d5001c00c012031510211401d1003002d2185031000720724415059440b014158884210408504050060340c0403941c10a15250f01d81d00e0303c0700c20024200442340190201400c0075008441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 171656483 1250 171655233 171655243
    0x30d1508060412111204030609060c111002071109010b0307021504020a060c0317090606010e0f0a051c0b0903192f0102040e01170f0718090c2c0108 65
    0x203010a20802075414183c1e000310704508821111006031030162110000341c00340c0b50081d80068034100d958010740c40401045210310142005903080841c1041c03000d11280e591030503102c08002c02190040f03071407420841d400f4100031035004c0081403c0030f550385411141d0410741040f24110018460340d10341d240c2007202c42011500807500070b0071a407a05400c0070030030307550340c05054000c80400400301800c00046800b08012801804000e0280100b410400c0004090f200c0303c0c101107100c4c012040c4a0b2400307542e01c1e03907030601f152000d072140240318442d41142054100900c2001e042d400c0c003401003206000c0084001d1031104070440721003a0303220011001b103600e0030200c01c4000c16824800d94031300f403002d05e40d060800100300b038000140c034180d200d82030004c60b8442a84030740000e84448182c0101940709004556000391400f00a049151034070300c00440d5030360401402d01030300341d9901440c014403800e988000050035500c1070030144000c1001035062003440e4403c01ca00b520000f100003003003031000454 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 171657733 1250 171656483 171656491
    0x1080403141305090906100b04080a110409021203040504050123010e120a140f210703021908030601080a05010503070e060325150e0d081605030d150806 67
    0x16075100801440d00c1c24070015402080c8499840c40c40c2c2c1d42c0000c0d20783c3c410140b117110b6492240684141d0810041c003210381c40194104040b041e10a000a1000030070015219410641000f02d030304440c500703807010400070f000c080300c0a9042815400c00c18406d0754000010000c41c2c0d8141c45c100400c0e030365100749081091410100c1c0c1900c00b040500d5151943c41b0700140e562710743e0010030645c11491240c0400d80b030000440d208480d411842c0220787c0041c3ca0600c41c614400203040d02902c43d00804442040303207080c43c041500c0e0000000704013030060600c20807210281b402e111002e951044018140601c40d0f8204480c0c00e40000c0c5402c1c0064943c88240c000d0034100c81002c7e00800d44141000d2910400c404010030054044c4074200e840c0d0352a030b0b00c403544e407151814035102001001f401d01d600716000ea00819258410f010130b2512412540d150031905810752500205100d81300c81c526005810041c01c2e603134020b0070600c804038030705481d03149590041c4081c10314080f641c207082d5500e2450b01d2321107800722 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 171658983 1250 171657733 171657737
    0xe0609060d020d0606050a1d010b57060601020a08090f010c0602070b1803070b0c030405010e01050c0408010e01060f26030307020109111906180902041d0601080403 72
    0x7a40d01c80040c01c2026420b51018070941000ca415a150030100d100645981d01c42c24161124555003c500e8008492803805400301019261511b090b141c4503400c104001c00184148207100c0790400c0b112200f800e0307108a1040f00810281c03a00d41e4921204001302c13560580703c00c5500844006c149251b00008076258902d034406011410500c2c46000c06c0440030b18140114148121950707084000b030414402001c081d8400c50102c546410907801138980407081d0f80310307001280d10401c0383c180403800e4860403a5002500b1800315590756914540640075107400c10b4494203d600388014040050881c5000d40b0503200300300000c1190141618025003665094490040030490300c000c10301403c1c1c83d00b0440044100c0010902c41e84032504181c580c910f41c8110ba0040050355a02d200342c041042d5035007181c292440445100e0396462210515003a10800307485400103100c0400c12601e00501441c1920005241403035085480d240d03507102004c401040c0074940040310300c120002038469030150420500030364041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 171660233 1250 171658983 171658999
    0x90b010509030d08061c0507081501030b0408030a0b03100e060601170f040c0e092103070f08070908070305150106050a05031302060904060306020712140a03051302030303100e060906 80
    0x212007503030138a2020344140c0e080192601c50300d1440000b25030b480c00c0c0d00e1180004203165454000d0450802c0200401d90184080c00001080400c001220442e040744c0c1041c80c2035580e4a40310000d41c014181c0d841308503018051003603130450078003d650198250008250640721903503180401120003110360240003003410280004941d1440c0e444111541c8584243c501d90162522000045540d440840e080401076012080501d155244c2c0c09000c07010540100c0078a040d070500000103004154980111420000d104001601141c400e90000004217085010740c1d2a1640380e0421544070f0225040750710070f4040910000034014840e208640401800303944603411070312014070191031001071860580c2d10003c180543c9003996650710a900040d032240c0001a52600e040c50140fa0815400d502d4905000d040c65000000d00b60321002c0306c1d0b203d541031400040036620b0080015075402c1824001e90144000f108110880e000109000140c484a12111aaa64600080000b5060100c6820780c011840e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 171661483 1250 171660233 171660253
    0x3050f1c0c110307080a0804090b01090506093010050f0103020108010302060307050705070608191509020702030f01020f0304020a0801060f06050a020f060703061a040b03151f0504090b01050903 85
    0x2280c0300c000320b000010142c41890ba503c4071011714103052500c0c01d480d04a800a01003100002074807515000b402c6c00c1c2004513134070f441e00c40080c440b0b0190b146d402c0d009540ca100c41da170000c103107035102522010400f00d180d40c0511842450139035444512042c01e4083d403070403000c9a03541464100c024100e96050703460010703682c00c56003400640d070006010442030040c1032080c0710004401b48141e00107007034240c1c0da5400a281a0501c81b05540e94a900998410f192aa86030007000c20540b105060b56171600000d6512601c03440031a24154005950115a500c04940319564420260085000c0c40c02100c0d043e001d00e0b01d4807005802c850080c030444510718900c580400809002d03101a00d2034581c03900540d800820b603c0381480c148201200c8450000f80e0f20a0180401c030038440e001c1420340c03009000c440c01d2609040501044c1d120107031200400f01100c6102564907500d003100c944045185c000e0034440801d89420160585c0c0003409810342450400c0715928941d4414002e031105038038020010400424 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 171662733 1250 171661483 171661493
    0xf0603020c120a0c1211060c03130c090f0e070e040f0201030e010c0c150c0507060e03090316210b150102010e070b0d06320f0a03050f1c0c 61
    0x100007001e00650b401200e9040c40d6011652000c0c0840000c1501c0d84000d60380580342800c01c1429449040d024803a20311520542c640340002e106a1000b85840c600b9681d844003240000440802e5000a008507840d4401040c2c030689a088400c502035045030074814814218213050300c60015001e100c03e8401a0700002d80410000c400b414000350044c1400503170b6100e240003003429202d2900200c000300d060f04426000300a9902c940507a0484420420402c9158103072008005c0e2040041c0500b0190320343c080c00c04140014011140340c00c100808407403968184401c3c4c0303a5101c08521941071100000b40d80c40344e0010120040c4160315501038003a019580e11411203000445405c1c40031411590391780c40304100e00008002d000c010300b080c0d540391034444d40e800e040c01c0c1c203664860300403402070144500c6119050040340095103010500e0042d400c002030500c0041810b000301c0303e4180394058440200003003030240c0800c54110148401c4103444809400c20b51060b90710039a2030b0040000381410b0410384c0030034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 171663983 1250 171662733 171662737
    0x15050a140d060f080c0f03010c17091507180504060506030f0405100c02011418030a080a11041401121a100c0f0b1e13060c0302090d050601080106050a0f060302 70
    0x80c00007a40056000c0d283c00c0340d6596500103812182d516404010340d01080e240c4500740d2901e5107401c800038080b800c0040401881082c0c0741110100707a4075100045094140e0a009113040844540c0c0740401c07501d010f640003400c00e43c402010050344429124081113509060145000390f42d0090302080c03940d02c56903c1c0144074400240300fa030f4030380a24a040c0c542d00500d4026006a40c078150b00206854240320403c3d0307424900980b030821140d2a0340d60b510919000070003595070201d070070705005001d1b40d582441c1002a1039040b8183d01c8400700000c0201c6c07121405203601c0722514083c0ea13102045051341400d00200ca040303e14100020103d40c1c2541e529190012840c52519298580706140729640c5e5912000411561400c0714110300c02170410808443c0512001d60303110170910000310300d04040c54070091145c0300d000081c08960300c0f10a11060a0f00a40440d01d140e2006059106c900c0c0140c1005900ea04081c01506450350070300c02c00103014a0b054500101752100440351803422481c0c40c00a87c025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 171665233 1250 171663983 171663997
    0xb1e0c01020c06090d03110304050c04020f070c0e0a0c02030c100b0a08010204120b250305060f030d080106031a063c030103060b01080702030d09081b0715050a14 71
    0x2907400700310600c031244040c02a24040d1030750f40024012510000d2006d419a10303100c00c4480a45010300422010070400100905034040070b0702c0050b9104540450300c001840b42e03180103010a040d012002500170900c00f034080c454808080104a94900b050f001ca031680300f1541c00e03c1e21a4000c1d410562071241702d9000c00441c000090140c120079584962282c01d9030003540c844421600c1c80c42d000014408046c801aa00a180004180c8900201e01101242c1950f451040341007507680c000041c1641c4900390b132004083d9004013111010303004442c0007002050240500b100080c1800095040380a56010014044400802c03413418000c1e9940c0c14800b411030444008103980c05601822101c40d1508184500c50000807896aa02d60640c1000015640c050810904000f0008100321615502100b42c42e40743c2c0b040c0340e012400000c4d41c2031052850184001d00c942465540a160000d81d50000f0b10074100d9190085a5409020100c000c1c0c603d0700611420b130020600114001c05480000d80c010200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 171666483 1250 171665233 171665257
    0x150f0c06060108040b040b07210b030c090408040608040c0302060f0c0c0927010b221505010813060902120d0e0303070203070621020a0807020c0f0a0b160f0606030c0b1e 74
    0x9d6411600c500801c503a0b10800501090341da00c0ca011135160038113104152074035100707480310b0a640c182031b1b448100f10b00c2a48105c8041100b05c09c0031800f0060702007004c20003107400905150711903041514049241c1d0142015845502c50382c0c1109000d428000b0600784245a02c5a008140c51284481100340008408181c91555070b00c00d21115903a450b204114500c00e00200012a8080c0180c840022280c1850305100e4003401c08a0070006a030340b01c00410361000c82000c050b507400106140903800340424010082d84a803404a02d03501004000510111100056607940e10b41d403a100107150302c0f84552440030b501a0007804e0240102c034010f04105038148001c4402c01b0000601052503412604064035800001e503003e0180024560304002c800d0030124201e625840e015a20030001d04415002d1064003018580450550550300309401c2c403d144642101d021000e40559203003008c001c200350f000407990780140903004030340720000900b0b44454070720340c1000f02c0b03c800c0e6006c40040c00750003c860b5100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 171667733 1250 171666483 171666497
    0x7080903070e090609030301050a06210606081b0408280b01030302010204030b07021911040209040f0f05071b1b030516050114070807020906150f0c06060108040b040b07 74
    0x1951810400480202078250000100d42042010581022005800c41915038005e01c0140502d9440141580407130b803050629542c9444d035140c8802002000241403060913150041c0050b00c00c5d00802d2061283c141065043d000327080d003054008650065004401c501c3d408000c00f0391096070292a001284100b00060b40000101c994980300520f509070012401030750042020010460117410300c0e03402c1001800a0070b40c07540407030400e030181104000e0103059000c0c101518861a200c0307504035914100068000c0c0320400d0903001550160020a2a0101192820300028601803144c01c20040300c864011861429401c0c81d02d9040089855100b0807102e03081e00a00080025802c00c111855040c08001045965160a002400075802444051203a110030132038070000441000440d05d1183e070490300c070781c071a44403a00820401d10115500071803001e00090307000c034100c07115400340203604101c80803a98180c0e00c800c01110b400f00261030040c00c20a910001c04c00080044182c0344e840040c91404003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 171668983 1250 171667733 171667747
    0x11107031407050a080c030606010f0c0609140709091205030c04090507051c051e010602030a032a020601030c05010c110405061306060c02011101022505120f09120f030f0708 76
    0x741920599034417a01c005e82c40080f00c0101d5080c2400100c1c0d200303d09082496190804501c05800d24540280003400c00d680c0310214020091480181d00d0f41c2c1020710f080f11803041c0c543c1c0110380100000c00080d0341188805146c8091648144201d034460b1001081242c04c048c40c0c900d0140142c1030181c80441403010030302c522a45811000c000180d00541c61001040c5424240403c0058080720100e843c1030080d42c20042c400140c00104036100e00115140001c2c101c0500404040700c074000c41c0c0301100c84403c40d070040319259030005105051740e000302000c0c1260b903600c0307006651031038560000a00d07124101520201074a070580c070507684003502030b01c0c48011701c444544050890304960010001300d03042c407241d0f2040d5644200790104447c0d9500013185403ea10105049400d82c0304504641142051070054007006024440035410b0800060381b03d80b078084483d40c00085810030604503001d08003404d03090540500002e1010080c8070910055490114a0102c400c5c60f94090301040d90540d100704039031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 171670233 1250 171668983 171668989
    0x30f070309080a0807060e07240e0a0f03140f1507230406090815060f03070e040602030117030a09050f1206100e1806060112091208040c0501110703140705 68
    0xa400f003284220762030f03561004140741440c2102d080d1014207545900c0701c0c5040c00401404800d400c000c28001d0346c404413001208800315616410260041d403c400340c1c92002955840702984501580c0c8a040811a00740c544181c5179598080c00e80041c00e960700000d20420015a040116600300c502403178000300c0443c0129034482122a4034182d120380020004007004465030005902d009840c494019001c4010380da4035040c980e0ba40540901c1c812108404c4c11100750f5810804017008169141d000f00d210300e014100b0400a4000344200e0107980c02d401c650a16550022089544601080c3c0310106901e00700781c24414141c180d524480c2c0c00040c804600410700c0c0d02084194401c80840f04501c03404c50800b070031644408005840708800c4c07030790b0503e0b0040144011035210750046081c40c241c0c20407010480d10801500340e450001d0038021519001c000c0d8117510505080c8924001d01c0c00313804065541c0d00444802c01030f01020b207256005810305200044c4030162103045440c40b8012140200d40380c2c800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 171671483 1250 171670233 171670243
    0x7060b0402071a060301150506130e070c020f0109080604032f01020d0b0a0302060a050c240f06030f070905131a1f06140705010603141509060108030f07030908 70
    0x40d940b8400b040c12a43d00d12000c240d4142d40328109030020710000148011400440f2020700445200e0b00011440700c1550002d00b12a40040007201e20110380d07030818000c0904613003500341c810b0b130041c2c00c202e840390b0341075001d12180f00c229030b03c4000406456480b6141100d1811403202c03601004100ca00f50700314240120814000511092800140d40d1404582040d04480f5100d145c0e40c061040c00200300050390740e52040e00c03980000d60a1060b521258101c9860800d440c0c04c282c0300060f40030035920b000c050009901688110110080c2800584904041507540c20360110381142d5030780068014402c50489812507504103035079414420b10040c460b03945607140b450410340c055803022010108002c1200621100d2a1034103d103000d203610900f0000000c001041d00c501c42a0300303c0c0001a400200b000942c014401103411400090380100e03850320640d01c0740c42d000310303c0c0d000022003404240c0c0184c010465504880310b6800461401c0c06c80c00c9440616040a0300c02d0f4148031a05c01c1c005106801402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 171672733 1250 171671483 171671497
    0x5030a0906030e0a021507081309090311162309040311190507060509010e031c0f0503090703030e06041d1b070b010e0c07020406140306091204050607060b0402 70
    0x3180e030505401d01c03030001e08983c0b00f01d8000c01180c0c4044441400750b2107001c40550005009442c280e910400d908080100744501d04102e0a4440500c01c001449101548522000345c0319981c0c07800c403416998a00e55a0354203c82e1600007054000e0000c0013059009031b6800d102c03140c8902c1500d0f00500300d000040c280201110180e01180400a140107078400501c00381c0b1a084200c03500141c6c000b1692034035a510700e164090101030190001b540401a0b00842c1180c4400400804807400b200418035419030401c5008803050104540040080c82580070304203032032181c0c81040040084c0b070300d07540303044070a400003200c010b0300400204000318801a5210f0002040c981801d51801d0724180031a0002c0c44c3c01104441c2a20082c05000d0b80d4006018041380070b0441c1e06c01d050030070064031509001c949034487e2705802540180351210002c1e080d107864190030410b1740120240d034201e45e134060ac581e4840101c861080000b0a080000b400103181c03400c050031260b0f01503000080c1c3d0741d251b031000c18100e80c040c1d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 171673983 1250 171672733 171672737
    0x20d0f0f06090509060c03010311120d020a171c0903140a03090201120c081602070b0703090504051006050703080a060f030b060907140409110c1e01152102030a05030a 73
    0x1c00c06010440c114040c1c1a044a100b0005142a10b03000040b9201804180170081003001d9070704d2104026900e568142c0c880c0704080d020b0359407440b03481501941e0782040010407507a45841341103941304004964140c800248042500712944401a1503c500402002c90210148070289080002c0c0d00504000740140c0e42c8503403000220020103000151280b000340400c0e204007070a003403020441d0b03a80700d0107094201100c92801003c180040b0411fa0820a0b25000608a03143c0450700318240350b440510310302114403d07103040280391a6240044141c29a5010395004076a0401840f00000e02c10314036143c0c4900d03030f0800000d40a0b19400c0708882c01040381c0c401d48011191074103000841c6842803046401c00002c0c01c00000320344155883c0b080902a901c81c0200d4030740d480c400014030500070302c11160b0181005090395101c5445d5a1420740342e02202e002541d1039032070705250740d1a094200380702c10262111030b50121b46c10b000d400540c949041001e40c04a8050040c15070303002c0060003c202810a2010503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 171675233 1250 171673983 171673991
    0x903010f06080f060f040c03020913120207050a090c02070521070b04080c01020604050d0e13060f23010c060506040f050c0306010e01081501111606051206041a04020d0f0f 75
    0xc43c0860f240c000060244482d4041100910002402440c1c800b81201d6066030b02c1e049a582e1082803500c00d0b070341c1b8800030304464403001071120340c141d001c15108240d0381d04444010b01d071a00d0746100300403640200800005039000e51414091440c0ca20400e021141180390825442c1400c4a0503034104015035014039a02c0703074082400d020018040c003d00d07000280031710040125140070340b105580c46200d034040700280106421400c01c0c948800c60700c1040a400018148074150361201c499940c0e09580c0f0840000b00c40fa0b006d912034000c920120b4072000c0f80140c0d40c900004100c0c0c1c8461009003805810785034490354401851402d002c542c0074107446400c481100b15101d141c0100058401e00400d16407504200000e400c03c00b02100035a09000302510a181502c414185010f049240520540450ba030140ca075030b400080460344940100f00300b100f001c000d118541c4461080c4001d0b504100b03140e00701114002c410030003e0400f903001e0002420340100104640b07120751803034011603d00542e601c1e081034403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 171676483 1250 171675233 171675253
    0x91203203903130b16030e131b08060108042a080d020d180806130201200c10050a0f030b040b04060303080402030c151207260702070b030601090b0903010f0608 70
    0x42c40f05450001d107208407006107851850541440701121030b4030020705000c11541102c0d5140c43e13120140b4241802da2204100c0c240d140718840845400c00c02013000044e003004005000da5124041c000d019031380c00712200404a003810070010130000a00e2507400308400a850001c1e40c180200020482400260040c2c100c06080708030050401000ba00c5d02c0324002d405480c1000104000542941d000441c4c24252a60101510049400301c00a461a413001d440969104074036003c0031640503c0c03894101e501100300c003c0e40c0000e1b1424001c0101201c0070421244214191a003e0740202c500481f0040c0b0000e40112290002006c032556a042500003502c8030b4208000c604082150003100c4008442c08030003441049994151481421640c04000b44424007148140c2d000f50644ca12543c0751546007040d41d0100314003146001d8040329060014400c9603400034000040320112402808181d48e417005050030401d00c1c03d002e901c010003c0b60599030b20801c500d0a100148038a5002d004040064105500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 171677733 1250 171676483 171676507
    0x30a0f0506012604060204050909030c100506091f09020a0c0614040506220b0705030a0b220e030f0c03040509010b04050d11060706091203203903 64
    0x120081c4902d0503c0b8502034900711120102d1110b2000e203000096603a0613556a240000c0a4020b0740d100381d402503410010302203011008000b41600e100100d0844503040f054420500a5a000b6580d05400189500200748503441e000c04005070341c0d4000220180c555500d12000089901403200180020303007011100f0708100003806403007013100c400c01d41c444460400c1d132510382c0c603290060195201d55a1161070501d2007030348015030b408042c0d0060708a5296140c00c3c68044c05680c0f0403100203810600d4440620703110701d840049003842080b8001c80031041540d80305104001c2c41e11180100c0c0c148404d02030a4403085c03c1030002c1c4051002c900103951030f01d250409100e03809106801c41d2110034418407061016468020008018980124042c0c41f0708950b00c000c222144107003c4042c010f07609126621003401482c03544528194050342c1c0402ca079580c50151900840c52072000700c0c3d01aa002c01440c2100e2282c8810081800042c903185c10416103800e0b040540c0e0b021560b13000e10190800f0a00140843d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 171678983 1250 171677733 171677741
    0x1206010e010f081f02030403140309010207110303030420010c050715031d03071b09181103030f1b1603060501080706030605030c0907120911030f010e07090902030a0206030a0f 77
    0x70f901c10062003c0c4461035040320f400700504000031500c9901100040625200341d401d001c60140c80030580d55203003050310700140030b9804500c0984079407940a40381040c40c1030001c00ca82c03055801501201096000d004400c42c0c007800c4c050300d14104803241c071031603010500a1016200400380501025544180d01201605507a2000710149107000c4200c03844007072490100071600526400341c148083c000130120345801d9540580c20a044080c90305e80c50341c5041b11b403900724a200034040c0f0011119100000c0c10036076244a414001c00316000207104044120365910501140041003409952600001000100001100d030f84191703440c41d259001006881d105000700c0002c0c2c0f5152405104842c01c02d40400c0d501c2a00c401154062850b04001584440c0702e0505000c0ba01400d010901003a5581c0c100079000c512007004e0307984680203190036000c880070144240e40000341020094580f680c42d003030340302c001804210801d0380c0501440040000503520b82000714814211403000140c2c221955800307030304a03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 171680233 1250 171678983 171678989
    0x20f0406080a150203070807050904020f0c010c03060b0c0a060f02251202010b0907050c07170c0f03190f0f0807062304080d020d0618020405030d030504110409021206010e010f 77
    0x5071320420501c004580d00c046959448041401d01990314014803010074024071601d12211804040440e050400c100103401c0700e00200100d50701801403580380c803d030085c6485540780200e4154007211031200000c0e1030343c00100d031452600e00c0042c00c0c14220741401c4a03000030b9240d0114202e2481c01c1c0c02003040048088285462002c0c07008002c080000800304010310070141841081c8500450720800d400c1c401c1000c032029100c81c503050241311040d01c00d09641c03001001507031845500f0b0b0310b0324503826050014450314644d01030004441403440d00c3d1501ca07400c131540c0405641a00744c5122000100d6480002003080da8400c440005031108840801c80d5a01c49004032410805003640901c80400d400d00d00b0340d001d01403400e0f4010b0b80c0301c0a18581000828160b8401031400212803a0b4041c60000c03540508119802903056801720500e0510403400ca45049400400786400e0813460326007400c241c0e000d40c424520151411b108490602261480c055090307101c03001e540f074150010301c10205085030392402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 171681483 1250 171680233 171680273
    0x60109020a0908010c0f0e0d140c03010f0209031902130603032c032a0d06020c0715210207020405040b060a05040908030f07020c060304110405130308040f020f0406080a 74
    0x64041782244c000c001c8407492003024204070382c501105040b50343d281500207051380d00c11984480312810801440e00c5585403905107110b0b5103080b038100030f2901c4600171580b0300000200034001e00e02c030460400e0018401d644090b130304901c0d0b030302203850700c03c4040c89017401070350294a44c009400e210441440788a803c00345500121912011001490340b000108980702e2800301c01044000c510087c20f2008940720b0010280c2c2c00078001104100703010b0590700500c07030042c0354400c2d40c003115120003445a03480d484143c03034400101c54202840700d000c14404000500c2520f01800b501e41044c0e030700024141d520503134090307440c0c007103410900101d40750240c0c442009100a82c0d051001d00b00c1078070340c00da242c000144001881c024500004d40221310a000358002201c005003101e85034103050910000b00102d408a8600640c50300e404038030010076105102102c0d0798190f807031a00c2030380d03580e40d000c3ca0204032180403600002c1400741c0c681304e0364541c044c603005000124014002d00015090214816083c1508061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 171682733 1250 171681483 171681491
    0x30911040207053a0804020f010e0112020c10020301090c2c130204050d21080421020a050f010c18050d020105030c07060507110607020d020618010905060109020a090801 74
    0xc000785003c940f442943d200c15007a0351307110f8100210245001054a500651390260000309502640c101d0741c2a030040d4000c1c1c2e00d40c034000711080019140a031440c1441804214164100701c0c82080c282c0050040d0000603080c1d905400e0008082e100761781080c1c0002e40400c1e100c100704144140e008480880e0250b1180034400d1500d802c03800003c0740303020120340501810350401c0700041b50348190102d0f802072030003400c1e4a20440d03850906101c40016420610225001c0f100c60780b1115120740e03040303401035411544011900e0820f8550f080700b08a030103101019030080400c407030041807082c040c0f404410300c403800201d182555908014000c903a5820610b10300380882c0781c10b00060b151480c88000c11039080c24016640e40b00c400d8855098000c159000700071b0703030520080102642d40003920540e0b00c10032fa0112103243d00d80070426a10b0b450740c1800340d0016444100027070684082d0416080481055600000c0d14042e2a119581010000d8100202c4203800092802003260f02c403051a00401411000304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 171683983 1250 171682733 171682747
    0x1805070807050915070609021c03020613030c02090703020a02120708070b0c040e0907030308010503011a091b030103050f060606040609150302190903111c0f05070807060309110402 79
    0x280c050325000d0100c104001000c1148800c079254480c0481012000e40c21180c1c5407911031030018040c240f855800c9000301900304100d9000c2c2c8400480840455264000d00141e6580c1e8000321100c640e2040c2c20b404200d16500000d0143c0c0303403480d0507805101550707005640c0e9105980c0191505030301070b40803904210200b2402d4040b80307201d002d403901d071944102d11100c25102c0c1580740d01c00d409250003e0014106403424004640d00008442d4100c0e80301741c50b41c84141e070fa5942014201d4188113891061150f40d061400454600854060380c01108519080600c401800ea41d4503681c000340c00480310b03980226180d09200c1e0080002d641e2114080743e03858038080c20000010242c0c0610711032402200404202558910700a8041d10307400c0c003111451002203842d10b0401000700350302d84416a14501610104415414180750300068400c5600c0c1c501a030301300960b2242c03610000c0040607522400350200104110805000c048018080b540d8045001241d50500040120f20f000d0100e01c5284108851 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 171685233 1250 171683983 171683987
    0x21c11030301090f1103010b0a0906080402130b12011d01050f010312030209030309040c050909011712071104050430080a0b04110406090609080c0102120f0c0d09180507 74
    0x880c19a501031102060788913458004034081c0140307034000c21104102000100320102400090422451140e0700c405010b940d41800355110f9005880c065002200350443d100f8104042d0460700c0c052002400c150041c100e41c2030701c14212946400040754004080e02c02d600107201c03d0007056000002030707850380c0c21075245a07605c2d400050715408200c10701d07030080b541e0140c41d902402514818640500217004192010400401c1944024002445180444000f00742d8610f010001c004400214009061410800724002900d400c0258201c0e43e010344007903424001d44450189900607885184180c100c801031b0080140161000c030b1202ca61800340d4a00c010307507154404042504a110641e000500c0241c50004c40c020345445210b01c2d089400020740061001c1d440a245801c403159560340180700d07611420501d8440f01c601881c00c1c0103a00c5080405c00c98400b1000400d04071091082d800c0c641160313603194504110034030509001180d41d46804020100c01d2034190081b0b4201c09404019030f142113a00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 171686483 1250 171685233 171685237
    0xf0e06040b04050a1203050103030206101a0c070f08060f0106020d090306050c0c0109111509090c030c070c09020a030b060a020a030806131407030c020f10090c15021c1103 75
    0x2070010500301020038244101440100c0000c3d0b044042c140b024151418060050700003844202c006100d06400102141c0b902c1311b00e80181d40c500b00307248158415003404010300b90000b500302802f83c00390b000000341401c10b20720000c004000b54405070440d40341c0384800107000c00f4142d01c4070043d9040340b480c00c004d040e0311103045030599901c441c2c0040d613521100366490b02030040e50f0700c8018030f40ca0500c1220500101102500c03001d03c04898480c8804421510324415010318400b480c0c00840c607001003140b80201c0c0c00076640c0584901c201c20305000c2661900302a0301d5550b40110034565000840c440400ea15000d10030124505440542c905140104003d5650484031800707420801c05002003225a0b4610700d465a416480a60620102114000c403070600f40c2d00380c801c034002c203140c50301070704d8101c1c0045244250700890b80c1c06440c0016030785401d10013901d07511008807481494008080b640e00044140c401008809600510a111440c0a603200c4c5417240646942400001e4219102c10400001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 171687733 1250 171686483 171686491
    0x608160819030e09220b160e061803030702060f040608010e0103051f02090301020c15010504090506010e06040906091b080106050a0302270103080a140306060a0f0c20040f0e06 77
    0x10b5010281e0b655500c480c0a10004a001714507800c0c8184d40003040c8110038041700c0c0590001c036001c18500c0c0001c034007a6030701600600060b030810710920440398184a0004a88130504019050f0fa2030418141e0000b441640109136643d00005c0216040c0309056103c04078901401d203440070014a54119241c040c3c1d035030240e034121064400d0545a41480c102250142e5251300000f400a5440e041201c10468403051f48130306e844071108040c000002c0c503203030601038007808036044070242c040340e400d007d81581c0e510b0004086540040e10b8400c43c02c0051907c0c4107a002a07401201c202000d030110310303401c4180070460380c84096503030705180c03082c8141d03550a203500c0101c940c101c8040c440400c2c40100b03404014080c42c82d8800c4c041030140000300f4800c1407401000f91505650310398040d2404c00f903083c1d005000c280d41e000d03003011003800070b4050700d40140a4241d1850560400d1181a225642d402d04514424411007403d0079661801050604150045100030207900300d0a021794001c03008115500c00f0014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 171688983 1250 171687733 171687739
    0x211419060b03010c09030807020f13020a0210022a0a0f06020c10060b03130f05010504080715020313030e061218070603090f1b0b1908070206040209010b030a0608160819030e 76
    0x14648c8115503070700380c0710100034001404103203c0d084040381d0b0b0780007500000760704c50150140122a0030340302928401c0390130301c4061400c0c1c0c10300450b0311400310380003070b0380820b5142c0540b0400c2101c00201d15140c500585252040704050390701d12810000d24207110011030340700d01c140c0c2001018403100c41144281c991090003484420030079821806c1124242d1407040d07014080703520b804248018003891034005c024071400391011160040b1103034400f1049101c2110000c2200141c036440800084c441c100404080d0001010541004800c400c2a501d0030803da0300d0460000d05140b103a000c5500500c801c0c0c00401e03031410208021282a156200700b0960094002c3c44034114a4204e8581c040c1c1904080c003074200c6600981c0c03078290480142650a21a9038101d01241008001400b414800514144544d81c0a08003c0c0680d05e441201d688580003c1c00d45040c03140c1f2040003140502081090b412814003e003d0341d4a1a49400c0c5164105091b010780301501c9440100c601001ca034100010035a040c0e816 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 171690233 1250 171688983 171688987
    0x14010f09140102010605060c070906170d050a050d020a0908060c131202031203100f05063a0c081009020a0507030c030201090816020f0109211419060b03010c090308 72
    0x201d0040303006020710380001e9404030780891004100800010200e05844580808000a60f180c0c0c21412a58004112480c00c5501540100e140c0c01d100e04040c20240848e030401c41d041010755030840040e40c000c200c4200000301d150703104002c58101004180d4001c420f4200742c915010b460450300c84011403d02802c18102d10303868080c41151030820040358007200c1c00b484291281000503440704810760520800e038000c4560680450035241500c1155240314404c000c4100b040f016040c10201010765080482d000c00740001000011505405002d10308142c82e50b0304100da2801d02c90f090201c2030aa00407a00e02c0e40b050204942881c1c1200498000c20f4050402190703400b183d15080f0301620000000500400011a51000c1c0c81130b5042044000c900c00c807090894207042c207004403103070aa20706c144001e4620b103000b0103404080d58040c2c0d41005004040440c1c407011070044413880c10b22240d8045406d08500548070b401e01549104240e0020003c41c024131205610000040c00e0601c6c40c003001c1c003030840c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 171691483 1250 171690233 171690269
    0xa05090d14070b10030c0b180a1404050414120702040510050d030c1b090902010e040504050607030e030c06090a0b0106020f1f0e0105090c18010308030a020c030d09060614010f09 78
    0x80020b814002e661010b4144a11611f60445120395088440004d0340c00c40d001402250030316011281c8c3d4290759408454502d4511924200b0000e0407000e0420341e0820083c41640e140d4140c00d1114542800d800c0e00d0550751048d17640f040c00300326940140810b106c92580b5405100c43e0b960045020b922035054640902c210040d400e1075100d2101d00404207540c040042c000041d1b18a86400501800303000341c85842402207402c090000392501254000c0181c0c2050000815141c02130740001000c0308014100c034180001070f444140b4050701a030b5070398035550149005000b04010030101c1400b500e041e00c084c244000d1503039003290303403050900008213201c081d070f4541d40015461035112840c61946407000388164200851032689401c0001000c900401c88a901c580d141d40760200f42904980d8000e00c0e46145035200004036000703401000d4440980c1c0030400145004841c4d601403401081c0c094040000c805182c0a009048401749000c010305101c42103414480e00ca820500c0041142da5125908002d105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 171692733 1250 171691483 171691501
    0x80a0204050405100501060305011409042a090905070317070b0a020a260412020c0904060c05210f100b070f0201031e0f050c0c030f13030b0a05090d14070b 68
    0x15500c0c10072410b40d07107170400010315164550842c034100c40103500010f50b042d03011824008060340440b0040c000c0708807c3c035200c40e00000e40183d4204e45000c140c0c1caa414580790100d02060b41e00314001034840380d10500e0107109208000c2c009000520b4030b00f58480c54881c1c1903480c0080c03c2402407201c441d450b03001c90b01410f0310b4081c014195040320a41c0e107030300000b0b01c0284101c41180091300c00741c508518036400e400b806400042da111031628010103a01d60307540c490b690a0040c1000c094103800f040014042c1c3c1112085801010b84ca1040c0460125410310b0621100023240c00d0060444104801c620710400010b03041000b02d4030358580043c0403401c01002400107030085d1401e07144030b090501c0caa100290700c0c2c10196010510403010b01400380070301d0b00c42c00040c46190140101c1d92050b60000c0025800303030400c100041c000c1c4184000e070048c1090b0360392151052544122503060810303448100b001072044007440007015062041c01c1c40b22400407070100540b041c0c042d00744011300d242c2d00b140c08207003000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 171693983 1250 171692733 171692743
    0x114030d0806060403021c030206060625052506140a08060112060308030a090c0e01052808030703170610230c010507020703030212040e1605070c030506011806080a0204050405 77
    0x540c0241210000e446184222640d0b4007e554080c0c005014500114006107040c6003151003d002800e980b100180380c14084941c480c0140e0700403141480346521030b6420070b8001040006000c10510110511442c1c554050480c201802c00641003001c2013005048180c0c00c545241e80114080c602911000c171685c0b60100200180d40014115140c08010001c000c0c81e9500424801440350000c914900c1d55030280c2d2480301c10038010309520400604961203d00d0b101d114000d0360244811040902c1035488500b20300750b501511056001400060699000d00301c007041a0350030070303000d452080036442c001c2d100801c1c0b0134400009d030849030285103e200d01e40c020402551398210200c0e0007001203040504002e543c2d00d2540c4801c802500031030f000101c0a10860f010b031002c8800900104880b980c80d1481d6900c1036040005140502c807042c0b0042021031050101344000d10b1051000700019418514a0420707030058144541d411410044140041c0c0004200c984025905507404107850301c6528025080c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 171695233 1250 171693983 171693989
    0x40219081b0c060c0c01090b16030b0d0206040317070c06090f171c0c0b1009050106021504030806040e03032e0602030706090303060b0f04090b0d050a020f060f0a050405090114030d08060604 83
    0x30083c942d040c084108126040038270211202d40f0b04000c2d010b0b4840070302038047c844a401a51104061200300081001c0214072403030786060840d00751912a075a40c4d00c1d10030344040d0b04003500060304108148201c40740d181941020782800707948403581c03200b40e845959484a17082401a007a1850501c070900007401144a05509680b10744d1294141c6015074030070840244074800c144c2c2d1103080a000050300c600104040c14460703044840c400490751030351802e079032050015041c0354000341d6031400e000c0c04000502c080c5026421b03403174858443c0c848400c031540141c1ea80360000e00e44600d2454080280e5034000080350040c55000342e0100e100f044a0078140e008014550096078140e01c0090180c0700401800000e000395440b0440030000a10b205041c001c1218001400910700c3c0d028112003405440c148100425003280240814a0408013400408007904484103100210784003040500c9a03203022100c850142c1810f609000d030426000340041e644012a000c01d034280001100880e035a511044111000303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 171696483 1250 171695233 171695243
    0x1c02030709020f0319110a140d0c030b01030b09090304050108150d12020f010213030b060301060b0c0307020918030f13120308060301140c030a0209040219081b0c060c0c0109 76
    0x40d407181502030f000c244d10490300e803001101c2060b01c500308031144d8801c0d914450002c0082d40d0625a44800540d00400d140c0356041840300c0c1400b80c40d058410b18001c010072042103503400308005010300d00143c19180034807006c81c400e026507420000da050001007a90101c40e402d180042964031200011161080f0150006401002a4010101744181c6042e00d42c03c03c003183e0308683c41c034800c90311124201d020b980c00a12150350001001c0000c502900030103034003c14001c00000d40c160351546842c5140c1c0c0301000381c8515420116000b000e42c908041241c0e800301c0c0c403034006000107100a6140e6140d11403140000806900881e100300c003074010000e44005000c650254401c280f9260070090419442260624480c1d803c0052405210030240c40d518007415070300d02068203680f20b041510001c0d401856000303811907828000320a5407041c4030044603950103103440304501070400c000c01a200212120303184d00c0020b800c000300520288000b8030300758400704a9000c0d980340c21450074594050020104090b05c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 171697733 1250 171696483 171696487
    0xc020d03050703080f150d030302090a180b0301021204060c020a0503210711120306030a170403020a080a08041211040f0b0108060109050307050d0201030209030312010302010e0901051c0203070902 86
    0x100340e0040010551039000303481d002542c2d940d01020500030710f011117501414002c440c11500c401d0804e440210000340c801c4c100036049c080740782c000c00e0004115500518000c2c100c1007201c0c0000301e0718895104690b2054001358078003082c00410210406000e003005292580c0c490381041c60034400c3c404044107503801000d603552980020429403030070000d0000e904140b00705e440032912050080758501c0308608004040c01d05880410707404c1900d40c00091607540c050040504074400106a0011a0800e0001d40c5030f003504c60f4154014841c8016040e00a209281d12180004000c680e0314410741d81100c0d40ea0264031840032840c5022145020740440c81078100c1d01740185031410488075040602c4500080e660074006d580c5d01c00044554a00a04c203054268000c107509004a05111154001c21270041c100545004480404207240d94051101117944880d40c2e00188110340e82b01414542c2ca200403a45c1c41515410030700003481001104840204481c05400c00d581151403d02c007101c014500918215 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 171698983 1250 171697733 171697759
    0x715090518130b280b01020c0904170d020c010501051801090b0607021c110a05180903071b0306050106090308030705180405010f0e0609010312110a0204060603090b150f010e010c02 79
    0x620001c00ca0060a00300002d0700b4004c018140c0b00e8440e210020301c1c16401807900c0c1083ca07090006040010f8820303100e40c030307580d464070070b007842002c005200101d0019001a03868074018081400c541c0c041e0859032080c064405401c0c03415405210752819030740010b0000501009110004040e48a007403c02500300980682c0001580d40200107407a446001d600c03c0e803070600d10740c810404184e615004040c0d010600d1840035446891301d41d01d10364046126400c582c41e221703da455071500b840b10001c080080104000007402003005e240101c500510090802d5610b907811552411500d0000803c00000c1200100b0910401041c01028403148140a08100000e50312900c40c0014103200b030140d442c440c3c0000000c82c102e810040300150490780c112101500500054004652001340d20103100715038426070800002580d0b640c40f400005001540300021405500d191881d445100140000700ca02280070700c00b051911207011102008600340307080909a015540146d80c070b0850305030041d42001c8014145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 171700233 1250 171698983 171699001
    0x7080c0d290406020d0b040b090705090a05060705030c1204030c05060a05070c091a010509100c05071710050109140103060507050c0f030903160602210706020c0715090518130b 77
    0xa050600500d501070195090040520066a0230807150540203020b41c0c0020f14014811005800f500c0c000624012000c0c2c2c0c1c480006406030040141542c142d000001c404103001810030003800385800406100d0b0070b2904c1d42e111076540b1507080c41400d000b00c0000807492180c91060b01111506035100c00034107040381d218040b10000340095100d092196103d540908460360060f020344460007001001c02502c01f1a80400f02d800c40e80880045400e4480c1c0078000c14001085807030f0f001440c07451001040d10824402030541a0741069001064030b92138000302c480294a84407069040d241c008501103070300d80b40d4040445141c8100d8446070707aa03000d90310840203a04000300040840b50411401c440300c541c130f0103c00010034001481081c1c05a8025400e01d140c1d20744488035010350030200003034507041c0030303150301e60105a0b0310031040400190018501030001c448407408481c60070400780b404503402c40c10940400c14110b41080101c00b400c40e10400119229070004003000c8082d4001070080c520f0500070f80d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 171701483 1250 171700233 171700237
    0x10c060e031b0709020f03040210090e0c0d0501060804080d0b0102071203050405100e0612060105190206090f0105151903050d12050a18030806010207080d0c02010207080c0d29040602 80
    0x70b05010380101803000591030000e000f520b440c50a03102d41c1500d1601c8030303800c002c0c9c9260040400003e0001d400030000c0c0e03449901c42ca0f14403a84505400b5581c8400c091500c104842058200d80107214420043c000820080e00c15070b074007070800c40d03000584142c140c4010707458151194490a24005440010010168000042c0c030481d403041d60421084409035000340d1358202030003400da800c8102482040b041a20720302c4d070281c0005040c181b843c034100c074207410f241810308120401000360f40244180100400308100e2140c0141d0703408020045814000c00b40101010752116191180003490700745020368070b030110000c00030350f8440202c0b0400c54000e4000703000c00c95417080101c1005d240100094603840e25018801d5250700105024420000c19941500e0080014200750304520a9500100e203141c400c00905a29403810b49501c941040c043c800289000701ca13400c90015134000340c9440605840d2040000003d035402940c1c44e0040c0d10355900000700c000e1184440d149411041c0500c0305004490380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 171702733 1250 171701483 171701527
    0x201020706060f050d030c0606090f050601020f060f070c02130f0c0f030204030b060607081611040b03010b0a05091f0f05120a050a03110f07151806080402010c060e03 73
    0x40c007070300d50348894043c5402114400c442d007122038200d10200080c41000c2803081c1d50300c42c5000013903042d21544d0b810101d032404140c644003a5a904103008003580c0400c0100242000540200068540403070401a00e40c00603000000b4804038005110855885035480105055092401c10209680800c448068604500803201052030404555030321032107070080742c1c242e0790400181c44840e2070382c200303010481e4030a0200303885041061100d04803031648284030f005058020f040c02104101e08070100003c035255004040c0c030a0f0700d4885a2600d42e00c1d8a0041130450750120354074060f81c1d4440c0001040c070401940f1100c94008840c42c0854070750703440d11828003030310380a5030003051401c81c89a44590311242211302408551103180d450b400a84507a210500d02c0790410261000a081c1c0700c0151302e0046580c0080d0000d101140c4004001d0780e000040003c260101000071b42c0c21450081c000d4490040540b010f410080c028070140140101d41c0c002c1c407124408401269983c110910034032054540e028 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 171703983 1250 171702733 171702743
    0x2092407020108070c0b01030b070c060e0a030207050a031e05030912060f070c0b18031903050f0f0112030c02030102090d03110d1d01030f0f05010b030412031103060d0c0e0702010207 80
    0x402113024544586051442294000c01d114116400c5485134246440c000f8071030020088602c3d40440012130030b0040480029030030006121091711441c020f0700303281c001c0d084140a201d000d40100b000c12061071564920130003c94048608043c50304110b401c502c60646150b82102003c40e0b0203291b80000610f25114482003422030415071a09601114462101c450140803071800c4c0d800315005180555603045044101402c8070b180010b85a2000c82c1070318201c0303c00f8040399686040200d840c201070051940b01e401070f0040c01d4a581062480001d488103564098100400031070307070380b0864400354116410703404014420f400000b090f24000300100c10040d880d403074901030054641107182c081e9503140070000c40e5007100002d613200c07030004400800800040c009800c2d10340ba0703049004003d91141c00e01a05030498280d550349031600702010039405a081071810540b4207001c49158101d40416a81c102900b140c820380c20440b5400c000015545503003022000a110f40306102d502c82e0154010311b0064818 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 171705233 1250 171703983 171703997
    0x5180f030a08072402120601030b0102250608060d050604151e020d0c0201090507120303021207091d010e01170c03070e06010215060609010f020304080105040f061b0909020924070201 80
    0x90344e00340c1d003603004241100320030f0304401c80455810743c00f07034200310315490041c41118503038520384000c224207410300b458103414078a4420040c4a0160b0046503e5840700c819038041017400d5490b5622640c032000100085c1c012820034011118495041c1c10040f071451031818441c02280a000707200009520481d04c10f0002c034604102d041c1d1442c0180581c3c0d0380a900140075040041c13a0a4040c842c40c0d62040d4100d0401d0b03030821992006801c2039401d140201695540d08000f18201883c10703428481080b0446440c0c103030000100807004120035803d040d200760180810329080710742245c0d85450031000056925009252000c070300c0f009401042c2d480b46000364200d500b10074024000701800e10064640340c1d04514108031048940d4001c1d1104480880070f44101c9181a039030384801070840d14140c40403160120203000718424403a05000f0f05070228450740c00c0300c200402003400500602030754420f081c1055004180510596514818414061140502c002c403130200403841c0e0340607134403890302203001c2040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 171706483 1250 171705233 171705293
    0xf090506130e060408030703090b130209061806061b010c1205010b040302060f0a1e080601020d030e03340c090e0a0528020a0e070f05180f030a0807 65
    0x2502800d56140502d8000d000c00e034507281c861040c603600c02010030b4145074a4401020006d0202c0840340d1107040b0004040307250b00f10710f104211559078098196032003114589000b6060039404443c450300554201c800565a030020030b0a29104c1c0604840c250044d441c000501a000360002c04400c0c1c4466000e104000c0f40c0c2c1c0364580207002d170141d40000b940241040c04504000b0000c40010081d03c1000d007000d0300070000c0e071074441d440c0d42d01440c00c3c9070000c0c04c2041400306650301001070315162070040c2020b10100c00a01c4400b80e40b0700984505883d2203013028010321418800040c0d9100301a03000041440821700d07410842e0f0360024911450131a50324000c8480020395000c1a00139089031301c04007070817a140307130b141c80c84810760140b11003a40c141c0b1480c0c1d086030042c0d9405d01c4034402819114000b8002e840c0c80c54000d06826502c061720750511004020752810142c0e140480070b41d161003200ca91145c001c840011030b251100944000380321090000308102844545198010311104110b80c881e1442a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 171707733 1250 171706483 171706519
    0x10314010e030f1206060912100b010c02010c030f0309050102030a02090a09020316050315030318040f060f05210601060905100219020d050a0f030801061103040510050906040f090506 80
    0x8690004100825402c4c4580801040c0d403c3e04160015001441a41000601e1001600d0005909103034007040e44684280000d511040c045c0110114090078035500c0c100c1c10760000303800c21000310b500508010007503080b491004e01076441281581d4008008548030303c1c0c83c101e00b000950054503000d1003034415000c0040c1080f03d80c02140c1c0b0408003900a41e070320500e00a420369242c4c102a1020baa00e80e11320141c9010368900b0000307088246c404150b400c01125131b1000380000c03141d0f04560b0016940c01c3c21403d100c3d4a110380210422960181c40305041c003107244154607001c0c40c0c06029070345140602000001c0c0b155102901c0070070744604803203031650404594016a0b80314043d409180c404501e240c0520050710340068036580850065065030380b03030a00d959400300030f030002d14030803070100340050700501610f0307844042d207403034030191200039440d00741400700103011100083c1900301000307030003c2e0520b616151201510018180781e0741c015010303a120810320700a060110b80050150348414405030070340c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 171708983 1250 171707733 171707737
    0xe0105030f030309120a0c060207120e092404090b180106060908061f05060d050a0f020715020d0e0d030c020d0f05180a050d060e01050705030f0115090509010314010e03 74
    0x80c4c01c1c1c00142100d0030880141c8509400c000042d009100184c051480811844c0c00242052803048844184801050070050412105a507009015552003820004588400c4840311101344200794080310700c94038030740050007800c04550020180d0718180b00740f01c240c007114220010038604140007840300c1601d520701112601c2842c030603003aa540c03040000c2034a5041801d500c0300b01558610380b007040c150300e81000c40d20759404401c07034640d0f060f5680308000e6005068071420900c0714401a0548c03a258082c0c982410600c00011404141e50b400140b1000d1842d03594800c85031081e00d0f00969030300c407a0f0f0110290052049074555000360040c0803144803000d115921600030034a0039144c2c01d0401b44100d02a2407036103807604040d90814042132002c144da56a45e82280c10480c400c0801003000e801d481201da003503c5025103101c080c03280c00d10510086801030300c1144d040d941e80140c00500400a42421146500b8507403000b600080e6060000c424004030020440003241240024030012290004299880c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 171710233 1250 171708983 171708991
    0x504060e1902130b090409060c050304050d08010501050703210504050f01050f04030f120f061701061a250206031302331602040e072903061003090c0e0105030f0303 72
    0x543c003003070f09206840c03410780588600100904002145800c640e500710444524114100128001004200401c4003c0150385d1a42d280f614022009500d801c0c006800c3d400307006070003402c0c4444030450b034201030b6500e40c40c10310b00600b02000748000d080c90b04005031540540e00d2140c0c01c40d420080025250700081c22400c2c0a50703455941d52409a00c540011641240340c1a10112210346400c403e214040e132a014080282a90100c80c4c56148421211a400c4a110394400e41d003007070544c2c0d0690301c402c400105850112083c01035003c000400c00403100d00012070024000c0d4015404802e224420140a0801035014405d440d1140370805d01d60b045098041804222800c501000046441c005920381c00703002c00c6441e00c10480000d03040c0d40e0010b42078880f604901e240c66840120200071404140d00100c0341c0303000005d40401e11040040720059244001803800c1e0050810038036451070a2300c01e50040c400315800003482d40006e5210003424900b2007081c03043d9440783c466094008030071400130003200d0107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 171711483 1250 171710233 171710257
    0x909070c02090c070b0a020306031504080c0d110304090209060c03070f0605010605120a0b03010e06161431030f1406010503030f040521100b0102100b1008100504060e1902 75
    0x180c5d56030703001b111010b9400208420b4040c050040c400b07821074216660503010f988030300d0f0a81c0d00c2d03600c0c54200f54a401c84a580c01c0c0108021b01c40d903054092408811201528191140541e0300c0d19840c0c081192445804812100c030f100003d800d80c01c0c0a0303c60802041c41d40300701000c0c005640e94207001c403518000c500131407204070300d800e0101d0f0125005522010380c05401074000f007565070720002d043d03080c032000701d81c660009070101d8500c03102c0d41e40c042e842c2084010b000307400c0c0c1e05001100590100c108902d032200260b40100d425001e898ad498080007000840c2c0c0001d111024165600d0710100a2150324070b032518a118072000450030745400700c01d0b21030314041c44a56504080c603000400880803e9915001284d015403550280d840100780100140891030341d0020a0300710703806000906d8809c648040711405032030b10405080a1b6100c80705142c144003980303840c004030b456210030203c050007180d119503409807420700006024074002c1c181c1e91090103002c9509850740001e03c0007809901c80d4402d0301030303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 171712733 1250 171711483 171711503
    0x30a0e01050c0c0103050405010e0a0f0b01120302100e120412030305060922062004080607050a05030f070e030f0a02090109090c060c060b0d0f0203061602070603020c030909070c02090c07 82
    0x60154484c6e480190301500520003c18070801c0c4441041c00e02c2e90001e02600d950341840c4a04c000d00c116100800c1c01440031500d200101d03e550346000792039001d1000b03054121a1a02c49410804404003c0401c12080d540c05c160ba5035681c40510b81c440c1407a01200328042801e00b40011224548042442c1c81a43d09805031207242c45030b08020350303440d407210703c0c2200d001e0f6a0f1541c1000309014003488802440c6240f07105c42c1d9460230f181240c1d2408030024416006c00030108880c003891f130741c40401d07640c01042490340391a1545502d001038882404100c10203400d40309034250b0481c01c40c00020140c01e502e0090f510840c0c281d0306c03454058240c0c2c940c4580544078000300201041200d01c101030045a0724090750002417082841c000194507403a80000588032280c25614000540c942031003c80e801c0080c103141c0c04855461f0501c041d480b5209442a54280742e404521308040440034401c0b6a0240da000b09054468942000c0c0079050780301c0850240e02552511000845810700071003165203058110302560313 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 171713983 1250 171712733 171712753
    0x61f05060c01020f0d06031407030312181205221508060a09020c030904110a0207090506010c0203010516081602071401030609021b010e0106140d02060f0a02030a0e01050c 75
    0x4040303a4003000d1240115075007007080b80114030420000c0c0004c0400c01e00b000c40e403503155041c4000300028005e0291401c0d00001c04c01c200180e04445900144c0008800100e2030144519160a5100c0c1c504e0020b0101002140b009061030f03400f400600c1d83d40c140c401c08104080404041c00c2d1920010b000304c0c030010a400000210250192007203651010008103a070105644640315402640c01c1140c0036203c41d4000300704d060191400380102c0802c03030310b22040c582c245a07812070000d6451105116003200d5542e180c012814a903c64030221a006801030000c1c0040e09180c8100d84010383d4000220001803070440225a4501a200095a40b1400f0764010084582402c1035401012800900036040c03554400c0d000070b0300d00e841d00107003204081040808a512901c20b20b89405c1d950410030f0103074236900d80b05061110510580307401907020001c2c0c49240c0d03418400d10111f2514440d50070000c007104c001040c40d006088c0c1c0000180880700481e500d051403014200010f5459010b0103600c6c404a0300203107940 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 171715233 1250 171713983 171713989
    0x2071a0412050c0d03021c0305060607060b01030b1e0f0307031a25020318010e0a120624030311070b0d181202010b0f03030a08010e07091505070203061f05 68
    0x1c40395040c082c03070569044042840004d80b52158181040700076802a1002691010132042150704841e02c50a06100030b190540c0040d81c035110346e850040c40c1917a07840074281203910070b5010700701700d407009460303040711b240141c4800d20381c0940c42d40030a22452070108081b23123900b80480c0640231a80d01035100c803501c0d5124400081d460700b009081e041e8112014002d54020000f00c600756911b01200c3c2c01071581c50b500040745130030406007140d400d4103214414140c40070321f480784010442118031400050100408901d00307c40039010401c00840c540c501041000b82035180c0c1c42c5040c00b120b10a07180e581c0000702030301c0282d464600fa07105203c082c64082c0100d281501c90782c0c110380b00c2c104802c504800007040503507681070601b0080d451080140e5549051840c14204402c002000f030804070001d42c00c090090000905141e4140038805001061101113807131680140c000c0c201034801010401421026401c0040c281d80000300207034440d00c00c1b2400b1030400d01c01c88140654402601345045507440c140070034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 171716483 1250 171715233 171715259
    0x50a0b010b071b0605161703070504060e0306010620120c03030105011e020606010c11031203060a080c060f130b030a050a0f090c050f0a18090c05030303010b090405130609030f02071a04 81
    0x1c0c0c0740d0022040d05500c0f1f00000c040218840d00345500c1e07403903c65040c52001007821308030000141c001d030700c448010700c04160072a900c002035186002000900580c0f04c4641801c108116040446038140407a01a058900110180d41a81c400780e0301e0342c1c40c4251003c0e040020f00341c0c503510440581c11a40c04255203520901907207900c0360141e2100080e007044000842e1030140d07491a1007030340141c088140701c070078584809000300810092004014050901e0b00298540c07041540c903812061000901c07802103c03044028800820700322071120b803285007452923900034010880340c0d03c00461801000e2103d843d06840340b004080d401038a120546030801c010300a0002005202c02c5c0d00804600000a140b00480c80e5041402c0c410240460396803501d14140e01802c8040e080b60b846500148018000c0c822900706441082c00110b4021410344c0310740551088001c0d1013813000e000c060030026103c040c035030800d190041810032a0b0840d0105951480c240c440503e80e6001a03500c03000c1000200032400003021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 171717733 1250 171716483 171716527
    0x12041d06010c02100f020115030b010e06040902061b070b0c0a0201030509100f0902100f02030a0f0c08120f01090501140d020303041707150206100b07050a0b010b071b0605 75
    0x4100442030b03010340003c0c902c00e405034000700020310b102441c0e0116a60a0148003100c0300500446488181035544074600500c050040030220b101402c0068241e44d240c0c1c1040e452171703402030941d070780e0390740002a0f030148000c61801c507d20038440d85500003048502c0108846504c00190007074511041181d00440c042e050140c4150700c4c900c160541000303502001d01c500807805282c6400003070f0350000b91050000c8800c0b9076002d6801e10000308500d07001507402000310303001b512241c540558510701150040c1c500101e000c1014004003c01310700b0b40541221407410708e0007180d100d543c5540580e40d41b041b0300c2c01d861090095521855402c800c582107410074080c0301080c20b200030700342c07170038140c581402047c1c0104084600f043d9610100c42004054200000702071030704030328809080e1500c1d09003143c00b100080c621615000c10340c002031080c280102880381c2800c00b035204c0014562035039120103407007540c3c00105c0c003510404c1030143c10280c144210003840782100e07050340303c090620917080d00310032180088071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 171718983 1250 171717733 171717737
    0x11070b0d05130816061131150806040509010b030c0103020a050702090a0c080f07021f20040f05011d010503040f050a0501050a1b0e120f010608070302010212041d0601 73
    0x1a007400009030481d002d04050131201d000184042054280001078420110f4036500048040014281d0801d00b14410a0442c48480110089014104072407115188541c00414403540351125212140e40c4211181d003d00d17001c4409000307541340e4903401d0f070032500c403004450381c1980b00040c2c0c00b0441d402a00a01801c01190030000d003010b0203900803544d0800c1c200c4842d42c0d102e47d601c1d521107400b50001903181d00004415048032a074a032a0300c01960350445d00304c0d0315040d221602e290b668040e01d9a080402d01004810080c000d20100340000c0519411900a00641c07039025040811654440d106c1c00d02d0b0155203000580f82031f20000700540b07083d80081c1050351030071180400040840c200b003080d0440c0c41d11510000540b494403099050480d50f2520b400304441c2c05510042c2d03140b5511240461030760304100e91000018050420a914000400010b01015428050002103014010441d481120700030b0b0203890044150b006c000c0700611403402066041400a055005000c0d13000d07000c207510075018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 171720233 1250 171718983 171719011
    0x709061812050a0204240302090a09020d0302010b0102071e0b0703021203011203080c120703050c09040e0303100602010203070813020a2d05030705031e2b11070b0d05 73
    0x148408080c0341c2401c60180c5003070b8403440f401001c60030184920b245030982c42c4076901880040422001403c6040c2c84064811034004001c2010062a680020001c070f50003840011800c10310314010b8041c00131070703850070b000d4018104c000585c040c0c005031400240e80c2c01210885010f08000861440350440c40050f8114440c3c28807000d4075080d00402903010f0f203a00050181c4144c158680100b5140d00101155690042400082c41e000000501e19801000504002c1096610094a04204c2c02062110b6a1043c01d14115081c1c44402100550060846107410340c8002d845120581c280e20054030b200c0300140c1c03810b00042002203900414104644020710b0041d91507540c10b02c2c00c43c8440c0207080e080c20a281450041601ca091389a0000104810f802074440c9500e44400640c45207000c50316148840c160359a42c0030400c0080c40a045150040100c1e05000080681004060a894401503001c0398407108a045415000100e801c100c882810860745071202c8a14041c01030880904412541451 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 171721483 1250 171720233 171720239
    0x504050c0c0a150e01021602010c02130c090618030b0402090408070605010b0c0c100504210602040b121f030807030516061a060f030c0705100504030206010f0e07090618 74
    0x1805080c5070796004a41800941103010302400403200354810b107041300c0c0c0c03040001c08010301152281011441d02400d0000d0030314618008601c1c3e40818400c1c0440451038046101080742d0401000010f40e80c00b82d4914011803407050b040d248a440d0340c04042c0c03101ca0b10500140051070080e440991003441550050705045166a41c070303040c1c50080c0c200010070351021800300b83c0803404000c0038110031000c4420801e42050600040e0261003035000c0d07020500e01181c40341c0c062144455602000b1503010104540e00d03a6107503110a141e80100f00c1603007008a00c00e000c500e42e80400c400844101000d030141078249440e542d0394600c1980120341c02c4042c07120034000390482552482c4507281d001e024641c04104048803840d024080c00b0075508880c070800d0140710440a50a4950549038440100e40d43c8641c1c0c0e00c10b9060183c5000c01036012400302e03505100802081647c04034400c3d0403900f481541c0703110317192190820214190300b1038000001034220304003008400d01c1940c00124100c041d409061045071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 171722733 1250 171721483 171721507
    0x605060723030c0d0f03050f0a050601180b0901030b0a0e15010c0f0318090e070b070303090b01060e09070801050102031c1107050f19030f030e01110c0607020105011e0504050c 77
    0x3402c1004150002140402415008400e170310700176041c0c0c9030810051400302410b85203402c01500d901c843c0c6903140c0010780f45900a010840711003003078181d060035117941e903000308080d60b2084002e140024103000d106045818030044070800d5501c2c000c41140075695411486400003090b407229410030402d0310340034001c0380702c0e40c10042005009903160315081c10011480c400e0641c0d25404450003e01d0607200d0146a100421180701707941e000d5910301c0e660f02c102c0c201240900984000030b014030204000005803d074200072400020304090b00c04812907a00c0103425103203200d01b40301c5e0502582080040f103003051030544440b100c411880c1c20001d0403095041e6075900541117a442110075601290100d21555010008401c0039480384005469140d420303500100002003200800042c1a01c4110102104001b07400c9a65089155200240c8402411582940d2000103440c0c1c0c00165280ca400442c54070211746014054024102002c100589400288001060003c040c0c3c8501c3c0024840717200b941c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 171723983 1250 171722733 171722737
    0x90501080118150c18091b080105010c0201050715050f0702010612030e040b0409051c0207080604020a05060c030c0d0905090a090305161509050c0111030412030f05091302031603060506072303 84
    0x8540309134002048041c0a056241303001d10551040702344007500d4010050790b07902c0381094510550a10b000c3d9100d076582d142241403c030780070345d02c0300c00c0605001c00c22081030f03203094070944558032a034000e1040c00d9542c180040002d56a0b000600050035100d0a5910341c04e0a8000702101040604009071903880da1325024140402d2101d060f154000b0700f118a004554100944006000c6131009845581403e13400200030100c14411a401b524012a50010004050003640d0a440d444c60580b40c0e54040b03200c0080c124403142c0580d5106d0032148000c581c003040d241c401c8800665054603614070f0300e01c0c8204022003422410200b1103141100309081c8407107c0182c001d499115200d040108001c03109907002400c265004d4900c58165030040c8010800d050603048864601c80e01400c082e4045146141c0c116290700c0b5000203150440b400d201404540c10b400d034025842141d0f042070403001f6440c029411026581079106e11a44208c060000001003501d081407a803242d0b203081001d095030135000c40c619040d0703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 171725233 1250 171723983 171723989
    0xa1b0303060906090204120204110d18030314100b090f18091e1005040606030206070c1a0903030d0b1908070302010e0d0302061b09030304090501080118150c18 70
    0x80c0d10307a031040007000ea0600a140103000400401d60819040415480c445e01c072410010748900c1d190041003560305018070840380002c200145c28050002c2d1140346902d1090f40e076000300d00207071a080002440c5000d03040c103540a000c085801d07007035491814180f0b24894000310150713544141d61034026445e50703403542c00118008004034080c0845161075150107042c101300f00c4050350082d05840400c0c2c60480d0200351012010400d400005103a1290b0400e0700c010002d640000303402440006d600e105000b10044140100ca48050b0658900b8072031107202103d5004900c100d41d0560300c14040d03042c10404c507810140306514003910494121808101c1c20881c0000b5030302168594014583c1401503583c020284c8140f2802540c2034501c4031006e9a0081d5502c8008090b807400c005600e401c0e21092880d0002c80340000030080850303489645414480006000070304c038206196181913415801411084440b501194104a0210110660f1840034028050000303e00c4200450300000d0102000880c9924001e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 171726483 1250 171725233 171725237
    0x1b03012304060606031107031409040f0f0606110304030206030a020f030106090e2802090a050907020c01030518120c0a02030321070903020a06210f20030114060a1b03 73
    0x8a8145030500b42c2c1140c181360401402c140c10f0a414804d1001c1150403201029410310341440101d25220886005008101c045548241010902c00c140f4400da0400c0256401c030080800c40c41d80d4500080c2c640d844001c2451140360070902c4104050325206001c5d66000c02402c5026240c0410070b00d041640b80d000343c0054010547c10f4000b48201d44254064a03403141c0310743c6010f501408245249034011000c0362110360010340004503802c0c0c1e5102c1d078002c800144800b6081c2074440c00d0110019441e0b00000700040d000a01c0c000002d203901240b41e40841d01c1201c0c9101901042c21058030310706031036029140c070f04110b20404502000586080006241024002440201c910a0710306015000c59014160b00104040d00c00140056030324803c0c90012111142000071809180c84a2050410017400b10000a1454002c07503842c040c006810494162400051400c00d601a030301706994039000c2030290780310200380c0034940035140c2091b1000740451295030404c030600c0ca120700b50301c0004110305602240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 171727733 1250 171726483 171726551
    0x309040e0f06010b0a02060118150b1b01021204030e0a080609030a090503030a140d0b0909010b040b030a0302060a051b070507050411040e1f030206161703091b0301 72
    0x44941480494003620000e40e640b803034844803080c025520001802000d200b98810354014400030072700e070311083d9490b014010090059a5038020000356410074100400880c6a000e0b4035146008184220b400107a00741060940036101e644046409101070b001242d000b0384403c001049070319040200d6481042076000544e036a0108040007000d200c003540c4118020f83c800e00c0489141c640090b044021030340c050010a0300c40c64400120340c0a0103686132042d0f0050f4442013405400c036419000381039520300c01e890070f000340c040e80300615954100506001e40103030010000704118480f0b0350000368004100140403880001044514002903126078021600c9a000c500700b080705041c2801100200503c0881e1141401c2c50603000034840d4100520107031004844d1400350080071003662650b0055600908030b503803a061011540c480c00ca0a14030b00b0782e00c1d400ca0070740d0f4500076115041142c0c03203013500f80d01820380900705103c00b11250200c464120b6165498498101d02c100c401304911303050402403142d4030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 171728983 1250 171727733 171727753
    0x1020c120c15070c0210030f060f0509150d0b07020c1507020109050108090d05090a0807030b040303050c090a03020d1104181713050907050d0203010b031e010e0c07050309040e 77
    0x2407508100103060a4240207202c104414030782c1244031a080d458054540e5102c0c2842c80c2002c50083c6400c40c0008560b40c40d1103808102c0d0703000310140000780c2e403013500e1840c4251140e804800403211481009644810280301010004650590181c0c010841c1d00498041088900000e850791102086400d00701c04082904c00a660380f1460300d50080c00c080c00c0803903060810f40e004940f1802c1c00d0380c04c4000d00000281400b2180c0b03804014000520040c4c043d20302441e1649444143c07200300b40d8041e0002410000843c00c40030381e80084030004400101945030481c41c5034203021214007042e00c140d402c500e111720000804e88882c056890312800983e0307803241e4080fa600d06818800980d00e00c0345500c0d0307001e0003034102074940340201700182c0b80c0440c1c091040d56507041e000c407444d1140c211034615990010000090f60f481d101c01541c06481c010200301c00d040d00d2901303c0c07980c3c003a0921071109802d40d5200030a0000860000606c00f242c015000d49203004003010100c0e054416408a07250035600c844106 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 171730233 1250 171728983 171729007
    0x50a0902040518030906211806010f060207050f0f090f0a18050709050603030d02130e0c1201090203061801082d0a08031305250611030706090501020c12 67
    0x1c560103000480d00c03840b00c94041c0046613032401102c056074010040080c14030038903400f605017245045100da14500051500c400d0908590801c900749500f0341c0300e51400402c440e40405a1582643c4840d401000e10310301c1d10702001140380004008540000e94004540701c5510b038058100c5c45201c039111324805134101407d0900841310020002b41c07001c825503c0c120005440441e07920211190691b000c80c1a0326401c000a065118090040c0b595034030015440d4000c000e150000d0085805a5408004543d200783c071106542c4541c19001340d0000b031550052000c003c10381d001e1900824040e0441110120390143c500a520003a08000015807050344d1200403101025600e03140742000b24030002e0804c111080044da50041c988008000100c08000a103502007840d180640c1150414100d8010703103000e294040711401c681d02c8010b0000304251020485501610a138400000058001d624204503901c48070010041d01c0c1c0212890354003000000d14400040012001129034031080da90703100f0072601e034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 171731483 1250 171730233 171730241
    0x40819030e0a03020915013c050901080f09030408030409060515090a0e0603010b100804030809010c05161106040806010609081204091d06070507061d060721050a090204 74
    0x100341c811240140148010384480005c0d641045400c440b4103440d910b80741c0141c032040701341c0d098141e440c1411b9011100c8200c1021815500c80c080c1503061020041000d4225030078490603100c03a000c1200c0b503020070281c0642007000d80d0300c907030148140c90900f40c46080306030039980030390300249142e40c4030001448030741740c900286e281d1454a00001841d20081e0400700c3d907402400e11610090140c6100000d685031001e40100d0520003000380100c0e204243e20102034400e85d402c0d02c0541c00600010009403040005101d00c01e101441c903114141043c0ac030041030b00c11a040d112041354136104802d001440c1d92981e801070400f51001c440079004540c10500000c1604400e9440707001b0f26442401c0c40200e903032044080300c041d0340603080d0101c0d12003240c0d04100813284202096a0451189404108407581d018000c0c10005204c3ca00c20300a8450784003a40d07026007001240c807211508402e0214001a0181c1300c0d9840a295150704041100044943c2000310b880441e407004545132581d01c14011031405100e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 171732733 1250 171731483 171731507
    0x905030f0d0b040c0c031412040605090114060a14030a060203040515100506040504110903070801050a0c0512060616050f030901120c08010b0c010b0402030405010c030c0c080d020f04081903 83
    0x81c040045140300c0740c2c001c008410440f03006d0b00703220f513480c40755030035182c0307a42100c14141d0701c181d40d449103041614000c00242000c80700c080c0c040d448c0110f5004014100601c40380204002401c8401441c03c00c440388035013000d21707080300b81c2c1071044c1c64601e0000307035450001e107119500620250036113040c40750001c811003600070b2050702c0d4001c001005001503035401c0c1c182c40a8800a403000694545046030000046c880d80c02001c6d80351046040025020301c05400441c0301e130082044c2072020400888081d102405003400038400c10410f00c00040250420700d014040030800c0804145652a80b522003070302304907482441008980000810000e256000b4010f403c0c3c1452074841040940d40c0d002000b82451030601602040c0302c00000c603a5800754007500002d450b01c0c0000c4c804c55490134140342c0140240b80b00d02c5803c01003424441c001601d580140140310190340c0200e0041e2810144a401000950000c000030707583c00c80501010440c20002c00550480141640790610b48540324200036101105600e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 171733983 1250 171732733 171732739
    0x1203031006050a0507030f0e130605041a0d02040c02010b062206050301060503070309020103061d04110f0904110109121202060f010f12051c090f05030a1a0403030905030f0d0b 77
    0x4100e000d00c5034424115025141c252907d4610724050900c00c441040d200b00a00c0e03801300d800201d645040700c0390781c04001100c10444c4c0c10480411400b80707566158035415105540030b0300030f80e011005401c064010b402400814170000a00c0c0209000084645e0005a5504024611a54100845214001c00b0006000a4105541150300d82200180340d4403000340600101600c0f8420241164000e810001c007070442e102d03c0000c0c0302140580c2c1c0f140f208003100c0590f098040040b0307a02260070100340c1c2203880b030805000e80c440340c1d80341c1c2c4420300c0c600c640c40746503410458000b400241c0010b14454403100c81d442619a07055244080c0780c02840c003800501075800d4025480d0040004100c004403150441d03420111041c2021041e0400301d040066840000f501402400004c3d1b03c03041e44440b80700241e500302825000c81c15150300501d541e410100c031008001d003140e0100b48500c103540111590b841803180c42d001c2440c450036503803607096420000300c0c24035061010814040e030104500035842640015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 171735233 1250 171733983 171733987
    0x3021804030212070f1e06051509060a0e0402010f0c0213051e060307050111120a020304080d0c0f030503090c030d0807020d080f06220c090303140a0e060f09120303100605 75
    0x940750300017a080350540040011001411451004d0045a400511103400c11020001c03403410302c1485042c030901c502480d1050159400140d1140b81c0451404180e86000c00c810180e569140c0c019200003812550110500c0302042d4264010b0b511441d04a481e61022400480e1a0a282c1c801251860020054541983d0b00c4820048991000108003048841c01d18000400c6540100d07010305040c4072600c0b03041c0d94840025240b1045030000024011610440200c6100c200007000c21170344a50344890090003142c880d0100c4001c68030a0b00a035410054080c2601c4a0691190000c0e142c4100040301001240c02482080680c0740c044c0007a02006d44142001c0e2101d1400b081040b500240081c016803098100c22421204001c3c807990940f0ba256172024100448070990308060071408480c070045001511954021000708044415501d0740840760301e840300c61454503420443c1766003200d0504481f40000340062810f913501e00e400604102010000f655484c101403404400803401074116106000c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 171736483 1250 171735233 171735247
    0x150605010302030f1b0f0318060105060c030a0e060d140106080603030a0e0913121814010f030b030f0a0b09070603110a0e010c0f0302100b0a0b071b03021804030212 72
    0x340c01082d84004420820142da01c400140e4010074010b4041802c0e5a10007c8100a0190782d005c07800300000034a5002c58000340e80e1101080401d12910790400c0880c3c02c240b00ca008258002c0b8031041400d000141030718245080300d0544800c03904601201c2c0f002100f51030040100a070003002054110909501551910005905c06007440c2e9280061a00400055000071140041c1b1103000c20b44075848150b00f4040794041d54000e02d18100304a0315032078045c07481e400056a02658486461404043e1903281544925650030b078018400320007816054011940300082d228824020781e00c0715072050b144826281003000030645003c6103604a02c00b07052030440b0403888400f0000955103100204d1805016420881c401243c200340b40500051218140800c9841016004541254034100e142c8041082030946030410401c9a258030600d102d035001007214402240301d5070802d4140000012660200075529400310740c40b2403824140030450300660081c0000c140e41400f002401024240b00c990800c8a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 171737733 1250 171736483 171736501
    0xb1804030e100203191b02030102030f0a0c0509090f13060e0a0c080105010b091201060e070503070806090103110103090614040c03120206040c09050402031f0b0406080f06040b1305030715060501030203 88
    0x2414454041c086c2400c0a04503540442031310712151507000d0000d5440c2e050400e51820000002d440d004001802c0c02d004440c00351180003a12243c68008102ca005038072494458440f000c405080000402400e03021030b004200e0301e0190041001d420b000400c611720f81030402c00041d40c203c0d0840b14081c0d0602e401040f07140801c5040d6074800c80102c810b5018042a902d809004040c140d01c0340700c145001c40c040084658018000c2c6218902a4442d2840c6590300d41c200840da1009010044c0745400d00c04d2580d030705510903446010107074414a000500d020508101e400c0c0d410302145d048401a02503d024010030101e54407800c0403050030b0000340100c2c2042d50324191805201c3c080d0300c2006644800260039550b08102000c1040e140306615040c0502090300500a841c09643c030034000c0d42041000500c0080001d1480c6800c01d8850161007145c840c1d503034441c0d9240707024020342034000405014601087c010710007820f02074400d0a8109400138413a03c4003007a0b8201d80d004a044c103106204000840d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 171738983 1250 171737733 171737767
    0x50106020c180f06040b0612090102090a08030a210914060106090602062202010306032f0f030613050a0209010605040914070516030909060e060307050d020607060b1804030e100203 79
    0x401300316000b140310500c0c0c00c04100c80d4018202c104039420500b5050141400d019030052070040c0040d140c030007126860b0b15040340e582c4240042540080d85c403003200318540c40c543c60b84600e80d140c0d500f40400d00340156240c400d424208884210b035a0340110004100c0381da00300821000400807800603003014036020b004405445400e140d0b00070303e0300200c0f5904d0216031083e40f02d6800b5591008000e4000450300441c42d030741145d960309114011401410080070303442e1803100d150036410010028491942c5040190b2481200f10200720390074410080700c240181d854110041c081c0041da030303d142e01d0314034007910107040c0c4120f01c080368150510a01400080ca07401f108907071809001c0c03201091640110310381107603401001c0d44400c40701454610f0215000b0300070144240101411001c481a00c2c0d00c900420081c400d011000070f51000c1c0c01c015000c0080d105030806c03078403440000c109403660190301401100c007441c1194214002101041080030b00d1410f85030500c6000607600c011400c007064010b400c0004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 171740233 1250 171738983 171738991
    0x41a03060c070302070f060305040203010f020f040614250b0a09020105070210110303100303031505180717070302070203010e07050604091e020c0c0a091503030e030f01050106020c180f 81
    0x1500002101000e050080040500802c5440c9002d03079a1030b0747d000c00600609066504900c00c0d400c001e9147d054000034003e981c809652043c0b0a803400d0324001050b9401034041110341a01601481002d41c1219a01203c0380e486a207011600441e100d2403a100000740e40c02058020b00c00c0c500042200542d911000303440b00107505030b8a0100240c02000207a40e82801e514107484c02384400801c2084401d144003171441124825203080c018a100c40c02e0000d681c1c0e0780c902070f00c0e400110f10501503c00c14400440319030403c0d0503042a40740380254003c2c075540e00134125042e50200e500044c0c0d54003103043c240300b207590005429025081150034135000030064401c6215254210351180ca0000341207081006c204800d05007600210b5460415038004da4984040c1007c0c03920034241c500d0001740219050144106d051900d030f82900d030040c25542d003a101c0d126074002c0e10390140f11314100541801802d1083c03501822030b680041034064450b0701007107072808901e15400c004c091390400303004000251030340103a08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 171741483 1250 171740233 171740251
    0x50a0807030e03060c0912010b0f010309030c0602160b0708040b070e0a0b07150c1107030f15020d0509010f0c0903020904050f030a030b0319050307060c0e0604080c041a0306 76
    0x1503a10036003800c8403281e854840141d490b0050b4000d2041c00d00140c80202240c4ca410b8a0654100880582c62801c07100341e00031141c2c004080f20304a28982d8420792001030000e1082c2400c009c0042c03d500c071181282c2100e407500456a11500207a410b10180d0315400380c0c4601c040c40c2101c06403909a48035200c0320400b414940c140000e401c410307092991035914880c060220708000d5501c81c0006d0411411240001c00150100b030315040d0b0010045120f40184002c11600c5001440d040e03203036070b41e280ca502085600948a45140502c04001941c81e40010102060f000e40c1c0468241024103001d0b0031a1000c10310b1141051038400000072940d00010f02c88112501241c2a240c16502e03410014203090018031182120b000000351100c0741030305507005442150b000d80c2240c03d10410042e840010400c2e03404007405681c8280100c81c0026126000071248603420f15010f84041c4c01040480e019800541100d403c5130003100c240320341801c0c207100e0082031460340c40c0c3c210700075444080469103500c005003030005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 171742733 1250 171741483 171741487
    0xe0916030504080c0a0303050f0a05010302090708041b14010801150c02040b06120c19080708040b060301060504020f070204050f131203020906030406061701060b091201060302040207080a140304050a08 88
    0x34041d0f248150742460320741d5030548009890926000f0001c2900700e074814060000f000114251000714894103060703e41c094810030854940318401d03501860000c0c82107901806ca15000c4c0c01110703a03c030b0154010038070402008507010040002420300c4a058101d02035480e0310200c81030100380d0083c3c080c0025901500c00141d003102d400f0101d017241c860112010142c01d00380c8140042c04102c9001807403607500700405602090001103080b101948282ea00300c00062041e000b107000b1a005d0f004040d00400010000075880b076030780020405070703004840d00021040d004070710241582090300856600c0810781001c2c00d02403600301e003c10660424080040d0003c40d5200d1500340d013500950481d2003623880205115124541450f19074090501400303150007208200c0f100c4507011005010f250191810403c0007800c1c145d4203c1480003107014504c000c00d156498160000142c0c50b244010021103008050595540c200c06202400c2258112030300300281400700300b0800892800b02c1c2d540503041d4840203941e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 171743983 1250 171742733 171742741
    0x8190e031002071a180708060601170916030b0a0b0402071a040c0e160905030d0f0f0210140f070f020a020607020f030f0d020f15130503130801020a0e09160305 70
    0x20020440106400983c010b0034184070305003205403009000c0700e09400840d486d0340c1c0c81c1c100c229221401580c1d031f00c3c00b1901c036002c1d000511012500381584001688200d65010b802c400060f041d0310a00d5006070b5400c0180000d000c03044841c1d015140e05860f040d142945068115660380c0c0d0103d6a04da2182c1c508034006010504124501030000c00604188050340e400f030900c07440b600b6422425030030600c08255000b000054608002c0703020582c144182c1c0b0784241d60054280183c031209101c03c044000c40c024061071088080c0c180c0303d511425000b491081c07180c1d1070f10400001000e00041c12210500000080c3e501d441640000c0050308107a040d43c01c6074803580c103840481c01c844691030310a40d060140981040c000c0400141345016400194201d0342070580800d955078503030001d1041c840104101e1000903d42045983e948400d45204000b00c2e45000c071028821607411241c1d800c101c88994002418511041e848058000d06002c00c60309201c1608050f0980c0e09454401e0703141005058a0b24005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 171745233 1250 171743983 171743993
    0xf0f20130503030d0e010c08010e0f04020604091d1501030b0a020a0507061e110c210d051e010b0301150c030905031c030e010213030318090908190e03100207 69
    0x1050301408694407144008049401340031505d000700159071074076081c510810700c035180b401d0403035840256181080e00d81c10401c0310584401081a0b03003040e000c2100180304450752061210102d8006c5114954281698000b41401d0309803e0041c1c00c0003102005001143c44140800d40103000c180d070042c0d480c86008002d0b2024010004081d01c102d182085400364621500303803901d4070450041d0108410745490450030300501881d4542d015543c80142801c4c1416400703001e04080c0c00b484400d5a040c044c400901c50181d0b18110340c440105a080d02010010840304015207014014000942d130440d810300030210003890303002c040141040340743c40c4050f00340b45c06a40340401030f06018055440e003a5800b418030344840d01c05030704000000c0c5417800034550181c0600c240d50300c940c2e0f030300340100000d0716640301114062110342248505c01c1100c0d20000383c0070110700c50980090300c500f05042e2502154000c0300c00d6417180044043c14071850495220743d03130b5004a5440f00989101200680340e45950400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 171746483 1250 171745233 171745267
    0x8010b0a03240e03040902030a0b010c08160206040314070305120a020a0f0f060606050c0f0106080c04050c0f030907030312090b07140c01180c0b0c030313020f0904060f0f20 76
    0x200f0b42d260200260106503900e56400542c07090045003000d2200c4a0f0003401144c0341095100090281c10040c05913050720003151400d000501c1c0018021410700b500c036129108610044040c42110398402c2d1020030400100380f00100b0383e518104402400c0c40e061540203503c0300c1c28010014824004500030b1402c0007660440410903d4000c20100034031521002d0140081d84490f0703054815209660102403070000501800040c2d03603034203002e0502c0d03001c0c1c0303001d01002d05000740005e480300200b80a41001b0300d11220107180b140e2080c0c0000c4c922240340d0300300a011944407044a41c0124100b40c2e401c0e0100340d841059a4011840386040e202c030b0200c01c07940c00e80300c2c0540b075844c0d407655003491607166083ca1245941e0f0070b114042c1d00d00c120459034136081d60903036201d0610500345980003400007032095a9a4048643c84d640083c0c15000040c52860024000050803a0119040e0b41d07140680e80c1209043e20803c1151002c4c2c440c10404110f50101e40990398144e506200c00c0c0e1000080c20305a2805440c2e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 171747733 1250 171746483 171746501
    0x40b0112020d0f15051f02071502030a0909111804020c0d080415050f010e0406060504060b0a090f06020c120f010908040e070206070806010c03020a02130608010b0a0324 74
    0x4011912072280c01030700ea018000061003c5501802d00540c540e090380500c81400448000500011011b0900c1003203074003000a6110140550290000005030140b03111800c007070068007075029556034a0310b8803010308801c501e60000c40d0440e1415101c0003c0341112400c444000c4502a04a110700f00050b0009010f442080502110741c09041542e0414540143d00580643c0c4564000241100c0d1602148102c420031108151581c940500401c05100e032012400d13045400f50b24081007141d25200450140c4c4c5440d40821000d49001070320080640e80718000d000a00851a00768580320b2170720400942d1038000c0c0740000c5c0705250048080c1c1410504222010810003808000e01540b074035030801b039440390807610600400701c001200140f00b4600c0410f410744520321070b40b10300b451512410011140c0c0d5900140032402d500c540c0307428a016940300000c600c074001040030701103600d81c100000715003036420b01080140141e0000e5000c0c40015010801d50150b100c0c51200d542400141340724100103001c40078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 171748983 1250 171747733 171747767
    0x11b05210a080901090b0103240606110d02070e06060904020d0f06031a060306010b2208030d0f060305060a020705150f060a0e0f0402190f080d02060106180302040b01 73
    0x1040405190320080c289498030760710b0310109603650103242c2c0d09a43c24110014440c000c0b4000500000f80c041e00c0c2c11400c00400b2580d004d4045201a011044030b401d504500d02245100c0701c1101040303402c000044e02c000452028203141c52601240c40600c890180c10b2910441000c0340c2d108094a80b42d042e100050b100b04800d208a842085e0924010800c40c007041d41d07803510b101c48504078650040c0c0c11030f005150140050005a01c1c1c00300303024168000b002214050408101407810b075070100b0f004d480c0580ba40382c0146540d80340402017101180e00a9094007101801d050040020800c0411174a6110201c035002580e120094070b4201c2c01d01900080d0b040340318540909010f082050b04481360304c10b500a0b40c10300c1d502501c80c00159000e040c1100c1a03110440b08000203001810403e0038007510b02091071410b410603443c4c82130ba5201c0082c540000f20194031002c0464842541001898014007c5003402c800010b010304024000c40c1a5000c0a03015a440700744081e503036442401c03c29040e50400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 171750233 1250 171748983 171749023
    0x21c0e040b13020705012405060703030207020d0c050a0609030c0509070203120f150418020d052d1204060f11030f0d0b12060601023003040c150c02011b05 68
    0xd00b48120094104070004d440940c40c0540d0b001c50218910140c400c4420085c100d4001c4c030f880c200c10880c041d03118590840030160203000e0f003001600d40c01106403019102d9031320301c80e0984c100740a101d80780c03000f6404241002408541000031030620924401596000d60b4920310036510744c041686140319461000d0f0820042030100008044504803032030040c024800c80c000c2034180c035410071050f82c4010031110812144400f044005140c00c0403c91220340c41030702629035850111181c107040440440c821600d5082008480c10752500034040c98840030398804d410741c10282491002000806c000040e0002d01c010f4000303a40c681c603420021340c0e001020301c458283d600c2048410708006170a034200481e00540040d050008a0003010070098407c41d010b07401043e0926554040342c0b410968203804480358407008400300035100c0f0302d00c02540b28034019655440300710b10308002d40c0fa2a0251501403001c00180301115030050f03a00645d12407103510904144910b0031840e042085c02c040382c0b144000103402c50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 171751483 1250 171750233 171750259
    0xe011d0f120d08090609010903052a0607020f0c0307030b0f09011e0615090b0d0b04020c03040e0f07030b150304061503030905040b01020304140405090f0d0210050106021c0e040b 78
    0x21001c80783e032144800d00240d0b8a80c0c0c4400381d105080ea010180000c0100d602808413441c507401b4004000340b0401000f207000d040040c038000650030004162402070040e004000e80c101945800c2100340030860095005205091071515081c0c1000c0015102525030340003003000c035001750025008003800782c5036660791011071b40406642d10020182440340d06188000108044d901c24001d54482c4200d40300d120382146172881d0f06419100501c03003207802d290710a50911688403581400c001501c09000380d268484040e044c00c0c00d0000680000800400806090909800d1a910b2f0500e140c008001110100d54a9440d1031501401a010758503210440e4582c0d04000014594440a9202110002d50742048200f0702c03140120b0b1a80b149020b1840c881c1703209104c0c2009402c007607014070340c011411710540790b0f6440c2c800b6409080140c2030340c1000c0142d000d0301c1e07204500061442418014122400104100c262039140d0911030f2100307025240601181400c0b1207500d44440c1c00401c1078000040c811206c61038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 171752733 1250 171751483 171751487
    0x30727110d02130510030515011b060906020901080f011d060f03010504030806120d09031b08060112020a0605090306161803030203070b09010207080d02070201180806070e011d0f120d 80
    0x40c1440341c0c51003114103001075401741c1e01030b215183c000c0011084180803076a88100540c3c1142c0d40e940c0500c0c8800c2c3c500c01d02004108c0d58030070045841d20412016903104a800c0004110003005032a02c40d501c0d45180042042180c61700c40c801000c4074000c092010f44e511040003c40d84210419031036015420030742000300301a804900d00b803141e80e00711080320850391048481c0350303211115048117002c6021000e06001150480205004040004c215280c021b511842e4640c10041c003030307000f0b1581000480740641140303070202011000c0d151925025052181c0000080d54561014100710a64910303940c4c1011014821088694814440d004c0c0101c00daa8a01e40295070b541325540076900c049040c004100800307418000c580a55402100f898201211005510000d5020440c01c90500c95845001d0342c0340c05c0760b45c021400408881380680305500c0c240c4400340020001400103410090303040460747e034040c20070b42100d20021081c0c80c510000840c40001c210100c08141d42811584030310403106680f59 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171753983 1250 171752733 171752767
    0x4030306150c060e032b0e0319230a0e0d0602041707080708030a0f0e0901121101080c04120f0204020705061f180c05190509030727110d02 61
    0xc0d01c1000108243c42d1136440322612405207128460881c83c00d45801203440312507420050030541c0d03288002642e90080c2c51000d203582c6c01600d100300c100c44580750703000210790021200f580c4080300e0441701c2511050317101301002d02c2c425030707050754144400c41c060800507403500401e000e034a50317004600311f41c0e0765211078040001e0001c0c96840c054038896000c010a070038801140c528100d403000c200031820500d03081020341d914100c0c1d12422003001105484a1101d80d2450310490007411340b041e65015000441c240030785c0880f00b48025a050103684c0e0240404408010f0442c0c08440c05202d41e0640c040c2540b40c00200d10f1507249000e03500c14004960748050050214101c0d00841c0070801a1900d601c17219145100d9400380e00c990541c1001c041d040030340540c040e402003000044030b490030758640480f201c111012641110300804c0007410119001100c3c0c282044400040c154003042d0021034422a4031002140c00300f8140007440c1074544400111a024080c103403007211120486c155118680311251003100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 171755233 1250 171753983 171754007
    0x100f02180d02030307021512010b120702060f150310050c0301050405060d1101050a031b0c11120307110f0603150307121509050c100905130204080a03080403030615 72
    0x45400514928000d00d40580c0341c00c03959502078003450034070b0720742d40030001800180c0302408082c2004001003140c6c80690710500d4043c05012240c1611043c02d90044c02f80f51302c000b4140c405550050045c80b1b2101107010301d807548494405480d006440c2d500d0007190520248120881916042a040c010341c0307814040070b14142c55055504020544d540000c001c810782d50700380c010b000b802d08a800320702c195210710000d102c00a00c07400c0101d00350b1a1000989500201c95066600244c4950201c60400c038050403180b554503401c8410403a00780031254070075100c0c80341ca0b000a020030418172a429654a418034100034403800103190607204d1800d0207940d506a1484140103229009145001c1007800707800d080b504d2140c0d0009020400002e940034140010b010003030003511f17030740300d0801410b0b403640c1d40c45042d02c8080c0056455907a00e0745410f05024283c00090500c0b0b4400740140000c0c40f0310b03900080c0841c40160180b40006c25070b151810140c00614880d00318040003044864a90f2840d90420942000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 171756483 1250 171755233 171755257
    0x9020a09051207050d0602031f0608060a1514071502040602030c010e060403090e1021060e240c07050102042d0f060c03050d09050a0312110a050c100f02 67
    0x1441c44802c1040d403915110b0050302d0f80909082022004540154065507101c404286842d251340c102180182821196030300060010f02607800b00896070401180090003804040b10943c00c0280e4400c004e050811200c80c602040c44005c82d119040c080c0d01209421845001842103640340d45951000303440c1d5202c990840119800e0084540042000140861040f901540c4082c001400c202c010301c8540c1e4043c0c5000c581403600170010440c074404c0e005002c030502e042444c0d25001002440c01d034041e0381c060842100180c1007144000c0f44542c0358044244211500c043d403150340c0da14256440c40e280200e00028041d584041000308070066011100d070f64501300755170104071b41d041c40020481c04d901e06004820303012a030010308001702d9000e41c80c11034049120f81001400c20b02144120300803900c1521007500c0c03d51185141409041d0406007100316515101c00512003050015189016889404c014404000c0009600b00d02c1c804180081913106a40000501c480441da5017100c0c060b408c18840940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 171757733 1250 171756483 171756499
    0x30c05040e15011404050a091d1005012102030d0f02120f0a030f05060d0206030a060902070f03030c050a02030403020918010905100c02070602060c16080a03020a02060601030923010609020a0905 85
    0x540f503144007174400710b03800100022a04c90801d0712010140c200c0780020f0702c0b011510301c2584e65a41c810f1010841c805401c7c800080c01c0c0d8540390306c40d00c600303290200054422006d0b07540c140c00341e100406e0026083c1c5690030900305205d4141e8040749030580683c4008448040810241e0744248840c0c0200840312480c2e90030b000480d01003c80ca000c0720b10a41d0719942c400118030f15907006045c10340145034003180c0b00e03800080700b5503550300400c1a6404540c0c100c0300300115090440405400d40300c3c18044c100c080c603096040c00d84140c1c000e59a8815030001038418040300700050600c0407404000d60103803030782c10001d20540c2c51529015a0310041085c60700200b0b8103050340014a070b0b00c0094000c0072146c0f164000d0640d5204c000c2e584800382d10105c04141010740400810000c40d051000500ca503001035940141d40b001361a000a080401c054001c03410907050103041030101d48101c01c0e40c01d00000345400007802d240007200c00d03030040195070300c800c03220350000c90b03124040360300100103000b103400c10790b4198 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 171758983 1250 171757733 171757757
    0x302030c21030f09012a030c050102160507090c030504020108010915031505070809030f0d050c09100206100609032d02040c02010b010e040203090613110d0f11030a1101030c05040e1501 81
    0x10311b500c90101d6440c8500000d4040d07402c00300f032042158100c151702a03000145060b03c074901d094000804c020054445078000582006100c5041c807950300c1842e61494200710900700b949c002407100406100b20915580c03a4544030000700b44070110070000351b40c40058038001500720400d4a020300343c00c81702c1cad00c08940c86030002000b11002104807034100005c107200c2480c203403400b00d10600a01001e80a100340120034000cac02442e403100e04052801c0001034004000b40c2c5020180c16460204503080b28040000351502000000e50310704600350110002100040c20507604c81c0004040d0f610408040d500600340b18101041d140c065200d0340d480402a42c0780395001495006000691006441c1002da0394000c80004599000c94402401e22901c14504800011001c0001903818070300040161500c0d038000522608011284103021006a0241c0260107911665101d90491100d10481a4141915040c4071002284200c0c1120b014201841c031074100340c00c06000758903900385003400d80390110b030100c4289 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 171760233 1250 171758983 171759017
    0x70e1306030201200f0d030905071e09051302090c0903010f0203130b06120a120f02011406010f030e0a060509060c070c03020f0a092f040302030c21030f0901 69
    0x32010740360181c4407100c42d00103c102096a035811007076034207518000e00c1e581802801052004000440302542d000c00e1a815900300a400d022181d44a6080c140c0c0c801e0700d50b020ba040903801c3c1000c69481c0c042c005265680e0803015241d03d03442c41c0009600025140c10440b16140381005014111011b900800049401580c40000c900c000d44480510202e21400440025008461190b1010700607195498034124042181d10302901110f0072140c151103960180c440c40d034446005200048284001e000650840d000d00d030b0b40b040003a10040c1041240c3ca00020043c0c026004a501e40580000b180c41000707090910400520f01555500c20b0ba02804010920b5603886070240c95a05070041d40c081c94692841d03082007801103c4841d120f030841540303080003400e030445200b9281852409802075210074543d0720070041640441004d280140824002800580c900007000d0721040710944600601c1881e05000040c840e040104034182c80c800001c00b4445070b980c00020f05802182030304c80345400c0c1d035601d00fa = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 171761483 1250 171760233 171760241
    0x7210804122303130e0c040803030a020c013914070803060a0e01030c06030f1104030b040b0a0203070e06090f030a0503130801020711040b01090f0b0a02060a050906130515070e13 78
    0x2103860359003000e00901c030310790403030f0941c640004000c6e81c0589800c3d0740300202400c0d41c00417200c54180650100c1c0240091000307000c0c040c001461801003401403441c81c5201c0c1c0314094159000464401c440310445103450180240c18004082290810748806d0701e131818400a51003142e245000d8800300f940025200002480c46040e241d000103004141e0380ac2510450040c142c0860410303001d0745410780d02000307400d420010700c051030040d1607900303a03480c050408c020f09242c0544480b511034410000c2040540e485013001c0b880c50411521950744948660000d0095221211540d51600502481d0010048000010400010107030b0800025076982c0301e080b404c03801140005020030403034031000c3c042864a0380c00070700c01020504056004a44600e00100e055085800010a201b0b0010301a90240e40400650b5071082c05101d00344010320b0600c0301e00d61111405803001944003038218030700c0300f008400d00c0000c11120103403c00304414504100014443c0810420503401140c40202032040380c0300e503000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 171762589 1106 171761483 171761497
    0xf070b06030d111e0304030501020d0b0111010b090a0902060d0609051509010f030f0f06050a050a0b0904111302070b1305010e07210804122303 63
    0x400e040c0b0349401d20300740506105420f424812400310018280c1010b03501841302100210f518240300d031443c01190001043d84d40040b4415050700d03001d5202581a4109070307580880c5c0400342100d94200c0342d014841c0c68200d007009002560540c3c864001d100000d01c084d01d214a04030280814500319076513a0044d01c0c0d01602c560501116101c2e0b41e00f0702e0a050003c5807a01165490060200701c100c80c1440010402ca0000b8000c00a2050070700700d0241c0c40390440410b00c41d40c94050130080080400311030220042c0e00d072081c0291682040429148159400700040346114401001c104c1c0c06040c0c40300d54a5119001c01642c1e00084c41c130030302c080c010f213802c4000304000b41030752809500352401140036503216400701c40104030550581d045104100550b030241000d1800c0c50612345c0c181e03c03464103d85148010182114100800c4c0340c001e42500702404103079107070301c3d91900e000f0740c517449226 = true := by decide +kernel

theorem cover : BRFrame.Cov 171582733 171762589 := by
  have h0 := BRFrame.cov_init 171582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 171582733 ≤ n) (h2 : n < 171762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
