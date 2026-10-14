-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3692
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:56.178975+00:00
-- url     : https://prove2.me/submissions/79cb6d65-b425-4ab0-9fdf-79bbb7247ba4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 663848920 ≤ n < 664028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 663850170 1250 663848920 663848951
    0x40c022d07061e09062f010c0807020c0f0a030308091905010b010801050306060a060f02030f1801080f0f01030609080412060b010e0a0f031b03020a0e01080c01030b0d03080a 76
    0x259000c203000541c0c560110403440c00012168030400e00d01d0400407031391032500002524040030032802582d411a074891038a101c0c035594004c180c40e00b40da07800800600e00f8102024003004000c2d20402d00501c42c25032240c40e1403d01801301e02d4a000010541b80e51146107540460320701c0c0c4001c0c0010618040d504105045040344121180300391f1041c00007280d0082503070001051204142d0145210354030047c1804042c1e201d07007400e9001d48003285000c0c3ca0041c51400183e145100740321b0482012400019903940c4a40c06000805443c0f00c240c1e03e0520700d485240201c0080402a0380c0c0894241004004100150b072551003602c001d407050085500309a95000410504044240c1c00d0b102540c0714040c5210942e448401c0c14902c1d070007255806003540c10b0113100e10840da001d010051000f252900d0440c2c05c0b80c80101007a0046130300506000000d9101d81500309904002e00c2114000e1103681c00144896000b401802d510020140818280d005036880c2101d2103a40500700c6a0410741d180c8000035013105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 663851420 1250 663850170 663850183
    0xd080c031206091003031215081204050901061106070c020a0302042c06070f12060510020706030e28060902040203150108010b0c060f09070e190506040c022d 69
    0x1040481e00354600141406110b04009250304281e1031248400e10001c0d41080c0c142d501644036540004400726128070315501d0007020b4010b517095215000c03000d40c04100c480001d00a580050742c46104e0380e40e0355001594036810340010359200d0b070070000014400d18410040300c540b13a40002d0911002640c1c03a00883d040f00d008611081c0d503000d80306a00b411a111029503c1106001440102054170707100a0042c1030b40c000d40100800c00401000100380101540c00c00070140a0042c411740003036041400c080e640e410148500301c0400c1c10902c1c0e2001485004c074103025030615001c091007105003a005845e0803212500c2040750801d580d407421501503100c620186108001001c640d110030001c000c009800036405a01038900c1310810002c0c502084800300b005a0485120304c0c600c0b0070790320340b11640c604010b0150802c1e070a206002080020501d000707860341541ca192040d040005848880500060324540e644240250b8803c50f46140c0e1021060310915403540d01d82d01207090780b820040103a04104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 663852670 1250 663851420 663851437
    0xf0609060f1b09140402090301021c0b09160905120f2a0901030f080a051c051e0f01060e0d0503070501090201020c0108130f0303020705012c0d05090d080c03 69
    0x80e07070380442c0100ca1040caa8041c40015003400e0818905203000041d184e90380b019100e01c3e0013180c01240b02c290b01c1d2425010b551034208072100703030000041c410301c6440052008044c0203229101d84000304108581c292206245421280e0360382051608103014003103142245140110b1034819100c07440503074a020710541c07808402c01109441031011221007034074003080440308c451184010314010800190041c81c148840350784259a00e41f1282c03070100070b952a0041c06194110314504040305901408140c2c840c6104158801020310340001c520102e00405000b04d0740c49118248802c014416180100c15500301400002c0a07665031060a903036040c219040310804948680d19a1540030846d80c0620500207010428600007020345407a40d10112036032030808015040220741591207080c58130a8044607040780d0400000d0080c00102e602d01080d520240748802150f03400c0100c040030201020480c00b41c80c001c1d80d07562343c2c2010005c0003000750b4103080000407124040100181140c583c000d1010700702a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 663853920 1250 663852670 663852701
    0x105071a091c02061305070f030602090310020c03070f1118040606060c0c0603020d0207080301080a0201030f020f0a1107090c0203030108010b030111071b03020a08011d0109030c0f060906 82
    0x40c10001c00d110710786070075900c00488502000c0d114045140d03000881d29800702035400b440d501c180c400e08005013445110381050005001800010041c40003540003005500305c00d4088803407a02c0400c844100300e0149040b9040240c00410200b004902c021000006242c0250a100710720489080080c5104a15020b4110030113500302c2004203003c06803184800611290500984140c051390b01c036458000c55006680c00e0580c00300b81113032400b540ba410b5810382c99119183d5582c3c1c0d40c40e0080c3e0359403101d8a0750220300007400e081a07507000b51950b000350350138150328040c03203401e01440384802e403503015254510700824422524005070411560089505140064015641e2541000842400e588190200e14020780c1042403403c1c2c10f103004004c0707522450708030030f4942015801b0184030704042c50303e500203544501e00c1c440c04030740c03042e041d1311103904400e40c103043c040700b40d1101c00d039142681c641020281c0850700040c842d1000c5151000500065482420002000041c0755268021a8030001c021410b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 663855170 1250 663853920 663853973
    0x306040e071412060702030412050c03030304150b0a180f0b0d0605040b0106080f011815061206061b02010804050a0602190806120c01030b040e010f0c080105061201060806010507 78
    0x160902403c40144142118003a1055141422001c1c2d80c1344214482c259402d801c0135010028010188140d4483e1000101500d66a0034517084c242542d5900c0100800b010b480d041c107254040ca030800c00001280c444138828004040800c040c98014803042c600c01c4903007525419201101c1d034808450701c88035031043c040003d450405050580c44c10300142c001c4020310081a081c04404144900440d0440d0a00541c40d0008041d0100b48005000f0040e040c009100d00350902051940c1c00100283c001d4014660411081e07a07a40b5044500c81d0341c0d00007060030b081041090720302552240d5140c0785e000740102c080707501c1d0b0035055542c10101e0b40301b49182094600320403030740e040c0290300c01072107508130004030340c0000008003c0120702c5e240c14582c11814103242d03880f69013035256104c94200c1102808084000c100c0440000b0032840a03140b0b9080399000540301d5400485d032440c006050b40d041d0100c241250100d0783c204401501c0c034020107001181400790501480700010b4902d1200850001aa407d41d0b10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 663856420 1250 663855170 663855209
    0x91a011404090501030605011412031815211003081b071206060302130e032b02070b0f0105010302070804141c140f03250623090c01050901090b0306040e07 68
    0x907c009499a051310544800b8000303c8141c034000151100c001c007486141c01680410000038dd5003500641031460300100204403900c076100c2c6089042d00050900c0d03c282c1442e46c0d041d0166801071a030340001403041350140074842c0540110403041d440700900c00b04865801d40c564003401401d110b08201100c40c07a4440c0418011400e05100b02c42000c2d1030101e0510042c1c52000c2d4160300d0b070042130121610806407400305030702122507074184503240d4207040c400c40d5110800d04020744016022a00c1d10068960754000007401e5129100312444640c00c491032340c1c2400d0030300c21030701009012480c40315800b50384a090503445c252490700d005029031090b00c0a24084181401d0b10307092080956032040d480e00107011420004000d0888000005002030322400d400000b071a0031401450580c068060740d00c816845480551903e508090140d02da40c822903204420001c01188c1c0e81c42110015400500340250820a980c9820051508520300500c04035120100041481c0340c542c003940241d8200d145880c4d50003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 663857670 1250 663856420 663856439
    0x323060c0406030b0f0105030f0402040b30030705030f030907030210030b1008061c03050c0d0309021206090c0d0510050705030a150e070819060303020703060501091a01140409050103060501 83
    0x14148102545c0f0b1442d8040180e001034250b0200038041c1402c40c856100160440d99030364442c2d41c045200030600050314150101207203a40200d40c00c0c036a541c1070880324880c90a41e0000607030700415800402545094810302540e1650380001c0e08580891042110100040c1c0c5c0c3c10030800811100f0340d400041034082032040040210069a601c414030103261309000142d01e8130300840d800301400440c01002c4040d04e103401c8480b440341c032640311042d0144088088a096050b0000c811150007100c13001c58400501904c02c1e2a00e44c1503445506a602c020281452400c2501d0320f600c11030b024030150341c0c0544082c2068015280111101c80000d40e0000810011225911074a1128001900d01000440c1020011408903002514070401d1045000004418041203070b90072050794151001803004580e2460040c3d51001903010481c0c01030304140000c1081000d52061501ca010404c804a0080c0c0203500150740404403d184060801c004010100d002c107106d0207014029840341000054a614005011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 663858920 1250 663857670 663857681
    0x7080f0703090b041d010b090a050f01090b03090618031801080c0409090b06100201060803030a020315130920011d03010609141501020c241612020d11070323060c040603 74
    0x726100340e07040c400c2208c184c5960078108151202682c02c0f540080c0400010795054200e40e0007000d500c3c600000300000307060080b8205001d4808001028215002c0c4280d4540320700aa001d5a00b5070319015011070305640c490441e442e0403c060015951034681c84504100c151032501d8001d660002e49501800a503040210210300c29519501c000c014042c104800342e5200d10000d400303513141c2078000c004103942e210003d0014010240040204140310308028282001d09a00070050391381906500340300019918954200e88070050595034003030343c2d00f4460740780c0d40ba411412405581640da0741c040841e00c0d114500c545200a500c901c2d01c45580e1070807000300641000000c0c0e0290441d041066140300381d03124541c00390341c0c180044400004805886c1c1c425180c9005520700d0061182209110764180007400c1c034828041040e81e42529000442c400b01915194070328a104206039000050400c007042031003101c29055142d5040e032010401c080000c06241c5242981c268036076010000301000702c2500352041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 663860170 1250 663858920 663858929
    0x120605100f0b1813060621050f070305191a030c0d0b1803070b0c1b07140d08070f0b01080d09050a03080a020a12120c0507080f0703090b041d01 63
    0x107462207a8103000d600516400f07001080500140040c141548a54407981e40d03200ca0700c40c02908100c900d540707880040c000d0307000341c1101d071584a100020003000c450f5801040d2044e9000b407009042525a0b0302d0480040034010200c660300b0b0b00411604603c11424020a90840b40041d0000c0f22849100105402c0181c40b062061040001160003c0029151a01680c1c0800c0c051082d01c0c400025898041c210f1050b544002d020802ea0820861003c1c004405452103203000c4181d2480b658000c412159500000e00a4120343e400c000f00c10300d80381c600504a489101d100b680918100440c60340e5210a0410420003264810b950f4070040c01034070320820400300c012040d443c000d00d640b86088003050b041c007010702020741907050014180071824020850f007945158840c0710049400b540c04030040c0081031010b0070030356090610101c48800ca1181007a44e59980e04a10300b030745058440c150075942e903408404d04800f4003102c2100011071268010140c40102921440041e1200c400e000d007002c0404142c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 663861420 1250 663860170 663860189
    0x304054608030c07052b03020106060f21050601110708061503190f0201032705011d030f031e070201050f06010c0f0308090f07033005070807030912060510 68
    0x140f005071500003d40c0c1401c596041d503201707500e01c00c02107580702140e00c441001c56a0488180b20a010964154805400c440c140d03070b20710b0204140e21108560b080c4a10512125980d210407a140305200d26074041604200c05041c449041d052218249040210703640c8601440e801000410184031030040d101109950102e015003402003400d041c240600e910b849010703040344400140c00701164025480320791003028601c00c0200100904403c08101d10020f94101d4803542016142c4580203488005040b241c00ac0b040954200720014050100b203400040800c071806003100f08000340381e00c0041212b0700403c0c2c103500208480c641840101d0048002800687c1040030040d508400303d6240a07050725145ea1502e45603406881c0c84003054a0b18940c80d0101c102c074011044008200f00a01204011a003000c084900340442c0c11000c82c01d0f481d00342c8010201103842003100100044c00b00008100051203814094902c0e91203988030002e02e0b0b5901c00440389580d6400500c600d5040c40244200106181007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 663862670 1250 663861420 663861427
    0x1902031e07050d050904090213051008031e0d02070204060807030311120a0f1206080c0301050a05010e070c0c03080d060e090703031b050c1201021902060108030405460803 75
    0x140d07565a2070039801c0f202001c000001c81e002056581c0d541203101220740090158051740c0d4404001e030000c01c010703200c0c0182c18083c4400020f5283c2c002c000c1d99081c81801c0c41c44101a200000703501581e0f40045101d12040b5400c0290a0050351075108002c044d0400c2d00c0103244141c15454083d0120040d80a000140d502814445081c0c5804404558141007103203484500c41501641c140e4034101e03104032401006040943c00710701400b0000700c480d88610210020300c40c68440040d0b4000700d580130b010310701e00820007100040c0c17038900443e91a00700503c02c03035400c078040e582c03030302c03406c01c90f40040e001c0c1b103038481d06c901c02003102100d803400c101d40003541d40001d08840d0745035a074003906001e251410050012041040305051060910030300381f00302d0303000c0c2101c61481c0b443c0a40c40d000394401015058441031480b0000251440060894180c46450f4029031510b4280700420240100410348610381c544e41201000404261a8040c0c250b044107c90b901e075840c4800d02600d40300d085a412014040d4003d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 663863920 1250 663862670 663862673
    0x7050f0309131e020a0c060c020c1018120206070b07020604020f06030708010302090c0d1a090702070e0109020f04090c0f0f0f0503011406090603090303101401020d030b0301021902031e07 82
    0xc641007443c0f204503d4005940700c1c0716103815039900996030300242803189884074001d5007903008102040070b15001c491104030360000c01c00980b03100b40e10b940189400005ca02040c026031048000d00116030380000c0985092010b00c2d41c40044009040320031900580100040c40110300f40344008188104080320403e05629110a004201010511000c0d11645e03940c004240001542c03801c42c0c041078946402480300c0c4401a0140c09505449120907000d289403c0008940910105010301581c0780c1200c640142d034a40441c602c040d40192074444030b01581007000040f000424460807949490940700c0d07410030080910084c01000c01c01c0203c50601090350942100c140e4032008032815211000321581e4610040404540c42e405121451a0800b00c00010b00a64801c000080c40c0304200c400c0d640300c00346e51502828903001c40c0340c1e0b107240e015034040000f010016019030402e4400c000003074001400c20003a04502c0203140402460000581c2001547c01d140b00c5e450382c40401c001349a50b00d001e1510855 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 663865170 1250 663863920 663863951
    0x12031b1d1e09070e04020a0306140d080f03060a051c0204050a020c03220305240604020a050a080619062109050c09280501061707020601150507050f030913 68
    0x1480c848600c01c940000006203c0c82c0107200101001a0140c411504c40d40c0d224009401085540a60329503407103410b2a03002c8d28601820014010b0307512017a22801c003102050306003800d80000e0162a4800d1540e83d000c03465841e6010340010844039a4100d0100545600601c41180d90190500d4202801044200210b900000031a500c607124200365a4101c850341e44c03800e003004081d0b00001c0950260141303003100c07107000f071111b03c65000d070b407907104492034075494200401c81c815580000d012800030710810341e00700c0c064120168400e50207050207001c17514445880c98075038070981116011440341042e041c0f5401c0d07031a12601241c1080c10080040621580310555203014010300316101c1d000d150001502082031101ca00c05004403031232822000c480c100080d4010304024080c11001464540e1242c82c40800485040c2c01003440e60080c141a0f404c16101c49002c0809081c101c09000e010012040041e00400c0804620308113a0088c0d0345a0035a242041b0320381c1e0600b00b00a0ba00c074148075100c00301461 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 663866420 1250 663865170 663865219
    0x20071a06030c0114040e01080607090821220305160f030206030109020307123206130f020f0313020406060c05032a010e060f0606041212031b1d 63
    0x4007400c002031341c843c101050f140c0a100755088980c000c1c60a4000061504001504901511054a800103295200d4490f1a500c02500c0f502ca540e20310748800d84082140403900807c00d45851020020202c1580c0d922860078000550046910b58400d4403502d4650260500200c0540980301000c0790a501e10b070001613881c0010f0240300045030340000807408807409111410511103459109000240c81140c0380c5112807401c0b448820092a100359080c000316402034a544203c2c0010032007140c0d41201502e000080070b189005600041c0e003042542003803203039240514071482c0c0e40d42c900102003503148144015189668400400c0c8070301c4160140010b41d0100a5400e1700c00c0c9200003185180c840340300b034180782c021200011103951809203271560542022072110300c243c201c900d01e01c0356502d8400600c06640318070701c6246841c3d60206500310006805284209070b201e01840e000c44d908201c0540d401d84242c02c0d9424501048147c1d8000d1030f6a5186940c4940b0079000b101c4004000074202c45e100304880 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 663867670 1250 663866420 663866443
    0x40e1b0c0c04150636030b0a1505130c090f0e1501020303040b0c0c15011203020f060108190507051504090509120301060324080313080a02011b030320071a0603 70
    0x24001c0400c1c5c000300122140705c551204211004c0410169a070609050882043d1012507085042c8100d62568940605a5a00302c8034098000c0c00012062500e4500070040d490651081050034140010303030000c001c403a000681855424140e05083c0503c400c003003150788a1310345066420610800001c40c12196007968042855603a1640d60740c4100c844508044407944180c1c1405e10f12400451920a2480c03c0308035144603070202c2c1c0c00d0806c40c0ba401503442c88240700d5030300c003544070181200c411150125a108060711550840f02941d8582c0c0008010390580b4095981081c40032030100001e00e000d001d019080307041c0c88054440e5102102458245100501440044c5915420900d000f64210340c00c8040501130b4a020120642c0c1ba000000d4903948a03802894541055030008200076602080300d441d40f5078141c40b85d0306640940b0080700b8501003683e5080d810305940c1d021a0032010342200c40c1d00c01d8490782c00a85550382c03c003483c7c248520b0000250300503c200a120400c44c1d00c0e1000101c505491 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 663868920 1250 663867670 663867707
    0x415090f0303082208031914090c010f020309031e2e0b030307060e0705010e01091212091205011506050306030637050723040e1b0c0c041506 62
    0x9131003440f044680480000e100420030040001080a44c0f070012088604030540540d0902400c1d690080c104214102514410300507040030242620540c0648803105144040d801601d05102e903440002e4103015840002241554060035004030004d011702044a82c49d2524008225500702440c0864400300341101a0341c0f02039035054101603d0340c0030001e48109503480300050115070306424000351505c14621880e1301141c00400103460540c004e01946080c2c610102c070034182c581c0c2c0350711003005415240b0511003e201500c3c1c0c0c04644181407064042c5824000e50003c00e21a1a10081045c40d050f10b0b4440f008101d01072050012568021488076000900c504010122585034072400580c0c94142581507110466100701c80c009aa09030041e52088900d07840d100155403c5840b030140c00c1104201c7e502121000f0403090001d41e08081e030b0650040380c2c80341c0f2420303011030f00b00ca6100d003a170054011600035071006410a00c6440c15011b10b001c01101c150900c1178040c640b41020388200390460120321b54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 663870170 1250 663868920 663868951
    0x521100c030207062a030605060702042a05030910050412080a0b0d1a06190e1e0103050105150316050607080f070b01080c040207021e010201110415090f030308 70
    0x240d511940603540840d41048007001094081461510b20240d66814100c480300c1034070038104403a02900c111401c403034018094a103081000d9080000a0048090054810030a9400b100d00301c80305e541804012115a140d05560b4108004818a0a004c13003007a49107450901d4100400214000d10948400049040040641d200d18030950007600340308d011180c0080010203000e040c0b003060760100341407140d0410803071429110b850512402030f4107103550341c589212195041041301d803103d010326807040381d0403200b007214541c003400c8903040c1e44281e100713440e560f44a00c244200d01c0c00d23200028081c2c42c4100c00a0200c458406141c5000010078401c3d54410b11020400d1001d0041c0c00040b06c00305074040c42e00745d564030300d249001980003000380038841c224450820020341c941064802c40c0e1007541c00500c03407400c101c0b94119005200c2c0907411020304654961020318803d4201c00080c1c8040c00c5010b50440d000145a4801000810954413040c08554007407010004281c0000d84a03030000c1c1026200d240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 663871420 1250 663870170 663870191
    0x2061308040302190b210c1602060a110d05030402030f07030201140c0f010204030f0302120c0705040e030c060403030507021011030c090a180518010b03121b0a0804052110 75
    0x1840859030303114901181e00010158120700031204134400c1e03402e9148030010b0031f40380c0100c10003003401103052010002c65036540c1d22015240080142613280750504e0314040d81c0380100301c900c0c00c18294010b00c0b4017007000441800210b19007840813968a44c00da100401104d0700e5500001d01c04144541d182c1e4203800700007240e160111040c0111440613a82c14025540c4541e40d25101c0c501282440040d0700502508000c0003140d51004100da800015600c000e021190510702000001c04580711b903841c25200400c14a1171841090000c0351103103009071000192850250f0010303052000c0c020200c00410319003104440b40340b20302000d480d00840301d600d019860f003010402141136500d0b1030f0800070681d10014505210546103800c214402c400700c141c484184071040c02d005d03083e02c110030b096607031541100c000980b81c0c054000c090440b2048031042d030100f00d91030b000e460341010803030403055814500010f01400581403401c800c80f0407110030780981200444520060340c8a900e42080041429240e07494444c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 663872670 1250 663871420 663871459
    0x6030c0306101e0b0f161e03020f0f06040605040c12050d020c0a210602090a08010e0d091a070204060b0a121b1b050a0803041202061308040302 63
    0x8500014048440c2402c00751110a4007040c14441d801011803001295103e5a1089000208861400070382c10308000d10045c0100c182d030024410750740c40480c102c20031404900d650f0003000151650249450046165040080c2454514010f12400e07501441e840208000e001465652058001074005401d85961810544c807170080c0e80030b401141c10301c0d000c4400b40075021405da403a51540780c0071100049002003c3c440d0000c40c1e4441c0c400c4003907000088081c04603940b9000f01d599841900c1c01032278090701e400000c03005481034001c109540e644c0e9400d05002541000454400d002908019185a24024402c1083c02c8003040700024100302142000c11901d691704a100a45040c0186589407070342041c001700b1440c0141002e1408505059200b0101401c6000e030074101021a60750409813a5000550744083d1000001250a8442c0005c0c1c01c012a0a10004c1c42c056440703072040011000003840001d2078624081c00d00300e64141400040c00000e00350404031011070f030341610180c061941411421 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 663873920 1250 663872670 663872683
    0xd020306060c03030c0307020706080c04060e0a080d1701170a03120f0603030f0813111009050a080c01091a040302040506190e06040617250b28030c0f05030603 70
    0xc0b021403001005124203038200c400610b109020680c2204e0b410344c0d4459048400d0360040e164803081c0d036020841031080f80e100e0b0b079854038805006401d400380296140c0c282131400c110460042c0c001401c80c89400f4001c014140120b0052418a40181400d10044c501607103600c9180002820b00a4509501c034030500c2035000011100350b00501080101d55030300b8017404480c18600034800090400c0c0c002060742c0c0c2c000c002410103d80110b84112660075110a104454808a01c00c1c0d0038444030030000074032540c1c8d00b42100003030300c103020142c030b85484031a0024000683e41d0f040968540800038407080c0303d074240740540303046035012a804070300c680340d19011400c840c480030100e07141c040010b6404100b4820190311503001d000c080e101040801d5840859050741030314603144054035000758004007030940413803202aa00258410105403079540c5d42da43d8032502e6000810000803010846500740f040e8082c401a81082400c6040a1000d505050001800e0b049000f00c4d034014081e0200210380b0075107080141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 663875170 1250 663873920 663873937
    0x90310020c0a0b040b0a0606020d0c1709030106140405060607050a1106160335010315020f18040c030509060f04260706051302010f120f060b07050709020f0d02030606 73
    0xf40b0b81900301820308a0304401c00716119000c503401c011001401910005080f084e160381666800f40b0b401140c2e5800d0903001d81d03603140c040b40e198180944070095400384103003001089a0742c01e980c650320b00038003800141e03074005200c0c502c1079406000da04d0100b40701103903800840394011056810142e8441c0010280c0c000d0112000e621030134003044400b09900b040e8a25000800701001c4054040d98120110a0184601041c20202802c000420000b1409803500f0481440c4440242c10100040d5088482d0f0300300d00a1403501c042c5940c0840550b0030944501b02c00c1c0405803400f4007036441c11806199441e10068818551380107076400250034010654840610246064401100041000e465140540102100b07a544618060205504042c0641c2203a062641a110f1203801c0040c032405440d9500d1484284600544405c1110040725582c4140800751245041c02511a01907041440c585010f0380c00c9199010300c10001282382c601c40308159014200f030325078096a0b0741d0b141c40c01700741c0c1c3c0d001c0c4c2c551317 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 663876420 1250 663875170 663875183
    0x120e0304053f0f060609090309010e0d0204090c030b070518010c030903150606110105060d0b04031b0b0123090105120f03040b07050d021f0e010b0a060f14090310020c0a 74
    0x1da400305101c000c03e814a294601000f166501e8a90a0801443c92410740d007100041d4004c01125030323694000c0314050841180103040f94040c400c0c1360085806d0f10000e88044510b99494003040c81001050343c0951f800150600d45141007800c580e5845403041c21990045040c88a0501024109445294420055075118180042c4d040c031040c041d9020307041901416002c03c4940c0c08100229005100709441241c0c020400ca05141d000e842e01140034401500c00d0f410030004004a450f500300100c1c42800c6a440b0300c4100c2d141e58580142c0b0755003800c10982c00101540e4425503407225903680c1c0342072410740f90120340380d03807048808030802442e21410840b0444140000308000903e0303002c1c0805403541c1030107402070f90044c01820b4012a20f4281c454800d1522030141c5582c5047c444440d0700c441e24000c0140f00005442c001c52002504c0000c2a41c002c0e0005106041542500e99110040301e40410a807521282840a60300010b82c98148000903034200c1e40c3e000c210180f40290421070301901940000e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 663877670 1250 663876420 663876529
    0x61e0403080105120a0f030f02011805060403141303080301050f040e061b071b050f06031b07240b0103270209040c0509011e0506070f110a0b0a120e030405 68
    0x286c0540458010b230703090405540382c0306c440c000003400d0107403224050fa44a0050100e0b580e41d60740c2503518505a40e420344401c1000d1142c01c0038101d0102201d40554094900e50f51258900b104202400b500501040d0040e81044998440020005451303500b2074000c001004c00c0400502c0849107a004116000c0c2c80800d4121050700403d4801c0083c10a98505a0f100704598410b00f003809101d1000fa1200c041c00400300140d8117050011802074a0040d00c0380035104114035092000b0071801005032030031b4402698840c030310140d80d81c1600c203a10b0001042c010115100c1102015008050b840200203800b8151101c0010100b05411501ca400381000408140c502d5840318114196102d004400590004000300b012070300e46002d5040d5200680e01044090005d17215036605520079940d04030f819002510390101058028289024118010103035903240d0302c541080d15080c064600010002c0f400e03800421040c0120b1711140c2c02108010760b003206d498012141d2240c10400003c0056000003914a00c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 663878920 1250 663877670 663877673
    0x313061106060d0b0a090302100912090801050c09060310080a031707090f05330913090210050703210c080a0c091e09050405061e0403080105120a0f 65
    0x2140d40c0c000340e0010811249075544507000d008410007400d4000e415216250f00040008403180c10038001640b083c4191181017003004250780940f8000d03039048a122075070390f8840442903840180f2000803c9414001c0c460f45c200f032078101130729214900f0440d000320b100100007250385165001d4440200401c50032150503521504005158a036609410000c2440800106c1e051510501c055001d455643c80c40c1030701c182c5483c4c1000a10380d5091410780d00c404040b000f480700041e0b07080e8100f0b409882c4081e01503a9540c90001c01207500340c0002c00c00d04003450622408096101e440581240070407d042036556040b46007015143c0ca1b02018039043c408500030308500c2404060381000405801c55120703882c0c1c5845102500055641c0300c0c40340350000e80389a00800c0300d400203001c0c0125a0100390300900959485181400564400300c40c103941c16401078007402510144030102c024035104101e01407001d0304040e0341c01014001c040c418284100d410505180800105200c2e816070542c1c01150b01d002d00b0f209 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 663880170 1250 663878920 663878927
    0xe100903030f080f060904030c0c0f15050f030a0e19050a0c091a0112270309050a0b07020d1110030e0708150426040f05040c2604020102031306 63
    0x11408220001009812640c95840c090040c01d800b0340759130304400e00c840ea50075042c08001c0100070000d41c10000c41324001c0327000ca10924000400b902040380c403a0019810710740860314014000d039004041103030230451442c02d11907040982c0d410441c03000d40030805920020034107180c540c00090300c0120341b54100c1003c0811400040e41c00d98140300314080000569180025401c4070000c800750100080c0c1e69480c010550310407501800c039216501c2001815401c0b0030260310401c210740c00d011041c001820070781c07002d16411050050080c2740448403d4991801d0104810f100e01804000a01450180d02c602c01007004540780c100000c1d42c00b600450031034140c000010060000196141e0329802404404a0803c20104084e101c8411340503017074000b51140c0c0d13960a090410307013000b000c00c01c611107101d900798420640200002e020440c0712011050400f0104011612846550418441c81300e242c084401042e840ca0040003072181d900130f106e66210300040c2c1c210302c61032007008281d0406030f81c0444e00030341 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 663881420 1250 663880170 663880187
    0x8090307060e0922020d0602160b1008030405130c03061a030f07080123040603080a08010f050109140907030b061c0501140d122c010e010c0b01090b010e10 68
    0x800312601070290303c42c48601e2501840a502202e1202d41c03850031140035046c0000e00d24011032150350010b20341684040c0c600c000a0b1003243c1101c81180030000d114003500c1c140c031040040d02e0703c00003031407400e80381100017541054888010050180c0f100340c130040c03280c025030006004141c10006007401e50315030521090240e10803200300344c4000005002c5603282d44542e03800c6059035152440001403c91150b190714072100b640c00c950fa4400d031201d00200004040c240a003141c1501d689a21803654100601103800c98441d07040941000401d180801c02c403034401558001c0803205075070504c5c20303031114401200900008400d1980050002503564500e40c0741e000000e14001c2d000f8410065039880d1088407aa0380f80c2110501d5110080c014400301140c94007206d54103120140c10420700035424444469428600c4982003206416000a20500d0756005030f9038120312182440c000300c0c00c891680e91451140018015030814584c0c408102c161399020b11480842c0300704c01421090b0004610900410783c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 663882670 1250 663881420 663881447
    0x1050a1a211f1d190f0c0305010b100807020a0b0702010b040516020c01051830030714061018180503030417040f03060911040914060106090602070504090809030706 72
    0xf8688110300542c808094040022184054041c051201c003021408942c0002d00c84150303013a64a0031007540001300c1d0014a00c0045100c0c80020440d100c3c0300042080d080c9100c1c862000344030201003082502c2e640865074640d80c40d405114580544c9422404a00516001d0361032038000f450300c424480342c24070804490025050719405c403500070100d0001180c2130702032810065001c2407000500c1d0014500101d603040951101e205500d02c2e402d42d00e1b04016405040344111041d9000020240e05111a81664690003041c050007440715050034103240c400e00515106441415019484011203199076410090003100e6140c4485914031030350400c10341340c1d401918111031030740d140c8060195039003401040e50101c401c1c100303200c004180396448500143c078003440101d0304201001d1081c07030b8503901c0e481407250160107076584a940c1e41300d04180700d1900c0010303045007040c058086810451640e001550b1030a03108240c0d0045080c05103454403e51500030003440c0c55145c020709102203042e5501000048804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 663883920 1250 663882670 663882733
    0x20c0a0801020c06040f02281401030b01050909070912030909050709080a080307120e010f0f0533061b070603060509071803140a020301050a1a21 64
    0x196441004600b02d02c240c403440070058003c00000b40c0400c00d00c801201d0801d001520805000b6040303412200c1c4190501000404071202c1607081c000c00545204072140c00000b820100501c1e403141d0000303880c1d070081002d098031510707000c0e0019030a24401c5c1e038880010219128281003188c00c034039002d002e6001c5409203002181c6040002900c8a1041035500201c078046030180a080380d0b0381c0c40740b1801d80c0c401801801030109460803040214101c0c81010044035944000003560041e41c1102e10a40d1260084102154100340921001d4460810580f0303d01503040380100361b0710a40c0d510780042c0d060120072079600110116130101e00000700403040c01d840120304152842c1c1e50721880c0c16400c036011030243c10303040050100000c01d43c1d8001c40f04e2200560441c1525202e15980303030b035034103106e41c400c02d1500780f50b4002c4000001181024050250440d502072000d0040c2d40e0f8561080e18103620b0003260510a4090070181442d9a01d006414000c04c000311054a08078003c004204102812018410520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 663885170 1250 663883920 663883939
    0x1b07080a2904080304032a03020105060f01200c060a0302040e1b120601021c02010b130e0a06020915040f1a0307120c0302090d0b0a06080607090303120e0d020c 70
    0x9801842120201403107072810501034940300d80e220f2241e50f0300010000c40c1032104521940c2e6070107081099075210061000c0f484091301d045840c2c003e094803400f528035406040c03140001d20b1542e802244580306c045081060140b03840c80844824a00702d120410300d0b07041800040c1c000300c481d6054000b00165086040d407582c00303444001995400180104000507040014000500880c0fa41e20b130303050300f1900c144101c45145d103086c43c8070103084000070704510150f0355450301ca031241e0404201d150016000180c04000e5040c0300c50109454042c1060020300c459400198100c1903075511260a150a145890454072a51140b00c0c1010501c1580120448442c00760000540e005585c400c491180340e06c0d590714041402c1c45074100024000b20096081030640034440c0700c01c513866401e545010b5030701170801c60025082a444a0088032255045962560020000c110b555900500c61404a0f5414681901000710b04a042c5004009a03085040316001d031100f20a4101d6000880c40285c801c115a80c0345c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 663886420 1250 663885170 663885203
    0x1c06031e0506070e0a08100606111609090305120a09030210090206070f0201020c031506150a090e1504110a020606011b020108060310060e1e0103020a09021b07080a 72
    0x80a003064000c041e40e100d40c0c0000c10651090401001800000d0440c10040e03443d4540503080c060300b00c4542c0003c07a03a4a004203d26548801004640c008000191000315250310005003c900e03170b40101d006442d00c6204c0c0d1002c01d482072b012124860481c0e01071000a00308221182d014012480003600140304250030302900d5503080c0314591a540c0e0081c070540c07400180341c1d91340d146070340f60b10340903070541c003540110031100d44090015040c001c000842c025180c0c07406208020400f1f10034001c002550b10103200100f041da800052403000d1b20400c0400c0105640e0b00381c400782049610684142c2c0240c145000b202803072003030902612240b8040d80030b49103159903020044680d0002d054088004c82500480c100141d405100a41e41103500078041c0d603807a15441e01c086040d6038250707000c101015481d00805c05202402d14040c0c02c1700141484064055156070006070781e4001c07602440fa0070507400584054a180d0044d9554130301052442582c00031981d078000d180c0c90311520300c0306558003030620000a1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 663887670 1250 663886420 663886463
    0x30d1805191e0530010e10060803131a0c0a11012c010309080903010203070c0b0a0c08180a0605010306020a1101060b040611070f0b070c08150a0b0103021c0603 70
    0x3026a00050850780ca2540c11900466022844400c44c9409500b281490482010300380140400a04c100004081c4d18440919010032690158490b5070b05800a000e8211901150120300307003281d100c1c0c0c1a949861003045515000382c466401500990b02c40c15810303c080210b40c100394009000240c81d407088450356108400c4450380c41c0018007881c154268001c8465600940c80107840d00c0c01000342a0404080801080c2281d00c1503494101042d010103031241005048080c442d03010b60901020701900c607a06002400c0c141d0041c02e85411b50840204490f484041002071000c069041501480956941d041090096100541a10000b48041c140f102000e03030501900c400c503000307141c0706460070740b038003000f261500d140b01002c01d940c0c01010340c000b1b04641e4800038a0094004004016a188a2490410280009640b100300d00f0b0b00001303c1c22480c1c0140040065000340c000c60042400700c20080101d0081c8606c52a40702862080000707400b44600c5035010800f84c9204481541c0000b0014900d034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 663888920 1250 663887670 663887729
    0x3030a1d010506010e0105030c0d1806050903070309051507050109061b1814040213060806010e0111250f06030603050f070b0d150308070807110f030d180519 69
    0xf1400325041642c048441c0d442a0021644406400402c0d800c08031031613290780035124040e20180c010308101e0342d04410f1002078031940d13070855640c800451409040c0c0c0d401400300c400c0c1344a0948200c1c44068900741d0880c0f840c0c1180e24041d40a030081124104514240c0001d200f0791030103604000170101c0003c0c0c1c0c0381c0a889100040103848001c11042880c1403c0c0030850690b0000003504140c00b44205980c0a000b034540c14003408040c1c40d440c10b01d2400000050000801403421030420104502c40079070741c1c8001c150103101502c10008121610442c0d1609843c00310a50300150216204000000300a6071540c0050152071040c0150f5100c9208850700590b2170b10180101c4005c0c1c84200a0b0241d03009056000c00c241a203600c0d518101103581e40c883c2800c9402c01181960305000c00600381c0100583d826148022080440e00e1503540b8104ca00400d50b41d0517414581401e0002403560541142c00c580c000038014880101407180b0a064040c090000011174482e00c1c00518480f80710f040102d00c0303d10407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 663890170 1250 663888920 663888931
    0x3061b08070e0120030702151c0204050604060e012007060e030312070507060b0d1a0f04050d0c140601240207080d03020703030b0d030816020703050606101103030a1d0105 75
    0xf913400c0e644190888883c0b81d0400c01c03065101e8030040140000503103541020680b11403003091040d4642419025889010f402c074840401c43d14070402c0240202c1d65040c0588050fa411894081e01610010006031100e020510100d84001c01917910400c0403c40000e81d101610f071301c1d94511407910182d00a01d9600d01981004401003004100003038140b500c10340c06040001e018440101e0003480392000b2850b1801c5442c003d5403040016501c40e200c1d4000011a00d4006952030403000c40d5242c10703251980c41d4100e4100780400c000300900751f141030103281c081000080108805803180ca5030348100c40ca101080011001c09103202c601103e008141c004210a0101c030034010281c041c0e5040000b0803002035100010440c24145d070f9101818460701c418442c034524500c60340320900903042030180040060291074400045521072038007400042c0012030a540c011030207540303501c02c003916440240c500c0b04001c900380c03007584400320800550316140e030801020591000314010061811101560a8035401c455 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 663891420 1250 663890170 663890177
    0xf1406150f03100e030f04030828020a020f190b0711010206010608040b0615030703270c05120f060411010f03090b0610030e07120209090a23030403061b08070e01 71
    0xf0500c140c40d10310b07006001c41c0d012000940340350400100c0d081055400c90f03042601d640c0000300e0b80c4c0500000440d41041e00a0034000c80910305205580002e594449040000b40280c440380201081d41e20743d03441c04100ea070044420052020784803c0150400e4001c4101614000c01d42d500460495001240450582d052617840f400181d440da1100c2408040180c43d45800c100352811a088070000b69016500440ea1941c0208104001141450413602c4141c0e8103c811111404e100c4001942d000303511040300c00c142d80502e030181c09000710a0070074003004a00340b05401100108400c0211002529a0422090300c0d5811451284031044040b00d5582034028130b55040000410100c0c940000140481c00c107038a03002c1401c0a9040106050180340e80c03144440859400caa10110700d490585154020030000003082403000944030141803002804000b6040e109280004913291014011078000d16000705080c0503864501010003101850f550541c0e000138690340c08102600e108810150b94004140d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 663892670 1250 663891420 663891433
    0x4021005041505090d14010902180c0d0b0402040302301212040f061509050f060105030402011805040c080603010b0a1401030b010324180902031203040f1406150f03 72
    0x30301c00d6400d54016221560310042c0c100844002500003100804c0700406c100000c02d1520181c07041c0000200c01004413984c80c65420200303c1c1103810310094802d00641050007007206207500d404180248078640000e508a0000300c000120107500c0d260001c000f122650201c071032015540b1303075562030301505101340340d084070200501d07282078400040641e0414042ca8000c5800042990340000312108103212007810410614200240001072060759401000388142003010b01e80003000034a5840000c2000b170622000d1451080c403035200082020182401070070130810046402c601070440181120100e200c1c4d824080302c4112403d000c4404011a4074070030014a6010760100150040c1c510406524109941d5203120071880ca0318003018800311005c98180b80c00507080c1a00e0324040f101c0c0102203180141080045801a10006010103291164241598691329039203071802000d19894009441c100c45a4160f000e050000305009014100075403030042d1082c940b50506c018243c0c0311000e56032542080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 663893920 1250 663892670 663892709
    0xa0213051e131a0604052b140319020318040e030906030c0a0f2102070c080303071701091e05061f030603110d05100e01020d060b030402100504 63
    0x462405a500488180881500440e800442c07200c0d6208201d8400305034845144815214540200341208242510360340d15040c103140c0810060000c081d8411103c18007001c80c825a00c0c48844c1e8405a02e501101c4d42101034040e80005940750041010b0301601c0805c150000c070800d000004603000401c43c51040203c41240c082000020801002d0303805141c08100940031540c2c0e01c5900440c03185161200031510307080290740003000001400c29000510090307224481e140001201c44201c002c07158100580d42c1c0000381707001403503405143d01501d902d120102c1445401c507007100e0100b0f441d454820098034140e036100c100000f651054450034091480d200f0068110303079503076044a5400100540510006022012954001150320010b040081d50706c150500400241c00710041803404100d4460fa2840c20544074a80c81344801031903407220540d90b504009100c030b400e40503103241c089612400c000940da10881d072090f42d403044070228402c09102000f0510725001e00b05407020307540340d03407440350703024550 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 663895170 1250 663893920 663893929
    0xe070f081b0102010e030a1715011b031716080a18230703030c05010b0105030c0d020304140d020d17010f06050f13150305060d02010e041d0604050102120a021305 71
    0x14501002d0455486900c001c0c15540c0c104010300050703106940d2100e0954500100c00701c3c501001d071090002030303404000c41d0a03580e40300b0301360001440105460000c04600e49400d132108200102003210910006081080c0d506440440c103105080d01d0b00c80e1034481d07461502040c02c848040041914076110b5120b000301142070072400a010301c0503515482103031403071010242d14092556000f140003803103410501c1c007040070038010400c01e04401c4c2410350450401041c00e401500078003a41c0001c0036800320005061007611202801c003107024000741c44696840e12802904d07216000300c1840400d80400d60111060428542107040303c7d07141c3c40941d201810a002141d107580709440440000350203100e02c1c0350162412148800612142d03501c6c1c0e050801020340501501c0d0002d00080c4644644c128034070250340c01c2400c00115082c01c940005041c0300f28001d21074210003c20403503106108210822080101c158020510035254511000e050f80e06c980111040c1e1060303c0a07000c048140007010000f5007013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 663896420 1250 663895170 663895213
    0xe090f071514042402030310030f05011806020a110a0b0606030714040f0306060b13050910030609080c060f0c3f071b05070512030f07060e070f08 64
    0x10700c1c1010b041e00c001c0c1a4842d20360441d8109003181030403138400c044503603480508807903540030b140061819854111040080c59005200207410100c052805408000003036103d5005003c031001c0c2108428100e0510303000035040207500c0800309840c41d01c4034201100000d080035905c1c0d40444007030ba4564800c81444032035000030746540d00384284080780c2043c2842010141000d04150400f1910140c0396051442c03e9403031640c0b00410f0307403e0412402119842400c40002940d030240da02d00e6003a02c0300103842110320340c3c90b4406451185048020b0b802c01c5035403c0205800f1500710129042c0341c036400c05a0114440c180d0b136040003000c00b00315000b007c06c52020601c0130b400845201c040b005040340303d0180044858181c60201010240400080941065610400c9901c51001c1864080355580301c6640c1c3c00b15014441c46034940481e0041e103c00204212014030410103219a113035030041c43c04001601c2a00924025405484070110380460500e12000466600c00d00078404081001a241c400d600c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 663897670 1250 663896420 663896459
    0x30215070209150307230a0e060d110112020f07060b10020a032f061e0c09131d24070f0c050a1b05010306090207240b04050708010e090f07 61
    0x41c5c003d0015441c4503051401c401890364140e42d0f0340040b9460204414000180c014461302e038040011300ca40ea072128140e40714001d82c0b107104650206207200041ea00403010750280551240009500f4502281d2440a4440140314003010302044100100b004160070808038440f0050b8002007400020074442ca0f1140c9006c4190140d01d8034000ba0300d00741d10b248608030040b006d070a5010000340704203200d24030602100c2001d810004161400c0c030424078245807150b900c440d0f02c160343d00210b0000700040c0340c0c40b042008103400f2020040700608441c0b552266811200c0c140800050b983c040205000074140340d201d817290342e40f40007481d1610b2809845622040f4410f44440c030420440341e0004d4007032400c5000341241a0982d811651804000405a913580d4016150440c01803042200245004030398003094140041c18220801d66401000c00a05208400320b5000d4100703402d000c142034100b003509043c2c500c0042c2940325030395480b500c280c4d03c1c12110640c0e0204d9010060401c4139a21000700d044862 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 663898920 1250 663897670 663897673
    0x1d0d050a08190c05180301140a020d1104030302010b10030908040e0403050c010f1508070f030803060111011a01031d0c04050a0e060f0610180e0a0e030c070302150702091503 76
    0x40e100203485100b1074029020540100d9800550010405c0c0b19010050074500210000e00c491100803580c808500006400c0e10603c0d6000b01d48601800029082a2081c0070104d0005031106d5a034100240a840e005940900545448a41c0b0410f58840d01490400c640c225207940c0c900703490002541c1421100a00a508020b02070240c02e14019081c0507001c0c2409040350007080311040c02180707071010b440a62003400c095114680c1000115102d03012101102c0d000301c031280c0c899543c0e03c011380c0c58400d145100940c0354a005c1242415404041140912400c00e9904021014407007510150511401c140c050315540810b107844610310b01504030580c40300c01c110021440c00c446502c100e2800c10140c501c0c20203100008100b01c01e40c28805200700c40c3e0700051521380c01ca049000742d1090313001ca2a01580c80352069000000310407807110380042d000c5114a4045a03030b12075156140700e0b01c86002d030204030700c20001211030a0001c1d4100c070640d158144c004010031040e854010001e081c21041d180c0d266010f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 663900170 1250 663898920 663898951
    0x32d02130e0d031a011b080d0b03030301060801080106050604230f19031109040b0403030b0105070f0308060405090f1203040c0314031801080708060925031d0d050a08 73
    0x320541031048109000b00c40c2c401080d25209206202c0c0c020f100c0300612810001c503404a618000d04410a4200b440e0b003054074076640b41000017400c00588117203007402d5058400040001111580001210b0489241d000204999612242040481d20a5104550802c1840f0001c090301a40303c60720010b40c810002e01d51002c5101170404186040b2254001b65162079034110100305100d0141c403804141d90341101c000007940f03425561a00b047c00041d002504040d906c1c078008041e40d00410844094035045400003000c0407481c81c0051a0900884005029608110114800810000d10ba5030000d0100008c0c00c9401d103500040103003038200500585540c0403034400040401d04a401e14803000e81c4610145a440e44a205411742040084120b01d0401041001700030550380e2041206801c02c50451f6942d01640702c0e01088181d591140d401e20000065a4000707042c80c5406038040b09189040a1a0803460315205200f65101d072075031885000070920400005585d9441081e180e03512180c91442400c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 663901420 1250 663900170 663900191
    0x103020a091a0405010b1c020a0503370516210b0a09110301060f0806090a05040312050a06080f06091e070f0305011a04020c0a17041e032d0213 63
    0x16510281c4c006e86a0003000030750b50b060307520150608482c100d444c0d1070035854109070710f41c000d0152100030004a108a118040c0716401c2d80100c10f00d441d6020185901012003480c4d8902070b004100945440301050f40d03642510032050300841c00c442c4134030302e0104412000060803a845001d050b00086082d402010b642e00450703500040d1240414000a04010320344035818651301500c800240b04810080c4181d2030204543c2d660780364100fa511000516001c00d4a40701c61070b041da10043c0d5504100410743c1000f04101c3c0c035180d5580040121548681180c0c0d002d6560892552985415914005560450001c10206100d84001451061400c00494000556491084102ca816604101c8483e5110480106600e0629586509001045500710f25001c8100c0c441699095140b00c000e00c0d0b2107821541509821070784003502c0082840702507261001d192600040000a503e0200b191550703061020051000303c10350700074010107107014151070503031855000c00c856468207807024842617803180804e92 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 663902670 1250 663901420 663901429
    0x30b2e03150f09060906050d05030a050904021204060b1c0305030105150919090b0103020a0f0e0f210d050403021806031606020606100201020f0702060f0f0a0f0f080103020a091a 78
    0x801000d018000240c4103050040785e8003941c41503071156208a820788202c20201e00c001c4220380d03150b0800d040a940d501c64880101300640105c1031029038540303100041000384842600f02c10040740084420540b07000c85040d0341c1e0003401d0790b504060b0001c2d40620041c01142800c0e0303006807036110328944d91404c0004803800100001d003a00402c0b26940b1844600300510640340c0900303048100e00f401c0960409034040002480d000380c09480c50100420500c01c0d02c4ca03901c070141c0d42c0480310000b6044650780c09400c1520460b03181e00044c1c025042c4106059500c4407449581a502520750003400c0700d42c040292014068a984081d04136030745801518601c104d00810624440003c1001d0b4000c0d2802d07242c00c100300400d11010f0120310080d03900420400601c610600b08032006194100c980584031005152004104d00038403411364401500041c1030b54425411000010400055969803007075083c8241080710400c00a2000a40014180c00240311040c05a004860600c0c4607200000c2210038840006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 663903920 1250 663902670 663902699
    0x7120b0d0503070c060215070f031802030d050405031608030a23040e010e07020706021009050c03070b091f0e090a0b0a1511010e1213080607030b2e0315 67
    0x1315403080444034100850384c0c0600030b003601942007500842e21342ca0840005400061a17070802800c05a449600c001c04c02060064080240e40190458505c82c4981c03201414551250007414840d00c11502c5120000e203035007410070180c81003d800345043c806910340544890354450144581800340003031554a0b00c00c04c601500041941c04514615540361403080c03555203102a0800d0119005440240035003600041c17801211044000700185110607401c242d401c0030140040d5950600400d04006841e1207258068010041e045905c140d0400d041d42d05043c010210010760404208020444805440c0101d4002d500145c440780c0031500340000c40000344000026003000c43c2c41c00744003820303840882d40442618140e0a01300e00030080c4207100400303181d55904c8001e4030042c65071700052060101668180300e02c0100b2401003250300c5800c0100018000e0010303504994040c000e181c0b12401400b140f01032924180d66403d00c1d0503070142800c001200500701e020303c41e045030503034054000341d140c00c100000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 663905170 1250 663903920 663903923
    0xf0a050708160c060503060f2709061f081c03020d02131505040e1501050403080a210516200f010b03150103021c11060a1d030607120b0d050307 63
    0x10080c00034020302d040e104410b03e0303400820810106008112a50711001c010307040c8500200e071007941c40304144640c407820039505004d40e5201d140d12824003070500c0000600d41e028801c1d8054681104a071000c4000100c0400c1c812100d156000c0c0c1a001100d080050300e00a14804519000d4942001c00c02590140d90220034100b04c1043d01c00000c10a2241d000882486100c1c2454401d103010b140401c00103d20102420b500d030454848034100708142c3c001c2045130025a0300040e92500c5014141014103160020400d9074500d40391104a102c000f000b0703115441c818000f0603c03061000001c0350003151030382000e0f1081000c00d030004c09190100e003c100030b080b4000701c0700d00003c60b05031290400d2600303180b0410200300711080c4410040c401640d5400c0c1052030042114000d03001c0440b44c0c100503110a90307042e9a00d4101e200020450400769201c1c10391903d1052503500e40002c912000c081c95a22030f421109180000c00348145d1070840021604405100c5100034416a04580c42e525070350304542c4506d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 663906420 1250 663905170 663905197
    0x606090a15031415060906070b040b010e0619170a051207030905030604020a060f0302120403050325020d050915210702010204030b040b060102011d06100909080f0a050708 75
    0x180d0360041e8036009081a0480f04100c290795401c1c9000d400c401900030103070244c411074022036001a1034441c841543e400c02d400130007840480c10281070080c00940c00380188182e108004c000194a030034014181149103907075503d906c401c507240c0019240221545d6403580d805009141101010480030415040400b56001c140303552060545001381c1b00700c400b588924081e0304902c0070400549c2d11400d0410850f4501d0900154122008000300c00901ca1040c840c1c592412400911091581c418091441600004513031480361035188039030407055112290344030040e0301543c25051100d00c0340300902400c840280080c04000081003916840340c21445c000001111407074015001102809100d90b00819140000c600e09800c60321807900341c030801440544464890350210302e85074400d600202c4800144100480301c0486031141945840003668030080b603107500e8102240381c03601071041440642c0d01c4807426140c061042610b00d0550080584101800030500c01000401c03041e44c010400c11b0326060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 663907670 1250 663906420 663906449
    0xc050102010f0605030a03140c0712020f03010e070302060f0408120910081b1305030613020a050a0e0109090314040305030702090c1602150904020c030405040e12120606090a 76
    0x100080c21a900d001d01c102a003030610708204000d480201d800c4c0d46040c6c0600e0b090840100d040f00001d094403600c10703020f0441c8148107000560601c1580140318542c42145d15400070000c100405091310f0080e6020f02241d0040d5908000506c4d180c0f000300307200c4641c0c803125410715907a0100c1d00d06085441001310b02040002804818030320b0320070342c5944441414101a000e60601a01c00403031030040c01c810402148001903480041d0403208580741c000d0000604858107880c0130081c0d5000301056030300032806980c40d60000b14552500c48003c0d829540c5400c100c0845030300c3c22450344003030181c01c8001d42c28403641c07250510070010501c00810166008030b00650b65100940f06021051038010900c417921082031104c001e400c3e5101849500c00c540450307481030103000548406e9064405d0100c00c42c1c0c0030744000343c001034014011018004552007160104001040d803241d0b141c0f12114010203a030180c8040120030485c90f18003824540160000e03108505003412100416905292600310410554824 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 663908920 1250 663907670 663907679
    0x1c1e0b030f0601031a040309090903020c130507170406201e040605070212010f290d0f03050d1104090603060e1612060f050c0405010f1805041e090c 65
    0x400032041d081d031040c00100035561543c3c4031901d19107040840c1000c02040358001c035003810f102e40d01d140050f104642c0304000303980442c1f0303020351380303400301c90103a8003030f180344212010b0000c494494103115036440d440d081100300200c2c03040410740310010402c540c65a5038003080001c5084403014034651050061075241d84c1c2103848034012007400780668130800c0e81c200300010301ca0786603c00c00392564154141d071002408901c1c6a01c003409003194502148145103042c95291242020301c070306050312101c1d01c000540f01040d000030700c04000d41c6564058201d20300d112018000070b124400601200d8005200010070003ea1301584020350b009500281c80c4584a29050082c00707114854892039501481c01030446034074554020500300c14910400324000c4012000400303200154110300380460f180a0100064a4a5507070040260401e00806001500b050301c01c2c070100703008010384202c1440c0c0d120f00004840c80c1004005c05414821000c200c011222030f58003240f00006c0c0510301000340709100112403039041c0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 663910170 1250 663908920 663908923
    0x26010207060608100c02150405031e09011103071703061309060510060f0906080916030503070b16210914010b040b010e061c09050f0c040c08010305031c1e0b03 70
    0x441d50003990380d00d002d441e06885d0781c0000e481114003000c5d120f504017940d5a070a26a007540035122404038a6101c1180c01c19407503040000801c3e428200741c03624a0a040e130355184598a0260780303401464562020302c04070044c04840c0243d0f030f004100610000350540361010850a230f42002c4000c80e94a9116001e10507400d000385078040150940346095440007484480085c52000342d0301c2039200b4031100401180a01c0d2040c040c2c04461204083c210050a40d00c1c940107580350710220044d628440200c003c96200f007030440700380e9030345200c81d503500b40002801d0402c80e107101c2c001000d0000c80355036010070400040c400d14a100800750310100001c1c0e05001342052001361504000c4180c10028040200d189c65507070441660701c0d100c40390030711995590348070140340c008020111020f0054801c040c090400203400056100401c042540d05110f0203062840650340840207000080158100380404002c08003003640d2801d8180111001240f8083e00380462500544288a240300c0551201035410f0142030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 663911420 1250 663910170 663910183
    0x1606091703030a090201050d0c050c0d0203030108100f1b080a110306210a02190603060801060b04120302070e011d1e010312120203010f1809020a26010207060608 71
    0x1640040c00c0d4900389001141900c1c1e12008103402c0025903104484070543e40b040007910f900d600c04400400c9824601c01c00034049810071104034400c1e100b41c5440c8080d492010090380e0407a4221001040c0141052143c0d00c040c107502000f4030f8600380e507a03200d004500c0250361201c01203601d86d100c905403404c05121001c01c1d00d01d042c0d98000000010410320103d0b85890309060103a8900d2400801d512840350040e07402c00486400c040d612103034000140c561107110244410407650b01d07460402c94070350758114039400da80740b9100c1c036103444d070701030104119003640d01c050791748090710a01c1078420180c0c950348000c1020600b030b000203280d0303100002e08144041c01080010742108141d842c807205800400c28115401c00c05004c0101040e0340350650143c8503008801e44104035022440c150f440c4d40c2c50340c1941d41d0700d1041d8031881e0100b0722141d02000c18040c651090f52003258020744420130710340c1421700c5103002d9004031894020b208641c140028040d0420b10140c00d40a114002c0440d82e140f42c511314514101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 663912670 1250 663911420 663911429
    0x6030e15090c0126040615171525030f0b0906091b04150503070905010509101d060f03010f05060f03191b03090308070314010521160609 60
    0xc44505024451400003000b41d80c550b8246021001d420306507856540805034144003030244080d00080c08100040750704000b9151864402d1a0003607580d40751550402404450040c0385500182403103072030200d40108090380080780850081d03440701c44000c910307660207188400800190b91440b816154602c18000c00c0e0016030116503118113030515000048180ca8017610414403801d03000300340862403031110203480050134802c11076062105192009040c1d41d10884800002600f06200070a0640c00350040d298401d801410040040314030040136194007039003075540d40d8001d40c55007142035256140c1c40101400181c80c1d003d07030703101e515081030070b075094a09800c040d00c209020710000350511112000c2c8d0b03600c6904c643c0a940c030180005a8200181042100d03203102500410030584a5900b540081c41c4143c4a999000c000380c0d45c40400701c048400d1980324880c2c00e0681d4004016a2034885076450721043d01003111045c48034000c4040340f0b060004181c1c69010a2080b0f410052160011003c0c002071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 663913920 1250 663912670 663912703
    0x1b1e0c060306100311040b030f0f1e100513090620300103050d080901020c070e09160e180106030206030402090a060b0313111002060601050304030c0c06030e 69
    0x10840004180340401071903a4002c804a1001c0c2402c940710742c21442c14044103a01099859440d05641203081e4000c85260550402d1007010541005884098a200c1c3c3d4881140100e4000e503000c0a200e286c0c40a02030080300c0c41e0203500403034141d407820401c502c9104c090354005404200d62410f50292009408a0344510405400c141054000704040741c260140c25800d25444104168100700150200c142e09290544001c1c00402000000280070010700c0450b00c802c5580d90341d50740c0040c01d0340324594507296181c000301c004020000c1c0d8441d0301a00040100d041c0c60201200010118190840c2d900514520b0910f0302072090003001c10b0340204011040d800284001d90454020800c9448054402802603a0360300005103411959403020014002c0c00e28460b40c2d80c200b201101c49600c80d80c00081da42c0f9001c4160b1b1110b94680703003c20300100100754003e803840380e0b510801968a134100800c15024080d01456000000e802e01c2c03d41030160000340c800060b0098850303080c40c80d0900c10702149809 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 663915170 1250 663913920 663913933
    0x6010504060e010e040501020c0604080d050901050613020924041a0307020303041101050c071e090207050c0918010c0c12030915020f04050a0e07030b0a0303090b030c1b1e 75
    0xa0426002c540b0305481480324030030615192443d04a00a11a0154500302c5010b28800e00041040e0880180603200741c0b0f840c1072065846040c000d90807078000713855080c1d101c440d008103260380032100c2d0054031101038002e00004007030305c00b546c1203040141958510215520000340500c69140c0e0a00404001d9504030401d44c1140b607c814042d581c2e1002038006031a03807056204210709a072003082240d040b8107400c0d0642d415103584040446c0c003134410b0442200f0490701e901c000f00340d54055100759850306030031400500402c600300050000c11803024089018101660700c7d01c01ea0640c00f4011041e041115030b54001110890b41085244203c060301040105030520003101c01007041c043c400c2401140f052801a60342a8500180c0643e114540c851900704042c2540062600700699243d44a90000c0d20180b08485d110000c203e0b184505000003000705400b0f0303409200e2142040b01940d40049080242441c0c001d25055000d003040f4498000420343d80300004c1181c0a01840940622915116000b0403a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 663916420 1250 663915170 663915179
    0xe071205030a051819080d0c030c020d050109020a030f11010804050a021e12030c21030109020313020402030903030406140115142101090b1503060d1407170601050406 73
    0xc99101e600190780400c040031503500c9a860720030700002246600104500e181d0300701d5802044d176607032a5214165250150f0707699160400e00540000c2040b5a0560b2520f0350701c1119801c12011070300b01d2400756019943d0300003450043c1c032907100d860041c3d4000d0303086c1400c2d4040752030314014000040c80d05504002041040c070001840025005a401e54100c41062076485d004810110f00412454000c1e0f0042041100000b10840071000f083d01040ea00c058800345103c200b180d12400005980d1816200c030200010000320010340e02868010018510135880c04009800082c00d81e001580d01040940000081c0020002c0302d104100c400443c074542c600656242c03501c90500080c0c0700b000308042c0701e1400c46980324504403008554a452000e89007200c41d54900805204001e000d000c0d01d0070940c61f002040c00d00c0e25001d481d211031050140034a40c510f980c0e00041c80140040701000300e80e44080304614800c0b004041c400d55002c1d21030800c0100101d00c2c2421039918010381030f80306501541c54444180b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 663917670 1250 663916420 663916423
    0x605090c070c12022d150a021204050a030b07021c0f03140f06060c0a0f0f050d03022b0f0f0b040f060e160c170405121902010f110304090e071205 64
    0x14403c40100d070b071076111752040220400a62031200d9040d0307400301400d00c0c8402e40075542c4c00600032070300c40f6608544d054921010109100d109a004981c0c0c030840350941000050f8143c0341c4103600a030688140c07404c5d50500003110148600200040c00400c01c0d1500441016906204d0b9a82202e403035a0070612509000924461002000d02290b004460000720311480e00001c11811100f1035011144492038005402d1100c00c09001f0a001c9800d4000c0040c1c0c140300314828020303605030402c194080e2113070b00003404078403509001c80c042c028202621074041c2c5a81d1851845412250144240003007100001c2170100021541050311032220240781171400d0210a804000c81580000b03e0985208030700700c620015924030410701801070081e1903a0005051b02c405c042c0c0508102c2c0e200703031030301c0c45a15940a00d003901c45050f403110001d1b900720b500c0d0600c0503605c200179140740c074540c07810851601c44c1c403d0101401c50703029401440e1040c0c4c5a400540040100700060030003000c0d003100c1d041c0c0e80a0745a454a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 663918920 1250 663917670 663917689
    0x60a140601210b0303040509090703051e0d030c110114160215010b03181605010807082e0b0d050121030f05030c0d05011202010207060f05070201120605090c070c1202 73
    0x3901c00f0390714645201c143d101081120040d00b0000d15a000b2441c010040d10703034507004c900040310103009a00c160380c030130850500f02a406044050140241c2005080114000c00c4e056403da8200054140c0d8403800100070701c0341d000b491101c000c400009290100f200d82c00c1c401010303908000c5520581842c1401d405082c0d03218151552006d0f500d54030384502c4d480d0503203080003855503072a601a0760b0346504841010318403c8100c1d0310a03202c00c80d25a6a442041d10341d01821a51910307011031000d00740204042c0c502c2e101010b84042086031202540781d04160f500340d04070700f203101c0340340d035881006002240300329840d070607a80401a080601c40646950050905001d1221724042c481d0100128a0500a201c00d031801e1b02001d500030841503941c0e070010188944091003d9015000724400030800500ca2400303200c0107045620303068a001e0980d401190041480c0807059002d40d82d50a001c5460341d04c01100d0750243d40c0c0514119210110b81c1000602e03d081b42c2d0000540f084040c040c1401615260100e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 663920170 1250 663918920 663918977
    0x21c0504030e1e01230d020c0a0501061a07030c03020f0607110708011a09040501060317121003020114070609120c0218060307051c020d0c0f0e0f0f09070305060a140601 74
    0x9104000051000d105da880c082c5540c3c0112072400442c4004243c00002284800c0c240030b10000d00003d680c801e091070120264100448244200b0400707400401d0180c003c480c0703818424812115400c56040c88a81404401c0d10b0000009000024944054008000040c060050b0000070045c03652195a001c551b600300c019051b004070340000002d014003400b903026500464005003070304110711165001000685c050030a0b404206d800002140350b1a1158020314207482d03068442812001c0144101c0c002c541112008a13584c540381c2c015071001540b140f03280e00007020760361100380b021601841080041e4680d0007003000d24502841c100805030b580050850215442902c543c134400c00036081c080c144c1074203003002a42200070341c40000100003c60181c03a00702c07078183c01c400c1040e6845101080e21048103441c0340180c01c010b4030100d40b07240100546550000759023012100b0743c55982d52661b00700030341110b112060316030b20b44600c0102c104280c45186c3c40042483d042270750001613600c078a40d000c0c03007844 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 663921420 1250 663920170 663920207
    0x6091109090402060c0102071110020c010f14160606080f06040b010e1801021306030f09030203070803060a1203080a1803050307080a060b070f021c080409021c0504030e1e01 76
    0x490b080d900c5110031103c40030701600081d50350b00001e0806016003811000200d000e40d079440b140b04c0c1c03503610201b8810300c0413030140e403041c0c2015401e01040fa40860a0f2481c1c85822030208040541d01001840c1d40150314414140030803000e1a00e0b04081c1814032903c52002c082e04004100300c001210001300505540206103440003d0f12105045c012844220210640d00e620004400401c402603c0a58084408550b81400300340b41981612040d10400d90000300036038003e201803000a0240c0f070156134408000350103902007035504d03410350409aa103490b007070b4007145d0114148001c0d0440c1340211268965103141c22200043c441e40d00814510000b0140e504001f540d50200e9200807180c0c0040d0f00a000c1d80034046e4039040581040803200703140354070807440b52103940c660004a10310f18640e1003000350410b10030b0b402c2c10710700138002000e503010806018028951900c41703140c081180c0b261030f000314000c2d555000c8410b604001e21615441d80e207000c90030840b01042d0000300d680c0c8032516076a403034010070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 663922670 1250 663921420 663921439
    0x130b0d030c03051204111002160b07020f04050115080f0f13050c150406031d060c0c070312030b040c020606060d021b07030b10090207080702011b0b0c0c0106091109 72
    0x600700c3d164003c00b0401620b404240f4180001d10400401060300001c0441c1c101201d114150016a56000c803426408418003244400700601e41c7c1c41000350072031900141007074030303201c402000041c100e5109822002101d20450356050f8119803002c90f90340c1c0096404c1d4030300d4007400c01710000650b03001d00030104c21081d0310b400502d20400000b808184414400507081c40c0b103407001111090042d030001d004140000b890103070100180a10b4410131074540c904080070385610344801014214543c01880100800d20980c0d80000008004400700b0101d035400343e8001810001d08010801541c42428522003103601410034810075548400c00c0303400346017907110b00681d1020275840d00d040902280c9017080361405610400410300854004071442283c00c0c1f0709081c0320a441c4c8c42100101e0203404d00160110006201200055000d200035808080c40b107400c5daa90320102e80d44a10703080300200c488424061010910180e80c4600740140c0d070180c2900ca00c107002c82040c02c1c82c900e040b0300808100c42d1003695801e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 663923920 1250 663922670 663922673
    0x120c0a17070c0b180a120803060a031403090f1002070e090712050d020f06010e0103121407050114070e010815060418090c05060301030312110f18130b0d030c 69
    0x300d0480307803401e6002c0344114100390740d140038840e60341080c0f007103280000241800c80c1c0a481c1005685003a0f92108030108070303404440d280c41d00319400c002d0045422100e949004404150804540b1756041c00c0d0000440c0d03108010801c0c00021450302e6403070340c001c52a44011150701070300440c403042070b18007040c540040c0b592004c244502e0020160301400b4203d02d03584580081c13150220b80c41d0500760440d02140d404000418000b035880b2400d10403488101b09041c01400003500300b0070010307032102242ca01401756850b0540d1078640d60307100302c8040303a00f41e640e1007141d0a917030480920036500a8003070804a044a40e0780c00044c04a00300140502500340180c1c102d0b00495540d030b000d407005000e81d20355503003041d8001da5502d4004d2a8504069901c1d0b00d6900c40003600e440d024044a040c0c2e0b038960380c2e05c6003c2c101400210090004070040116100c0c06010402c2d12501140c00307800c10b04c000c0310003902000d02c0704007804041aa40029001640d083c1a0815426111112120403090307241c6891010000d49 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 663925170 1250 663923920 663923963
    0x1415071113060b0d200910030203040602270102010c11100f020d0212010e010f03170310080d050d050906010f1e030218090f1506010e03030409020a02070602120c0a 72
    0x983c00414810001242c0f51504140c2035101d1509180400c41c0342101d496a60100c0e2010300a40c1240d5600c03a56024428021a100f80c024680042c0701301030141c00e1950b23442055a17008502c000000180030184446045d40d0780c24040c1812481150030030383c00390340c22903156a40f10085074200c504c55544440c0f50490700c900c6075040b41c41100d20700400b19110319110002c041120020310404c21080798001c0082426100e40c6d0424007280d074041c007104500303407000d055440282c000504803141c00715070100000c4c1c8201d00f0311006420030019540c6640d01d030001925082140c801134901c80700d6a10610040c03041012032001c150585020000e000c0c075402d10449055010482608025040700c01711800c2258500040c1205004040200070744100c030700c00d10b0465686849201c00714508103000d1003ca5065402004000b07258400582030300e20300340c0c981c1b801d0000e91340503100c601e0059000c5002007250329030502c010220803054101c41c519041d144500199100d03506070303002d00307a04240c83c0c51b000d45045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 663926420 1250 663925170 663925181
    0x30c010c021f050c0d0c0201020d08160e041e0f0f060b04061103040801110a030c020a030815030a0203030f0a02060c0408060a0b0a0816060822060506010e03071415071113 75
    0xda07131040b1a59200c481200130070440d041c01e002c030b0140c403d0001c100302c0b884c045c840c250710aa24210160744a40704804040f100c030400d00c5c5480b03421565805186a03886a01d110b40f088600b40381102194103102074044030100d030042c005081c655480e01000380034081601d4200c404a601e181303445201c9a0f003440034035046105e00e502200c0250300c1c144940265410060140c210350f0405d407001c20440c00c0d40d040580c0c807a407941100400045a003000200000a0482404a0f404010301261340740c008581c082440d5502c074156454400401280944000c1c0d41000391507801040c00240c0307420149000c1d82180e442001401c01940c4680325044800d5645480c129032009180b018115805240c0800540c410000140544000500740e5000510300080c1d50489092030a244023140d4802040d0f078640d03074000c00d00584a14100102861800c0349a41c1c20010b8034041e18440303011f4061040071104000f412500c40f2005400010709009800100385445d280d4110804243da50b101000803030a0b18500604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 663927670 1250 663926420 663926437
    0x20c03030103060b03240415020c0a1203021621020d0503040807050a23010609020307090501050f0d1506020f0a020a0e09120301150909020403020a150905040f0b030c010c021f05 78
    0x644030b0301804002080e40846c2401503000c1c08481207008420900703a000c2c6c0c8a40c400544041d48013411410000d060101500180c0015240050400c41400300c3e4403000d2802c0350040e0780015100c41c200d07054501010103030402014500090810099019020f842c5000091000c1c3c034422000c24032100344001803110b4540c40e40e00c2030040001102031071118004100c00e83c020343c4030f0b41c80c01c0408205407115200300c902a010325180c6c0034009103000c00454266101000072688200c05200e100380403101030040001100c1e404110040361401c11100901d030136540e10003080f1035806230b00d5150241c0c8031840d0301406e80b520006a5410b90341e41c540110324180d2061108100181d001000050501d071204208a1001c41a500c40d030f41c083d40c800808080c3d021341d0002a6008001c60000c00c0300c022110100c0400c5003107030900070304d2260760701c0009049410707906003c240103850300300c0c55405103420701c03a0070700306202400c01109040c425004107203801c1d041c07040703076a40243c078082111460f40110103503050706c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 663928920 1250 663927670 663927703
    0x10611030702210606030111030a0e01022203050d0306030c14011e050405040b030601053001090f06140411041a0325061d01030507051204051e01020c03030103060b03 73
    0x8000109840d4054840f0700c82406070700410002c41e0451406024030121003490f00040c84c11070700c50320351000003443d200880a1480d03508003c9112000e01081d5540d044070300002c00300502a02d10f00b0320a003480c1841c0309410070503103800410700c00100c5050354503054130101d82510803419241c10060314414038102c680000d212341c50003202e03003190380440203000341d800070360f42800f60980da0002d15a4031a030a0142c00c1d841804144501c04044041c010707100c03424008034070090302d031030308400d00c074211800d101040e1000141013126400340456402009206a00b07007400040030315068070b81815210a40144038031032a200c2c0480c1c800484858140326041100a003a10400710004441c09111404060804481c031014440010750074081e090030701e20910fa00741c2d000050303018400110014a0020010130500205000c1204606541c40171a40715603c2800100008003991208032810380100c0c01c05a100d03801040055050007003c01900d0460b98000f1022504480c0e607000207050601c0d48a10590b903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 663930170 1250 663928920 663928939
    0x8030a11030a141630030c270f15080609190b040b060c060105090c070b07030e1f0c08062211070803100e070c0221150106030608010b060909010611030702 68
    0xe90413425465041c100b8015001181410044140c003a50030304140311002c02d100c4a200c101580b403a1032100920400038030158129038450f8800481d0781d659403c4280705140c034810071102b4541100d600da41211040350f051100b0302c0c0c880601200d030301656524003119615024035039102c1d1115040303801c3e80c03803000748031035100d000c500003160740c80c1c1e42449400d00c5500c040000c200c000d0504411038070302c1900320b03502c8201c99a03404c1094020b00043e101840340f61103001a07030500340d5190b1b03418242c2480e0581d0042503080c15810020000d51014145610450b05d00b5454014891028003001000e0f858100c08511446400c0490045002e41e80001d04401000170400c000c1c0c0411040e590306460704920840041d8139401012121142481c600940042024038601d4005000b42007030404001c8000480f1000030000b40004c8401100380d0201020039159941400302c0c010030b001e0b603201007900752040c900b01010500005c0f12400188140000d000003c4c54410002006104079551503401400c140314 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 663931420 1250 663930170 663930203
    0x80412210e031b0120030f13080d0e0109090b0105070f0b01380f090a03030305091011160302120a02060604060b091806041508030a11030a1416 63
    0x20750140404500c1c482d014040240c004681608421149820306139690103034101000d58500030b1084d0a089010309110a02c0b201010340e070440006c1140c1310701e03071000d4460b80f407070030001502c0d050140e8200300034400f00910004180e6031100c8404202c03191000007040104039240141c640b4490010003030404c1111000201c28820303401c0c900c5049404079044a0035160002c0a0303620141022a00c9401c100d9010040e0034010310000f01821070060034083c2c1c54074100543c80010383c0032210758030407804651640c080240840f8144030141c10b00243c0d04084c040600021201c202c40d11403941c80c80bd80490200e10003007807510030002c1110740550600310715070318040d484010755160800c42d00c05d4480c42c24044041258240744040d500035180113018007040b840d15041c0801e4040380103000d10380050340d0308491001c0048941059005064070400746503900c0e041c801c020003d4000381d05420003644200082222241c1c0400c243d68100100454292182048010b030303d451041c0890141204104506044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 663932670 1250 663931420 663931427
    0x11d0603090307120906210618091101030e031e16060e0c0105071a041e0312110909070e03101407020c03010b0d031805060a12050a060308041221 64
    0x264035004404500d03400c440413400f10f44200c80784c0681d10010307035118480980c004c04855840c0401c0c403100c00c086082500c5411400d803111102d005042800d41700e8210074248401d0b450380e4031485000f80f800348a003458600c4510754910969058684a054135844521040c81503c241d43e03080d484030441d08a50496421701ca13020b002c9040c0f81c18601e0040680b01e800030b60054080340c3da075950000c000c02e07203c4007840703480c0c600c40001842a541c0c03080c805800f00000041804101c0d071035202c7d868005010324a0282d0100f12191454907030701e00030301000441007a94072a01010340c4084149058128000c9070000b0900740f0b0f07201201100e402c4d082001d850703c070840c0702d90400d22541c1035a0132030342072041c00010142600c00e81c8900982040c000040d00d00400d1040d02058410501a1500c1c0c045030340c2c1e030700810034a50162180300002124508000807583c614005c2030780214804800b40600c90858884076040d2180d481244404c0411031a042c00300005105100c3ca83d00c10b402484000c00b00c1e02a014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 663933920 1250 663932670 663932677
    0x1305031f2418060f06030c120b03070b0d090804030c170a03050a0324030602120108010501050a06030c031d030d0e01020f0304030c080f0a030209040e06060f011d06030903 75
    0x1080d09080c8985156104080c0080c081d580d405118a0030742540307880d0100054040852051800c03945a49001c54140c13881601100180704982c4d001a5107045400020144880440c6035110541000070010295400203601002d98841c040956660400617065500401414100400c1328034041030000034066418039500440d050590080301c11107103844044d0300c48200f054020003044013801506c480e01c1c03080d03015000348242c0c030100c0703410340329005c0788a02e14031210390044598940004000303002e030200d20401c900400c100c02c001d2296505000002e00e51a0040c0070300d008160341d5102e8009036610981010340069011240745032a81075170800d0355100e90149203a84655810500380c100350381014422a04890123900c5060b040d5101c1c5d6801711070080d0800c0c41652180801d001220305254060014100182030b518016581d000103401d100c02c2d00d003c00c82c0b442c5540c019008200c0ca80c0c6070001c1451900c0001d19202086018201081c5605000300b1070040e0040008002c1121000001008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 663935170 1250 663933920 663933973
    0x41a0726010905010501020a0b150607061401080c011b030e0607020405150102061005030a2a0f061205070203120a0f020705030309060f100e0a11030405100c1d06130503 74
    0x34030144e80c0341c0c0016a51440340003c011306000e1000d0001d9021890f240e824010410010302c240e1400d40182c4801040c0c4060394200e00315010240010070142c6010082050324900a003406c6001e42c00034610401c190302080d4020341070002003213040200f56540000c55140036070061040040d4240310301c5c0c0070718510442014601500c14500461009070080d841c00044520090041040d10030943d1005a201024002d800a074a100a006004c2502107002503001c1d25158404400803454840014070a003010102128007610f0b0000384103409074040110741a80c8114868000c00d51107031070081c00109900c0c1141c11502744042802010440088020742c081c0380440101c0d40c068641c050381240144040c2e5403c00384c29203042c410041c040d0745c80301084d88102c91003000540c943e00c0840d5190750754401c4a0494881d0045d6849041c0c580a602c0350b640c85848518041d0b503800b429280b40c070003030805600114031500c000701e40c0c0307200c0710000c846200107810080c098881018400b000b481c0b506020100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 663936420 1250 663935170 663935189
    0x81b0a05030a1d030a0e040905010513050c0118090b011404090f0b030610030b1504090f02040c092607080d050c070b070201140307030e0a1401060509041a072601 71
    0x8030b80c1140206954010f550415016526002e24904c0c00e9681c0000c0d0340446411a03156030b00704010074400e1240b0303807040c081521a07490040313a91510f20304001c468844681800341c140d440d12555190049600e00307562000d000002c46007960001a50254001e505080b1116000240850714843da600000f01c0510b040801b40b1620705004200354131005d0444004990100d0000100041040c40401580000f005d004a5607074940600214040d20000c007400c0e00e0305d11160103c2811410940302c1d10352400e81d90328004038a0340c10020304150414141400400790680c001e1a04a500c00912864001b04040411078103100c2030528098126000b1408140d8a0300415000181031101001281c8485038140e640c2e00d014070141c1100c1e420b81d000a800f00c0304240d640c40051040c03039010802e01d00194002c9a40c682c4400c04200043e00f52101034001501942c1d180041c440042c0d480c100300802c030301200840b0340c90303503480d038004848088501c5020201491818055807202c407031181454141c80030001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 663937670 1250 663936420 663936431
    0x230a0c170703080a2a060221040506062809050103030e100e01080c09031b0405060f0d15021c060501090f030201080a15150203131d07081b0a05030a 65
    0x9803030645404aa11002d003850000300540440785101d07044038010301c5004015001d4140c8007446894040c48001c07801c03900340da4001400103000354020202c0076059400c801001451606a403211303190036018000301d0003600816000401c0114040c00340d844c0801110308207451b076a4910109014190070f1000784c01065109800303905038108201c90711012031998540d0304000724642d00443d60008020002c0817507403000e10032f4030b2841d5024807514401d0a41c807000204d8807501038040208071080039002c548103c0c50103503c21400d2315072040325091590800389141d00000101c42042c0a845040c0c0e110b0040c0411800321085024a03900c2481502c40a982e4000080d40b182464000b20f0351500002e401b1800c3c81c00000d43d03200881e00002450030000c090315940030ba6400c20851603407010082c0c100942c1000c10819000c28402c1c03641001808004007048021060600988071b1741d001500b00c80401400f100064054100c2c034a90704480803d4100250b0b4032201d800c4001d109810a6511029403030910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 663938920 1250 663937670 663937709
    0x617030403080a0e010c0204090302060403180f060c020616030824010e06091306090b13020412031b050601090c1206030305160c03060515031216230a0c 67
    0x20940d020307a03500c04581460030002e1401a1a124841c45a8904022000d800e140040e1524040c903841c16210790020426421301e031074080d01e22525281004c1860040800030446020785c02c000b90101c800600340001a0b50b11400400c41621601c1001000c106185120008045d0b00030581441003000c00c20000d82e005131043d003140480b4840e00e649000810044c08001145021801400145801400c00c0301004070800c010b0141c0d00d069101c1030030180e40301c2e070070f113101c0c00c00040340414440c030342c1c1c1c045180c1030800c28080000300300e070840901044144c100d011a00816580301c1090250050200c0341550b03510342c0100003402c000214200081d5041d001d03040c00199070700401054a5158840a08043c0d820199804156002900381d030140032100c0c000001c52080d2041c01d024080955214010319043d20900d45410081c500350154034408222001d001460b41500003042d070391107e4010361800a08900340d500d51489003d410150090010300420009807028900c12510310139041220305011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 663940170 1250 663938920 663938923
    0x30f060e011d090715030207231203040506040f02121c1d090a0f11030a09020a0b030c030c03040821090c010c02011403060a0803040902090306370f020d0617 69
    0x9450f4001280c0c0901410701c4010f8840080c00341c0202c80345401410005d15840390303243c09010149490300918035481c8034a00810074050310300d80046209000d851810540d5842c0e6991100800140c6002c1d10301c20301100f10340d1a0710500040401c44811901070316500f03194912011001a141c0300410a01c40c44c3d1149030b84203042070010031030002c0540c805a510300307148a01070310921000141d069550480070f0300109840d0f001e0350046010b808001161181c500c107200b4102c82640210901910520401c0aa00d011b40c003183e17401240340c402c590f103039103a9262482e1b15008e0001404a1005c0110100c0d1460000004e003500c04c030003d404580703841181c200155031503200044007a0000e00195a0714071008211002542c01c03540103091032026507a107040690964101c0c0d0040b4800d02d030001200b070228507041011903007220303145144400c1c0c0c1c0c00761965040003080c8140e1800e212522541c00030300381d294940c815095616000b00039543d0b90381c200a802c000b8032180c080c10100c103070191440c2d1020b074030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 663941420 1250 663940170 663940229
    0x806091614060304030309111002060613050c2d0f0c0c090105130902270103050d02010c0509190e010b072108061207090213180e0715030f060e01 64
    0xc010749401d03e552150380302103010382520700b0705030b80400410540c103040c2c1d04c1d17030a844290481782ea406021541481070801442c00c0d0084124101d440c1460280b0104689003000c841a403400342d440c02d00b10206002080d07801034001c0160340302503035003c1085e5484810081c001e10805402d5005e584480000b4010044040c030203000341500101a0955039490b10850740c440307000c42c1d0004000c503407200340041900b6410302d24202941c0c200f100e0440100100101004074460700710340c0e400280300040400344010998040c01410902c40e02c0c6240d4174a02c040d103100040c41c090000010040082c0d0b845002d00607072544604e208541c07080354031404c0c00318086ea0381440750701d05078182d980d00796544402c410003680708840d450f40484e03409207a90004506160303100030030780d07070312504580d241d80e51415904011007a806050413000300d0900217059181000882d000f805c0c2d40760359040342011080f01008800414002100c1d0021300d280c40c001090070140726501034100c030341601018032b118009251202c1c0c0401d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 663942670 1250 663941420 663941459
    0x9180501030317190b03120406020109020102070801090b0a0203041e1b3005030d0e07060305090a0203070b030a09061a15070b040308060d05030318160e0a02090a08060916 75
    0x207408040c040d20b113400030b800000d155030006045400494180544019980c0250301032030160f9540c159040842d6014042c1030024101a40204002030841e00c032070540315001800030f00101d078000005401c00c0540e415000c41c03a10a918540c0e405c44582c6408812500c49003a00a5002c000c0740c000100260444c100d2402c2c4000d404080c45038010320010090080c0f50071104440030b010620503000214060301c40c41fa044400180200740e210f00d05103018049030b1001d410440141c0100440c1c0005d030320009050741c22200c00400d240d80d0380d941c410000006011900005103c1030a01c3c170004070400303182d810140c0c001412680c101c540f1040301c0d144d1000d0702c2106030041268481c4000100400d000b50540e03984994003414502145240350795150842d8011a051800300b03801080e000190002044804110702e80315914058907410301e078840440d20f40080c450f05403a40c001400140589801c0c1942d40149100742c2282e071182032140001c0c2d190013210114400c0ca1402d1040007540c2c0401c6240410f01c91b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 663943920 1250 663942670 663942691
    0x708150607120c02031020030c09211204150504080a2603090f0606030303090304030b1f15080a02090d06020304020a0e1602150103031e09180501030317 67
    0x422903a581103190403009541006003c040c10096000d030701d0074440346030245951403000034500403c0b0352080d03203194456568458548284108120585007900315500083c013220003140000c490b6904118110812249180c503004003141c001382400700a0241c01030362102c100941740582060404c9607240180c1c0304001d1943e100520700c0012442d034601129840f0001d15207e0807440141034680c00320b5109032402400b940c400503101080d02014090783e504114100c01840c9181400007880c9c1e9a4001e5000252030300c002a00441d400035244011812003a80803036249252943c0c60846802c03511410440c03070040360f41080060b5070003049100316294000000d0001701c400d011911450020340000f80300301c1e00030b07682d4100420184001e1250901c117904400c1070500b00e0058400080c200001c150180c1d02c1e030390b0030100600010381c10401345000d101c440040f000e20801030800c02c0760216080c0e8130400c1100c041c601c0300110b0215681145060368040d031210303a141c000c0040c400d20301d000b04454506a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 663945170 1250 663943920 663943927
    0x25060f15050409051e030f040308040905061e1c02040e0d0f09030201021b040b0d05010e1501030f0b070c1505040c0b0c0d030c0306030c0f03141c03020304030c1a07081506 75
    0x10f4585140c201c1e452848020881f0b0070a00700c8900e0703402e41e9209400607540705030301007410403a4000f940506030340310700c09a4947e110900740b00d010696241d600485248141068101140030030080c08800c0c840640040080c40718020490321951110304200c01a800103c0890000040501a2042c501101d50681c003c2c10148458160300c41942c0394281366561041e00e40c0208402c030307696285202c0b030070b40c043e2000290850b009140c480c03600006565050800c2504001000410070050300381100c203070010380400301641c8401e001c45a01921400c0102060000c1c1001c019145440e480f0710b10540c030400f040c2e40c0c001d490f0b814541482c0200c08a0b49101d0748100e4544000c6031080e005204c0c07040702c509000c0360079610b0780c1d15010244a43c0e040703c1040d40d400380c4d04006024004000c4c04081e00518050444603510f003041421a683c804540014160000042010144a07180045405420081103100102400010381103800c0c00da46910018000c000401c0415843e0b5040c50540c020041c4075070302c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 663946420 1250 663945170 663945193
    0x30212012d1409120a0306080607030c0801120309120f0c0b131212030b0a171c050406080103060902010c020a09090b07180e0406060906080708010608070b25060f1505040905 76
    0x4145c1e21500032131040546070100006c00600c1000124014100d9403004902c40c0007910009141c000c05034009441451002030560200790000084000d94801c8691101d03418102c1c1803008034641c0b0030000800002d61100f00150307101480c80074221640c681c031041048155070b0b040406441d5404c5c00040c2c01c0c81499204030403201d0080d400380c40b00c080003a000740038155a640f402420096038640780000b0303802c100d41c46d98400348202e401414680d1282041401c2a0034580300411101c0305000003083ca5030340d12160015a0b0069026824040c1d004115084054607140510098a00d400c811504070b0516402b00d10b01c2400784802051200449802c803080c145040b000c4001401e02070800d40d441e03a501c50011038294903d000c1d0401504080d40205991840c00c1c40302801c41d907007540110b00c1074108020a21040440600300d410003140a950700074003800c05801d010001203c020002c0683c1e203480034901862510750403024403107580311007180d080b56031001404295130110f40e0042030342c0c020010303041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 663947670 1250 663946420 663946453
    0x50601050d0c020f030c0309150a212c160302032e020a03050f0f101503180c05120c06041502032b05010915030212012d1409 55
    0x42c20340c401031044840c0045400315482c150ba0001c54030500c941c200042e01c4205080072401c3c824214000c08074540b40444043c002030049019646200da0310101d4907450500c0105600440d540c02040d64881d4411140c2c04980c40e030382c08040142080b0b90003481040811006d030b0344850f8040340d0300035020b0310001102034000e207559503012020700c41c400015010020282003920140c001c04a4580f000034007403c1044140521601c010601401c0c40c002d4410001886522150403045564058103122400c141c2c16098000c3c103a506500c00307003049101503040502107690003500441e5010384192840030b00c02c1044649640e6508080c0c0e82200d800c00c01041040016964030035504090b20540b400e01e20391880d582104403034603002d0402c6402c03008610180c4481c605c1440c0c010003410400b000b00f030480301455000c46050348000382c0b1407507013034281d051514003c0d00041c07505e1300400071040711000b148010300c11660381956150360040c5410000c000b03060041a00c1070180310414020540544d00c40c6400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 663948920 1250 663947670 663947681
    0x60504090f03050915031003020a0509150f060405041e110a02060f0606070b2d040201020a032d0c1704030b0408070c0e010b0c1b1507110d08040303030c03050601050d 73
    0x5400102d00070130143c1040b08178010b98003074540d07031b01c80310325117031840c01000a4210580c00c442e10490b5580d0a124610009084004002d1820348010242c49822000510140115440381e908107050168049180e01000441c01840918800810504200000c440c0c00c2d4000c2198007800743e4040404580180c2902c1e20040d0712540080c404c901e13049071907684019900041e115801d44d1002c11003d407010044001110030548003030071104242c1d1816800003907035030314082c50103000d102284100d84000300002c6405c0034042101586581c1c1031108000007014802107103819210250301803000410004420b00700c904a0307411100451841d200d07615014040e83c026030044613004c0c540d204c0002d221311605491802080c20304010394840a5410405007400110b02c2e00c055011800e00c0840a41e070380d00c05030b4040a4050320003c1da00d514240c070340b0705084030214090030ba00c00f0f6081341c01c0c4100f0200030b00400c107903480b07560140603407240303014103409443d02903691034040341c400d0007400f62055003513018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 663950170 1250 663948920 663948937
    0xc0509061917090a080315040216061a0f010503091c0f0e0a0608070f170c0405011101050f1810090507030c090e07140f09240a0b1605160603050703060504090f0305 72
    0x4407103c039158200064200d90066100b020782d10311648c2b00340103101041c400c5141d010341f0758a005c038041010b400024910707113083d09103d05000f0044089448840704000e04030210340d01318046039699072544806010031090b070316148001003045004c440c250501e90000802c9030001c0d2200d156a45504000b501c0c0982d280404004101314201100f41c032031030144005015900100806644a00306030004100c12101d030f180c82c0107a8109000d005040818403921541b00c0142014283c1241c07070784014078100360285820040d1213040441034424024040b61030b0b42201c0c828407251146544c1c0d091000d0039605202011503540d007200c41c0c200100382c02c041e0000c1d00040c008200e425103020900001e0a01c200076200805001c0c0d014906107205028500d000c0c3c2e0614041740c1c3c12418500d44840344015118076070300226600c810300440c0c0c04020003000441205c03051100003030a42510791100900928003114640b001074241070303002a150820b403080c108105d800242101c0c0e010b5254a09980a6000908 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 663951420 1250 663950170 663950191
    0x903050705010515090112050a06020a121406090601020a0b0103080a030e1006030348050d0206040b1b0702010c0503040515040e010e0c04090c0509061917090a0803 72
    0x3004000410030700c01d581c46903000300143c1e01102101428001d680c45c0582090b4145051182c14402040001912844941d0300c41409691594584d0b007c40d0704aa240078645001414290525514880248001d114140907500340c505550b03560012680c465080c280a05002c80c45c600610200d0200c03c000c1c040800d083c28040b4101d01101c00d00c46c079001000050101f415075420741401055842407481142c9a5031402042c1109207a02420381001e80883c101800e5019480c0c2c1c1540a0880410740c0501070b80100a8403852003e00e0401b0392500400c680c1128010b80540014526401100400445004c10300496080c0030481d07006488440003142e00751494072003403000103101d6841c1c0c041c450410080102c95030311035140080c04645a48184c00c03411020340c2d50b20410081f480c0d0313013064504540004401041b1051100410341d40ba124000c10160404e000081070241407103140200716001c54250394241805145103030000c2a110103461000c5150000d1071408041517011001e140c11160150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 663952670 1250 663951420 663951427
    0x10e06031311120604050c030304420203030f060904030f05030a0b19090534030207020901090204080613030e0f030f03071211070803040b0a300606180603090305 71
    0x240000c01a83c002c010a0f621000400041120520441e90000c2095008608150410a000b9600074010301011244882c1d00020800710540c0e41c050344458400103a01003030b110103087c000351a607104450912141000c500801c1150501105880c0700c1e54040c0e44040d241c22441000b1211035002600c20268117032661341a071b8281c0d0703c200003032030190800790103080e21614000e014415034200400e20003a0401e103413604004440104520407240000c800200000050014154000d008000c03010390010340110011445020320f6008100fa00d81c4102282e0042d581c1c0721180d40d54155850300280041c50030510301c07072582400c1c2c601d400030b1000103082d00d00140740c0e500800d03c4d58111400035034208248074540d01d90345400140d81c06901c4014006440c42c1030a15030350036681d110794031904c4000c1100144442010340b2030044124400a00c0501c1950011070303400c80000c030307003411031204007581c83c2100000b07d1901400000c00035500400d502803020f441e0400603002082c070014150305020082 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 663953920 1250 663952670 663952703
    0x1403070e13051b07020f010f0207030b0703050709090e0a150b030f16120506070f0e0d0f14070f05240c060103050d050f0d0509030c01060f0e06010e060313 68
    0xc01150340400705410002a10300c1d04010710003050b011500fa400002208005807409612080d051800d602001c0c2400a403d00840c40100d00c0c00000d5030010340b020b85054203002d0305940c1608214014215550340481c034644860050045445012035044d0542c4462604000540050103607038400c80e6500001401c4141301c0f0210f41080201052200f0b079170010246040010b00140425000c0c0007542c19507658042a5035980d0b6031450094a9003061007014a0b200341366034482c403005481d2141c050300310b0642d5915894119520100781404456605402c00391003420369002074590101d4062082e004c0d001481c00041c00040441d103e20342d40d0b0f68000d03124a482400600000b8264070303000c04020070300c030741c0755040140c103001200941e08100320080102898880245060360164000400d0004590f260444c00350310f18422040c1c0c0d11100d50904a00140d801b090a030780301c048542c000d82c14805640d8000c01124100d0345c00400366400310f0180080f0351041144944020034074403681c240707488804038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 663955170 1250 663953920 663953929
    0x11120a0f090524070807030f090f1a0a050c0d020c0f0304030c030c050d11040b0a0e0106030e060901021912060b030f041a10090902030a210f050a1403070e 68
    0x4001601c0c0740d0f101c51403000100f2610843ca40c02c101505451401070305040350000c01c410030240070a410551a407001c400685d0b101c1d44181c2d100c43c1d2041e9400307400d41d0949001601c0490415815410b015002e001900250150203903d1107041040030322842d0041820044000b504412540e119501c94160b02c940d1ba0001000104082c40c05549081e60031451803800e0b40c520401c1e07805c42d078004d400701d041c1d240c0064000e81c2d064401c140100c80100e4421645004111051a2544503081c0841c42600020b5103079090780c040b034100e000e16002c1d80d190b40e441800071800c0c0c1c07003041c0034040e0020103d900c2c80c000318401d000d071502d001d1203800045081507840b04440030a42064811001c154910001d01c020014072a500582d08030708607540800915010b503c8070407812851281900076500c40b03400000f1075a0070300c040480350b50b01c494903807640d840e0f1307040f0000014130010360000803401c01c41c500221180101c059809080b041c0d0742e0071f0b03103420340101c15180c01c3e0005403107401407085100d00000982e84 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 663956420 1250 663955170 663955181
    0x708120901020c10020f04030215090a06030506010e030106050a05040507110303160e01170103140307061515090b0403121b120201060b04080a0b1b0712020c0411120a0f 74
    0x400100150f2180301e040003407814a650301400394086481041912044810301c41902d0480750102c81d100a440e80b0350418a803984215103a055018007140d4010610940650220303000d1102139a40e121503604010034182203850034010607510000d0316104101628042e000240d0280c440d1400c050f03800e41050642e8071b0b42d0010707500300c030204107810820890310344d100d401038581d44e0003460100355100c034118458031101c0040c04080c0c104669142d80e850819810400c0703c654640c000c0c401c015411454696645489840c0603c0411100d01a2000e1141c0e1180c1000016a2194001c540c50540b45a4510b4a0021010ba81c070060092041a00700e080b5140000741c04481e0040105170f145a10300d045c002c0c21602c064115150b02c10050005102c0b01e00000b40300500164024030800554940700025840d241240c3d40c0405a014001100020841c44440352000c030031040c0c003103e60441e5958100000e44829039041040841c00340103010710756000d4a1015000344501000080350380140446100381c56 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 663957670 1250 663956420 663956431
    0x906120209041a070507031719151e080c040b1c05010902150a030b0901060f03050411090405070602010b01020c0f0d150c030605030f150403050315040c0c0b0f011a070812 75
    0x8401040071b0051540107900da20404c0d10018000701c5610b4520100e000c1d88403000d0640326060364520500092041040c4640041d16448a004d0300c4401c20b805820342005443c003e400d540e0280302034031552801e1600541c01d00785401400484e040d0303440440000e1000700f41501392519929003403044096150345048454500318024140e0380c954511f200074007510540640700e801103030701100400285a001440b01c2d0703485442c0c500480e0b181c07581c1c146592002c440c40703040b9030702602a8050108012000801d4411944583c0090111080741d9005a850724203052010f0b40107038410318030407042c2c50660706068245109481760403130161391aa006c01203070b25560781c0c000480c1c0ea81d082800076140c1040b08540840706d403001401c401030b8096010141c000041d1004007400000f00110700d00c041100c4810700d07040d00c09482004490791281e001802c400c0e07810011382d408524000401e25048207400c4150507211200481d20900c04205e6020880340d0283c00e050302c80f46000e0007203608090040a1150081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 663958920 1250 663957670 663957677
    0x1080a2703020607090303140f0417030912070609150210050411010215160f051e120703051015030b030102030109091718040504031704060f060906120209041a07 71
    0x580c124900686000c3c40901a00b0a004410300101b00203544a010f0398140140d00c078009846030b5000011000d81c0c004c6800a8882e51321a109170b501c520000005000791100842e01507180d0640d5000440c2c54541c0f5003d05030009500c00e2003809a107161008095503000c1314412100100b120001c940101c3e0b1082d41d0480c4d201c920100103500d40e40c0e0410a03080d82840b0709801c1d865509200c0400044090084040818007103040701050055000700d041d91841502242c060350700e0007107003031400c0041d4450850003004000c40e00c003180c1c89900c07a2103111301ca120402050b2070b60f1420520702089120041e86104200350302d07103186030301c651404c2c0003450080c145200b01142c50a00c81c6815201c0841d52010420041e1080c0400c4420590300040310f0303240c0105440014440e00c650800700e404018200703240300030003044800d2004100d0759501031545003000003000c004403078075100d0160540d001c5100e041c85140440e00c84070090328105685c1600300d4401c0c898100d01d0903060002000720751003180e115020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 663960170 1250 663958920 663958991
    0x10f0905180118020a080412020705030601030b0103030f050708070212122a01140a0b0a1212120c23071a0f0c030106080c0d09150e011409060601080a 66
    0x107450104000f08207185501003d5041c003482c1203008140360b600800160220050a82810405000f400003c2c00b0b000c015054450341c0d0f03102e0030010020071003840120001001a10f0003801c213072182059402080e0320425443c03501403207800700079216200d1004000103000700f0444180c00b1542070010400c0260154003940d0b800080e080350003556500d0000c0c1c0d9816410310484003081040e05c0392081d031107122040700191034101c1c407011900440842d000311500884403003002c02400408101003c85101c01d40e50308141300501c041c0041507a400c2a010740114689050031184040040c2e40d1f41d440501c0703d0000c6040c60042d0302c8240c141404102e034402201c52042c18000ba4116080d0180c0d8421601c2c40d416107903503d001c10051a8010040c12070100d50b0010412041c90080c03a0007501440307400051044600c00201000c2c8000c0c400e080b1400c00a61030b11814031241000d01024510600307a0001508150355014015610804010100325041d030307583c081001c14204442e0340c0d01030240012648801c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 663961420 1250 663960170 663960179
    0x15060a11100213030f03020307050d0306091505091603021306030b09010e060904110d020907080106090e010b0904050702030d0203090102072a150302070b0c07051c0e010f09051801 79
    0x104014608030703010841c010800340b00c01a2094140408a80d48128205507010050500700d0450060241c02030a5005070740d1301c2c01c82c25900d80c010038241c900c01c80081082d1440402001034006452042c160040e04000005015500041940c0e1600c9034a0401500d0560448000d4040c4441d6070441004642d440341c2260040c1090b41c00540500b80c10450704802d030038044002120f43c03000500c010b100070714802c054080c42d06d8014074102015800f421110b05d60806510245c68250700740a4600051881600007421921002c0c2c0141214050394500d0f1030b1003100014080940070042c404015031104210060340000144001c43c41000d101d0001612140946880900c01f000c00307101c200764442100c400700760380c0800c0f11198129070b034501000c09554080b010a4000e03001e04607014080d86242c400304410218584010201c1ea4401e03402d9a20744607895403141201c48210700d45c00002444001d80c0c2c031141d4000e110140d283c22250504151071640e40b00004c15012001d01c2082c206104c5800400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 663962670 1250 663961420 663961423
    0x90f03060e061f030f1e060b030c06180d02010507021201050a0c090803090409140714030f01061a030405070e160906050901050f091306081e0105010b07020915060a11 73
    0x43e00b05109908000c80740540d01614048000d80c4e000140031044e1404050003000302c606402c40016002c10745402d4013241504000000300000d07540c5a000307028600c4000718a15105045031300d2000a040e0740d44203d480c0d00144040e420000034101e062010801100001da61505440311119005600101d8107103030440d0500e055850817180e9505000c603010080c401107401006403a20503000307031000103100d505410325202ca40905150741485004502e0702003540745007550188004142581100c0c1c0e000c1d2000046422110b40e849940800303003171448100b41001c43d210003035410074010070403119502d44503000343c1c1c14a40191410752021985660007042d00380c102d584800103040301e003000ca041031070520000c0c0c0786e44500b0600328003060700010700304031a984580a41c1c27400c02500710304000c1151030b4030700a540c0f050810b84c0c0d10203180140072082030216050103003c0c1a030300740104a078141829642882a42c00c0c000e40081d0f88440c107005004156100e101c00b80460f40303096507032070800141102416 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 663963920 1250 663962670 663962683
    0x40609051204060e09010312030213150c05070b030f061c05060a0633051c06080c01180617070c4b02010c02010521010e0f06011d01090f03060e 63
    0x45000e17450707040040012820781d00070000c0503885403c0c00740ea1989131000a2965540350b4001450030052045004445c0e5030140c01048000c0c0300d4822503400a0711001e0881d038502003154061b0b1011041400142281090510301030724603401c0b01601c1f402d00f080ea4400d410400103c50f01002103540342c5040040e46054070101c140304008042040d0074156640d1301d20888002081400107100300080c3d40c0102c9408000c0c002d280c200840801c014258071268201e41320458244601c1c0001c001000182007c16820340318401c036089900d9152031510607800980e00c6a000419140a001c1549250b1001c699451510482c00040e400c1ca00480c074403400c0704204c014402a0441030341210a104401d10300c40c101c44525444e902420000d9504440d403004075000c0c801c10003100d000c1c40c20321065805010513511001e0603161551251b24099591103415081d0003021114a400119895604201c1c00081107825402c1101031411520441e11608509510002a80201c0e2040e54400e15070054510501a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 663965170 1250 663963920 663963947
    0xc03070318050a031112180102070b0f03011527030b0702010b0d0b060a0b191709030304030e040209030109080909060a03030c06020c01140a0e010e0304120b04060905120406 76
    0xc0c841818a0311202e80c0d83c521440010f050200c5440d25000d40402000b2110b5a0354148032481d9640010a010101d030303c41246000f4058842c006e0049025403194094500700c8103114515030a50303103414030a0540503590b038206014002c0c086100808040910028514103905012a05440e80795180010304200014143c07400c40e49481103030061035403a001c0d0300f44ca080e045019610503072103100008880b45040d522050690702d00240d55801511415102d44e40c1c2d03201600c0b030f016030401c000c903041c0e0b5851045640c562590030420009000a000f07108240000c24098030040c24407010001080c00c458900314180c41008022880d09a1460300d002c480c0d82c05030055408050041c034681d000b0707112103140880108003a40110700c41c042c1801c01d40c400001d280c0c030f0220f5940d20303060142060009000c1016100900d5003007040448000d900003007164222440700301c030701c204051070751505140f210000c1c00854099407141d0320480404c004101e040b80c0b10944821306690b4500c0d0501c090f10b4000b18800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 663966420 1250 663965170 663965201
    0x70209070509130506060c03040305210403080a05070f05100f0b040c02060105060d020d0c050d0c08011401180812031602010501060822020904051e07050a090e0a0b0c030703 76
    0x5442072a1507164030b2500f4082d0400300803a0685852000560900407222040340c5171102140020a2000001d4995200000c2c0075041000140102560400d8401c900010746080d40812901d09103501c204001c0c900140a041401000c0d551540d81c01e0520741e40c11440d0f04003c1d00c41055010ba41402d104020340c1450855040044004e101c5020b52503060520a0600c1703001c0c00b00d40040803940d42d4040700c1203403082030810424408642000b80240d0082801ea4454a28120310525007902135030a0301e059408408501814866030401118080c0d424000c2541004551000052100c01041a0280d080c07640c0354441c3c6070310f81498010302c200b914440407001c586c1000e004205086e0042071039904091101d010b51149550902c050388240ca91044c000d411070340da0b40401045c450702092418002010340349401444403114291070b900c42e0320340101a0f00c103e80360700820194082782d10000403010a0740c02d0362081b0784140c960018039181190600d40488002040040c159458416058a0855000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 663967670 1250 663966420 663966427
    0xb030c0307050d030c1704090f02070201090b0a140c03040501230909060f130516020a1109041e030c1214180102031606090b0f06060720150702090705 66
    0xa565003010740b003158011030070500100c080c107120b0709000b0b440c19040b40182440301e103209480d550329840361050b4035030300e490000d100c402645180200d03840c3c543c05139a00210182040c400a140754031030725022045c032401c1508020615881e0700500050901400910380321842c110001d0080102d08051340c8200030b9000342c8440c003001ca4404e0302c2d4071f45400c1c0e6400e04a03950312808540740101c00c14200754400540c0c00e681481d040b407504040c0c4220000140e480f02410599400d0f695107004000040071042140910b901d00e0400d081c4460348117003d4807038070456201c1500b0603110103079512000d40001d044400000c0a109000c058810403c80302d242000c0c90940030702d070003010390080808d6610300300301461060384a03a1081054070f000c0c00d210314a503078811a83d0300c1c003100106040803044800c0c040745800191080791a05030107100e42001f030111445c4c501c09640d03421440070031545403041c100e00c910b459980760f240c02500384172000c80d9122060380e941240c010400b0a00d40201045c04021082 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 663968920 1250 663967670 663967693
    0x9020c03040b0a1709061509150132040611030f040b1602030601061814010f0807020115030308180a03021b0303370c03020a0b041515090b03 62
    0x81181e049a07411642035440d01245501100d603064541c1541c1c4032042e4442c103100d80c00c0070104015000f200e00b680385c0e00036001120148083c0110480d18124642d6600310148559401103402c1c0c5044903886840500602103064145441103810715120140b280218084c015180c01c010b01e00c042103103c000071410498002c40c034003181c1c4070342d000e0f41d00c10600c04500c042c40c02512211100748140d005054407807660f10384500404601aa02030303108030541c400e10014586080c6103804103514010780d6000e598880c008821303100808040c2c54401199a113003550150a4000d940345c0d07000c0c51180d51040003074200f0090b202640006000700764059001001e0b81c50002e42c0000d400003043d800014507402004241e0006410341c0121070340f000c0604440f0159140c045c010075880600305540d80c90440280000354811551442d5030000200075a00c40c1108001081c18152401d5000d440b81e00364549000c4900184000d1726032005160414408140c0d0134030000509014074a40d0b034105400405204484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 663970170 1250 663968920 663968923
    0x2070c0905190b0a0b0f0c07240c0203060a05090f0a0302010b0a090c0e011d0604031202070b04180504080712021006052205071e051e03040809130e071d0109020c 71
    0x207174401d10707078210390000c0d0b078072590b4202d00203a8a5000a24058441c00759072100d142e10310055441812000c0e0b0b08007212007080c24000ea0381100e00c10740103030040c519565101c400750020107002e4207142d034600c01c02240320705610f400c0200b0001ea52196001090004d0818244a0346404c0da82110303540c01e04000c2807145695000543c07100e07003035091038421000304d40191801001490072581c079400400014010061000202e680c403945c814641c00c88051a6590400c082c00740614085d1845880c0805d0350803134022200e8101d140c0040c098081c003450300c00c0796510b85004604000c440f1015030030071f8908404000151044000911003039900c1500700002c84401080b1a103614400c500b440e6035500815000c80c07054289078203180480a1200390317400401c10180c00b030303000006092844440c05c0390f035222068102081d41d010f6607000380c00301e003482160010424190824201a04403942d5840d0700405400300300840c50080a08440d02c1044000d549002e0720201070507004880518010405800d1a0301c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 663971420 1250 663970170 663970189
    0x40821060609040c033330030e06041701060f050f01110715090e060409170a020a020406090911060306060901140d1406030f0a03140d02070c0905190b 66
    0xb04440014803400b98080643c010070510b84074a401142c45900440a022070f0750a0f410100300b80b4000349222955401d42c0e0085040741f000d260141c000900d0082c0250303800d010b103501401e2207420030340c072008213207404164984c009034000441010715031060540e01c10b0a12070300020303005a00307000c41520306000c00f01d280342200d07214207810458000140784800c40c00307003e401c01518001e40c0003006030115141c01014404035014a510610301c0c0300201e10030f4902849621152540042501d010302e10341d0100c00079075013003403980500758000e0b82c001e500140e90b140f1948001d42100c001c00224004907062800601c241c005403140581c1080051041d155290015201e20040929183d11000d26425146001d4018800a04e21140c00d10206651050080403682d1180c2c905400320f0703900410a454a82c1c1c0d640c40c0082c0039010a4500344014000301c0c03440c005062100e401d20015141a076503a40350080e221b03041c2c0c40f0441e02036460051000b901070b4070040240e401d8000e50144064044034000800e0040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663972670 1250 663971420 663971437
    0x1d01020303130c09060902030415060e042406060519140403021009031e030f0806090f090f030f0406020d170a050406090209130507060f17040303140408210606 70
    0x16190800d00d400c1001c00c41c100303c06000380181c140301c500c2d83d403504070029410980782100c003a41a00700c4d10b41200f106200300750855002c3c880c0d83d50f942d15551580101c0c0c000c0b41560300f06603001c0003105203000c0003d000f81070040485941b495038905110400c0722400b12150f811400b0046079000c1c03103080340125810750307003038a4040780c64800e4514402820303101c0001551000b40700f5074008a140940c01c0f05400802a240c0c001c0e00c81d0110360030140c404441140d0102c440541c0200704501250210541d8000302c0e0b8042c5036201118951501d000c1000d2950700410658140402c00003414000e00742d040c0720403054410b040c2010055950030303169229005a00600c00d101441c0e4600014040c4511034011000c8070f900a001040203003001c00e24140150002201611284103160000542130700c200030881c5070380304d2980e81c202d01c41c402d408035a0300b440c40584141c0030941c89408452040c041075120500981c4907845240d03540035071034180400c0161035003030078190400e520104252502c5240880c2c1482 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 663973920 1250 663972670 663972691
    0xf0c040b09060d1401031a06040b0117181905150907060806060d050a0c0906080601022a0315070306060903110d230106060e0307080712060905061005011d01020303 72
    0x30301042c050a00108400c00701e44c0c00c208200e00000041c00325480d056503060a090f04024015540c18041c0410340e94080d0000d80040c2e03001d034651000359201010103030881c0e01954481c222142c03080000b0724012004416028481e001025041001410403521518025004c2c17045000e242540e00706444200740d11608013400304980014800da501c5008075054200e507610308001e141071100c10800188000d00c0b220010411641d804a03090380115240340c0b0900c41640104419945410a0300c400b0300141d0045107400310001c5130064564003070224160000c02051040c2451078156001000e441c0c46074007000c20300259000500108000d1102c0901a0340b007510100e111210f1847c00d20408114040c5140300500c66000d520a14181900400115407090b44d4504000d00304800701500c0721458482c007a6180c0c05900b00300042512030100308111806490002015601500c90303d080c1481250342c2da41090072500140059a001105201102c0070040152a09a11000043c1d620f00c0046c10160a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 663975170 1250 663973920 663973927
    0xe010912020f2404140f010306141905041d0d110d1b051005061503010e01030609080d020d091401090308271b1804030f1b0f0b0f0c040b0906 62
    0x100d800300703940701001d0803200e00c0f03d560f00c95480304141c42078504888960310484091000345a10740c440c2c0546015200940c1010300841c2d07102c0c0400c04030b900d480c207640a1901020f0b50008980d9258828680c0170b151006241500e00850700b001d5050401134800c1d0740c103201918000140b000400a5018405402810070f092a111181070560068001d45c0c0b00514a11680d1407124035982140c00860141d20191081410882c03281c80d10031050001b4014a1110340c0f842c4e00410100340d09406c0810020301500c0d0140c41c24005154040c260707481007003200603c984903020007080240022141421940b140000c003c0901c02e950020040c28018000a520704c2100003a00344c1700e040e440200d0969003a400440d01c040f5903075402111012007a05e540d501c102590340c9171121a100120740c413807107994141d48074010603061007403e44401c06041c004249251001801100207010400907440b1140120450901851b1079144122403810041c184035903080e0602081008074400d006495001d0f0b0200c940b80d49 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 663976420 1250 663975170 663975199
    0x922050103120c080a081e070210060b04050607060c170109200f0304060b0f0a170601140d0303050a060512010b13151701200406020705040c080103030c1703070e010912020f 76
    0x8000c010090041f541c45508040c446066000200341c0c408002462040c0301542e0f0b60481c1c04480c3c01540f1501d90011010860540020041d45c85940f1400740790034038031884080e6500d02400d20b4000d03007103c4156503540e0300240b030380d00c4d40d094003001c49003520f881c0924021410503155094080984010412a1210b5918049684d00c07041041c002e10050300c43c403102c40e0740f80c8030400a03024011484100307018800020820526040190600041c0074060f0708020480e55800c400810000f00712140740c45d6a440041100e50f13404072140c680c60000f40011854039030b24030801c0325110180402485017840d10101480c007440c00a01c603400c4507200c0110090705044008001d000d8061096032114007480c6492050342014028090801e403081d507402c962038240c482050004940700b2464103008104803400400010744110200391086202d4041285003400700041c910f01c5400c26240c01011421605e06ca202c0c550340202d070700e00203210f040d02403030598005030081140d080c0c070b80301018003482d0061040b80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 663977670 1250 663976420 663976441
    0x91109090705091608100509011703070f08072a06110c090a050415111b0f0f0607170f040b07170c0306120615060922050103120c080a08 60
    0x800800b0060709604003454901121500b545000381c401001c500340e90041805803111002c29016181c1c06010007185900f002407151090260f40e2100c065484100a24000140e10469100010780b284c501c164a8842c41d1a1104480c0c1c150301000c0d90340e00f50703040d26101100260000f0000c40e181810000c0040d07a4602419040400c0d01a150740c2090000090000c2c09082e507001da4401d0380608074200c1c0d0031108200d9241580c0c0410030030b07584017a0034071a000311610000c25080300d04052508480ca02c80c920030f105410028200d0100c01290042c004100c19a60060289003881c6151130300540203280035001210452800340c00903105004c841c00003903180c0e008400c4160411003040c034601c0c09160000320000fa0382d01c2101d206000325400e01e41d101e0a0040024594001d6210315004090544c100d02409541d80202003200d03440740b02d0703000355030410a1703881181c071004a0800d0042010341c11070801c1d081d00360355000c0f02c10030088013180d6000801e01e480240c0d1f9030042d00740b6008a0584600a222 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 663978920 1250 663977670 663977683
    0x80708071805060a170a0b01170d18031b030501090b060a05100c0f080c1603120804021c03051c06240807030f1d010207030908011a120316030c03110109110909 70
    0x4000c01641c5001042c00010b840442d00185913080403540f031010140ac0895001d096a002c039113103e07121800601c001107020010002401c142e000540410340d0ba41c6a030750948005610a442c0c003094a4103028071828070f07500391005800f041d1b4035080e00c0341e24040d0040c50010080800f40038a111a40d61f41d04000f491003c5482000c410300440e0024130303016541c1c46070031074907110442e120b010000c0c42c24103081c0120582c0d0b20135500204038441c881c0a80003408801400d60004a0130407004104441e40c41c184035040e030300e0110705028000b4000e4102914111041003001120003814026065125515840401142c0c8401c1c6e034900030612200811490b0301034803104850a614181d568001201600154040e0400c00c0c0650b4554a0b0f166585a80307508a8154850100c801d11180c4416490781c1010345001d0303d809031120440f841c3c6a080340041001e42c0001d00c08600040440c41b6200034190311580302030022010500821805500d5a180024408001c03c040d02486054000810100c014840b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 663980170 1250 663978920 663978923
    0x3040501091a0405210124090e161d0108061614040b180414010503030f070507030210080f10050d030c0204090b07120c0203070b04060e07080708071805060a170a 71
    0x11044030070072980e510741c82e21a104072074000c5503103005a20b42079940110743c00242d096803280101f0f1460700b170850b41c00103410510f5030592a842240b011001d4021088004001003044016840381301c00c03a80d161460607041a800034030140c0c42001071025415264601808042c01403c0048002000702e100100502940e8030510660318003003000302d9070000015040b0801c00c012101001004024049801c0458081c041c0e20707003581c0140180702800e00c10364018020940907100304d94800740d80341c0c00a100ca2915540035000240c2040500c08281c1982c41c3d03240e0000541c025000340e0318200000705d0b10420b0385282c05002c01c1940e41c880b10541d203644c0c4c408201103030042500380c143d01d01190058600343d60308490900c1c1c1403421402d07207040c900c0801907801142c0c1c0402c800c5055243e03512458080c1001003203585841c00b810360000741034a42005078200400c0100302074485035180402801c440d01d001c0744c100901c00e00301400c104041c0d0f0340346a017005541010150117070340018506001d1a01c49403000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 663981420 1250 663980170 663980179
    0x909040f060c050414180105090a09081c0b030a0f03080a110307020c030d140d021810080405010605010c0803131b0303031b090b0403110103090204110309060105010203040501091a0405 81
    0x11a03401055103c00180140c503120f000c210043d0788141c05001c0c0a048841c41c80e000d081894005010514011101982200203244080f07607201140d150f07980700350b0042080046d0b4440c0c0803286104c80c0301c140102003408408070090030040d17100741c60f10300e04020801342c000d0801c0300c000300144149015070300008101c42c1450f03650b500c3c1d103000140030f0742c0c440516061600c00d00c603d03000c0d0b410b50b92240c03008005488030680802d003000c40f003807800c0000e50046811259212a041d800100036110f180500c1c043c401140d5a0614504150030311710700f140c015030026810000060b58100100e41144100d90300454060703a107450280c920301744074200001c074410b2290382110703c040001c14160b140d000581041d011030b117a03640c80c1d1030b0720340261003050a5100d04000a48141300130004201d121005400401044c1000309950041d90b000a045410104001224000220a04c850300008100761405000b00303000962600d814500041c1400d4203500c255030801740e0604106403c05000c005450050030041c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 663982670 1250 663981420 663981431
    0x703050d06170c22020c01020c061e06060901091202130c0c020a0e0702120c010605090a0203040b070e0102060a0c0c05100926160204180b160302030c0909040f06 71
    0x44000b004080003042e5407030340b155501c0304440d882d1002280c41e6108821a40443c240d030412501000794201000700041c5560901140309a18403d00c030851041c010b24041010318106c5080d0900a11b40181c005401070710701380108500d0780d03004100c034025204042001c01c8030104520025402e00c2040440300c0c11981046001d801141c0c0040900c051300c0d100310761101d860b540341c44040c40c0480c411541100140c1c40003201c0b0542d040681d006004000070f4600201e50032361110b01181c1840f40988040c07001980c00004c1100740316401d08401d40040491402b81e000d8418080003e5440700003601441d50161b030f070745560002c14003912086001941c041c00b9107a1840303da0b40110300504c8650400e44030000c0501300103140071100c007a0045c100c2900110a410301c0108110920b0007a2040001c036040b5507140c1068050900380e0090010f000d11a0018100626020003001000b0440d8400d070024140140140b151890001c0d098402c1e80100303450202c090359a40c10042d5210710b6110000d0b10003450070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 663983920 1250 663982670 663982679
    0x10c0302030901180b0f0c07050d0f0906020d09170a02040e060f0f09030d020a110a050a020f0109050d02040921051312020d0b061311030115090302030d050703050d06 73
    0x540241d4403800300d40c8000c016101c5001d030410f030524030304040104030040f040000f03000c580b01d081042ea00b008001d01c20030b040c4050b47c3c2c1c8880c0b83c00d1030440c005006c0b501c1842c0b24942c6a50000c04000a451940b02501d00c2903801a406000d0801a00400c0641c11314444000c2c0012020440e140d07240b40c00401c01d102c03886101c1015502d8800980310080444050310001e442000701c07001c610300803504040154504441c442e488002508220a903200700a00411f1013100210200300000c02c60303000d00e000d0000910240704020714114506242c0b03051110a240c204110340d0703421782e00394000e81c040e5004140780c882807070b01c2079515141c03141035895011245441d14059501c800580f00d4045040881c20317500d52211600c1407100f006400c02540000340c61281000a20642c450700d40048c2d001e044844c111000440c00c0c0b040d5001c6d444500000100440100485801714803400c1d605035560814a84080c1550042902c030b0755400980803c0c000005502801c0520a8003255505480800d0821405441c1d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 663985170 1250 663983920 663983927
    0x40503130902031b0309030a050c190b070f020c0d060905010b06040e01030606060c0f02040c02211213030e19030b011d07030b030705010f020c06040306140709061d12010c 75
    0x60301c0b00d18480d80c00d400d200000091324011280900c0140c001941480c1c40302c0000c403a1a03010401c0d55045000ba02d0071082c081c2c03480880c48441910410801480d807800000080450070811010340031548400c1984503540c842c108185440c0c0c1d040400852501050306200303001d0101c40d680c154000303070700040002e00000420780300303810390384101c601740400c99540d103084030000010a0050300e4080040504d000619041c0e01c484210035160060714640c2241020000c0030542d010b0311540030340000a200f030780192200320340c60390001c1c010261a9200c80183c4000300320700d0141c02903c0c02003210903070042c100d40b60701c9d88060007942c0c00a01a021980c50314908030903e851800500342d11a89480441e40181c046d0103010740000019009266441c5003400445844080d24a20307402d40c0079200c0300c580c01b0b448180043c0091405840c010600d02c00483c00c1c0e0a030110024419010446c58402c14012a50b210514000c50400d4010b51180d0f51905000126240d4a46480540795032900b0003021000e0380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 663986420 1250 663985170 663985177
    0x1030e0f07150203070c05040216060c051c0509061617090703020114120a0f0b1807020f06010b040312120911011b0519060b030708070f050621040503130902 69
    0x301032255051805075850503aa41e0054020080c070100940c403080c01f060400b640685168108002e05c050200ca40703440710700071922141e0b0160001100050b1100741c500f51241003003031080f1050030411503403030000d050301c1d252032028208141940c1d40301010202c5921402007080706c400030126801e028103105124994402d42440300f207002c80c2403940c04180c0248a04191010603509401c032076103541d56044140000e00401d204903000030351b2125200410388901850140012810402201a04007a070002e8a0145142d040140da641310741d0040c0200c030324000684048a134019414902d6103060141520010411044003030443d00d400e00c03190502440151002608800b83c8424440b99410704142c0c1e5203900c50300010b0415030041a184142c280003810070301005004040009000c40030000281c10304000303520150315036001c0c0800f0301c03201600f181e800340200001c4070002d15013104100703520f4140d100011007000d01908800000e05020381802201d6003c03078141050b000490311024203200a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 663987670 1250 663986420 663986429
    0x60801050112020307020d0c0312180203010b04110f03061f08150402030705160c12050319032a09083a020a0f0821090f010c0f0e01030e0f07 62
    0x340039800030030b03a0038294800c0300d02642c0789901034200d505450b80d007641c0708608800100c0804c40100600c0100040902c207025268020100d1091083c005004042c04c1d1404140643d21403480e0030b8800203050400012102140f1001da44262a03582e1000081c06181042c080700c0030800da080702142d021035004030030a206008080703d5840100d840c2c1d007400101d0004441c402c021a0b41008820b803070000e080d58950180d88240020025680c8a01100000c403d00c0d1404440d40d500c080b070100016981c680803002d0003440e1b40707010011459040c15030f02d045400c0003400c1d48004070b00380060400a20800000c40500080b80858011208200304201a0507030404824000c140350400b91241c0581d000c50041b840c0c010ba03004000d80318440d154800e940c0f11541085504141c204645001800f11078000030001d2051142d045903450050245400c0c410058040880c90f40b50503004c1c4a002c0d00019141c3c1006010301d0441c54800c0c00c0380040c9c004000c801e00083c0c19104011001c2e8a2110000d10103064a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 663988920 1250 663987670 663987677
    0xa08120906150a1802040504020409090506010e04080d05090a02100905030f060108070605160609030e0a0605130b0904020d050103050705011e08060405061507030309061503030203040e0402040b0306010608010501 93
    0x6a03200c100a224219600484690000100300f04120080d8a00e0140031014407480c00107260940e02c00004040f68016800303c503103d511020303400107101080c023a060042c595040801e24601c4c0c035542e08070750343c441e11401001499860340840c101010400c552034042ea4040c1c0290482c0c0131100c40039065062920a8501ca4841c10160f8542c17010b0209100b03040320302d501c0080008500300b110a035450f130410b080480401c684040b00300e010800d83d000e2260700c1402511442c1e401b20344402031182c400d119400032000d004c0304000116800355000c120108441d0851210b81d1240869000940a8422590401559800c01c00044240140814104211003003602c43c00144e00b0003a40c241c3c403903584000040d0125011100180d0744d400d0940103141c4c81746000700391ba9403100681d00000d072181c00090058000a640341c160300e0070001c02d8450400c0003411a80c4981243d071440da4002d50301d200f02e009032030210f944070380418215100c2da00060b819400003005d4415942c1c44900050203507200740300f002e001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 663990170 1250 663988920 663988933
    0x61805032d0403020d062d020301081207120806031009080c06010618140a170d0206090c0a0303031e06150e101e1202181203120708090a081209 63
    0x929a980044400300d0b507015000314400c00c146e8071400000d2141025403011031841c0c10302508040d00c190642c1045500c2c0020040e243c0d414500343c2841d00d40b006400c01c2c2235550400c0003001241440d0b0103080f400080d4600442c950b80c4a4010030300708a10704034154212810141e400b4108807401002e030810703a900c0c00c2140c0307080c1e0307a500003290f441c030b031050740b034003281c850034030180002a11406100c2c0200300c098601401c040e03540a0040444008440a4005070002521107145c90350502c06140c0220480c0001d28207050150300056034140284001018195525604c02080f1024203038010000820799017085110fa68001c4600e4400041c106540080d0300741d80700d41f170355180071044103811450559468500d0910300c60503480c5950045e0424081c000d00b01004108010745000521400c9034805140940303030608010301c402c4100a03240101d0940090141c1003090b4040b520301035010b40d05151039496034942c041c0003414480e0406000d4011103000030301d8208030140700c0380740d40208025004c580b013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 663991420 1250 663990170 663990247
    0x21031e0903220f0b0c010204080615011d0306010b1305040207031e2c040906050a0e0c0409120822030e0f09060907030f1409060a061502060406180503 66
    0xc0850a81c001e9004031143c11106001001c03030f940141030254924000149000c3d184d2881e90f26107541120300090007008141d24980650b0310010400b10208140107184c030790a51000003a0f141d050500485001a0020500c020280c0c540e000810061501402c11540d900450400400f003d0146a401c6145589000070030300003403154040500083d10300c1903140ca601045224050680c814800c807a510a4892058002040b850310660340603506078440001ca0f00303a41000329081c00c0d9800b15885c890381ca0304d4049404100c00c2050410074480c40d04c0c0010a40d6240d0f0b03030000f030424505c000103100d101c0c0e11203494201604101101c0d43c0120840b100c40c0100300040400c2098002140c1176030f040340109001c900300f0fa019800900500c40001c8002c07804200100c0d403540d4141048401e40030961194040c400456400d02c58000907004221800e00e4060b401107000e540c6040142006103e1540d88448075a008515103090760481d030f1040c142c0340d0725a0703594144095803200c4503841c0070222803901081d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 663992670 1250 663991420 663991477
    0x50f010807061202030c091905011101181101050720130606050d0506211b01020f0607050c010f0c03360204020c0a0803090a110321031e0903 62
    0x704441d001c3c1da4000042444401d84400382d00b029105841821083c0310180050340c950442c1c400c000600c1e12503841d4103141000040c605100200a10202c0e41340c451901145c80030712031102141a0050b0840a004030a100101c800b44150603000d400740903242c00d031200305213000d0040d400d003440484441c520700d00586031550440d040b038840c0c05e0100e0001c000f0f83c2c2096440e500b006a02120003421450304d10420840e01400804002080d02d05400078520ba4503020030611000c00f55101c00c2c401082400b102c450140d94607c4040d01e048148500481c8600c0c14000035006100720245241c000e00959089150240141c100412030080300000b030301040f40510b0350351540d13061815808090240400c0c8a400b404000d6000e04400d00b2140500602000032913081c0004500a0510300e00410014010b41004401e1004084450f4480e800906c4802c8a20741d011000184045081c95007603a0307a101c0212000041d24100343c085503c040010401120100202c00f40034185110454900c20148170800305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 663993920 1250 663992670 663992683
    0x30624031203070f02100c050a030f0b060301030201080a09080a080105030f010515010509120609070608090c010207031401021303050d09061b06020c03070503040b03011503290a0b0409050f0108 85
    0x1c0015a40078400542c001d03220f60320028844040380180d81c041003c000300303807054410240205021500010b82c85441aa052182d01d00000306c01d00200910002d000c0000d071184410700c40603042041400c0440c140001c0340e4002d880030755010380c0c40c9541e5070003c040a00f145400f44a800c1c81303401031000141000d9010300490b0b104c2d20024090044004501c4015900c5402c0709918035040240f031104180444000c102c11401580600c00400b400c614000d03000308040402031000c0400d0704610500602640c0000e104c4ac1940c3d030103507030383d03031030b00321030340b0200e009000702102071028039690300000062140c0803c070310100f81015030301d021510307072101c0f0161001c04080d14003c00380500050303103001080b51580540b4840001c10300b038038034200050b1980e6287d9001508409511640040104400101d4000d600140350070360909110a62840f40d0340f0302840355124807444440310420341480d45a44130400003018211007003a071a00d50340c0b28180c0d41c0007410101d4484a070300d640c040000c5146040010710 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 663995170 1250 663993920 663993943
    0xf040c080f090703020d061a010f0e130b03010c17090114010b1b030c06060f0a080a0f080903010f0902030c040506060f0d141807060305130602130503062403 69
    0x4100a0341c8445460704101d5078024000c003200e0280101c0400140d9820341c0950310036010760404108603c10200001d11510700700c075081d043c4040c0007010707460560854040c2444801c01c48160b410342000800c0000984003101c0803940c5940382c4a0f0150030300781c2144404400484542c0544102d40d10420400c5c01c03100ca1641c1c100500c04040010441003482000070140c080c802e841d08400100b44c040f400385913410940044156400a80400449080040d0003003003080f41121000d20407450427000c10307240d5240d5040540005a41034015042c01680c1003140c0b40d180014008000e284904800400103102d1000704a100f4001c41d1103040441c6400e002c0d41d8010507009004920300b0034540c1403107040c0e0780906c5040800c5e076207400032510600c040c80400e80c441e112001652601042510f080c03810510b0382d400010504d0f00d0720013403000c1000302001503514a91300540041e910318111b41a01000d05081d0700051b03062103404200700301106200700b41030844a0310800341d10042c18600425840342032040c1c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 663996420 1250 663995170 663995177
    0xf050901050a020301081b190e0915070e0603070c020306160e0f1011070801090b040524131b0b2101120201052505030c0c0406121721060f040c 63
    0xf982c07e84d41040802e07050131000c000c1c003a041c241080d111012209005600c200304a10101c5c00704000681c050164600e40600900c0003000c034500341c08003400002e002907030305000f2400803002810490050901e00012a0014116402807070a500101c4052000b0846030000500c03003000c00000c1c0c00c10107200c12800ca070082c5051650b42e24003800b00d400a80c0302980c10103c1c1315001001030844028440e044110380940f5101001d80b1303042c244189040f940d002c0c2070940181d40015600c0c0c1c040b61254803a00070741041000501a510f9060540c20100c40a0070782401c01c040d950700007080702d6440010314600c13541020004090400048507041036001344680002a12081072a00041d881400103040c41003c0c1040b141070030a440f055410346081640d0221016800080c207000c20072020001d401c000e0804079028400d041c1800c40e030328014141c0c540010400906803c200301008581410342d8050040d026641518410030b008240c1001001c0d26414010131041d01b00f01e006051038010000000011745 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 663997670 1250 663996420 663996433
    0x71206050d020f220614030a0b010b09061b0106031713050423040b0a0e0f0c190510020c090703181502091c0506070806090a05070c060f050901050a02030108 69
    0x40a128229082e41012503000d01440c0104c1c0c6441048103001c1d400c12403a0740d00290075424548181d02d6455181b001034403d80c006030100700000c924140031030540d0b24820100380c440090700c002c034440c1e001d50407070401d621080301112004d01c54158000e40c100ea010300d103040c2800c00719000c070204a2081c11410f08450320301c4070080c0810700b49500070442da03407000c221260310741c0d80100c0c242000102c2a07601f04c40807520340042c041042c24600543d20402e91000c050f2082c501003000443d6101c44910f030f414083c4440764016030343d402d00f682e06013000340310107822600c0d40d642c8080300a46034402801d12612030b4142070045040b1038420310446016180481d04126069a0f80e102d5103001e99113100403038401602004200e035951103000490900241b80d40c0340c0c003e450180d1174054240344004200c9020001c20008000340e40e980d801c90f0b90b8101400103070000752601c890000b155a00400240940302605011109880081e5940701500c6200c000c0000c01c042d4607002141801e0748020703c40d0078281d50014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 663998920 1250 663997670 663997673
    0x170d0b0f24031f0312081b0a0c080c120d200409150f0b0c0601080f03090607060e070b030a0c03060522061a030612011b081e0f071206050d 61
    0x8000868204000d00d008190701e29525400708000f121a4100b194000f000c0b00c0701c2604590071100031604207200c8580e06140310301c0703461822042c1c000c800145080200b0944000c1c240403100088038102080f40c01a0741c0064035812044695520004007066010b14046c40b01c800d6006d101c29503070070544107440c1c5c10b1070140b07003100c0d020207002035034075050741c0b00d2004400040382c4180d100c44a0090110754080744c0c443c0f845c0202141002c5059004046507000b908008122220200403120040c00849030301e62214000c1c10b0060041c4007000100c1c00364402c200740401c0c244007a1018510504403030b48180f2404000030800c905075410381c8525500400100444c48042ea884107103441407000b01e80000800303070340e51441800d0000c4000c0340d0f40650080042401254240070300c6d5040c807108010001c2c803107443c50842c104008144038951404100c50800859944403012490030003610240235090300901709480c241c00f4100081e5680c0d0007180d11001c2d0f120103030307003107008080c01c031384004124035200c1f01319 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 664000170 1250 663998920 663998989
    0x41202010e120a03021911100203010305072601020a1706190314030c1b0102010b060313120e030a05070816030c0b250f02010f0c021c170d0b0f 63
    0x20003040000e05409110341d00c1b40310201ca4000c2030001d040c1d80ca0a000100d40d004160403c501050344e1202240104014004208005001d0045403c84104440c00d084800d841640005448018110a500000d06014003550003201e00c15050b2038002014080e03141c1c0c1c4104a444041034880c2d00450b00700e21020000b00b51a01884d4100304d0ae03c40a9a02e813802a0714864100000000b403c0744503d52201d11400650b0309100700c0172041c005841203441c5050510f50041ca4050740040288003c40660030808030714071414150300d010388040c7c2103c016401e2450300d2034135140c0d14000c54415128046142545810003290322003141c2d00f02c0f0404501070b0415045048641c03290580342882410f00f4200754156122003858145540201841c41c8138108520004014400d00710f07046040010741620311001d80e0794805202e445036010015041030358020f29010900012550703d800c11640042044c00a1a40641084e12101c204840c5060004500020403060501c10400540c198222042c0070404204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 664001420 1250 664000170 664000177
    0x503060612031b0313080106050303030406090512070803041208010b22080304061101050a38090c0714010905190f0b01030c05010e18070e0607020307030b041202010e12 74
    0x6400c002d42e840c02010090504038801900500c02240c0d1000031002c41c0100201582d02c05000540028420f0500d0180081da8a00028001400e1556541031781d00401ca410030403401c0c1000042041e54450350b5038200403034550021113042c0e95840300007486c06282072180300158144c658810042d801c101034a03440003a00710143c2e48144c0400350f5401d012031318550401c0030340300030720b1240d540810740c0d14103c80150940c3c030080d003003807011070521007100010303010320300c01500c00700c07588480d4030112030817000819801c4101d1040d5500448000148002c0ca60b0300c030010076400740144442c041100d51040544d0881c2c0c15030102a0443e003002d003046003428080b600e40c03884140600d880031416056510352002d003403003e0707200b10341c86030803c0b8081115582209242a40c0c1400f214859407036910b1034980b410425002b4000801c000c9100e0640000b9603801c0e09550750182c0140450f22110f440345032030f88552401b610151481262081000f00d102e105000381003e07000b50b074000d0600141451070300f4041d0741 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 664002670 1250 664001420 664001449
    0x6042a0c110607060207140a020a0530010e07050f0d170c0f0616050c060403030507020a0f0528170a12090516080d080c0703090b04060201200405030606 67
    0x10024581c000940d98600250a0081c003c1c4401a910201445d0072181ca2100c80380c2001e0907003058a240000d6580c0e81166070890344c00350b40780240503400284d241c1000050402c40d2103000c4c83d01c00e0a000f0048150b00c54000c04a041d405c0b1421a42c071481000800c0c50403840155104403183c400d4400aa01c0c0e81c9451040010000114200452044a68204902d0500011140e0300c01010440d0085541000b204a00401d0030080c1ca040c0c5189030341511003800410180a250b113a0f40401c030303a40c0c0308029030020540c106821401401700e61034403e85500c07141c124072600d5490341c1403072580e0744512a07800071010351040c3ca01e0226800d03200000625000708100e4000e102280720303e441d05034454020384d44002d1155002e0034201101181c12403100600f0b822510311796000349100c041c100d8000300c0e0b903504862041d01890700c0303c203940303012182c8a43c9034010b85915040441d0001d003c0b90150490000c9281d035244010040d0020000c3e680315025130b12481d685540321002080c0c20b400c00d9400c544041c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 664003920 1250 664002670 664002683
    0x50f070209090705010210020c1c09030b0a0f20030414070506070305040311100c0b09010b09150405250309020d08040e0726061e0307150818060705030c0c06010e06042a0c 75
    0x258ce0303079150010408812902c0001042c1c03189424075013040b552146020341c2042110000c59a100395503a0001030000403c0204140344110200c10202d104002a83c02080010201c80d40c440042c40c0060081e005880f0807074685004c4140b4001c0c910f081c0ca00c22002402503941c105480b44603442c0e0003e10800a04a40e010b03542e02d00700003060703854142c03225106100d040b50380c45104000740f00703001c1141d40090805825402c00d0850498505070040051080e0b0124600811012410700018240310703c21302e0002d041c81e100180c0000ca4810b41c5501d90b201b0350070f40d16141c40362200507035000344280543e40740c03100c0f03c10001d000030000d03c1c00f0942110501800c00580c0a0704d030058000c41e10b01503054201400803901c441c0d09034020395212078401c2e0f001d040021035500091202009650f1203030007500c1c00c01484400b00004800c420b0101c00d856150020b94100d581950b501c2201045c82041551440c0c01507082c1120001c00f880f42d4112941009034800c60070014000310081150010050030044661 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 664005170 1250 664003920 664003937
    0xa0f0b04140d0306060e0114091504080d0e2407060c030b0301060f050a090e0c01030207050a0c0909030e010503250201091406100f0f06050f070209090705010210020c1c 74
    0x2101c000304008070458160f41c400040d40c5091002c09010b500e01c2e440d040b41000b0303062904240d14114881aa4541081034400e40324106400b400c000340c0c0d0169401c048402d05ca490000466241e10501040b00f841003510000880017591001e0f55046403203540b0b04490302402c104070800956a50710176604e04a8508c3d0004940300c3c4240000e0a540b104da106480c400030003501030015180c4000010b000340301c5100200a80c0c12107035415a25014405513070f43c10702d1340c0400c50800b444400d0019802c016802411240b049494469507002001603041c1540040c4c0700850f84120795000b8000c40b03010701101030346000036411060030604810034480c80c880031035499000307420000307401d002825403070410a400740c2801d140031210058001c0080e07002e1038140384d50031803c01490407805409010b503011842d01940e101c080b000c0b000392038801e400d0000e400c01a030800b007080910300070a244080e60800d80c00e07100c000070b1200c43d6900b80e0250006404140e04501503403d6140c2c1000e1010961842d1030900080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 664006420 1250 664005170 664005203
    0xa03020a0f21020706020d030c1704020424031e1a0601050f0c15100f1e0302090702010e01110414060d0e010608160806011d060a03060e010c0305090a0f0b04 69
    0x50b004010440240c1d0018406100c0b40d9010b00003160303100d080380b4080020a01840004104800ca0100c0e19804403100010605544a6400030200da1042403918010030a540000c0180f140c5030b071000781c54800c845400440560910903844e4070300b5400c2806840c2241158500c58004840545442e0520030300708600e500783d4400001800011342d40101814a0a01441e980d44000c1c000800d11202100251007e001c000c00c08200c52040d15002008000e00000c0001c00300d01e00001d07500301a511007100030410682c1a415084014a541840001d1012546080c00840c15014a01420801034a4042d1000c2c0a040c403c0140c002d160700e1200200d1564001c103011030860301203812561098104680382035501c1c50b841003000042400100510507585000406103030311104541803010f1204a03400b1031040d9503441d02c48005941c01a00400040000c0510580200301b00b080d03c10100782007000050b4620b0012070b1400380190828007107020140c60b070b610b407072201c04010070455045104892829 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 664007670 1250 664006420 664006463
    0xf010b03011511121b0609030f030a2d0f0515011b0807140601080703080d0504021216051804050c04050603150f07030f020a0c140f030f040e090a03020a0f 68
    0xc038880c04ca02d40c0d0354400303840301e10341d4002030f0510355899444041440103208000046501e2801000e0b069030301d0b0303251003d01202a20600c2c020048468000c02c2c2c013a00c0c41142c050030011140860000c0014028070ba14210956004681e07004010000000480c09940502d1a00c40354814540688d104880150b07640b5410790030554058a0102104c010603082d00010803a8901420740000203018135455640c403aa803e22400c0000d0044c035403130b07c011404644034420381d4080301c08008290384940c05050400103011283d4880e0380d104101c0d0980304030121f0507400d0400d0123641c04c1030181114490400920024090282045801d403140c030002c080707420341400c106409440600700200e00c0f0304140c50000c003510006240001010320400c60001d003150041110310900d03922079203010b4a0401440f049040021410403d1840c2c04000303110b40c2c800108000400c16113a200d00d841d02c55031119500542da80da4040002409039011410490104100701000707048280702341e1061040708168050341c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 664008920 1250 664007670 664007683
    0x703020108130c0b1806030f16050c0102030a0507030c030c080a0c051b030c1006081903050f04380a1b060606200d0e041d0a05030a080f010b03011511 66
    0x201c010302c0800c4242808907000c00c4000e544408990440c25808c3c1150481440c20000e454002c0d10103a100b04051070b18028000d6804175007040d0700031516460114048000784c1021078154000901d03001e0726000c140d01134881c403c81080d8035900c2c1c82c81030340c0791506e50009100183c1d10406106082c840e030391407101e824501000c0d5403d150301850b211550f02d950035240a40440f11800c80e141001000c0c0480c01000605564001e01d6103030005200b611070074155124421004074500e900c8000801042d2040300c041503c059120010f800041303400300000b0400101122803d0744090341c0c003088181a040d1183e61400803030207510a07140d58a9003190b9030001100c41d0b950040002c50424000d546580b00c02c12101030003001d0f00405051010042d01c002414100325000c070b5440340d56140c0f19183c0c0d1840800c0c115121640900840c0c0b07081815007080c0b99070307400c00410140040c40150000b50710110054085040b0303405000402e003564280242d400d540042030070700300304000403000b40303e80000717080186 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 664010170 1250 664008920 664008929
    0xf0708070302011401140409032a0b1806131a0103030f110a0b010b1308010c08010f09110a2a03050c12030c0d18080705070e01170703020108130c 64
    0x186540d60200d49406425101084c181514800001e00108880c41100d81038400010b412100011100e4507131501b40d484407400080c0414442203024154070100002460609981c0a1940c62401d03507100e00b103004064101e00c95030001c0b901702d1000300f482400c0003500004114810b001c0501c00310944069092015826030055000510724002000c501c1e40041c0c002d0455000038015040e00b9041e40c9984003244010710400342d96400010348044545285141003002d070070440b0081c48411500c0f40014200a0280982d907040030ba8000000380310b44942c45600401001c40c180c59003843c10048040e01c21420000c02a000d07611030504c044120381c54003121803040740c841d1300d40c03940b5101c045000d10f2900d12840050700718290100140140384d544917003504d96a1541c0345010500d40c9000803100c5140f024001c008051030f0000c16807108104002c52980c0a0b100743c003059944a030b0340e40c00110104145503160410b01c2c0c009074000c2c00554410b2040980c0b12000101201120529a91b11440f20015503c0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 664011420 1250 664010170 664010183
    0x1112030702030306011d0907080a0f0e030d0e06070225080d02061005040b090133030203060415030201230f1804110307080a091e03361a0f07 62
    0x3007041175078010103458055001130400d0680c000c80c00c0c0c041248000301400400034080d4810008882200c06c0d0070140e40300280d0041132082c815582c0ca035580d642c200b400414501c41c1000000e0000340300016034103103c0e040c1c1f580208004021484c0740200e83c030481a811007200c0701400c0100d4842410800c0d450186c2856000740500d151140307030340811700b0352170700042d11a03810f1120403030b9180c1d50b5081c2141540d508034503146000c2c07000d003503440360110040c0144043c49210380f50100041e801d5409544150307030617241400341c654485007441c140f201c0750000a011412072030a95442c6c145071100040d61080c01e60b1080d16000368a11499900d401c901009403546010161103c024105405072100104103104d400703095040c16680a003014000502014004e540c924002051180d48003104034080c0300451600c1142016040007032280ca1810300c85c9010300c4413504208c019082c4000811041c8882c81c7e9000002c1c1d0400d031141c8180d4179010f07040f00421509010741e06a0a4400e00100251441000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 664012670 1250 664011420 664011427
    0x70920070f021305160801170d0e1912060e0304232b0606080106240201060306021c18050309010309020d080c06041703040f080a031d0105190b0f01111203070203 71
    0xfa00400701b00e4140c200300415400c8a01c11244071100080b140500c1c6164200047c030f0500d140007080030b0035a84440307008141c1c0890342c00181d984400310000246030141d001407110040d01000141d0b40d216a124207103040784080c03041d0000c907040301c0b1191881103004028200e02a200c01403074804e6805400307032401d0604020394400400c0502c2c4542c5000744640310003888064609a40d0700341f8001180a42c198200c01d551040c4100ca00c00e510280c05141d00c0f00c402c42d261200f0344890008031030404407081269103010310206090303014801c1803c540794840c00440c81c18814500450241501500c100c3c0c0000b40380d17501000042d00c41015041c0021000024000c5190900f02032078031600144245020301406c00030701c40424000080c490301c581c3c2110b0500c1d40c0d5011004100e0081200c8900c0721141105940c030109401c8040d0404c40c02140c0115060790a0501101140e003101d03003080321998890840d0b825000f041d4015050720b0a0566240161180d8840e55492241c00d64001c80e2204010382001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 664013920 1250 664012670 664012711
    0x9010e07030f1401140111010f0b04060914040215040504290d05030706200c0a0303060506090117090102071b1d0408031902040f0602070920070f021305 67
    0x1072046080740c464a41e403e0003412184604803e0b81d06040c0526280c1d0300030102c0c8001c1d103034011201c055186940b80001c00213008103043c480700409195042500c524144200012601e40500a212001208403560380301070b256030342044031600066110134680841800b00281079500c920450300546040c20031006502c4d00803003040c1d00386091940c480e12400b1224040e6010500001c161400c16070300100c00101100d00192184d401120300706000400c96001500201c51000410000641407090300c0900c0702c1762b210030411800b0f0103541c485c01d00040c50540d03460440e0201100c21a0420812000103240c01c03400d84840e031f00c4417001c8003100c519030b043d1802006402c41640e50014000400b18204030f030343c20300f9940c41405220240c1b486003c400190b920300308183c800e070f045030001d144601951800383c0d9944c44c040d480e1080d0b4170480e0605494081040001004480d40e00703444d06a01100500d410040e0750b030b10107204031504007a40c0001a501040c03420708814440c90303001d0301e0f0101c00143d110f44030703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 664015170 1250 664013920 664013927
    0x1020f041d10031707060e0d090e160302070f300e1807090e07090e090c10050a02010204090f0209030c01020c0616080d05100806011211060d0b09010e07 67
    0x5107070403070800d81003034200b0108000409048050740c1d03009241c4078180000f02c0940d0241c0c0035619001d008603161008003485958001501d10000e507054a80b000521760310078691306000022900701003460b28a0101101080c440e83c0240310140c4201f526a001d0a45a140c9218448451900d0020003185a040c400344a81c10949404622102e140c60300c50b03031801e040031a0110f031208080e0004a40b02c0c40201d10200d0044400c80081c0526551009081c584600024691003c610641d01d0715800180401d407950404900150484e0002c3c01000c4034048000c400c8402c3e0b48140403010455609001c08a0712126900564140400c509005a02c814140c42018280069001c0741d6041d548411041b005035102d5100b51000d007541e5025204807954613091048891041c8440001c41e2441c280c2000149080101010283c074260000c4421a03a03c40d4000e0b500c3e5110888081c04c00042140070b5582031900200814800070a80030204d40380180c00041001c05500380c00001e1a40d0b0610204005640d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 664016420 1250 664015170 664015199
    0x609051f0f1505030406020706050903091905060a080907080f010c030c020105060d0611090306090105041a04031202031003050d080a230c0d18050c0109090c05031503010e01020f04 79
    0x1200c1c640354040c0386004000061582038041c1d1000740200440040d050114960642c1c0c00e140d01b0510a000707618000c1e400c940ca0740c0c410300c581ca2007010780800040f040410b2440f56025200041d1450780b401d030501005907901e070170060051245100700c0801007007140c014041c0a40401e24800045040d40403950b000d02980c4800f4811021685000c040140b00d0361345140c0385074040e42107240028858030b845000d200e6480f0701003c07660103124003000d0140b4001e055002e548114001c11200300015210419007800001c182c0f0b0140010300140c108005040c001da00654021480d25104000140e581d0342e200e0400011004480104040320104034002e41e40340101d107042c040d900442010041c80e41401c07540020050b00203811044081411586550564000140400c04000c1500454124541581d0700e500420189000500520000910031030502a043d8080c3e03150301d40d0f5086580302c1e40b1600408101420081d4950740381e032580945d540080c1300500500c40544105a5a03a040002c0880c0e40320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 664017670 1250 664016420 664016429
    0xb0403020114160c05010b0d11180610051303020d0501021b0721080904060e04060e1b040504170406030c080c090303031f08011107140a03210609051f 66
    0x15880400c80f5001810354905070100301d03400c1c038800c2c034005803c03e01e0040000c02015600542d400407200300b401400310a40c040754100f00c074020001d0300340541e80807800700d0946960343c2000701c401280c48990b004e0340203800c3c01c0540403024240a682ca0300011044012841c0c2919607135400918500c2d12503801001c1122008440000d201440c40d005210301074044649043c0341480d0f0702c240700003c006c2c56001704c0381c0c0f80307100030018082d041d01d03201503c0b400d440076071741144c2281c64400c0002900ca004603500301d5100c80c20003e081d0b40c1c2002c2040c00003825004000315464885040007442c94200040a030001e400305034bd00054502003d800905440000b80c00244603984c14415825280c5e80002160b03481074198808400001c1c80380800c0c0c900341d01d590007070149075003420b40110303030260360001801c0c03414064504803030b00c085020b00040c1c881500d5080500040c0d0f1300900340c04821b11140f00c0401c0c1500441000510310784d03504c030381021600d05803502020300303030410b0b50012181039041d000c00140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 664018920 1250 664017670 664017701
    0x120f1e09010e1806100e0a0b0a02060f0708041101120c02010b0f060301181d07031505010b1216110a0b07080c0a0815010c0204020304060c1409060d0e0313030b04030201 74
    0xf03841200c2c1e800c940880043c4403c0c170404490361071949051144080102d150341c0030308017064842e11106108042d41041803007800611811000519481c1310182182c040d00081d114071001c0e80319506d070801010a800c07101d9040c0200c128001ca41d0f100360748a0300206c0300c190f0340001010502c520070050602c40585c61184941420310051200d07040300c070720302011006070031030015111010018040d072400c07070b070011791803a1f000700307403000003880004c03052803102c42110201004140e88410f13100e001c90081903240c6a082c40000006030400c03207030300310b01480c2e000d03503003004004551540801440e055240300c1c126803c1c030303010b414001000e8006803096084124005d400e400c0615070325008110000c010107148911400880003021a4011120140709a0f00588155074900e802d05011002d40741e040c001c0c03400240c040e00e0362008009000181c40034254003e05c594179040c0d1003000341020300324812000c030142c04200000010300c00b4808101004612410bc0c6048a1a1508000c2d0031a52080b808542c1d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 664020170 1250 664018920 664018939
    0x71803051b3102030702010908040906030510050c09280b120702030f191b14100204050102070b0304021201020c0607020c0108040b01060c14030a0e0a120302120f1e09010e 75
    0xda442c40300c4211100d5851080060300c0f5991400101d01410003000e02801d00c4c000000c0202d07640300180c000c0b005503409101103981d0343c80e00a4035182250b004070b82419034a1410b02044010389060203051018185072008250301ca90b60b21511741180c00b0390747c000c515042000a0034220500401806a4001500d001950901050402041c1240701d4510a402409006070b40300417054029102071010300010f01d0032441d13100440c50041c1403068068403040c2180701c0c207030000d058044030340200c80c182c80040c1d000e00b072400e00d48001c0a513190005002241c0c4042e278200003042c940802d102800c41050100010100b5007008070019080603100b0080b075041010107010000460080c08134103045a0140c42d00109209240c00c04100001a030740c0d801405000004084110700d80c480c41c6000344410403180050300690f10302035098001c110b110028090713004083c0c1a46111104405094107200001840346010300d89a452020782610580d5520b001e10082606041540c1c0600050741e030301d0f0309843c0d20700d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 664021420 1250 664020170 664020229
    0x50426071403100203060d0f1a0a0b09090606100f1b0f02130207080406050a211a090103112205010e0a0b0d05060a020c071a04081c08071803051b 64
    0x514041100041d02390f0b06081500c80402454142182d0901f803010306030641400c0c0804e012001c0c06082000e14800c201103000715003000008100700703002d03140080950400c00786240d8141e80e8504940300602c140120003403044000004010100c1c5400e20841855112505601c1001420b04212101c1103c941c4140720b6100055030101c200d8081e1041c608215403500a6401d0454141050310f20084088a544e12407034080b100c0c0303801142105040302940b080222045c81401103441c401d2002a00c11020851083c0d41c030b0400e50589030f02c2c24120458806610022903041703040e02d00030f90150100b52407900811802c502180304005840d101200c1d564a030400d55100c0964960380a40a40d0700580d00150f40d08111008105801c0201030040c8420001112642140f406400c64441c0410724014a0041030894010020800085045445070b089079214880e045500654001c0e6004c07107502c0c42c1202001240e010880400e5500c0c00c0780c54921640d0b88102403213002c3d9040c0c9410300e44009158010724 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 664022670 1250 664021420 664021429
    0x130806193908090601035715053906010e0c09130506010504080a05010608010e0609060f0702070b04080c040b01030606020d03150e180606010e0105042607140310020306 74
    0x21f0646040c1000100186802c045603201c0c0d4281481980126603c00030408002c800005840d01c06418000c44004241e841118180041340490590001403041028501c0828142002a91358008603041007003c10200710005c949010201890900d900c0b4000400c284045a0980c41d400708040c1e83d00f905150400c004980e0341a80300c05406802034441d0001042644140c0c00d0358001c0680f20220350070303d40581042802003159010f002a41e5003802d6061100d51030024000e030040b840280244000e5481c044510360300030010b803d1504501a61000140d458208000b0780f005e01003010190071034a0400c0108411903140e4541a814503040200c100b2800750003050318008040c480c240480d020101140c04a03070440281c00c0182d02151610a0002c6078048524a000c1c0c91001303800c071030040d00e8101c01950307001c0401c20301900180c4100300c1800940750304901c10b00c0584414001803c039500200503181000c1498212a0308a4005d445440113407034200242189003190030402c44c5507040880109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 664023920 1250 664022670 664022693
    0x9180c030b0601020a0c0617060f060304031b0c0e2a041502070b0a050a121103070e040f0617010c0e090103020f010c05010c030213080619390809060103 67
    0x900000e40220004020f40d00901c4061110350303010f242c00c400c0546501c0e000d80322259012182c5810006000050a10b01b801c4040c80c808010082c09241599655601141c0100340c204015501e00c282c006804000303160b00019170050704401e4035850b014542044144114010000d012091a0140340c3c0025100c0e4520110b0f000d0b40c60342400c0d00b2540000d10703410781c6030103800d500a0748107050000c1c0600140364001d014040060780e03030b6212003030b020000448500780c694000c8550140c40040002c11903e500592140c401d1070005000030038410b1802e9901800c0740c5055000c2111004050184100d0075000c3c8900548131072141451181a403140e804904c02700d41c140002406082210903441c2c0707503801085480860350740040280055400400010065040780c44801e019006000c8042070b00100424100c0c494010030148440c0d607101c404a070000781171480c135040032003e81844960368101300d000b04504503450b51a14020b42140180c001404528000e11404407a0801c40060000514508a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 664025170 1250 664023920 664023923
    0x140c1206040542061e07030e1c0605130c050607050f33040305070201080613060e09060a0c02030f070c0e04051e0c061c020f070c09180c03 61
    0x1030310340e070f04410041d58411184070200a100094104581000381e074500510400c1015958004207410780288100c41c050705d5054212009010b0000002d40303109006007054500a103481469a805000415481c440307440000c0d07108203c3c00d40d00c0b4113006540c05061780115015034042081c07070043d110308405034054012a48903e0f0005907500034014108050840800071505560400007501c0e1100020078100d0440c80c1c860148440ba030301c4018051842d2403080c1c1c1c02d41c8405180c808150300460309100018803080d8045c060b8102c2c0d840303802d464410400500220340301c510039420080c616034600304d40141110320f0302d41821181c03241c056000c4140c540380c1d0240c00318191254080d00e000c0e00a400b003038001e01e100d4041d00f0100800d1000005081c42c00d9510443c0300300c4a000640c3d0f4460329031424000081d04070074100f040c00c030b80d080351b0307820003007003130081c410040c10a0410f28050b10b40d03904c1214103486250304140e061203401801d204a01a4450000380070010620596800100c281c00b48070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 664026420 1250 664025170 664025179
    0xe01020a0207051219050f01050f0702060105061801080406090804090906050a020405150a030b04050f0a0509010605010f0e01052a160311060c010e0703061a0a050303040e2206140c1206 81
    0x4000d000c01034200401c01d07e04940e0b400a01907441e100344000040001284c10500510a100000a42d402c0c00c6c0111106407000c8440200c240f1250310041d170b907416003d00200d448036503501d404070225041e14080d0018002ea0400498238540703034244502943c5004e04511001841000200002c0c1e5400746c0c8000110410201036454001108080d8014050440d00d1901301c5e003030500304003a12071840640c1e4400c9007003110402803030301c402c4402800c8840500a50740070945d03401e0446a0306018002c0c880c00c02c407052400c586480300d10649500c441d80d4640c1b059103400050468540728010a000d0070789030310021781d070308101c1914588680b8003924441001a00450b80010701c04015082134002040c04880d60003101d100aa883c074111000b0f100d281001a850b06c60200e0080007454131140034011034200034010340c00c4c1414130104410b1002c02400a524841030342c00d6401803c82c0e100d105050b458000c050005090410031a04510b0b904000c1c110000983d0804c0804120510249100d8010f0020741c0e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 664027670 1250 664026420 664026463
    0x5040b04050405101a030615090a140d050f0105040302151012020a0803030424061a0c011d0304183b01090b0a0c02030c03030c090d060e01020a02070512 67
    0x1d00500b07030742c841d00b00c0008035403010301c010211740c1804002c600900b4240c0703110502524032803049070315004034a21550f1141c48901d04221100320004030307110902d40100141c210701d0207603071150700e0b107081c4090b078a0559440c3c200700001d054050107140c1c1e40000d96501486d0328505811804148409402a8010341170140d100e00255120010000058241c0f401100da4904240c184a644621510307041e40c2d000f4011000d500b01c0d050f4070700a901c1140c0510100c016109980c84141101e50403900440550b03641c2c0b0000d84c2c44265001c038401d5220311101c0d0241d903440d410401941c050b81d54200030b508807581070030000010411001c034031034080004903001c00304049110543d6011000c40f540c190466600306007102c1c00740414041030318080c0200c00c004208011590509a803a40038504103041703190030600004581c003e001006100402c401080c12160010a59a030401c884002d01c010006070741c0400c07c900143d4040103c071000d08001c4640d800c40c40c4100c00f10650342c0c100c0200c1c0c440b46040f0f40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 664028776 1106 664027670 664027681
    0x120318050f0609040902120105010f08060121060b040f0c030b19080c0907031808071a10090e0102040308071a0a1107031b021201020a0f05040b04050405 67
    0x90061420710840f40304120003802c0300702050b80c01641300d40c0b201ca181c500c20702c00c2c0c034060a0203100110b4040e00742a0789501c2c06505810008130b52000c0c4a03103281055502d9110415264007250224107000508040f401400006c2c1c41306a078036052074003004030141c01d40c1000f4038210050310800c10059100b40100410200751090700b00e15005601842500d040804801382c0c050490300b4007040d03240d510030301c0f201103404850003a41c0c070b084040b0f4a1010400c1c80b011500d80721580240c00d0f0750b6420b003031403100302481162044d03034038069a86101c00182034007901035400554201c805a0b8a0395142d0034000d1103954038950f200a98030301280010802c801074400c0d480b6240c0d20403113040c00c0803101e03902036641f1000c4501c088500800d4140030b40040e1760390f140d0103103440c15442c000340e00c0d20ba41036001340c103804100f400344051140a0006200d00701c005416182120000c41c3d000c102034850 = true := by decide +kernel

theorem cover : BRFrame.Cov 663848920 664028776 := by
  have h0 := BRFrame.cov_init 663848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 663848920 ≤ n) (h2 : n < 664028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
