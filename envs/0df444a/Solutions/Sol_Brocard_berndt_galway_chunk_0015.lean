-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:22:20.19545+00:00
-- url     : https://prove2.me/submissions/7b21e436-0767-4831-a51a-0c2c78fad5a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 2517993 ≤ n < 2697849 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 2519243 1250 2517993 2518003
    0x7021c0203150c040603050105060309030702010c06020d020708030406050105030307050d0f09030f03020c0f01140a0c0c0e07080115030504031d040f02040605040609050405010b040b030a0609020706020702040e0601050120 97
    0x9508121014108001251000f20050011146655024045070743e0354824020b0f288000d0f51084000d4104100e041c4c0994028a01505190301c5444010b203816200c2140c0000c0380c016080840300040d0000070b01c03007840343d640140303030140030202e0140d40350581c9903490701d039182e03928080c510902c00038640b980142c500490a61004503042014032420341c000d841d00030345400319519502d200c0d4400720540d40079948902c0e4885614025100d1840c80d22581c0b4000303a402071b05070502100c440300216804124a409075280c2401011a5150f03074800c0d5050540100032816500411001c1500d0102004003003680b10b002d51558901c0303440207002e40d00c2541c0114010300003026091215500004000071705a50220051003183c00981d9903a04143e240d80c20041030303510070301c51044070300014001802036a048000560300904031007000204950b450a000701030b03803c001c000b6038000f0b07030118540302541400e0142034035604001018008541c1803100181403076004060108082d40c14512000b81200c0806c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 2520493 1250 2519243 2519263
    0x7052506050c03040203011802060a0e030f0307030302030f0a0902090105060315031507120204080303010905060a030b1306110a08010b0d0b0405010e0403030608030a0e0609040204030f0f0c080307021c0203 90
    0x181403000d441c02e415030512036801039030228003961800c014805401b1902440d60482079005185500e00344803442c040340c070304c25070140296050180c0005c0200e0040200001c00d503140c803a40300540c0305d01e008110070000200041146034140d0411114500590395068418155003080b503159443c5d86500c465881074941104100b45c240c42104480c0c2ca24100f04108540318500310303544c00c850000d020071098140e000d98824825079074001c1c00184001d0b42c25400207039001c03001504503100d0326a81d4580b0000103800340c0d02d001c91312004c1030035441404141d000ba5401004401c03001494003900c1c0c040200103410500c00d41e94601404038160054444c19042043d81c0b410040042c0300550f1109004210280c003070b41c003140803a00e48400000c4011000c4281c8900d18034980352103c46120f6142404480d60010fa2000c0d40564200301c040000380e45e40a42c2c0c1129802940030842103102440e203101d6900b025005100700c0d50050012400580d07031014003003c0c681105410340020314051000c01d2420040c5c01e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 2521743 1250 2520493 2520503
    0x90207050105040506130b0402091b0a050301050406090b060a0c03030b060a050c010b0d1a09031209060403020c01030501080a02040e070b0a110606040c0801052404060306050901080105070525 84
    0x1811006005054000a010358020820340f20903032a000412813268401c440d00070041800c03500024054604440307056408807070300792500d01ea18030502e0131300b091764050710384000894000f000502080c28544203040c0a095503d0080010b64100c500060b01406070300301280400900a26901c20940700390031000f000328000d0002a00c070b005203c0090004e070803400034052250300c2c00b65014414a03204541c48030752500101c00d802c0080c40070401613090710f0000c1c0307846428402084140e0369188410251846100d030b2030040c00c083c1c1024a002800d01044c1410141058209001403100c0d10001c684108010b50480d00042e410441b9100d0500b00342c4290302a2520390004035084110039006402020310b107903c1004d8403083c0e81d5000070070040303400d58503030400000d80ca80010310043c06c003507540d01541c4c0410a840001d007540c030009800d40b5881f64000c4000a0340700e06041146041c04009140900700c40741c0240300c140340c2284020250300a02400b10440174910000600c084403100c8d0358603a03a6002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 2522993 1250 2521743 2521747
    0xe01060801020703080c03010e070f0302070209010e0103050d02070e0105010c02040905120714060906070305060607060504030e10020609030a0507020a150e0f010c0201020d03020310050a0e01091b0207030305130902 94
    0x1030624034000e4000480c2500440c0603500012509459401203030f068407401034030b110081e1180d4904880002c820b1480c0c1007030590130024000543d40b4004110300030500004000090342c11031401500340050748440006540c010380701800050034030070301e880c1034440c20b00e0114114a03240c00007501806d100e90010380140a489410390b40542d0f050010110300c1d000702254070148d0100904560b0b00c08003142d510a650308907070049540c2c50322982242e80c202303000400c0c40d07061950304c1c2c99400c00c0b10800d54045010402d14000d50300141010007501400240764000342c1078074640b200203a074480c416103401d807041100000310714003190755605070350002d01800e601d03000504030700001c0a0100112070640620501744e490b01d5404642c46091050025541030340034001412100100f500a0740002d40918150302504001150ba501c070100c008009082c1c04600100b00c0d45814105002c4072001c83c1c407440c1c120b000c0034800401d13540001e0601d080340e516160440c0d40d64070b0843c03420441481a00300d40281800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 2524243 1250 2522993 2522999
    0xf06040e01140102060106020a0302070303050a0509040e010b03060c04030203060408030403020304030c090f060b040302060901120e011802040606090302010507080304081303060b0a0602030406210b0303030c070501050105030d0c060c02010e0106 107
    0xca00c4a6090305400c2c0c085802a9881e00707010399031045550000ad00691243c0130900c0028441c2c4041c1801c03910b0707030a01d18207100c2c56000250984908640c0b20001d0380d50b40d000000a460200141078126943d0140107103414203680100e51915001007018200c80400070110301010b00c04c000f210011500650708c0d6070300d00d0311000030402400c18080400b05080c02c2c49030219079081044116021654002c1072240b0740003c0300015200c05c55803442400c8442c0da11442d8540000081c02404840591115070329810090762041004598a5401880801440c10810720050360004111111543c00045070350300c03a500e501d403c1c40c0314400c1c03400e540306003c10340324000208013558001c0180041c0494501d4000d0b526003400b240d580c01144203920001c1c92900400c1541c0201d0301c0001c1c54600045004213503041850301003407540e8400d03116500044c100250310814403000b0b2081a01404080b0003810301011800401004075821201c0584121380d11582000c82c1e41c003d42c816030b0301000c200000d001e02c0366 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 2525493 1250 2524243 2524259
    0xb060d0c09080d0207060e010804060b030f07030201090b03010e010501080c07050706080702060f0c0405040b01030207021008011503020408060a0203090f06010303030501061706060706051902030103050705120a02090103020f06040e01 102
    0x48521449002d80b01d41c0e00403441d034600228020f41500c00541d1001c1d00703a4451001180e41d4800500191101e0390359020000964800707104200c20303101580002d00c00b05103184001003205030981c0c4800e01c0c0300800d00060181f03001000120741150001d01e005040c503120090038180310700c11500c000300b03a485080b03030000d0120f812194481c0b062800381c095400541d10030a20070041102150000c440308404c12085c03107a4546680003041414041c0f500500380009540891120090034400c00082103c040c010080460f13403c0b151240d501d002d140c15070030145043c140c0c41c2d039014007800c038045c2e1030380100c006848800c00700003225880d8800d004a40b0360307594030300340500103141c280074110000c1c1c401c005a139401d241d40c010b5140201c0e4003501d0b5030714014164442600411010700b141091040881d100c00d040b41d60b0740017540c041d60117030000e4550607141404120018102c0310b02d02c80260444001e40c00581d0f05e0380403085c1100c0d01681c500941e00584000220700c0d211701d8000c220710320f45040012038400b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 2526743 1250 2525493 2525507
    0x709020a1403090a0b06061204020108070302040801020309030306040c0207030302120904090605160801050a060504030b0705091005040f060e060711040b0d29160302090409020a0603050708010b0903030702040b060d0c 95
    0x1d4092650b96005454040070b001f903911842d407011040101d040041030055202d2041d1542c01022898014100fa4a9030700c06402d80c0e2007a101541d46510110074050146024070034041070801700d0004180b11850b695000c0c0d2141715800020341444c90100e6040b1054907544c10251295600050070881864140405104007071030700c12040010762400000300326400c00d04001004d40c0c02c3c83d240c681c20b0602e1695501d442400003040c0300f00300481030103230810a40302c00420b0a130b41d481d01d8898030340303a0b420700501071525026544414200f0182071422989511000202c0c0c801640208420800d52148404100601014545282c00401c4460500240300d41034440310082541040005034100c03154400010140c2c00341c030760352888082407080036603060080d8010b0891708401f400c08100b800d0386800007100a032042d0f008138046034441d0304204406038000c1140d40549a1820064100010500865903d00850500901071940c1d000d00511590740c100541c0c01460141200703000c60111001c2c010709038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 2527993 1250 2526743 2526763
    0x50d0605040308090106050307032d0c150212160f0210050903060105040218060a02010b0307030303052a09010c020d0206071217060105090405070c020904060204170a02030709020a140309 82
    0x5603078100444e2a00030180602001c42d079005000305455801c507240d07150308100c0c41384031000d1600f010a90780c800100307800c8012840c6008524210795a450040d620007083d2503144c18070115000b0b4100940c03076108507400c2d1a2080d50701a081c028280c00d074945080011101140a540800b6034104542c103140d0040c01000d03112000c1d01a2055031341d0311030030b000a80c0102c440141001c083c00d800c0e100d080c201540908469016880041201e040200c003107401c003001604140d0000f520354041100b641c400701507541a00240071000107500c4400780300c140250080004213810800803c100800350340d2072220f00d0f0705050700100003654903076551420305401003010b0703a40004681e55455510324015242c4100348601d80c182c490034075200780b40b001c000c0104402407052040c4041d081e1070201580b81c2d5981c5c0d601c5188100300050380d440c2481010907280117501004116584048240320040c0c6000c9803000c00c89030844070141c3c41d0103c0302d0041d9209861711450401c504000f004000540f600002c1c940f1003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 2529243 1250 2527993 2527997
    0x3060103090b1008010605010e030303040204050405100204060f030605030a0203070e090c03010e01020408010501050904031e051603030b01030b060702060d020c030405130b04060b03091b0f04090501051b0307091a04050d06050403 100
    0x104030b41d1f4000642c2c2e507083c1c2c604500d61581062000401504007900000d90140c8a941552501100b10b2004d50482e001a048400002c150350504080181c25106075005040e08070002c014030401c80d80004d980e00c1c810700418044102c52341c08283c10450402c00c14250b050001d00a02144002264850007508507115005496003084000103003402c140c14090701854142d0f44418081007141120704041e1403540070801003000400030015000501840100071901c00d580120740840c0d01e400040559200c011054442d0404102c07030070060b0b6840c1c0450b4182e04588401680701c41c1c24400b80f80c158082c40e8010390304060004078801101565510034a103c2d001100c0401c651626100c004040780000c4850309942d0b44580011040151866865201480010400900800314101080c02e5035000d804c01c851680d115810300c1070080074a0068004541d40019450a620301008000c2107041e0310b120b009541042900c2c100b110041010860340944005405044611103910300800201000c89060300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 2530493 1250 2529243 2529251
    0xc030d09050108070c0f0602030f06040606030203070203070b04110306010b030103060606020703020d0204020d0603080408010603061b0903020d03090e07050301090b030c03030306040c0302070204050a0905150108060c03060103090b100801 104
    0x2984502a40144003034800694812030a40d5541c88151804e021030749060341d008480300c400c200040c1942c0002c52140300b52540054540c241034081c4030a42d22141c00c0313942814010f004106540c0d0740001603804050f0481520b2245850340d04100168403226660349030076020340e6001041d0b013507082004504803481010104035190341c0f01e000701c0e2141c0450000035884540144110058582500600109900c1000c00208070f580c0350707034960407944182d0080016035150070f030800500006100741141c80c90349510156001c0901d01c40101800c0042c04028442d41c4038180f0795050500c941d00aa000d00440883c0307540501345100d0180154200344144030b546070900503904144d080108030a107820b41c0c06001982103888400c1040041c1080303001030000c159003440704402584d5a8003c1e6800342c5241c0130002101c0c43c1508046080c060f410903000041c03001480100106807000030b5465010080344085501c80e00c400700101d01a0812000144c1101010402d00c40720a10400b401d03000c590310180208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 2531743 1250 2530493 2530513
    0x607030c080105010c050c0901080c0307060203040f03060e0a050a03050301260d030e0c030304030602190503010305071505090301020304050114070f02031210030503040909030905090603210903010c020c03 90
    0x90585200122660009000c0c41c010010355000b50f51480c0001e11481c01d454070709a00501250a4031000d91210099910060401e14036003000c1c0003110181020b407014601e05400e104101c1c0c01c03403501d48402000c2d55a41c281841c080041070000c0b00c000d6520400b541e4003501a03050042c10340d0400c2c0074100c00d0740c0c001c0031342a07442c101104821500c2c10403400030300703aa5070007004c040e0010050708000103854050070456801da42d03003c1c402000954414800180c4441d0030300000004040d91144160500c401040140f0201c0c50015000b02140c0351a8440400700d442c814040b507450003001955500740d070011050204000b07043d04516894550050000c5060741c520307404a403240d10200c804005a0400c0024500c04115044040d520442c00b0143d402d0f41590395030380f07070b00e9a481035014100705980c410703181d001c03d58803851200041c00b0441e4440c3d8a81845c80c0020b4480180152101103181c0c07003145040681640020f40d1043c04008008105001c111500a510781880d8410148030b8007442c0900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 2532993 1250 2531743 2531747
    0x171005030106050108011d0603070807030507080c040209031203060103021e12070e10030e03040e01060207080106140906040209040b0909070501030f0207030c02010c06021e070203010f0e030d0b120105090d020607 93
    0x145c1d040310b400c00041000c400b21326500412140c40a011940c15002c0c2c0400820044010402440114811001080b68a1030207400034208140e00c06441d2007a401001103000595000600a04c0f11540710b420994035141c44006034024400c0103981ca04070402000044002107080340a807015402c07021a51010340d581d0102120505007102e0441c0c0c3c000c624a149041140c443d0b1f203c0482e0002d2042103e103450345881412072116070903030180d801030717210740700c180b04c000020b0143c2c4c00100806d1190148a130401c80000e0384040004126030b00403680458900355960b1560043c62400fa0080d1000006080c40c00031183c0743d41072030141c0703404a8100f0607024540b140e103200701c49200c1e4050b036501781c0c60300082c1d0044580d500341c02400c0c2e84036a024402c3d44420058800800403a4400490041d0b031160244185402e560520ba088031046240c60b41d180c412060220840d14100c210a40018a80b02c00c207001400000a0b0700b90400303690b10b00420401e1407580000c00310641c100503000c8071103a950722501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 2534243 1250 2532993 2533007
    0x190c0507030e01030903140702040905060a05100602030301050a15020a020d2604080303180307060609050403080c190e150423060a020703031209020301050702060f07030605060403121710050301060501 88
    0x70001824250310b47c00804080b005050716603c01403000c1001040c079110149080c40a840d2414a6940d59081c00310454420900c030f0003c0a040c0044d508561400f000940042014881e2005a252159224907980c0c03081c040c0c00355207640200750705c6603020700341846d000900c203811010a100070b0343c1004500302498070341501d081710003d00041d840c45d5030303032000f0503070540d10702080785810f12040c000e142c00260940280d00140c100040c00217014501414001e060141c0075021075600d04081285142003400b6480f03510040315581000c1c0c0c00ca00071003001c46d40314802403003000010300c030204012810789610f0480340c5407a031000c078002d17001280c0c41d41003000c1ea2185d5060314025070b11503c8108002070088004005007441c503030740000c110825802007400d48408a82c00d40058014000304452a9080398001d0781015151404005090030480030400510403400050b2000106c000e032005000d100e040302140480c80901e40c0e41c0103042a111125144035180650340c800c0d42031000c0464654400c0300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 2535493 1250 2534243 2534261
    0xf2309060714040302040207030c0c0803070b0606070506040f050c06040801140601020102040b04090b0105070b07020102031e0106020a0b100305030a08090c0405060603070309050f01050c0c01050a0605030303040209190c0507030e0103 102
    0x480301d10b41844d41e401c010095000e803070218203001c01c4200391004942100d50150050041401641d07484000b07150413030000d40700401080c4201014459100440e600040c16588150f0040c800c2e01444242d080192500e002581e10513030181c800200440c009106420040304d030640303414401d1003070f180e81d001a4241d000300c0c01001c0c0319180c10f00c010814070f52950841c1d02841b406050941c5007000b0341c0c0b15400e020a044414602503034002040c000c0b03c1e690442c00741072118901e0803c000550510303000a4856102c8a80904028003020200360405400300442c001164064200c90f40c841020a001e00010b40840341d1000a0260042c1049281454041c03513205100003400d252031a55150020b400400701d00205a4152040000b4072803480c1091007045d000c0c84032040e18076150001d0115050a680d8003c105200c01400e040b02040161000019290042c0c1d049414002503a02c40010103095650552660302440c24500c5402c0855000402014024040ea132180d0006420300015000c1e02c03d002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 2536743 1250 2535493 2535527
    0x1050904050a030f030603050307060e0c010801051011030f0c0a050601080109110111030903010c0806040b030307050c060a050d06030f03090b09010807031a030a08030906100e0a0f23090607 83
    0x7070b080c400607200780d5156807400081d08000030410340782d8562038950340100d41e08480d201e540d2000052011030030000003e11034000d1806000f82d6042401081492440983c03850600509038540c2c111034a00303000341d9103c1002d403207507640c07240342c8010034642c1c5400042c0203940c58000c000c0003299098040c045d01103190780041950592040480044031001120240301d21540000c0c4591210f0343d50a00070400004081c0c1e503003e200d070a16400b0001112203011800380310f41d0041261000141002c07a503484010801c4585945403010030310113481920441d028100c0d180c3c60001d011080002001800d00c04501941d02d40c185240c036648072880720700c246804a80402e09100004801d02c4c400c0e000b004489551040c2c00d091060f4100209181420140c400c9071344a034003004200754200c00300803166107d5000c8141ca5209803030044074040c0102c0c042d00d403036540743d03e400c0125204d16040c1c10401c050206c942050a92200c10181d0070075101c0151583c0000b0f0140002046260303114841c0d122400d075841d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 2537993 1250 2536743 2536753
    0x10e0709060e120607080609071107050f04060e0a020403050d0e03060f0403050c01110301141c080306030a0819090e1006030e010e011107060b04180b0601020f0f03090301050105090405 81
    0xc1c0307098401800180321154440c00c000705207101c2103001c1c0080c40c02003a00d512800d4083c2013000c100300c81080c0040140d0100114108046030000c000907210f001c461003605c12070080c14003400428040e024503003240b00035226000520031405031035401001103e0166054030081d449803103044030446d10403185190305501610100700b14a407100c0311140c002d84641007080c5010101c0f001642542c3d0762049002030b90743c0c00310040140480b101040e003100e01d0216100380105500d803034841e841d850007050140c10b20002000051f6951030400004080c1e98000501c2c544540c0240340482c01c000c90b02d9068070000340c2c0c0d0140002d0b41c1c42000c0915000c2e051030400b0b000102e00303145045008000c186e00803c01e40d900c2c1c46882034060400e2048d00d03c440400f89220b0355489050412409541003100c50314019440d01a068a40c0c40300043e40d2130700d4540c0b00391100c400d45c0780d407030040b40340201000781e84030130f40100b403203403810304074004000d119000e003d40007440366a1b81c4030100950028129006091398001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 2539243 1250 2537993 2537999
    0x1050a0b030f090c040c030e0f03070302072106060311011106100603020706020403020901080a020102060903041202010e06190305010503070608010308030703020a0903080304030203030103061413110609040207050102030609010e0709 102
    0xb1203481160700c0a189421070380142d654074000303410780d13160b61200c001284c0e032207040c81500b480174844c003209040048000c1d442c1c04500d030741c0255a01030921a400303c1d0007015503500c00d03162582c0a5500f08079006002400401d45a040c604022244001c0980c042006c170002480c10900c0030404a04c59540340d22440b0301c20f0310f0940240c01a41c04000c04640140e801c000201c01a500d4070921406001d51200078010458a40300182c40e00d0006070a510305a0700c28041040780c1030010100404565080c40c00d0000b0411081c00b0801c2c078001d862551401000e21901d11290395031540c400d60403108118115140c16650318025a0b0258081c040903051f03800c10000039010138002e400610100f1001d140c444602562500c80c0c00c901d0f0804e4a0813401030b000000100301344a205e014040500000a0781c4002d10304100b1450184980c40d2180200302c40350b1389180b01026510441038134070110f0084d0095503215101d00d4258002e500848180c2c1c800d0715804004100c440b22100298132908040e129500f105007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 2540493 1250 2539243 2539261
    0x10207031112010504050307021801081b0406090e0109020102100e07030b130b0708090105280f061a0c1b1302030603010216030201020c0601050316030b06030c0303040b030103030801050a0b03 84
    0x780190029070000002c00122640360300900c50b0b140f2650182c0c0c09181c60380e109104112508014203514141503442d440140104880480d0410f0600d0b4000d1103000c0d010040310200c0c02410042d804550b5030352410500200511040d008071481c14401d0382a03a100a61203103c860440d8401254030b0150390000c00213100054a010150b504401b0403400001842c915684402042008a8105000510101c144002050240a07082e000441c00d41d48441c1030300000048501d00b030241e030185000035228580b450320f18100390321080146c1110401c48512800c0030510011540c40700741c0304c00c228400c000e0f480d0020808280d00320f480000040900c03c4030b0f200850000042d400250540d58555420050303180242810034806074403d111380c001580b910b41c0421701c2401e000c0e0582c0301e01c0c040c0c1c0100b20303202c00304980c1200300300a403030f4001d201d008561510340220b4642000012042d406100000300828600c1d1003c1c06941240c0c465900d082072680c0355401d100c500c0e2444d114482c220361007800440e40c0c0741 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 2541743 1250 2540493 2540513
    0x60315060702030f01020403032007030f0206030402010c020a0b090310052211040f09021c0206030a02130e04030207030b09010603030c0f08090a090510090506030a0f020105070b07050406030507020c01020703 91
    0x1d0008003203524004d02d41841300c0c04ca81c015841207010442c0101d0403416150000c682281c112000409440203903c4c640303507444078081c0c0c413a0081c400c0d04c0000008045a024070220310545401502984005440e640092031030380c840302c85548a4440c40700003810a054a02495104c0c803500e02c40010841c910364121341000340b100108980c9030b503c000001078035403514801c0c01035102d010040400c0c1c4411900500c030070b1a01100403025204030035110580542c131a10212a08428011001643d82c0c1d0a03002d04140c0003111b801085110800006010a042c0d00042044c00e0b030b801143c40f2107407601c50308911401c07600944002004504d40c0142400172032010301001f01031034080c0a4052410640c05d0018000c0c034126080000f00594410a001e03068130442c3c17003000503100709142007001d4205100041e607200c2c2944401401c0d030b41000c500c282107910903800d440265130301613610b6010381044c81000e40f058001d0701980e40001d142000240b101c2d0702c006140c2d90400e0041c0c016005071819a01c0c5c984c860 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 2542993 1250 2541743 2541757
    0x1a0d030e060f03090703110d020a03031d0a030f0209060a0e01050105030705090909010e0105090c0609040e122d04030b04031202040f030303021201060806060f030601020109020406080f060606031506 87
    0x400d00500052104072100401184251085006014035a04614284142e40344947d070481c007811000041100603250b00740c038102500c1e018100b00001c1c0865180104602d0b03000004a070b0005910b0300008104030013803089205507882102c00c403503581c3d15074042c003c540ca094070844101c602440f00400c403650040005603045201407a10790310344010700c004102420000e45224295a640e4500c4081e441d8003031040540201d04500545042c1c58003100180460280d000e00303501c00c558a0306039880107101000200320083c0e0204a8646562020560410f00941021140300a0b2a6840c40040041407841240d00b81c80d8402d0220880d6115030714100e940c2c083c18001d00117090341c06c10003c82d05414440014009502c00d07134000d0390f80d62450a4900c14030406a102c40140482502400440c1c5c0c1c55009441d11780403d03045c40750b143d0384e401004034050a01d0890103500303d03160100c0410700080108400300b81242490441e1260340710107081c0852444100d401499a02000f2102c003030310b2508070010300b08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 2544243 1250 2542993 2542999
    0x30e0304050405010b0a02010c020105150f04060914040c0902090d0f050a02060d0903090506041505030405010204120b070e010e0901090905070504050a050702070b040b040501080a0f06030501060602011a0d030e 92
    0x405072901c01003011280203070010160300001003005111641d090144043c8030915100900040c00c03e96021094140c040e04260710941150009185540b550f902440c02000164000e0040b2181560383c1000110140c6064070442c45422010803090414002c030b03414200c0207130107141c4424880e280c44000014a01c422a07103030103022680c20243c1d4502016195009100c0000203060625240140840c1ea1641c00280988428401005928090342d8450403184990030210b03500d0351940303030160080c41141c20014a03902409004000c0c81111440036100303104d5500c910100b80803160042d103084c4401c8034910b5204954030300510249640b504104582d61184003100d02480c0c44200040a459007141d0307801009544070b040052a90303040040600601007503100614050614849940e03900c81d42c01024180300c2e001c0b011510f0861154828540c0e040d0503881040790944030324109020b0011f40c0300d500300541c206103c028188829408500208000400044e641a51b43d50b060b680c100311100c43c00d074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 2545493 1250 2544243 2544247
    0x40f02030a060e0102091e03030708070312050406020d0c05030402090c0c0703081204060c050408060103080a12090b010602010b010302090315180303010303171008030a080603031b06040b01050306090303010303030e03 95
    0x40d10034001c05460000043c009601d6203500d1080c03028194020308103006d0b58060241c0c0314196200481250074258204002c3d9503120b42e81c1c281034640032110203080c1165443d140802c02031101c90b502030601c410742c0c450306224a003600b640c1242c42d40400c2d1001713075002100070003180c402c160380c0d0010840340c1d8030841540c041030340d685c1350010281c100c07841790081c848002c0108410062103109031268000d00742451410541004500d6648410500006050701c10000c1c80000311401040701c2281519000d9090110800c0b81c80c0c14006020b0a10601025608106003106550301030300039117200840240c02050322030f401000d14813144601800d0100416208038040104032024002180610700030b466200c00100300a4440b0000c030002000700d500e2000100c020700c4642c0c0040100c0e0441221841c200c8055110000001c2c01c522400c0401640d4040242e2162080800880c44c2c0d48994040c001d103143d00c0c0c0e662018140c07542c60459411502d5001000140f0010f07020750300080000c90710b50b040341c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 2546743 1250 2545493 2545513
    0x11e0207050a0e0906010501170f0603010902090c1b07120f06060504020c06070e0102010207030c020108060307050909100b0604080a0314040e01030b04050d030e060105010f0c060203010b030907080f06040f0203 92
    0x3102d64032203030850404180d00404100e201c11040004c80d0042400380703004148042c00035045802550040e1401080400b50700205a0b2641c4c2500120b2090341c0042199100381003500556034554000302c440c1000c03001c203118080c01400e0200e07950b000c541500039500d514040703560341c4942d0f400100700e0858406680b100d010505454520240980700c0c6484002c1c400e9040c20440544000400680c0781e0441e80100b0245c80000d40c000d0390004010342c2800d01c1d403183e0b00d80c1400203080841681115801610b001c0c01c100009030700282c04400a080d04108024101c80241488040d02c17580c050302c0502e5000c0d08620001a01c221001562040388280c418205610303040000c24126007a40107031003096090050206204091100303801e28200c0d0305081001c01810700030719444402c140700315414403038107511251206009403851000381e61311140443d036a41c4c64440400a980003a21400200d10070300b08045113a480000e119400040c5400c02071403e90788503610b00c00d119a1054080380c060003410401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 2547993 1250 2546743 2546749
    0x41508030408010204050a080a03140706020d0f02130f03080406080603030408011a130902090a11120a0905150702031204020d0b0703090311120301150e090f010302041505011e020705 80
    0x81c1010700042d00025a0302c4e440d02040200c1a00c031034101d40c035241c000145540001c0c3d001043c103202c2c1603c12510644a55860030454024000d40030408441d508000c082407034203285a006244030441035842d00019900c500e00403c0c504c0c8a80001000010104400d0001600038040780d0342c040e000504481c50640c480c04100d082d01c1c45501501d868860b422202071082c41e0201e42c01d0b59000500c50100401503681d00040d070026030188c8102203056861a5007200c4046007012500c2546642940d0481410221113050081c18444019581c902071521b107100144503080d011802400d140d40211b007840d40060009800d01009442240d0042840a40c200090b01440c0d40760b1003960346490000300d00c4002d04001e0000782c5040800f0304190040c212580701c0740c0c440026281580e0b22a10000d8500284400c281d901880445500394080c1c014401c1024400e0368901d41410b99100703076002e1040490107103c00000c08094040d050214a440d420745020151040744100044440d2048a810503a10004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 2549243 1250 2547993 2547997
    0x106150906020607030e0a0204050604020409060f030c0504020903030d0506010c0210020f060106020118030c0f020402030f040302010c0203030708010308091306090606030e03040b030105011107051503040308070804030e04150803 100
    0x11100400e2524104000168042c800180d0007052070905204560f020080c00da01c0d0200c241000f480b40741e0303d0307002c150103071a9541074074041d000b401020000702c7c1d2a6403a040082d0000e100441e003640c100400400ca90400d030080e918030503c007400460034000311a8800028000c010009410442d11031341400141c0d0721081942c22512040d006400902c00341890b2a0820b80160403180544e03050a180600c00780d80f40f8200d40146030980307000c0c0c2080c1b2581c9070050041040c52400781d4803d00101c280468142c8800342c8074000c0344a60000c0020142007101aa12800116000c1001c5050000100040b4001c180248403204004003680000003c0c4100c01d01120f01d241c124141071580e4000c140011f640504c0341c6401c405190009600385880c20b05a19014071050081c98100301800c2c1001a0245c0c0030031101001d86401000c20251041001e0b00f542d003074100b00c0b0164001168000460081b0340142c00f014052a09640d910801c2031680c005d1202400091040c0305071103007901c0e00082e4021082c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 2550493 1250 2549243 2549279
    0xb06030c07061b0905010f0f02120c03040513060816030b01060e03100603050714030604150c0c050304030302150a090507030803090708070b0c010507050408030d1a090403080103120201060501140306030106 90
    0x44c0c02d501d1904280005000c000c04200f268240044c409500d020307513400080e1844a0b1500085041d0341d0b0b00c01e040c0c0c840c254080d5030f1049401440d600d40c94210104130740c000e1401c0d02c80344c60442c0d24554140f254017904007081c0c070028001401140050050030720444490740380103000340465111414101070032044911a520548803500056400d1140c82500342c3c6d00007807540708500134880c0741815252540741500000c6a44da6550b5207100440901e4003e043c9041c482d6001825692144e6490501a4a905082c1300f9030414100c0500018002c054a01c907202e102c58106005020050440c0d40d1009107600243c18a82c244c0f25100c0e00064040c0100407090103000e0007204141c4074070640c000607003918800b4000343c080c030205101c140080c0ca40007060303e200454280001c1107202d03403842c0c0300c034005201c448002c3e0004604000c01017455088549241224414015481154940c2c40700300d089a655000d41c1d8006040c40440400d00c020008c080d64211400400003d9807903540c4040c2c1407403240b280 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 2551743 1250 2550493 2550497
    0x504030c1e02030706050f030610021608060a05010906060804020409030e06041211030c010c170415020a0201090503030c0307020909010209040219080601021f0c020c06030907030c090b06030c07061b 87
    0x12074981c114102400f0342401813419080450038803000078041d40d11808000e000500501420000600942c400c0140082c401e0706c10591542e8143c441ca1080d46608007251aa4521410000000380e2300d141803041d441285c50980e42e114940d00c850f42000003415a8003c10303030400c44403840b08002983c8110050000704241d101c0b40840f0034091034051103e40080440c40e110b5000040600150398004450702c44007544002c00743c1c600c6800c0070700714015000d90740007d0307190030246841c0c100c0c03d0380020b040441d071b40c001d032a080d050700c1d039580405079280704410032003280f03400070f102c1140142009603404d608280460009400c000d80e1002003000c82c3c1140420502441044281a90315038011071105c0d00080c0078400381850134180d82e03040c1c9252505c20482515581d480c60032107091072084c000c2070b101241c014440c17540c0e030070f2212400c0e6844010740010780d03203003d8901c40000c81260502c03a0070001540606003904540e1202c07102051034110300d9013560490740f40c035061068000544800d0350151119 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 2552993 1250 2551743 2551793
    0x60f09060c0f02070504060b0f0d0207050d0e0102061006020d050901020102090301050403050319020703020a030806120a0302070501140c0714030709020304061a0102010218060307030605060301090207050f0a030504090504030c 99
    0x40b07100914003040da9025a014a240a606001e0b01040c0e1049400d01844a1291035079100c03401042c1000b03114000e000b40036806241d0050a45940c0280003044504003682200e42070f46980c281c60300d001c40c01d8851500583e000120040300140120701030110001b0500006041050382c401007030945000703e50440004200100b0084203258144499105c04040b140450800721707241d401035a00e1030710000207018094410001a2965141d5121643ca003504000365100d0703590514020b555a0794900500e03000c600c01c035000d41080c80301c00040d00c0c40466624001c1085038074200c030800040a10920254240c0562134000c2a1505075000a40c0524482d500016041c09004441d8a1031082d0606040c11a401001200c02034101030a007012600c5040f50740907501d49032a10264000e00c0d555002e26003000e0044000188009650701400703a0034010420380d144451100d10346521075041c8180100483c505000502482c0e83ca580040c0d0f0262090900030388541d8180c40300d40c900b42d01c2600d038012490807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 2554243 1250 2552993 2553017
    0x10506010816080f04020a030203030a0903020907021605060a05120106020c030d080f06130f060605030a0501140603010608040303110c0102090307090c05120402031005040302030403170301050a03060f09060c 91
    0x7018441d154014141100c140d60b4070030707001c801040e00c80702422412105407148003280170f5640d6101c3e500d008550040850317a03106c1c40044050101d44041c8020ba10880d64880020205400400d5940036044013501e0054007a00b40710404c001c0c1c0e00000c003c641000400d011910120020810a1b806400250000c2c0250100030040602d04a0b00080e001d003040030040c2400b801c0c44c0940c6400390030500c1160f00e80e05026001207800010001c00490300d01580c280b160000b42203400400440c090602c0e41c405218582e207030880b0b13500900e040d00780309401810400c010000140300b540380d1508944a03240c003141d481000109114550080003018510740d60004103803200340ba0810083c40102007001040c0f14149004801070454001c411b628807021400c000010b007150760034001070050f840c64040801c001d06040c10020340d40c0e0018003084030843c07072450004500052010550741200c1c401412540454195560380015064800c01c2031065a1980082400600a8000c201703100300c2075a02e000301600303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 2555493 1250 2554243 2554247
    0x9040501030b1609030c2105030f04030b09010509030304080309010204090501030c05040c08070801090902031507050318060105060306010c03020a02091807060810030b040203071802040501030605040b011d010207030c030501050601 101
    0x42040d40414004071304002c1001408964182d011945401110b52240c000307210441281d859480c8010f007140000501016104001009030003564058808a481580c40b20003080c02c842046e41c048115501c01c1c40002c00203031079907004580c4010700f07100160901d9980c4d00c1c11010703180217030811154540b41712814461801d00d44141003142d5950b2409103a6401e28900113072030704d0340c103008081c070103502c90b1042025524200500c284554a240c4048410318085c074005000360001d58041c192113030040340b40c0005440029402c4d059503002440c0034a0358840c00c0040d50110b104210032820350150048000259079500754042c410003014810210242480000341e0500c2e086401c140180108039043c40f0000e221440300d1000e4a0740815101042e03156030000074504540c80d408082d1182c0802580602c0c4d810340d07000349c07046900a807403d101c07241e1518208010744400e045801e002405600c010021a4994040d8028112040c0156034a0949940b54a2040c41d500d070800d131407030303034507107040c0309440d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 2556743 1250 2555493 2555521
    0x90905010f0b0d0c030b0a110f040512070305030a0302031008030c151b090d080c0304080106030203060703050606030a0902040b1003140702060403020d0e0f06070b0a0606090b0405060d0209040501030b 88
    0x3020858030543d0700782d010390f102514072215000281840d02200001200311481c1d6110004592000520725192029000c54182541c07280c001d003801009614107041c10400001240000d5903409009103041000c041310441c000c1d00020255071050f8003950300000e4160060005042100054026021140140d500989540f4016154a0341c4c002c000200001b040b120300d0a0328080102125040303490203483c1415050f5015070440c140d642d0000040001d40400158800b0f01140c1c800d070300343d43c21513480300710650480d001240d640e50403000c00c000180808240f9400500d030184014400100a0000c0340825a0200412250004240c3c2c072100341b01e9008021820950006e07252004100a20345a81c0007034455554418407400d205103a0701400f103981d15a1150b600806020b00102d45903a06402c0020b8040d0050321303250748403031500c200400c0852103502000217079804055811b10b4149403200b80405944240804601581c0c01d10208129607518021640218003035110071149040c210415030203c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 2557993 1250 2556743 2556761
    0x20f09040501051002030a030b0402040509090a030210020a08061003090507090905011103041101050318030304080a0e010807021209010210050906010e0115080610021903050307110f030f030709090905010f 90
    0x1650b001e132500310b203c0d03500200b15070504a40d40b03000300340c0a06443c04103010780542d400c865032000e0004108003c4200c0069144140340c002d5013140c0c211032600020904038415801c080000910080c002190707800c00e0041c81e04034000600d00000c0315152502d1b11414010550404680305031116084010300030b090103040040c2c00c1810309903240d420f140d5144608043c03c5000941480000310000e440050740a03000c010f21201c40d426a9902e1402d454101b08a600408418020425503101e03880f4039481614110b10a40490f001447c1c010b21072180b065030341e00b00740c0d2003a0440c0b18664a080300d07500c07180156405070a8400060040c0d5041800f22008404160440c0d506640c100c0b0400f043c144d488840a504600c0507a140300d42c201584034102d040580c10050054028a06286c0000701a8400000d601c11992a96554004080d580085031180d21002d003a83c0e10b0390050001a86881042c401150080f00e181000414180c0c4c441406041d129004425036281c0d546000200380710285000308000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 2559243 1250 2557993 2557999
    0x10207090209031005040c09050a090201030e010e1e010b06040f0906060c0b04020d03050405090906100f050918010209030708011505041112040501020f1201030203070803040812031306020f0904050105 88
    0x52120400100741e0f980c4c00344c1e0a000046845901241c02e000381c00310754101404602505000615024440c1809425144c0040380001e01e00500c441201c030042c0301d03060044035110b002d0b1110381d1000021242044008044040303c2d541c80300c01600c0d81d60b902009100822009030a8020140751950400c2110f400d83c5c000b2082c400010240c0d400904041c4041d5481a411180340400a0340c2703007401c48031801150000768001907400d007840031102002511911400e0744123000304169403141c1403d40401081d204a40e0001204808540000144d480700555070840800040c03e0048442c0002d141100b0bc2e0701100007650340e400b15442e184420310340703a00544003d0f10240100ca01e048802c0000d032003040e403503240d0200354802040422400b07404641907140d03421781c015110011500000d85211003031000724802d01c141c2a00142c00000441680c0448040750080e050340030320040c41d80d400740d10042240d41020141e05000700000c4940c030203424801480480300741c861070030300c041c032040702c1044c4c03c0544 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 2560493 1250 2559243 2559247
    0x10911030d090608070c0305090a03030302030402120309030d0c020301140106050406020c03030f0405040510030c0b0c0613030905010807050702090a020309060717060103020703030e0609030a02060a020405010806060702130e0c0102070902 104
    0x2c1c1c4d400c0b218064000d0360518144844a20a0400311540d00442c200b055005445c90b80c00024141d16801a60140340202d402c01409007e070040b0a98078031562807042c2e090340110704485016801080c0001c922400980040b904811801100f401164260807150204101280a0148035410089605a80f00a50046250404040340c070503550103680700b8140f103540c03220b000607140c0b51a07419010046602c03442d51910b00c0e4a0b140d02d4559a0840d001e0b2454600c100070010f4210140e141000c00501d4041d11172035070007070500d8011034401000a0041c41840010882d841c0103803290000c00e44152510350005031a414020a521f050090281c220000c0018054103500c030947d4048a207500314070300b400c00603941d54031741c9003d074050007205401d03801602401017003180e0000003000820300c1d8140d40d401ea4595680d0325031518102c0c040da008590000e510180060401d080c6100140700300340c001400080c48114081e030ba0401c0e5402c4034805055070300080c083c00420350301044214040d0144a00540c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 2561743 1250 2560493 2560499
    0x5010302030303010314010b030109031115010b03040b1e0406050601170702100b0102010b0301020d05060a0b040f03020904060e01020a020703030e0105120a0b0105070f050c0901090c0e0405060111010911030d09 92
    0x20390320f001c180800307000200d02e09010182503c0942c040b00301300c0405002801050a2420090b1080c881c0200740f20483c010100407a514140c001903590586610361010b50442e103683d101c403648100d00800b54807441c0461101400c05c222110700540c452841040041042d203480c200050803403035001d0402a502958501340701d403503034012520050080c0340e03401c0055942c54900040780076250203100d040c3c15510015102ca004c0c2d90301d80000d0701c1240241d5423004170654031030310046248103070700c20003030403461340d42090005180203408a80c2140c0104008680044c0e5080040c4c01c80e440450100f0240c3d0050004008145e004041d0784a0660b090804900b0080103500300314a0100007420301e000c040d610903180c0110381c003641c00c0d900100d0f0844030b49010341c01c8601d000b07603440c4914103a15108001c20380c0005503e41050182c1051750490350b0303c00d2440416502480054080075088605100389078580304900f100900c80d12210300e02400004c202c40c501d4506050400300000d004804115070b5940034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 2562993 1250 2561743 2561749
    0x190201020a02010f0201110d140709031a0709030b010b030a0605030105060f010309080712020609010509070311010507030e060c01060311040c020a17210103060c03060302030c01030b0d05030c0604031205010302 92
    0x80d6040303030b02801c08240d400516803089004281d1030250240c00e60340894400b84651481d401410400c050107440302c0b058542d01000c3e074081c00a840300400c40a0081d401018140100c040c2075080710060900101550303c80d9600a0604800d070003420344880302104212020f0010702415000f414160001c118504085020600400c107540f8014180758441110310100319010302103c500a80085008403d8644442c0003501d51006070365202017982010040764900d200407c00a080341d80c42005079081a40034801518190060a015418001e00741e6a0f000b591322003500400001208100000f2003a0039072030300c410101003a12015020b20300d802149025180c0010300d08480c51b400002c1c0c2081c0b03284001c1c03000845d104030038446080c00c20100d009d1880c0c00e10400c0a505036880ba003002c0c020b80f000000120201c52440c03002a40c1a4003050034a03c03194082e074814000448042d0001c42c0c00e40f070b1501da107442c50340504007030380303840e40420104028154846079841e180440010248111351440d000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 2564243 1250 2562993 2563003
    0x80702010201150e011502100c020a03080c030702070608070e0d030203030601030c050405060904110706020705061006030207051018050a08070212060408040b0306010507060c02060f0c0406050403060e0102040b040b040819020102 100
    0x283c0e11051b04606140c0d60b43c68000c00c003080700d4204c490f40a010002581400945405000400314042050031001c501c1e490030300d40c182c2e403041105a0050086c50725019088072200f1016041c80c2c148404061100c800381c03500441e0840c0140a60001e594a080c588001030840d030710404403004010050105001551302d190840d003621108503004200302d40d0250440055201d404002081b135440090030030b040140125407030303124480182c0031105083e62260b095090b4820b0740d030000c02c0307604074891410000300994855440c11541109500c004041c9a903410f18200300ea10741a0b03180040801d8000440c42c00e1f00110324094203080281c805418544d599400c3c0d80190702400030812408000240964415000c3d1086960480424002a996418069110001078940c5880c00c8060800903582c0d40402c0c044604481040d136039546054950745481c03000f010b820310b0450743e0b0b5400f0030001078920728400151024010b01102a641c6920f40031046280c0100703151440044d000920080000d0307130b000b060f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 2565493 1250 2564243 2564249
    0x1602040b040b0310090c0530010617060103030e010e0f0d03090909060f0501050f03070b030402010c08041512020915070606031b06030b040510030303090606080706030b09010f0f060c080d0603080702010201150e01 93
    0x580c12103490a1008e03894050411500511a402d0f000324100340400c80000b4964100c0b40280c541c0060136103841d00445045c04515991500444074a200b234625040a0142d04407860203032500c0c1d5092500c0720314250990b80403500985600d9202e10b402c0c85407081d140314a070700425086440045d1840e03c0008261103010900c6200c0c0450301c003000003000d40e4090541001201d602c10082555951255040d0400e42c0c0010984400982c00d17480300c8941c050f5910845404080040120844143e00482020540d00c1003100b2200c1c0c94682000100060260140409032422584918005424090024112070745408420711581c10f2405200c40c0a0144240d0300980ba018640400c0da42c005040c000301814407503009816911442c02c00041e21a40359000089120302124100e00070b0741c2c1c4035071090511000e8080d0b01c010f90000e100c10816180209103c101151058501d181822560b8449504a8032242c2c425101c03a00f0000f80c250456a080c460801e03244034030403114203882d007021890004220140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 2566743 1250 2565493 2565559
    0x2060705130506040303030507021005010b03060f01020c040612030206160806060a0e090103060204050a05030303040b0105010f020a0506010b0301030606150f050d09081305040b061602040b040b0310090c05 90
    0x2040c01d010621852448007401e00500840c0d507072541e03490020010030080315500014016804803801818080c081d45048404110700ca13411a2a00020010308030022a0041d042d4454003081a4054030399014100c010409540c08801905d45811701905140000301005a8140d044010850054101c1031068008000b581c031580c90380c2c03e010b019500c0c49042d04005500040f102c00000800c54940c0042007a41d1007038801390302880c0d50380c051641ea404240c900505110300e000041c007003548510b4188001d0501441141c40007901500c559041850a801010110000000500130302c0100d0142000400038070100c0c0a00c20910700c001881a444d42418408000001944001034807103034100e040e040b078020302c600d07aa580200c00000780f010100c2c81058051400c2c8040d800903441e040095691509080ca560019000c0036070820000349034440c465a44959118541480364a04014601ca00c1008110001d220781c2c4c182402e107014035035a03220b244114102c401c86030384002180003034002c500c498 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 2567993 1250 2566743 2566747
    0x10306050705070b040510060f0b030105040902060403020a0e0405060c0403030206060906060c01060e0a0b01020307030f0503040501020403060504080912070b09011808010e15060a060815040b060f040f0b0a02060705 94
    0x400480342481050707800703000c1078540c1301840140400407075000600300d43c8290820001c0d59440204004807401c0c49a8a040744060004001905094210314406440280000d02e029100d6001410003011034109e01d8000515004000030042c00b004103d4002c0101080513080c2482c60345c0082d90f801d0010070241c000d83c0d44130f01291440d00d030401074500080f1100c00a01c4000d4654101a00661086a1440045041c2022500594000320840d80c2c01501903448200c1c10710f17102000d072201d40c00a001115503660800c800408540e452148a000300e202d10001559410a40c04001e83e69041d02c010f05d165401480c070401003041c290003114040182801d00340c07030f04592201030880d1907100d40e000f50030950800c4041803000502250800320000f01d075a201c00740d629a40306011085200e4004d00c00414402d5000c908008242074840d0000d1000902c0440c0c5045d203080802d00e9604250f4150301080030202d014001829840068405009008001401d18020020080d0740d0b0b44081d000d4000d000300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 2569243 1250 2567993 2568001
    0x60609060714060a0c14040305071a070503070f06050901050f01120302030c12090a080102040807030609021903030809070501080402060d020703020708060f040c0e040203070312030209130501090506090f01030605 93
    0x81d100342015566001403d4410350b160401c5120f01070407142d0790200c005042190103040e251590004d0b02e09a0303030400c0c001d010090900c01c00031000806555080200b20051200c403000580400c02068824805c25030406581134914220059480213070100c289a4102400c2041c2203400d03404071030440300c5068504000d408941016402d6200b215180440c60040a10580802050f01d004141480042d91002d040564030030b4501d00700e01030b40c020b0035041c7c1c01105007000032a0303d6400c803a6070305000070031229400041610144916000d03a008501082501041101840782802803d0041c2002e0030708040034a09940011224420921150200360b80411060141442048444054809603088406030b040c6160302c144c1000741102c003110b05618103840400c1420045460354001c59000d4020b1a01c03a00b076540d0007460f45005110b21040640c24000c3d901562350703100b103168441d0f0719918000f40c0c80d4181460181520030050409026546260034403045800c062072080c110fa4010320006501d4035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 2570493 1250 2569243 2569253
    0xc010e0112020409020301050906010801030f0305031e0906010602010606140912070b0f03100504090201051219090309050f030105010b0d050709150f030b030708100209040608010e100f02030606090607 88
    0x40407800503898602c040f901241d440030a6004605903402203482c2c0145503260001107550882c240001041c601c82d55822400090054000d9a0010401c04442c0581d4801e401c00d8406001d045484401c0e661000d4010483d81d0703020310862001d001d0030f141c021020103c031441401c03244130342a12140110301842d903c410b41c0105121860140c607800b00700994402311401040d04640042d01d110031a24a4100c000803540303414818186c80542c107840e090304041400a60f51f10684004100035050040301c0c80c410741c483c401c0c0c4525480503120b03840b920503040c1081c083c40614090b5070b0f4090b019070324010040c8201e491840503900074039010707071000ca156500d101084036415000d0b4440d20380408046900d50340c050704100a214131200e90364081100c95200d000f0542d894100f0b10030615142c01142c0000f05040840d0010080e01001800c08280642d481c0f00c4282107070f45180b101c4060381c009056400440080f4040d40d03402344030303e207030542c00c40c18900d0000b8030034410f0914492143c1000030b46202040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 2571743 1250 2570493 2570507
    0x712080c01050405030d0b0f0a090903020115060c0605010b0306240408030a0302041e030308150a03140102040e07030203060a060305040609061401090b04090506061002070305030304030306060801050409050c010e01 94
    0x30620001e01080c10f181c0f6040d9030f2a080071280741003650038141803108500b040c0c0340002d10524020f014080251810166000a0011140c203800315500d0701103480c100c1d20225180b0740200041c4c3ea80c46001029030032324104946041c0c200a172a6042007003840429602e507602e40050f10780480b0070190180c0711001c02c8a2611459110000724000440d0240b800303501179020740100c0d030500e041000310726043c048088805179503020040c00702d4030b038401141002105900080c515240584540010b03078581e1a03c00d0900500041d80c44580e4001905012909404031429080602400c06504500f0708800041c1c0700c1c0343c0ca00490003050f41d100002814032100317401c03500c201078015104200044045070f0504d809942401a0a841c900b00000592142418411002e040381c01801400080d20b811081203d04502c50714010110310a245020021036800d000440c01b8500c240c03000140c02d86003a40240462105034005031080d407424a407000070420108401404400134038103035107000149801a2204 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 2572993 1250 2571743 2571757
    0x1050c0a05061005011e091806050402040b031501020601060206010e0403091e030201020c010207120602090102070305120a090506030903030a0e0f0703030201060302030105010b07050304090b0d02060d090b0a0c02071208 96
    0x30307206070401e0059600380c1d1072424040e1354081c2c0e5002a00b03c0c5419412500304031444240303000450800040000c3d03a08940c42c15a102d803107480124480ea82c8000040c04d980107038200f00c55028000090150f064020209204500350a002428443d03140c060f0294035200140304103802903030500b00140130144136103000b8010703155003428282121610020380c81e1051103808100d000d0301c11b4011108096000144620403202c1d00f011608a1048030b070f590728003a40000b0b0090741980b144080110000e0380a2098619080010040c15140d45107203000502c084d1032580410300450381002400381c02040402200e0384000900c401003a1004005050381c03a0440690100809005645003c800c040d41034014400301c9008400a210b103036203c04101090744904e00340203100f03038810001000145005c2d009480b0b030741c10040400e102c180d40c42d004180241e01860b0b82c46001961424210100001501c501d0f8000d0070714641007140c0c4c00300c480084d507140f40c1e50040500c2d400c01242c0c0c41c03041021001c00c840103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 2574243 1250 2572993 2573003
    0x3030b13060305030304050601060801121506080303010b0c0d050a1202030612030a020d140406050910020a06020d0f05090c09060409020607050a050c01020717030d0507030b1806031203010e040201050c0a 89
    0x710356903810700d1a00e0390400d45045816000e900000135405103c0c452041c180c5580050103030582201d5030f01c01103070f000e50710001003100b6240d884c0003c000d402030000c4d50090803113070030f9180d890410004032401c0072410031050007848400e00c10b40c0340e29079001c040e0402e07e020100300165039440d003000080100380008004200d43c82300141d0b103010540d010588181c170360100d490f50082044030441c1310005029034042ca0340000c2080c1b15022032841c1080303001d580340c007050066500d203100035120030f000c1c0e901c024440c10a44e40c48560040103241240b00c0c4e245d000c201d00d800b0304081c184440001d007007080040c0c03146100d19283e49064096607078950840e0441503104040700c1840495181c40c90701c4402c0408082d01500400130005110140c4038100c0c2d40600030f0340b01540c60140c10541400081170058500000c140d0f564900c0d0115481c0c61240d085103045404500d00203240500c03c15251034141030b0780c072000c51000d2004004912510007102c0e000380d42401e1094540300041c5500d49400001c0c032010702 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 2575493 1250 2574243 2574251
    0x303070c03030f020709051302040507050409020403030f08060d03140903030c010504050106030b0112030504060f0e1201060e061203030a0203090a0b040f030806010903050606040506030309040606020c040513080703030b13 97
    0x1040641000c0e0011a1110b1602a0f820860b43c03424040d007207c4c1e0440300702012400901ea510014a82903120681c070040c00e040c502d0910303844684010403a0041e800840201c0e0360251501b0b5180c0d0004c484a0744020704445042030204513a070010700241d03000000c1d0b403401d580810760307114a903424815100840116070007044580307001e04249000c0c111912094a42c010180004124007070030001d58910f0b0780d0991078503841c0515001e02250034043c038040840411030642c80702c818541da1030100141515164002041d40d1b810a230080300c0d6050050030651080580ca4410f0007042c2011054a034005d2160000603120ba07103404c0c505042014000000b00403244a004000801205013a00007171103000b0355a9003803c1e692040156011403040c0405425640f1034000603845207056080554044006401d8030300701072140e00401c06036101c0d5004403000da0000e2941002c2e80c107140c8140d07644054420701900004c0f109848007802ea104514014081540f80c10300001c45884202c02d90491005100f0108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 2576743 1250 2575493 2575499
    0xf0a0c0f080309040f0204050301021201050a080703050604080901020109080301150f0203040f030602070c030b090d0207080102030c0301050d0c0b0c0309040e03070f120c0203060109020901030509060601080106050a020a05031303050f0313140303070c 109
    0xcc40016003401181c0c0b1071624500c003c00d448000280802c00c0c0ca5201d4010b10340c0ea00d564943c0c100e2600702001c01811507407078101c190009040d0340c0140d802810003c0c0b4400d070004290201800344840a00d82c80115801888100700d0650104265802c5030b40120700165200380c681001e80c00009990405442c20b80d41c0000e000d003160b00019841c007502c00545c00e4628258a450a441c241c2c801520f580f80c000d44180b00501052920745180c0d80c03120b11503001e10704140e60b03810048856810030705070f50050350800f00301070b040d07030a00380200d40c0c01c42c84143c00781d0b14240841c2da40300c0e11100b6000c0d02030020b070050a042e5103924003d41181855075001000c035451503035106d103080c0281d4808051207002908000200c0e9800400040703a5008402c16103455000781c0c20b01c5801c0f1000d4101c5440300046105008000011032010300003044401d0b0110f5214440a0a6051140c6006480d014000f1250b0041260041c2070202d0030728030080d1200703140d801e070f4102000800a403460166210107800750180c20000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 2577993 1250 2576743 2576767
    0xd02040807150201090201050405040203070309060f0c020c0312070602030c07060603050601030c0e0907031101030207020402041502070803040602150a09080a2102070201020c0402030a0207050f0a0c0f080309040f020405030102 99
    0x7100494003100c510710080560484100c4c00d035001064000d0204400340028425441d00c0e802540c1d0296062800040c000e145460b000180d585c440e031407190580c3e5612030031034595810b2106019400d0280c00800c400010021084214407603807902400d03450380480410401041041141c203050b03003190007484200e80303078104141c441100303110884000c1d80036030000699400c1c10410f18444c0450030060b044942c5107071158070001007900c042070f040640c200b00600c0140c0d103600c06000902a0803002081408541101070302d411032581240040754424401001480e07030000b07080d244280014290b00c010b0b12030880f9480a81041000100562400f0030556130b071941c01a82c0d5141500a218650311007400c13030080c04c04921569170b02070f00503002680c0d41500d500b000c0d0000d54000254020040c5030080f00c0c2c030340c1420304499111520b01d0340c20a6225405002811080d01e005e8800303113040c0c602003131815060940c3e034450300791054001e9455505c10207000741581d06031002005c1c0a8000d40d030360f00311003ca03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 2579243 1250 2577993 2578003
    0x20312070c0e06040506010518040f0906150801020702030a060c0e09070509010801060e010c0204021e070b090609070f05010e03070305010e03070501140103170c0304030210050316020a08030105060d020d020408 92
    0x18402450782c6040001d400361609001e028080d01e410703101e841c900603c881c24000c0081c240e442031900b040c0c46202000c00c1c0c4625118400b11036000d04400940030300c030340b1502c0352041c00d00c1c0d01c41e0380103a00600c4483c000da40c02084025450f81d00c00c600180c0440d490704181e42e0ba00d20751030070b250722a04810030045030ba0740010052000200907a41d40131960b81f1040d055850401c00b0141e81d001542411204d0010704180d8001e101c88210180c2111094080c0e40201c0d580e0350085000301d5030b0910000a029000c9800c000d213680003407001e006403207458201276034501e11100c0b500c5854100060300451039010b8505108040107540c0240081c02143c4104020a0740c030380c00030100700c8440d840d04170b080321000d154105c114103036039220301c010103a00c0c4e22402204090708600c01c100700c2d50208200020040c1d688180d0725001b880282c03500d980368585090700540e907464650116040d9007010007a41d0008604104990548104490464907407240381c0260009000d01d0801d0b168035440098007240d040b0340010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 2580493 1250 2579243 2579249
    0x106020c01020a0b0106031e0207050c0112051303050702011206140f09100506070c08060a2003040201020d120204050409050c03010c02030c06160c120c050c0406050105070b04020312070c 82
    0x8452000e0181001240d0310a4580d030050124015007005100143c405c0d00610f050031404005000400350004440003268041e060440307142d80041e82d10003565810907150b48010400c0301c0100300307900d0441188860084500d00007001c01c00d0010f241004c5a00072070304803503d100002c4041014540f41c41c402242d10790801d8070188035024060302551945490b03a8114070071071080e00c1e01e0484501c0c240500c0b440d60844c00c1c040b039900b0041c44d00070907000002c2003a90321034941b0500128402942c1d0788150000c110350000100c00a070100100300c0981d80018603803c1c41c0c041b5241100144004201c6003000340510381195a010f400d0406a0702400800038200c0511340040f4001c10801000b450b0070b99480c407070796007c454150042c03400106070009600009002c0455400c290031184500d03550456414803030a040310126140c4996081030100c10401044503ea054a08200ca14107040003c0d2050060020081c09444000000740c01c544040c8040585145500c0f2041e490710f4135440c0c00841c2800304c0c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 2581743 1250 2580493 2580497
    0x80705041d010e0a0b01050702090402030a080705060109050c0a050a080606040801090305041e05030a0f0203010f02030c030405010c0801050a09020705030c070308030708070e010503010e04061104060f0201050108010203010302010806060a0c08030703050106 112
    0x100440c1c131011641c418400200c00503103800c0d10700050741c1d00380820000f0080080c0e91501682c03555002094a6000a0007440e1240010b00010f60500080354225207024100c2c07404013100b40154803165801c20101d8110800d40d017840038041d034503c4001059480381d5005641c00c1d50030007610304101600600904281c03411000841001030090043c403121590601c241c40e45a07020b000100040751010785a41c07480b90000d000421516a0004c0c0c0e00d041c2d130b005607041070040600008202c24050f083c4507981c1c402d509441e001015524210001d110703800d15004d440f12159000444e401000000c104480d0000e0a010a4071359070b40d80c905009c20240c108940b5040840e03c82c800040b0b17200e100712940c400884058460350700b140d003041c00ca50300c1028000c0040303a0481c1d440442012801804000e84020405940d48861394000c08034020b00b590384c180d0102050380e0050005000503a040015103501400640b413981d01e60505243c215265804042c0260280f8000402e1103219940f41c3c204605070391807070b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 2582993 1250 2581743 2581769
    0x1b0501030609050903040e0403110d1d0301050408030105060a0302071208010e0f0415051801110301080706020c03061b070c09020d05010503190201050306030a020a0909050105060303030103030f080705041d01 91
    0x3154000160f41c400c403410821a001008140b025030756110b20540c01500a02e0840d0111000090540ca0000b15210302000306840e83d00305210b0910183d13020301c14040c1980248003e0506a445503003502040c05840e124490201d40301107051311030790641b0840b0350421448140100c08e14400342440b82c00780100708440d140e480014034890541a07c190080c1c0e40000c000a0100f84000380360020100a0840c107461042102805030904090161a50740d02d121403406079203502d0700308154607100180c0d0151040d50030180040143e03aa01068880c5c1c0801c01d540b5540c400110ba01078403404d403190b250001c0101d0841c0c400400d4a650329400f528809117a0304003005941d0325407080580e94018842d8480111190240030030045d48150044c641000b000340440705040415400910410001d81100e40721507a100180c5040c444240615a0401d005030061880c65055490080c08030500d085024184968540803804180c40f0303808840041150001c160300c0c6461001604050010a108112880d009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 2584243 1250 2582993 2582999
    0x609060a080318061207030501090c02010b010e10140a05070201090b03090606010c0203030405031002030f01090b060a050a0509040c0201020a03060e010f03060510080d02060108060c030103020d060209030106031b05010306 97
    0x1124040d041500d032400c0c0103505140288425650210a60200c0381d08034109110b500544d0814100d903d00410186e18081030342d6050003403c4080702c20603005a81107a041024002c01a604007151729a001404d544070076800b0388540c820382c0c1c3c0c07454456000744a0840007429503190b80d44100940b8166100f42e803000d0001c1c1d0b0700e2001c104140006d451080700741c0c1008000c142198052884194002d1020b02a00d09059079000000d0a0003880c813004645a9000810807903401c1c0b500480300d001d0000c5c1ca000b0000700c0c420102140044c011980d10000784000042c8100402e8080c0080d2080721130002d000b4000c2c07520b08a0b00038080d4020302c2c0c0203030100341040030105004000b25000c80c1618410280407009901c3c0d510740300060040540040030207480c050010500b21003c2c00301c81501c00c1e652300102095454a94081d10302040107158000c1008180014001640d80030f00884210350060740244e01c171402d480003e801480c1546c030003803a0150200d01800403044c0e14001c003040300c1d0709803808c0084a40d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 2585493 1250 2584243 2584249
    0xc0f0e060108070504060f020705040c020102071407060804031d090c040305010f0c08060f06040803030103030c02090106030903020c06090118170709150605030405070f03060f06060c0b040b060112060905060906 92
    0x2d01520310b00302003107003031000703104880c89490040c5902990748102c2d844140c0c1c3c0c4010804544c142d10072500180d400043c1d440c00c2c442c0600c103051483c0c402600030132000780b40c0a0000c01c0110042d05c000c0400084a0f158841003c0715442018044802048041241003440d0002c40650140c88212529400c1c4072490511421a104200000c01961140c007881c2e69428108608100c081e080e0303a9202c0428030001c10b65407002c001a5002c1c3d8400e46a00c079645156004200203040142c0c4188101818120394500007a40814011402903098401300c3c0c980c465140141c03107170340c01840c0c185650140c25000041c1000e284064805081561083e0303940d00d0340351202ca405072001508a0409420862820494203103c0c90040d030340b0500400c20b03a4805034890103810710440c0346034415039a0541350b42a00c161800684100001084103007481c00c2045c00e290340e0307502d941030010409403c6000b21070010300799034061500c40c1941d06c2041000c004484d00c0d6035400000304001e41e04140900c0640c030002d03080d82 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 2586743 1250 2585493 2585507
    0x601030b011701051203040806010906030204060e0c07031b0b0f06010908010e060402060309160b070201030b01052107050d0e01050103050105060a051e010203070807031112180603090a0c0f0e0601 86
    0x100c054562802ea0f00349018012030794402c202c40c0e41d00c2d11003000b000845202c00c0c840c85000e080c1020012881e9803641c01000f060394555003000400100c01d005100c400d1055900300c07540300780c4c5070504542e4550004081014074100328005410f00c88002c0802032400480ea407401d20880d0262a001030641c1c03100005800c0303403010156844640d000320049005450510042c0d40c0c0504e0200448400f5805181004800c001d00d86c42800c0184000c22500210360300340c003034204000001c1c84c009041902103189441c964107912a110024148030300815820380c0704600300e540310301003200280310080603003e0303682c000c1c1002d10040e01d041d40f030a13010407460300d480001001111001050319030442c5056090010b001d0503014494150300c010014500011210030240443d180030b40c40303462410b100c0000080c100040320b01810f619403010400d2500c0c5008600020700e41c01d4081d200385403240e0345c1c40e20561405181c00000740254901c90400031703c159a441070802594040240f080b003d48585005503219 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 2587993 1250 2586743 2586767
    0x41b020705010507020d02030706080703060e06090604020a090816050f0a0b09010503101d09010506150a18050409120f020a020105040501030902030a020a090606030605060403050607031d03030901050601030b01 92
    0x10380240c0800c011a42c81030001c2d02040e40000e1012103804c0b020b600003442c1c030840f80e201c00c0100307450004100407242c00d44501c0300181001502c08119203400b4001800b2450010461481942d001c00ca405800c3d205038110000743c0450412144101800110030749140500d1050703500ca000c0c0c00800046031b0400324400012640c80d00c6040342860f04800044d03415800c01400425440f0704402d00280315258003200c040b030300041d4429082c0c1401c008031401c0c00c0d02c1c0014003050043e014050011600c0c901d901c00c54100105034509603000b0260b84049409030032440d4022075001e0b007000e1402e03041c40191680044092441e0b00ea484480c051410140e8072002911006400b040e010f200401055000b60040e24409100406076402076040e607002400c0c1d4440d6811040c003407035907050144985500352250f0070241c40200c0e0000d041c186940d60b180d643d10401480e1074105901c8040c405485110740281034448850034040e01d490b46000001c4c0d90080c0802c50795140002e040204900095004030150f90340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 2589243 1250 2587993 2587997
    0x4060b040302010507020310090602030403030f09030909020c07170c01020c150301051302070f06050604050114090a0c0c0807060c02060a0b091302010203090a03030206060307090204080d12060b030403050306041b 93
    0x18180745800540d00c980104005031b030140101400540900d011f17125201c4070030304c0364800503182e082c1424020122001c002070325131100d00e4620a8804250016040e0048a001680c05030761244001c580301d040c240c06a02110386001c040c0303a0850a450081900e014001c0282d003142c0701c400307400c001c000012850340c0190000d000104014459401c000c058014002109140585400070303035592001c148a106070184e03117043c0d0310400d01100d46410701480f401011084800f1500d080b50500081c0413400280a140080350b45103482d100c2c05010b554418141a000761070580c40780f40d6410a000a0009400450010302501c3c0c0094000c0c0034900c1040742034080540082c40319503542145400010030074106905520091000c0081a0b59800031503000e180700e079002c0c0c51a810310301d081c5490451141c02007500d0a00611007072020900001e00007004140794600604c500d90b000c09000010004d079048a42c81d00d038000208014190400010350003841f0544007000b00703005a0b0321106404a0308114040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 2590493 1250 2589243 2589247
    0x50f03040f0309030206030705030402040623040b0d14030406090501050a05040e060301090b0a14090a03020c1504050301060f0611010b0109050409020402040b0703020109170403020d080a05130602010b030c04060b 93
    0x2107220403110940c810b00c42d05041840e6a240c0d00000d9980c1c104445100000e80008208401c5040c40e006110040541090800090403062079807800342000308112070050b651203010141a80c3e070042901d012070f400000d600c40302d081c42e00c40b4584990040c00345030085041610b0001c1c0c594445c8007200c0e12024103645032424941000c24501007060301070300496156407a14080d4020500d41192540914034140001428800c0d0640c060480c100003041550f4039004100b4000101ea00440c0d090300601e2308807201d00404195030481c203014062074015641543c0382400c0454064164104c0c1c0095456907111840303020f15200c506400d0300c41d0340341518001043d204040150b0704083d0411455a48001c0000d82420788401001c083c0c0e070892403080e40180c1d11080c61200f031113481c10340e8240c2ca01c0150f96051400d42181c000c945104032003007005040b0b00c4002400481c2c0d81c49103043d581c0804d680d442810045540f064024080d080207041244280529003240c41585002d00c908030440d1f90070300d001e80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 2591743 1250 2590493 2590501
    0x901050307030e010617070b040e06090415050403030b09060d0f1e02030109050a020a0b070506060d11030607020d0912030806090403020111040914011403030d150812040312050f03 79
    0x494980014150206040c0c40b240380c0c112000c401c2c042d0740f014003800306181c0c0c50704a100c59428900100f45e4031a440f080e070208000e2000c006903030500c0d603211400362542d1501d501d0f1031500d549004901103d00049520300000d110070160305800800c5610003c035540c0d4043e482c1c40c01042841500c0c0c100017070808040c106032034000b820034440c02c500025910070f00c619050007900401e007501c4011030116002d0b00405054400c40ca40544c0c80006011101900350900c890ba0380c425564150142c0100d10441c0ca0341c2c078800c10800a81808035000d07901a00340c41180c280b443c0007940d203031424810903000c503a4501300400c264440711503029005030195a1140c05482d07540030700068002c00f800507800c5549075494201020b84220040000300401d06001400c09003d0400284c89001a001f01a913800007081c407404558001064586201c5a4080082c0481d480d540080250711554001081c501410b054000d007036041d00c01400c2160f0107407510810320852404204c610384038090a8010000d0140042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 2592993 1250 2591743 2591747
    0x20904060608061c1b0806010f080102091305040203010f060b0307020c01081302010311040801110a1803020d0b10090c05040302030606040605030d110708070b07051c080118020904110304020901060804020102030901 94
    0x90028900503407500d003030303401c05a81784441082550018819a4885001004959141074811009080762402141041104000108030005404601d1040758a65020500f5541c0a40c0049000306c080300c4104a040d03a20340920a0035002100d40002600643c42410a55409520b02394423074030581c26841842800c5500540c0107002900c61b81c80c00c50014003000c60032880c24460040e02071400b00c0b000d500c940035140028007114440c440511441c2400c242040140c86030aa0035807560b0303009040d59155540c0401d0308c2c06040c2c071584814202d9042c07007014040c40760041c0c0140144d0f4001d030b050b070344640e442034184400d0796200d124013a0964440d4010b07114040c07003510032403501c031042d500b0755074099030301d50f411132501c20241c000041d20b04c0006420030400a0800c02040c01e0340341190610514160380740080c100c9201417007087d1181c002051042c0c400c04c559811600c0e0340b14018410480620b0810102c032181d001264100e02a010180010070301c01e0240c2d0060b807040d0390507802589445130440c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 2594243 1250 2592993 2593039
    0xc07090f0c030917070305040302150304050610030807030f02030705010f020903070605031003061808040602010b100201050f0c0306011709070603110c0709090201030608010c0e040c030605010c060e0c06030a02090406060806 98
    0x10550400c80c0030721002c0300590f224bd0240401c82c49514080d5185c0c18241041307810008058606182140800000c00024100f54143d0b0b0040740c150820745140c0c1c04224040e425803280c00ea0040803546013100c0d1801d901c0050340680101e40094040700c49103522400207807010700c000c0e80c400030811001002040019480d4002050407800c841c0d08004081c680d94400c4d01a802c15042400940d45a8144032107909005005a1b41032445100034031480c141107a100c0c0c00900082c1c201c010305500000000c000d40d014801000c1020384a10402d1007620385200d2540c0c80350b0040c080c030380000741080052440300c03111400b80d034042d06296010300308441c42c081d013000c020829408100d0525894030400030b11903a0a1082c5c4031001c18540362046600601404c000071030310700307400035414585410014403080c1da000307502d58003856000c04c00140c03010049100c185004200c2070f0720b59109034004100700303401d845034014004052040e60240001a00d80000762004c07801280c0c1e40d50000c0e010a00301100c4426404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 2595493 1250 2594243 2594257
    0x20d0204030b09060a0c0c0206030402040c02030f1b0d0504051005090a0506030103030e0102010506010201020408070e0402040f050702070609060309020603060402031e01120201090503010e0c0d05030c07090f0c030917 95
    0x5240503542d955a0b500802e0484036005640c001404004d2500200d0040c01e00d03500d080c3c40c00d0465002c081c0c0c0010140c4c040540302a0046565030040c1e4041030081044950b540e00280d0203a40301c0300c82c001c90381c0d0300101da070b42c000c43c0d54060f005040003a45d000d001a50b040d1180140396807000195420210390a0f006840c0507980034100c00c50015140d101e0b8402180614002d0755002a030300d0411002a003900c50180003a030441e807040004200c02100850408141c829101d02516a42c546000040c050045200c0e40c404080c6480d0601808540020742c0c04201d425a031210700100c0e82c0e6007000d4007128100200a50081c100b040090428601a8002c581c40101a2000e43e62800381144025412000341c2010124108447e0f83c0d10666800c08800c20050104034000e00004803001405a15050000c07619800f403c5080109070402c542401035501c0c04010070121003440e59507035449c9014050b12400c0c0c100c00c0e440d200c0640e4005200e40504c480142d0451424105141c0015008000d41d004003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 2596743 1250 2595493 2595517
    0x90a031b05060f0301050102010b01080103050705010c14060106030b09011a0406030506030f0d0f03060819060207020102100c0203120a0b090705090a030b0a0f0e03070f030318080705010501080606030a021302 91
    0x2400119060ba80c0030040d180e8904102c4016407a58100320002e4212040300c40c1c1c15062000980040001038000030f244410780d2001e1034504a000018a004450f030a04001c1c031146074080d42c0c0000c580d150781603001c0c030500d070700c1101c004d001641d80b44600b1415203103a2030094454001048180500c030301035048130350003134400b8084441c0c803002c10403180d041582c04080200003030002c640d00d0120540c140503a00103090800081c0c9561021000c00039411311481e44c0084c0099008180c0d402568000d01030418070310341030b80c07041c001d1400c1c80707200940381c0e44185004491245070901081406105200d26040010050030103180745c0c840410903155a04501115944845000300c04000507020034801801480307400000706800d02140c2c001000c0d25214903c0030815030041c00100081149407480005c644c3c2c042c02c0025207803a00d038805000743c2d11481c1d005450800c0004500d0100501540158100c1d0700c04400e41c1c1980e2141c200701522100584804bd5101d48413540d442401d290683c02056550010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 2597993 1250 2596743 2596793
    0x60105093702030405070e0105010e0105180f03060907030506070306030b06010804061b02070305070b030417030c09060403050a020109080d020d082502070305010b01050306090a09020a0305030f040305010b06090a03 94
    0x804401c0030b80e4401c0310f0440c0c441c2c000704810012401000070803400750409003000301003d5400c00009025000d41075400b00140300e9101e1071031580d103404200c00b1101c08041c082c0c903aa403074014492641c9403c64401105d05200b06000940b405100384903a07400d40b5400b8950320100c0e2664001104c0010000d04140c03180d40c0e9410040c1040a043c03c81d10501ea40d640d006818414918280300e0f0404045521171503000304100200701c00a40a074280f86031392040c00c0300a40e00c0e038641c20b041c40d4083c0036021110303400400009020090080c00994444003510036a90340c8000da40340d04d9a1621041e0b2190001e015074400c29400001d140200c610b540d01400b18070310741280c11903d1703018070b00b20306278008103d002d82c2200c01c05100b401300078010515009420708010b440c5052041c0460f0080000410000303119642d040c030700e0308554881d22103034000e68100003200d407506454140007070b9545c0103203c2100c0541ca0803c201d0714a00340354040d9a0200c00042c07004a5880c5141c890913402940b09108440300941 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 2599243 1250 2597993 2598091
    0xb030c0c0f0303070903020111060c03010506070f020d0c03060f0605030304140105090910060807020105070504050d140601030803090f010501031e0212030f0a030c030e0c060f09040501080303070206010509 90
    0x41080a180700d803004d642ca10007a1031031800090702130040810f004240340c21035000c00c02d00c210a84212811541c0c192202ca94070205401d1a14200b9085a030081d80194061486803c0c005000c5040040d01e0288004200e18208205c00c4d1088460620400d50150000d101c2005508085038851004100604241e40f4120a450000c0c0c0f036210100c0e2042043c64a401c4144241da0380588510391001060000300701c1e43c200a5405031141c0594400c0c584581102c0110008000c0c0c5040f9010305015900d0803123000c0d58692511030055001124000502c1c42400403d0480d900d05004640c12280c22100d00500300038843c210030340703200050700d00780c4e0410522010001034810030001007101511a2404a0b10f40380301d01c4000b41900c4a03c01a0f004141c01c1c0403540740e01c13a102080c242c960031000c4801680c0e4411500e040015070158042c1968028034140c0002401c01000c4000d40c450304c1c15509a51403a07880b0010404510b405541c02e41b81c21642201795000e81d0041c203007240100b01040848030014403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 2600493 1250 2599243 2599273
    0x3060601030f0605030703080304120507030212030601050409020a0806040b10080c09030c1003090b06040504150c0909020406020705030d02030f0301090e070302040e01020702090702070503120306130c0c03180b030c0c 95
    0x446c81c1e1044408510000400040c011348800319110312080b0300c1d181d80f408020392002541c4141c410781100b9514000404079425070b00038403c440052142ea18190348a440e80d860103400b9030402c40d0585d001d01d041c001d100c2d4842c548540980c07150216900c51070391a480d0758800d004640c205c8049107425104080d40360826540d51140c2d0100024180d0780418904082e20f4100ca440d240a01401c0c00366081400303000019100b12290071408645040c00108904540310440d83c03d5060303401244007900c001008511141d02048803000d48200350103c2c0ca0903112501c04136500e204801d690b043c4a901072005011215032500001c400000b0f920440d1401d03900d030b80003d41100e4046c0032000003a075000170f501e801c500300a82c1459014201340041e1200503d0000841c0c1c40f1100840402c0c0075241c00000100140d440c0c017030a45650703503406000c02c200d254001c001b84c10522074800036000b02d544001407500041515030140f064505100c0320a0841d102d03000c200031641c00041603000307103002c0c44140c4001740d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 2601743 1250 2600493 2600503
    0xf07050102161104051605030907030c0803040e01080606010c0f03050906030a0501090b0307150f09030812010315060317070303021204080a0f0806030a0b1b0a031b0c0203060601030f060503 83
    0x1d681d0942d24041402e500d444041c0700030500c42c1602850601c030402850070302c9441d200b0709008a81c1481c59490b5588000d00f0701745140380d00f00401052142074003150b032440002c050010f58410128003074442e62200e0005903620070459009001420400d140300014101c01148a030701c5109040172814401c41400282554104460b10305219982e030340100407036000c500920000305410342c0500941400d1107012481a0b81000c004824030151291140005204201000065812255440e281c800c04449014001000c0c4006d4903503d80d000d00c444425800d0b44a2202182e03403149104002d0521000a007550783c01185c4140c0605600340301500f130000012002a108a00c035420140e40c0303c1030000b02034001c4070040c044070100076003070040102e952800170300c5017011741d08012241c041da44c0f040004200c0a9141404402e5001c004c0780c0c842090350541c1000500d0480d81140944503000142c0441d003080c000c88000e50302d07520000c0801d185500942c003204482d000700300b0204002c0d4991004c64500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 2602993 1250 2601743 2601757
    0x7020607140a110105090a05010e1c0501050f090607020601031211030c010f0f020f070602030606091008010602010606080402030303160e060403150507050304080711010509120609070f060203040603020f07050102 93
    0x16802c030589240070030440c003407035580c540001d0034541c0c24900b8000104020400500030141844101e00d5103e401d541c440c48000031070b0078055018452071400d4034189020786800c0c2e405a404480ba10302099880704045131b560f10a02d42640144050f0303286454042405da20442e0040034082006011040320350240024030000031000d0011502c108041d800c1c0003207070b0140c40c030318074054410700004a000d0328035800c07100c0311500013401580700d884500006a03180718100c003541d4040b100400d0307404070742e40040015040f90345d582c000300101a540d000907202c1d41c4049900a6142e003007080051f90000401c810764070100001d1030010381441950700451003e80c0183c100382c400110005400d1100503c5000d100e90085041c0b4189041d402d00b0764510703003540960300d0000c003034090f24906002c031a441941030fa20151801007100754003059115400703480345000e0341d60601c58080c01c02c0203d9201c840003180011201e1030b6006624180c80d05c00120002d4101034814016207501700001008034a09002070800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 2604243 1250 2602993 2603033
    0xa0303020d080a020a020c060d0b04050414010f180201030507090b030109060e010f080a02090a020f0409021206030109030e0d02060c01060e060901080a0b060405060f03010626011503030507020607 86
    0x1c41041590182c07a07401c000341105a4a8010001215200c2c2e01154440f031304003003503c002d40c4503528484076001400810f001c5a8025181c071042200b800b06140c02400b0303503001d0b03038020088010540880750035682002c81c0611151019034480f0015446030388515402402803500c05056525031f03140d19481d610aa11600308a80c4a1000b4052403400700b62840c0180140444030015900d0140455180c4841c0000030b84511902d000040e080081501182c2c001c00e0002e91a99079a61202100310082d00600c204106045080b80021950f050500c0340c003070303480d03019181d0413210060081048490f510311903040b60400c105005050841b102402148090110050304504500c0c051086c031040450503806120f031a0b01050f403541c08506803c1610741c00440aa40201e200d5583c040480e01c282c00c502100c941561030654006410f2000c03d2500042184184c5a02c0c00c140c1c03c80803181c2a070300c1d031090514860310800010400640103a0080c91601e1020b04120300300705039901c88a40a00d030314503900320 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 2605493 1250 2604243 2604253
    0x1030b090115030b0109020705070f0305070f0803030f060603060a12060203041109010303050a0e12030a090609050409020a050d020102010e0a030305070f030504050c010e030106051e040f05070f140403020a030302 93
    0x320200080c0201060010610b48829040c2d195480f5207101c07920600c60030703e40703960000c0c4060a104050000801038001d807503031550040c3d502c0c54281d5940f1082d1081c1d42c07041c18204004a6046004000c403030043ea165184c40c841c9888080410160340d00182170701e54006141c40001594508100340f4411181c05400d0042e26440c2c1400c3c082540c0c468003000078440c41c880001840040d1708803064410111051070502d4407800382d00c0200d0b044111880c240e0090b8403001c11103500c00c1d41d0010a8000f85d0390550740c1c035118203650300140400e880130f1413070003036002d12552007e000a04003401c08610307450051001140724424020030720300304200105c0580c0085d403244104a440382e00111300444403d203d2900304020328140d102c1517211030300400d40d68100015540400300790390b4250003010280000804820042c014060411043d0f005c8044160155040c215100c0b4103184a2140600c681c4141d01d4001c00300e05401000c882c110240005400c042409000c0030000d40c440d0140540614441c1d00201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 2606743 1250 2605493 2605501
    0x602070605070c05030d090f08040e100503030408070b030c07080c1507080601080a051003020405101e0806010b030a02040f03060209130b010e100306030501020327010c0507020f120601030b 83
    0x40507598001d2400040c8400d008058001038070000444800c01c130154400075084959140c00150342440c1c07130340030300444004207000c070368059851060b03805250380c0d50641c0c03c85551882130540364000c510910140b078009000400030317550317500011030703021050030406868582130b9a100c8034a40c0096522030303001e500101c140c111180b00b0008042c2c00c01200d007440c0a452030708200013000104024200d240458550f00880c0302c1e1030070420b240300510342c01481800f17035240a98003030100201c1417240c07500c10039a00c0c050b62000808200100309540702040504140c4c0c1c01c1c20007050556002034100302003640c0c20480001c1042c6c0f80e92018000d5481030802682c3c4400040400c403500c1054403d50705110302c0d010340402c4580c0c00c8072446607414400d4a24080d4030351003181c19001800142d20192181d40000300b0049511003103d015644c090060340c84040b00001d045041d400c07900400700740d9005c22010088680075140c0400a41c80d00300f801003540b1725400002089a00b014002c0e8412078803001440300380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 2607993 1250 2606743 2606753
    0x1506020a030801081621050d020c03011805061602070b12010501030507030b0307090506040f09050a0302070605120606031b12010302010e0f0105070b0a060f0f0306050106050f0304140c030a060207 86
    0x603004008080007040c400407941c1200114592070b100c1c1c03d0072206c524600040c141600e0103c10340036600f200903100c00c00718000001c0c0d260000c200c1101d119500c0c2901300a84145040841c0b4040b50300000240201e5645840301d03a074580307030308012406500c95010002880a042001044c00710060401c08405502d13190014007030b240054a050305140c100b00700210f15071400104c810403619030002c0410360341c846601140003440b04404415455060200c06400d10400250851044d0b110f50700f00c41e83c1d80d5645c1e2085401d4020340e50207282411070307800030034002d1501901841c3c0001d1082c80340c9544c00c80082580c441e41e0300c52140c4c00288140c20004105660700803c042a4118064030912048047c3c000000d10620611800074090080c5c4004501c0c0159558401c2c000b400c200100240d803941c4802e0801782d4442944000c59a850400340007141d2a442134056581c4144202c80090035510340d9512404000090045840248903020044940740d50422408140c1c90003000c0040ea944070034104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 2609243 1250 2607993 2608007
    0xa0201060603060501120c140c010501050f01030e150405070b0403050607111207060504060902030f07090f0603030801050f01020f060c040f0803030601080112050a0f0809040f06050604050103020703031506020a03 93
    0x1e5000d1500e42842045242d801c0424a501c444403584005604010840d060f12020780710368902d9607c500104a80540b5401544403a0685a04035807005c00420030400440070ba4041c103580f5580d80d00a402444035000c1d180e01d269810070722480540351041e480d580403c0d104d81081e40180d402d40e102c1000c0c0516983c1040801c501c449021020300705500406508088610405c040209229592000502840020342c44a45001d90080540d114451180e04043c0c0e00c107001d000d4500540e1601c524000b00000600c1040e04490707041c2c881040c50780c030f048200182025850b51042c19070003101c6404404440034040c103403140e400300303000c251581e09186a90000b51a140c2100c0b04550003002070010681c0c1014446e81128409011880007076541d140541c1400340b1894010020a00003400208205984001c0d103107000702600c2c1080540310a00300c140585219204098224008100a02007544250014090b40c1e01900b800b00e5003290005403102c8403441a4030080058201d441c50340201540056 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 2610493 1250 2609243 2609249
    0x3020f010c05060121020a08010c0f0c0209040303050603010f0c020105100609230d05031204022b02090705070b0f01030506070914010518030604060501090e0a030203030c0307020705090106050a020106 88
    0x41d108840c040c0c0d0756500d9980300810b0050500588070807400c1000d500ba00b8404805540e0701500c541c1940b139498068502809a00a407240407401170000c403408503101d03109500c0c00c2500205030700129221610164002c00010305480e401d552543c511022079406409010b03000344070b0b0703070001503c0d00d803d240c20008000d254000004001803080c08100040300c0403228010b000d40c0b02102c9004c080391200003052055101401000c60002142c00c40c03454031031100e007604c43c82c001e44850102100f14020a0b5610a01148403103140c01c0c928800009400d215840036400301c142d041552400c8500c0c3ca6900344902c04850498804c0c2c2c3c10b00040c000c01c60b06101040d0028000d040102c0200c1c00c0c402804090303086445400c0c1081400303d205c0c42121000801c02c1e2901c1c0c406016958141841d050a401501e000d0043d0401281899201254500000b0b015102140c0542c051815a00c2d0051460b8140c1e00141000d011840b90341c6011501e59511800140248140c1d02d41c255a11346079600607003035485580c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 2611743 1250 2610493 2610497
    0x40e0601180902030a020f01020a020306040503090307090608030a030c0912060b04140f07140409020414010908030309030d050402060904060602030705070509060f1002010f02030a0c0801090b010c020d0501020903031303020f01 99
    0x3001902c0140c90014034a81107590454120706a100200c0040303103004465400a54940304282c14041440004802041000c40907800c0d915050744420703601e000e858503403284003600e500800510701c60320f1007030b402411030810314506540f41c2c65440344111b2000014810980f15599291240005490203110b618000351502c0c44044c110728150702c1411441ca00117080005000130901d07951403044000084a004c0e00002404545131030302d404407080395040e000e0007180801d00c02c203c0403e041c040041601e20030120f840003580380009204140010b840040c00480c1c00190501c0076560039030795800354201600e4542e000356120140d605210345041c40b590300c0039024040440900a031500d6408461007228130a42c0c08035101c0380e440300c0c124010800595440e031958800b10178000f030b810030380d0421640c9500d10ba07101604c0381d8807450400100d50351411400e02180038000e2000060400c0748a007602103015000041c140101400824195488440c15043e03c0c0e41d850010700c11072406d10780c000501e080038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 2612993 1250 2611743 2611751
    0x90605030706050a030e0601030308040b0f010f050f06040b0d02310501080702030706110301050301060803040803030403030c050f03010311040f020c06041416090207030305010806070e01030b0a05040e060118 91
    0x1210209840e400240109000c000c00000c804028a029820200265104500b240d00035030b076a08000b440715006440407168401590b0105910701c041407100c40c145d44015043d00308440c13030300d401c118041190517074080d00400c0520001400f41c5110000d0300c1d80c0e12080c800580d65016604484941c409885402c400201e100000c8102c0000313001c2c0700005030388081c01e110702a92121442640b0314010740000810280c2824548422240300f00b001d1412a50164020f10410791941d010585031700550140054503030007400040d020901c81d401284030ba03007060601728507260181440741c0c1030354000d0b0400d07990308180303501d01c4c0d4040c105845551032402c107001c000c40c288202448050b8640d030b0007400c003408000b050b800d2008200c0007441042007020452070a06034950f81c801d0140040e402000b026004a450403000140f40a800300d80b991003280e080d0344848600039a10010760042a1181c0c0c001e41091740c1803408100c54030b4070312510b440081e1880040000d0342c5010601101c40c900c86d13005421050030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 2614243 1250 2612993 2612999
    0xa02010b150702040906020403020d0501090b060102010917030402010c0b0f0108120403020618030102090402040303030b03010b011103031b04090908131a0409050402030a052a010807050a0806030a0210020f01060906 94
    0x5880540342c01030f504070b40100340110316051050107400350b50800f96120700d404110000b04501580801f00851041100c8503407646c030303034006900b25035410344003414050300c50b118485610355445c01194400d1050420702c0c10792220752a4130281c81002c8440d484086260001070001410070050320400d8041c1308101e5240500310340c003003449401008034604c0e00e000c175410300020b9550207405072952404050811515595603040080203055189000b501a5191600c3c003c881c3d4070a080b50410406c41d040114950b494901c0001e80b03408104040307460900d024040441c80c06014060304036542e00607110191106022082c12040441c03030717400b1840b034544041c0c01c41e001c0c18050701681c0480e040010001019903850010a08205092034000c1440c0903401151400e1800652520aa10110b407410340304078035003100544075081e080c0d40350004148280002e1007a144900c46046d0f0005018080d80d014014036400701c0c000400fa05400005030b0008401c00210010034480d10006154064080c40704a00d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 2615493 1250 2614243 2614279
    0x901020415080601031d0c010305060604050603010b07050304050a03030f0f0201050603070902180303340f0204090303090b010308041401030203190203040314041401030606080402030c010f020a0203010509030a02010b 95
    0x81d0903a0000c0601ca10000000c0c11a80a640500c18070004100d2819009460700249030701c403480030128034003080c900342c0462020300f40300050390300303469018004d01d10316400d090030540c0c0c2d40c101c21402c603400d1204100200380e0ba240c5c00ca4000003076120351182103600d00e4468004d40701031040030b050011a80f400d070820034035540014501c421100c0e01007005986070b0300070b005994600b840a0341c05415100c001010070f900010318140305030051182c080c00e440380b07008520001c0c203c0504240604141013425986003d86170550221401130b00c207007400600440c03d55580c4030211026030040d1511400400c0400481c00f000c156100b4100302442c0862a51521081c060040e4075280107030a030071540480001e0800d405a09510003020b4085c28aa8540d640e41c0300da008048040345445002904041d00094a14050924035005940c0100a059500c0d52900111011070110084030304522500c4156005a2004c0c41007602440042e03001c1c6585184441001e401d4070259000c450140107043d4120395144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 2616743 1250 2615493 2615519
    0x403090509070201090501020408030c070b0c0a150b040c0f0e04060303081605040e0a0204050301061202220f0903050405030105010501020c0607030e04020904020c03030402090c03060604090b03010e030c060f09010204 95
    0x40e811104508140c80c1d0301400c9005051402c0021b125610014012402040000213092859005001c03035403000e46401600f2014058031801d000154004056140066062508020009200500010004007020025055850300701d1a03a002c6041c401d44101100e91014040100907810b540070b00c82546180c0e00103100500042a81c1c2ca5016240707400414603201d0800c8900500c039000f011604c5c0c0c00c05819440c002c0d0312510506110703603c2e0001c00103107034400069450025030000d24034041c590304040310a500c0c00080c00025103150340c2c0c0c0e002503c0700c0810707c1080b09280c029510103840310304010a050031900103800141c1036601c04046c3c80b66683e00c48040300c88a03503240c0707020f011603d484000314002e40161000c2581c0035001290030f500310b25001024511440c0200d6401406450f42a441c003124802034901c1c035041070301004180452007841d04035200310500607000055240126003c00d0954128482c00406500090144210305003400c40c0203400400e2540218600b07031500c05001c8442d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 2617993 1250 2616743 2616749
    0x30406020a03050d0219050c1507050403081c020a03090b090105040506040305070f0203070e070e010801030302071e03060f020301030302100209010206010e060d05010507030c1215060309140102040311040c030203040309 96
    0xf0020b282000c0700c0c05a0140ca02240944240e610b004c1c6411070058441c1d0001e4400301568071a94584c03a40c00c010414009002d5a841d803a41c07440c281c00d503100d000305580007034130300000600c010380c03465200c10b1030b40f0062405404036a80019080b04e140390001c0990006040300348540e05041c10b10010031404500c4641280c0c7c10305005603119103600c1c0c540c03003c1044100c0603501d40034503100026644210003401d8070804003a0b9070603a946480400546048800303010180c01039100701001c2c0300701c945803030030b1900d008416a080c2c4812a1782e41da07900107403200c0341c18082070550084010410140c0400c0b40030080c0725040c60541c00c00180c640000e54550052103070f04951101a00866401c0e00c828841c110304030341040c000d02007131501c0040a009801a01c2d41070000603185164140075030802d100d00e00c0241240ca852449441c90031070201c3c064808410140d038000d165150000c6005400d100501c0250722a80148444040f54010041219461301c110020300d0b0040003000002035201e05800c1c02d07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 2619243 1250 2617993 2617997
    0xe010302060a0e03070f081e1603021201020c0f0a030207080601030f02040903050903030307030c1d030a080c030412030201050a1103060d060c14041d0108010606140306031c0302030402040e030406020a03 89
    0x501016003001030319049840e4012202d4425003100400c100c000482d40000510366100c1030303640c4040c048c2e801c980e1140000b800c0c440c64038403594107000503c0c1c50b410705100d00d0b2041e0005402c000c0604584d500300130302e895503803410740c0c8180f15003010941c052005000a00201c0b01412040d8915103135140916020305c8000c0c4141d41c2d80314024105400b0703000707a542c1203001400300c0742c6071700c0d03d450040d004100d482007441c04550031048400c403410200c013403229603c4014019200d10650f982e00d03c7c401d40c205010200c100c1c04140310109100301c0c12030a480d1024042d60001c00d4a062060b01d51045039070341c100700100c02030101300f0001261242d100d031401c25980000000303888429000d08449844c0d031000007a102c5c2d600080d001071006008841c50309040b2184580c08496640c0b1018142261024803580002c590300c011030721a82042d00000d540c1c0070202806481000b000640c44414001c21811600080303a400700501c02541864420400c0f800320341402180390604011000c4e40d0b84c034651200030700b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 2620493 1250 2619243 2619257
    0x6021501090207050312010902070c050f0d030309020307030b040804090509030301050f0105071104050108030c060c03060102150705070602040b0d230a020703030f1a0112140c07050a0b01080607090e010302060a 92
    0xf04001081044034001c00d410842c41802e540c4941c7c0c24006548001001e56000c6114640400c6a02d0f01407454447d40342e005044030746c1e59010f950250023418071310b0b10999043c05400d20010105024011271841a03115400881e40c442c1010010303400c941d0003402d0010154000d20040c0040e40307880407040482d13175003402c090b911441c451405040c20040d401156800505140000465200007c058108616503105541650382c0b107044130f110a00003280c426005034025100d070b00c5c1090308a07101603000000e602d0033b5803404420307841d42c0042c2e900a50180b24001c00004940752410f20f603202d02101408494a012403c00c03041211340345840c0050645035006034009003003410140240e00c080d4118014103003d01104484094100402c40e0010701240403e06110030940303100c800e4411006020880201502507403211125000c00340c01070b200c02c0341c6030310036050340601044504201c50f00a00d48600101812314120301c000b80011007a610410b0020004001440103944020a9a620103101d1611070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 2621743 1250 2620493 2620507
    0x506030c13030c1a03040c0302090c0d0c05040608160801090213030c0803090a06050f04060503061c050a03020c10080606030402040207120905042327010c02070e01060215010902 78
    0x40003403042400302a9036807401040002080b14400c1144225030b022810101058a1030403418070b18441124020460609000140018500b201d9040d800c140c4808049003000c082d11041ea003140c085542c07101c04141c0104041051903408071040d035010b04c920490020781d206242000c0c11840060040c4a8125008514072001d0b050103c0043c3c0103641107048c0c4031120b580e03965001e07101c2d0b10243d480750003250b40c00c9020a09a015004540d151819034000d2894946401000c5483d034001500c0c080e404010301100c2c0b1410400c1c003c161034201d004101030001d201c0c5d60326001e45056904014940254002d9080845140d0040d005035400785040e80c05594940d0b8910004009105d411001400c555403280f0b850125507002c000001944c005071810040c4143c0c3e100003114480c620071414100010030000200d400130307103801400c5801c501504590290799105001c03401c0d50341c58100940180e2000404018000140036441e00400003800a0700500c09178070440c02d07007800e050090f8400250002541c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 2622993 1250 2621743 2621761
    0x402070b06280b07060b0d030f030b0d060204080d08061507020405040503090d0803100504090206040303050a0c020301020d02070302150609040f0305070b010e150907020d1202070203010207030809070609060504050603 95
    0x81c42c0c00071001d01d031105075075490340602c1d0100c1c0c00040094071554517000c620f07000d6051800307000b103c40d90140c4500042040010080340134004070703400d543c2c100d0640640d50700020640d0001d07201400c80382002e0481040c044c14014a06030008151038030803103018041102003031001c1d04407140a5016680070a860b0344504006180d4406ca80400703400074010100c00051042c04805140504070070a070540da184d580d5000c02064801c449000b0390b103c4030410080001030302400042c0349031482414400c09207200740d0000780c220b80000c40480b04450300020800708055042c400201810b20040d122691424100080b59220700003c0005088465036000e4009143c003c0b42a502d92560046480d4420340e182c03490001e500d042518102c0100c10700036100d00c4249020031000340710b2070041d0700511904560390745c122590805a010350100300e03404c20207180507880c20300080404500075250280b40d0b0030550422442c1c8005a03103d00c0400519482c288400d0380d00c0303022203045800c22141c00792030341c4428180d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 2624243 1250 2622993 2623039
    0xb0102030c0f06040201021e0304060e03010b030d020106050f010c08070803071403090705011101051b030615030103050102120115050904050604060909030804020301150506040504090305070c03030503040506060402070b06 97
    0x41d490880c898524614229240001c1c62881140300b0307401d0342d0f001c90300c80c01034003d00208d0540d240001d40090000f8001c00348100c002c07542c0103000400104001d0740d1a40400c2c1070070144000e40c40140d4442c0028043c030b00348180300d090040028a8505140c0115860381a8030b4040d5650051950000202041340d0030301c90030b1079000b00044821030740c0c0e032400c014181c1b65864419100782d80c04200b00c200c0d40c9111101c1031180301e1050341100710b01280c8407074090102030280c5c0000c09003030b80171a9403e00001d1303034a411000345020314400c030700060340c83d1011401a1039000d0142c2c07091140d060145090214181d000c016240c800005460215132600d4410015001d000c1940260582c40d04e4003019200b0f0680c03100c1101d025034000e0b0000c10003603808145881b14031302e49014154000704100020441c80c201940007420310b6000c0c1c60414180521661990410030096200780c000482c04014001449400d220030f44c1c02c020211000c615101040c4c0d41c0350401c00006024034450041400409100c20803082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 2625493 1250 2624243 2624257
    0x5040501090803100812181002030f070501020306031b0307061d0402031303030506040203060109060806150a0c03020d030204031505040f02030706020f06090106050d0f080f030a0c030507020d050301090b010203 92
    0x81c0e03050b1a032a0049240031a4030781c41c8190f805d1031081c500e525030880ea988007180c4141000c49034008082e40880248200300030060324540c11480100481e0070090141000780401510030000940d49023000010035207003115041c950247d0007600c024142907070740c0c001038031000c0307848500b071039495880d01c10480e62003110140307001070300a0f00000800448100c00027000d120305110b40c504111fa83c40e420b09000482c0000c40d1020b0118944034030501c139031800f98a1072640500c00800c00910100c0e541c443c1c010507000021960040740042004404140d014800b10343e10400c0c2d0703d021800c103072a50b2140d41c0c08100c041d003410070041c0d88001140c24001c1c000c3c00095081c0e0080c0858024507a00c1c00029980c0a01c401e0080c2907004440104400701818050201210402000c2d800d0a0707405403140280303840c003001c04407059901044280500040e020203148148142c0070f0000f0305d03900d400c101500341d8400400020854008620310002b954101081d21b0650308074010000c0c11f0384034440141d146100c0e1070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 2626743 1250 2625493 2625503
    0xc0a080a020705010c0c0204150302030d050d020c1006030b070302071110021606080709050a180519110403020405010b03090d0e0109090203100504060506030118230a0905010b01020d050403060504050109 89
    0x520700200f681d1b000034521805500c00e0324100700d8883c03027061000d004489800001d500d80c015422072110385210302c5c050030b00d01024080c01440e105c10a90380d98680311a1182110b0540c2c0c44100c1041440f00e0710210b0360344600076042c00d40c60205541d641101c00003000042e140700d840752800e40c4002a10170024801c0152030327060381d241002e0700c84c032001d080b1801c00c0303900c1e2000483d070440203e0642804042141151010b101c0054240783c4416130314090440203220200c0950140d000301c8220030507001e000078040d120001507549a00b94018402540d83c160444025403004009000072040c2c002454140301c0d50a1030030344001c41400004841250095005c000182d0000c014071001c1601c039a6a0421908119010000150b80c1d60a020080c0024032071041c0da0f116130b081a9070480c8164001c03058400d801e250365001d824180482d01481f020a03102c10079801e40d5a1008002c00c0340134401c1c0020b09a090005040e22802c2100c014041e1180b4040206502e44440114080001c02d42211910681c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 2627993 1250 2626743 2626751
    0x20703030c1e0302010506030c040c0905060a1701090204180501030209070f050c0f01021305010c020102150402030703060c1e030b0d031101060503030c0a030219020105030a1802100201020c010b03060c0a080a02070501 95
    0xc3c10000e01038042038130b4007071090049a03044051071800b4400c2012192182d00c1d5402d2141c0340104100c0c613900046045401c0c0300107030200c0012503240b041000e01030141c01500680752400d1240d91320341c1d09400300a00d54058980001400903940f807181d840d41c44a60381c50b0800303841ca5046003c0350f8500818010070464030859500300003040042d00904081c1c0461000c00300556610b1004594071114150060b0141e00303d0703007000c080e65408000c0310b98400c1c0060b003101d400c1543d07951034108580c1c00c00d200030300181c0d8844086030440070068080c0a04006031034280111501074000803541401c0d0345008062081c0c2d03586082c17801100b03400400081200800741c98440b50950551070700c800144100310014003800d034848680344004030713440310101d4042c1c0d5120709603134403e040000203099048032581c544013503944010041e5101c200e0580926003a0780090386414841001078251015000090b03c250000c0081109244980d03043d50035442c035504d01300166480e641130721070080c424002c01501a50030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 2629243 1250 2627993 2628053
    0x140307020a0512130501050705010908030a0506040b0d11040b190303020303010e010f060c020607020609100504090b030601031106032503090c0603051b18130b01020c03030703020703030c 82
    0x1088a1907028000c106840880f0058034000d03105215003420030ba0200c0b001d48040c8040c0d40f0590103040c429100704000142404551034160705604104e440303800f015120000c0082d41d042600a0960001c82a2441c241100d81503841c2400c4860300500680500c1c3d6404050010b0355410307101507594402250494891500c03400c00030340b00d0f4424052440c4000301070000280c410803030111b19003100c24a603554900e894280d800c00c8155441004141d0f400881072201199541e01e036440200d0001e01c980301c16564500c0d042c41203054510f40c4404600c0f80e00311f0b0b0010404280b034420b400c05903910072142581e4035920480316581e61074903005134420087e001301324880c0380d540580c0844200d0b40110303030b2094115595981202610401c40d032084011303400c8140d00d0080d0321500701821742c0f11550f04040c0300f41c80312600800c489900e110802c0c840181c0b40c3c00000483d58041c00060783d80d080960281d46405000d4401030b41c2c9041c90300c8010104030b503600200040c0515040e22284421102e0140e10103010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 2630493 1250 2629243 2629247
    0x90a05010303030c0801030c05060304030306030501021215010f0509040905070b0403081222020d050102090301020a02030403060608010c050711030109080a03050402090f01150302090402040801060605070501060e06091501140307 100
    0x74001100802e2600c1c1810003114011980c081c1201e80c464031500d0146d06007801c0c0040d80d04090701c11070525444040c08400640e0a00151010300e26081c40d811484c81c0040d070948541029044490500510200d0b000c04039034807008030341034071006940226000045240c828078250307050380b0400081740c0218021041104050051020741d6080510704c0b104d844640088904207502802c0b5103840c09820359450050a07c0c2d040103c90901860005041811150105c0d080e80d000c8401c20006030000a0144108502d9200f80740103000008000c00078100182406091489402005040c90100d9444031203280d409421542109900c81c20003078450346e141c04084c02400e02541c6c100e00c260000b0b07000480203080400e00728102d41f45000034408400030400150025403104a10030f800c180c0800c03010070300610901075200200f5035170341c605030b60f02402d0425030300312182c50704000c07210020350083c04825902c41c001c480d00300f0038440500e0b8030000500c0050742e14030240307210a56a00404000c01020356 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 2631743 1250 2630493 2630501
    0x5010f1209080c0d0c060f0501050904020108190e0703020102060108030901050406050d1b0507140105040206030a02070c030c0303020f060703020702030304050609130e01020d06080102070203070e090f0106080309041b02070504020f09090a 104
    0x30302c500c07407d00406202000c0c0c0002d4039002d000d49508140018006009584505026a0003106007442e08255401c10b9103080301342c4400b0f032010741055000800400c00c43d43c0c1084124010111240a1070030301c140e00b000245180b16030700c1140104540810501c0d84988164400b0101c5181e4061080541000d0400680540c10842043d103858030901c11286c455107041c0100c42c070880d0b0050010746199585004000290807400b010b03a464040b0741400b200181284903587c01450081c1c004012281c6d1789002c031441c00c003004040e00d04050041c001000161000407e45065500071910991640d2250b80458013110301c64161096803400c0010181e5038841c1075004089ca221590000d025403501c80010764282e10035000001d40607401070034204038000200780c0312904502c0001c15920500d205451042c08d40b080b40d044a14150030001c0d0b500284e16091007880071100e000003000c13546503a250801780d15070540d88030329400f035500011441000b50551044071039620004142408901306606d15000070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 2632993 1250 2631743 2631767
    0x3090f06090c100f080106030e03040e010e0402040b1002030d0207080c030d0b030c0303070c030803040809090703020405040b0a030210030b010e030d05040305010b0405060a0603020a03020904060305010b010905010f1209080c0d 99
    0x103c0858082901c1d03240714491040c41521591102401a480e001c0c00714000e084c0700d0701d0b0240e10b000c1030001080c203c9030003000718001c281303e0f07040c00000d003024010003046913440c3e204980f065402026808160350048160f07819041d04000c016254050350519803031074803070804d1300b1480340000120503200108903402000c0580c41602280d00200c80081455a24803500740b001d000b200740300a04000050070710303000391740c400d02c00c0010368101001100415110b81d0180e891001180d00842e040c0142d080510427000d4040c0c0444802002c0742c51034011030382c0a10801900401c05071203841c0481c241e4020720700600703151005401c448c86c80c454584002c11b02c0d0020b00084a065090503507004c100d00d0140686405158004c0c05040210701d421420f170000c2d400f801a401c10302da000e0010010581d1140301c1c00f0011030282e00040351a4250740d00040100046810950501100710408000c0c40e038010301006181c00d0807a40004c5070040c50070030240c5401041080c00e05803040840da00c00007580f0613990012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 2634243 1250 2632993 2632999
    0x6080304080d0c060b09130605070e03100b0406050d23010507140c070512030706150311060c010b0402070605010510020609030901030b06040305030406020102040609060e030a060504030309050111030106020f060f01030803090f06090c 102
    0x103441b100e030704454000603014100d500d8dd0240d05800c015008661100400510050000030704c02c0d03403003012401d400c1c0141401e071403515035078000c1d10b02c0380000010404d400700701000812841c90a10005400c0394050f902130850340f040403174140c140c000d04100901c060800182a5400103c400281a40d83c1d80144404c8600c41d0903e1003190158481c1c489500030349500441e4800c100c04000c081c40303103503001504030103000d648500100070b01da2198801807200c6405000c1c08160b0b50705180c280f000481c0070744060000c640c4103208008503500c3c00b1080e5440c1d1402464045285070380f90001880034091600080c046010001d80000e1282c1c05600a01c01c5038460340b540c0741d100e03aa8400c00e0320007820310707004103803d90010401b90740040c0d0594071041c0d00a02c603050015030302d021a101c090842d00600b40038801c0260010040c018250104038030101c0071002402010076140c085a100c2e048801884005d04840c0d01001040038000305101969075100f0841c100c0328540360011280380d68507030401034540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 2635493 1250 2634243 2634251
    0x70f051b0102011109090c13090917070309140d0b0a0605010908030a020706080c070501090f0506060a030203100506040908070308011409010305031903060803040803040906080304080d0c060b091306 87
    0x240d401802980c400c00c0d0304103413040c00e100000082c81140d020003807130300300380701000c11a110200408059540103442200030006070140309103441c2c26601c07454820201c900300c040c00040d00091303101038100d045d14158030201404d5074100002c40c0c0c440500d58230040c440003000c0b0421046203035590080c0308481090b0f0f01c0a048c180d9400c0d91640f00c1c86400101001038020034000d00c006802801019080204004010701d02400798540780d0865100160450703c070300e0306034488010310508008c00360b0044002c450380d0180c5895030f4000f907078403101804104151621080021040e50301c6034081c00b50700d50086501c941e0f440b62858000c00b031280c00d000d07001384c281d4600d03594030b0281010740841d4180c0740d0060080d0315103002480c1c041c1071a044100d1660415031282804038014000344094002484008015503c5034208032000c07080c0c2c1c141d60004072407540700307003c1000400e0f070004100700c4100b03607400e003d9680706081c20b20380003410305500d83c150003812100c14440d11030070000b000e0f0200d90150b04200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 2636743 1250 2635493 2635543
    0x8030603071403060c03040f0804060f0905060a020a060902060f031006020708030310090504050f030d0b030c060a0507020d0303060b0403030905030c010804020108150d050d050a090801090f0f08070f05 88
    0x206803684810b071415090782c0400b0025900400c80d0008540080c040d101d060754095165840401980c8107030481c5000450351201908050f800485020103014111131a03801d141080c103000b9507c40c80d070040a0192a1202034020541d1269400c0700c00324160003041503901d2a102150003620304a174840d0070018803d00d18009000c00b00401503a00401402c0c181c01c2c0c6031468600148082c0101810541e01402581d920f00340c0f41d1400c00003084205003141d4041100040001058142074200400318040c403c00c218890131594014200c0da41254101c1e02d1101c002c0843c14210001d049541090b0700503980010003000b85a08080c000007224011070490312048280001103e850312709440c003c0c045040c04002c07668400d40c56079884c12200c809806400540c0b441c0d1980b40c076146a03503900300082100001c6403079606504c164100003402d2100004d2100721100d070b94404403441d614002401d1508c481c590a000c1122400880ea50a50031803518500002d00c4d0800c9a12518402c0d010964040e1000c1c1c0e807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 2637993 1250 2636743 2636759
    0x2091203070b010308030604380105040302030a1209030501020406080a0c030e06010510020c09101403060405060f0703060503010f060501030b030f0712140d02060906070905060a0c05030d090803060307 88
    0x303540d0154009042c0d44a80d107550303a03496a5820142c04598007070b4075131003e403209019450545440b5440c0c803c070149000c140324201020415640d0307500d07041103002c00091015840004007040202d074801036101c180f40740e81c0c004942c4180d403500300a00742e500003d80000c14030b5000792820f006142c0c407002040300c056a10f0b820713030865000440a09494005400422180c60607000e03d4456202c1d50055500c242d038030702c0010700100811078124141c2070510405109008504541c501f01d16410b40040803942015114203540b008000c042445202c152000640582c1c07003500b00074000e087c0038000380021138400540d1406450f9034000d05000918005540a05141c000307542c540888460018100c0c403400c03c100d4040c105001c9a0030f4031100c060306046000d01008000c080c0800c111035003d8031041c1802414541003110107403800040003040c88080c0699a1010b045900e00e140c5030030051566499460440c4c198061600703000c420340d203800c2032481405440e80085126a10840070f40707400369128108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 2639243 1250 2637993 2637997
    0x703050a0614060d0303090201030b1302070506010e220c090606030209030c03011803080c0f0a0203070308090109030905060309070e0c041d040b0601050d020409020d020705060f0106052d070602091203 88
    0x100c50b52108a48050201203802076000303d060a0062400bc101460b045000c100e08881911401104907800500b0340c040c000c0a000540c09415a40e00603507940c1400c4101c009944204002811580021034100080110251040004080c80007080c41300316920b8401500075001422018024003800512101e60318042c0314040310f031502506042c3d00b0781c0041c1c80448a030000140341d4400403e0401103000c00c032102c407000d450134034115801595514a2490010103408014110201c160304186030540040c0c1c00c510700e8000d40d0000d0b55180c3c0c0f265108441a40303004103a607c50345040c0d0900040c84182c40303d440084c415115940303201c0c8100c0320f03500c1130a00700100c11140a8a100744680c0443d90561040c00140181c0e0071003103015041503107404810041782c2c8201e0144400701c0c1d0015201007001018032059602c914005100f1510390315010001e0514400d44020000001c072011012000c50041e00e01240b13400195045251120303541d1401d80c0080d4484c803005072068200f0300710307483d07c0400002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 2640493 1250 2639243 2639251
    0x30a0c080103032c06070602030601020d0905090a0c051207020c01230409090302070e010806010603050a020304020312090406080601120605010f0f0312050904140402040501060f080606030402120703050a0614 91
    0x250740f50007038440c8404e8101e45a0742c01014010401400350142603030f9601d60141c40ba040c0203400050384c070b00701900003901d8240d00c1c003204818080302d981d003041035a076148109540051010b0020400a0411100702d80500c1400c00200f044040c0301c0c20312143e80d80c00111700080600070f0300d800200030204000345084480c03540000c09041c40420080c0041300450308072074055482401150301d6151606007550820300300340c2040106030300170b100400145505028060f0400c880c50400c41c614203154012a445240002c071280b031501002505a56603283c680c0488001c241c3e5500f41c41007542c4400f1507540d400138500e01640d446003400c0000c1940b408030f00020088031901e0840720441ea1640da5014080500154110113000041c095003003940c980e80544550000c0030140305020345881d10400c000c568040e0401400c0020a074140314410b40c001180981000003168101d840341e8603840010300c1014142001d5103a406124000002c100c80025007000c00c602c68142800056003000a0070300110b0111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 2641743 1250 2640493 2640497
    0x905010b0906041a090303040602011b03020403020102060601080403090504090501050a0b01020303070c0f0201140a0c0311010c02070512010b040207080c0706030b010503040204050403020f011506030605090402010903141f02030a0c08010303 105
    0x2013142c49652501005101001444542441c86070300000c0d085800c55406000940d4484800318009801b44464504d10046401c0c110700701801c40c6c0000b55102002881c090600941002080903d4040c016a900800c00141300b0711407840d0a1030401d018050541d800c0d100b01e810000c89040940c00401664400c1a00d0f54820b15004050703203031040e0440304070809905008401c1481e4148a0b10b440c0100804030b4140c6900002d803440b40303401489000c101e000b010b4503901d810504c01d43c1c0c582c0461a5001c42d042140c543c0b42d010100302e0b0b9180180b000e020b00790352140c1b0018114040100c0c04029103141d189107015510003a6841000b50305540d091000c0c0d42c001101040090300526081e4040b40c0c2050080c41100c29036a610042c450855091441221090080c40070810919034107004640c09801d00303070750845190406500203040c200c840d010061540c03d845608070240d40f01001103107c95000740c248003001800325982c0340000c0d40309807103209030141400c2d101e0b10114014080e85040705e90503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 2642993 1250 2641743 2641747
    0x6010b09030a0308130210030605030c090c030106031d0304031b09060308090409030c0f050c1e030705010309020310020f09040e010b030c0103020a0311070b01171605060306010306051305010905010b0906 89
    0xa580413a0010402001a0150a00c1250400c05a16000908100c021291314002200343c00c01c02018608064126070a1080e80c4640400c2a555052415281103071401d080111300f00d001d00081106a03100b09441c210103220120740002844104207501c50501d2440070440150794540125009039141800045c155603004c00400f0464141a840300303c1c41802441d007202440d0a99940e5884040c02d80c0c01510541d0181c41005480d1900c1d0702d03000a0856040602c400c2010303c580031a0700d41c0c50502c21181030590320900d80c000e5490500068850000c14901150380e9a9541c4405a0301e4024400590049140000039100d1768414400c40e0f00c00d4038010010007443c402c441c0114007a40c00a0050020562075801c191840e9942c040079010b5203115403c0d591941d81000d1416400d0041c8040d1162660301c4002072a001c450214040415a4010f80740913960307aa42d2030050300549600c7c1d2000e074000000354038888a40d03016034080c5058400d150001d121590380e40703800c40a10b01070031020691142c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 2644243 1250 2642993 2643013
    0x206030c091f08070e12010203070201050106030e010903020a021002070e07020d02070509090a060f060b0703020a0209070201050106090b0705010605060c0d0306090209060f070f020301050c0c12030106090e0a0e01060605090306010b0903 103
    0x541085d16041c600140401200e01c140482a82a070f0402e0350850050f039113460061102d5134150040c0c5001141a1700204050b0a503030320003d558201c0f81601a002c0c82d984413504080034828402e550107031244c2c0030301640908010b50000d66562461030301c0700060040c80b6011469140c07045130240201650307030080170b0600e055110b0300c0c02408070814403100a03684030400240c2080031806842001e000b40c026003142d07010740c018025400801440001164034000040c0701c0542c0101100007a6001c1d03280c400c0c0c0300d8800c1d00d0164010240c0760403040c0e01030301c003040c40e8a000f000021390648070f0744c155406004140c0c1c2c410101c03069005006005078402801d005003401c4400040152900d1070203100744540c190420f80200c2d007124000d03074020b038a03102d001600644c155003c01000c0c50003294134940d14503661418074010700d40c4100b402681030000300c820200c0c80c00c0e846500300311104501000200045079446002900c2603102d111014003e00804000040149060040d946580c40250144caa100d071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 2645493 1250 2644243 2644247
    0x301060e010c0b01060207030b06090609070f020309030601030b01090f05010e01060c0303140f1b03010303020604020d02010c0c0f090b01090b09060a05040314060708090309130b0a030206030c091f0807 88
    0x181285480c10400c5a02c0000e010849103c9100d0080816402906009041d0704014401900060082d405a500b040610100c1c3d01d81e10030055114020f403808010750800e050089040d07200701c034541e507032600c00e03440080140808005120304850a1a004110603013040d00781b241074840c00d00c10b44010038410801000001c0c003030310319000c1c16403181c47e0010384000c80460590180700c054aaa0009601e03501c204002041c00c10380120240e031030450407908661450358000d64800c40180001e0040d04005000000c40e40111080810030764003842c0c2c4005242c8400b41880d85940398400c2c01c1c000c9041c284240790355409004a0015500742e1380c001c030f00c0c00c1400c2e000e1000a07030000442404000d404c00c8000040381601484206104000b00034060030b0421680041c00c0380d10141900780300350010410750b10f4585e80c240c4000820401070001103070707209204001411001c12680b0103904144000300704101040346e8001450740e81401c8134003140030a02441148400c112200d99040400d8041021480c018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 2646743 1250 2645493 2645507
    0x141303020a02121f060302040b030708060a09080c0a050a1118042a0b07030810061b02010905040f0603020301050705030f0403050306030102040906030602090f010e030a0303050a0906020412030806010305010308030106 95
    0x344604075150754107030700d04d2005011210b01c4035003509a44ca900074000c5241c540901420420114003e0440605158625840b441c02802c1403041135900c00411080120360b0047c4e0780700043c03030004c1e25100407290a006842e0050030108840149480c59141d0603883d10240c1286c20310b21030032146a056a0715500d0944e071480003641d0540e5610390444c0512015440910000070b02401034001e5115005454060101c103c0984010031441d250301050001e01c3d4005000b80d103a107043e01160500d80410f00060b500380781c050704919041030405091200102c41d030b03003009084a03c203078000c0001e55a054011246404141d50940e41411184045404244a0000796400c1900180018903080d92401303440100c507043c1e0700c125039454010170418000c1c50912200c0071281e40c04c0c00c1801e40400114000703912025103100041c18541d91b0f00102e944d41c1444d41c071002000b64000c804564441d103504070002d410350807507412000030320360400046280d440703409954120380c0d01205150540e400d00e40180c42c16 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 2647993 1250 2646743 2646769
    0x2040b03030909040c0e01080d0f05070606030204110408061003080a0f020106050603100905060f1003090302010603060501080c0a0819030c02010c0b070801060207050402070203060103080f070b040303141303020a02 94
    0x241c031003030280b0009030703032081c22031400746201e40d924900d0340349001d400c0b0b0950401680b15031501c0c0c005181071802c1c0c0381c00c1581c1d42c000c60001c4c07a00c0c0c0d544040500c3c041e0700418050b08080e400500d881044903140704018010300994406030100c4d40c0785d03a42e440c1160301b03403d258000100501424007a810b0524003404909082c0d6500e0f0002155498a0301e0200e90035070400c03606088400308001041100b00c500d4400c043d000041076903140049242000810590484102e81034101a560762401c810305100398401c0303014640c0170b401440031396540e40519a5400188900c0ca2040704202000260900005443c141b080402c00030328828003810384041c0e03246500014164140010400d003c0000380d10034071814403c21594940072211350624000a1401c00b80d500018001c2d031040081030b000d640c0c00544941140c2e400940a80d40788115160401103000780c4100401c80010300701404100b513056041501114541c41e003c4a551b038400c151000e01882c6094040c0260308000303462405814032003050510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 2649243 1250 2647993 2647999
    0x3020604030618080703020a11010e090403051c0513020312030103030909110706140f0702030403080414030f0d02030a02010b01030b0f0f12030403060e10020403030203040b0703090308030c03040b0108010c050702040b 95
    0xe83c3c000e6480364429a0310510703040f0016001410000b0800400c08201d04201c1000e1a0807101d400614020440768900500044c080c044041003502d0be000c0d481002d40e080c1d040840061059042464043e141c01c010384078100c3c0700b4040c3d076840c80c0c101d20741c2c00b050301d040b6605660b402015500d009a810f0040c0344c0e0316143c40d14a4401c2014002190141c050b044c902601c00060722020f20f004000342086440c01341c004c2c81150810801000490300c0041900d09a40303554210001c0b0f860171100003072a09400d210b0a940724050361061b29149034000c806084500c0907900203020707940e003545c0110111072001705440d900c0b0106c41005a6603041c140c1101c4401c24001c0c1c4018007080a020307846186400a03402100c00a40300c904102c40002c0a0100030040500354100b035080c982956000f03501e038015401020301524000c0350344424944030740916001540c000d950740350750b802d001210b90100d90044800380c411071140d0740005010101485900c1c03447c0115540c036030429025500b000050105516061340c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 2650493 1250 2649243 2649281
    0x102030409020a0c0f0f020a0506030105060a080a1506050301090e0703030f11010906020c030702010905061201030f03050403060f050609061203090f01200109030f02010203060d020105030415050903030a15030206040306 96
    0x4001085d144900c1c10a80c02040f008030364403941e01c104035001103180c100c1c5020f40300500040016803590401c3d81e070140c20310b08003010540d0782e10a428004225100340722003400b00c59000004c2840d044002181038603a0341c5024050040710003036140e0395031681e200081c001103012034680300c13251081040c100034903486400424003a2607600c42d0410381c0c2021a240510340c00001d00c0c0d404541e0040c02e004000c143c251000c5092a0510f081c4403c0880c0510002c5c01d1903044090702c0e410140300d2401c0b140595488201000400094031000c4010002224402d001c3c04424003c2071207450240c1360510711108001c0107618000101301400182001080043d040c0400c5410070054410000c114145000c10b62000061184c0b050400504185880d0007040c29640f0410074440151508042c501842c2e40a0904c00da4949603442d141c200d030910441c2e200700d164079040900c10505000300055001d07049100f024405503224802404401c1a00e1000952000c1c04000c10400074210b5000078000f9019a2500d403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 2651743 1250 2650493 2650517
    0xf080106080403110106060203040602070906050603040b060a12050102030103060c020309030d05090a03021201050411011403011a09040e0a020306010b0f030604090501110c0a0c0b040501020d031a10020c09010803090102030409020a 101
    0x85c01d4071403039000400941c20200d0b0030300585904002410040000e5441480000d1401c00850201d200250002d4600a204000107034181c40343e0386034000030300700148448801c000904215000390820700044450a0400022440052001064581d2100300a002c1c1c02d0100d2a40760a82d66544009001d84d00140c00c140c0003c0580d4071116a00d225002d508000706251801e0b21b00580c004421540042c1803015201c60000195003940c20307207040da124400d078180140700050303201a0b903014802e140c9902034141010007200031001f00d85c03030744400e1095044030a540d0720b40000001c507004042003254500c40c1400040c00e20310f03183d00306695880c003c0e000021111001183c80c905544082400b55903035118140d008200300a0000040082109010640c10715040200003519003840110300300400d81c48643e45131204100411600b101d40b4010514417000c400c96802a48400700f8210551041603010000901084003000b110800d2805a010f103181c2070400040300001d4229460385c1c420005148015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 2652993 1250 2651743 2651777
    0x9070b070b0405010f0e12030712060b0703090510051608040f0602150c04030f02010806010306050301021b06101208070c09020301090905011b020303010902090f03031206030d0f080106080403 84
    0x24140980039440704001d40c030b080e00300942524403101d891100d01d8a00f104210241001040001001c0303420b000c69503483c0c41e80203007214041402c04d900f9960520b08007001946800b03000080400d51b100741c94008040d9a0740c42004062000c4c40b00000101d4010054148028004550b6107103a500c900c0180e03040c191100c4202e41030042680050002d40c3c0091500700010b01130ae04003a9001204880441c40d1506595a0003221507402030004c0c140300100c00031540d281e010380c00c84805050054001c41d100c02184c0d04075408020124540a01270140b003010508248040e014081074500c4e00710703140e6400030182e07103031403ea030320031303c000d5440c44401400411020b080d40006d40c02004a41400720700740e00f8a04045007120321501d50301c0601340300c0012220a068000c015641115424000161154600000320341094030501d0403c0e40350000050f20300307030140100c0302140038800540032600c9858500348182c0d40381c1441c15000012581c400010001c50f07210314080f5503c83d119241400450b003520800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 2654243 1250 2652993 2652997
    0x7030309050d0804021806030a0303020c0c100305060406050105031303050705030d0e01050612060403020c01050318060103060504060b03030a0905040b0d02041d0607020304180b06090d032105010608070809070b 92
    0x204030700260400c02480154a0802d40c03e81810007030300c2e00c0c1b9045041c0800040d81d100e051410040c141a008100410710342c4050110f010500d0002c0d2441c2500044480c0c000c00510044400c14495440c000c4081045d520940036240f0030850300000401443c8a520155183d400c08003045850344400c015804295009000c0c016402180800218943c1001e1040002c0001d6407404291264001d50421002c6580099401c11000c020700301a40d0740c0d211004416a080529952610180f00d10b00002041260aa200c5d51049024100400200311504101074a0b0301c01c914443c00084c807410b4050109140c1a800b03000040c0c0002c1c02e042500f04654007080603a58400705120240c0201c00e02c292002006202d206c0d4004213510181d494641002201c005107044402041e5259650f483c1031121a00c07908100d1360800c800a0501e01050100e280080107001a80b81d4000314003105514010078102c00d008030303416141c0c1a20f0f6451140d840e03500c200d98140c00244103d42d2803044020001d495075035040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 2655493 1250 2654243 2654263
    0xc0b1201050301060501030b0102030d0507020f1b04050a0204050d030806060715050402010f09050d0314040806010b0408010e01090206040311040908030901020d0608060c070210020102040b0a170601020606150703030905 96
    0x118859203601d803004050840b10150b11141c103140c103180d41010f241e80d02000300c0301e00c058101c000042584840100f00c0c03409001c0220103040348038207103a204103210410a40700804804903002d00c000c0e510308440e0b00c00d17800b0310310540b41c0005039804402c0c0024001e103041c075444800948541d00308001500c41002d07900c0103585542006070b40e04140400c3d960300c00c0f02d404128802d8149007916510700004903204002d010701c098200f103802e400008000c4000c904980040c1240b500b142c1040d40c45050f0403210354010b10a55000d98a0411190b11031201801f41819264000f1b00c07076420140f0316140c48030742d21010400640c0c0700340e032004900c000928040182d4060681e6000050300c4035040040d08080716015040780d520740d80001e0401800050040c222511280e06564500c040c080140041e8060300a9400206060f440810100071469110100c0003821107a210948009c0d2121801a07880c3c240c1a036416810a00c0365001102003c200c00081460034801e00e00013802d1040740d110a030920480300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 2656743 1250 2655493 2655517
    0x9030c0d0e01030b0904050705060d1803090e01150206070509040207050105070801050a08010509070902090307030b0c0904060b03090a0210020c03010204090605040e060705070201080406110d050f090a080f03040c0b 94
    0x9107640d100c65a06118620101009540d083c2c0c607030802d5140c1d20782d1106548141d900c1001d00046070311440c51150005100650200c00002803400c00e46000f5002000f28092150402000030002440581c62940303c00d038403485401510080e141c0340404c03540b40d4032a403080b54015400308401d20021b030003485614455206592844480d5040070100700c50500a6400500706a050005010081e000850300504076070100000580d00c802c1540441d0801c1440e5101511001c0180204600c0c0f1000b14001d282e840400c85040084c2038441b000031280c0d02090b120030556a100da5403d0b001400c11107103200070800399004941c0555600b100003030a99101790455000642c035013904200900b850700800d0603055144c00a00202e02e0610401440340c083c0120290410150401103000d01000d6400340302142c8042907565a200c09040c40e0102518003030364071484500e0300c14001943e9201c04204514480d902840f910301c0c10301c082000004580000c0e0050341d4915404030005042d00c0300c0801000410301c4a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 2657993 1250 2656743 2656757
    0x50d05071802040e0c0a0309150b04050a0516080703110409090203010e03070f0308100b030103060509060105010908070b07060e01020301080708070504050c030105060a020a0501020d060e01050a0303050304030809030c0d 96
    0x12103201064a40100407540d00c260040c0001d018142c00001c58551141c0341c082c019403100d00c0088114050300440c40040c001e80c1c2081750501e804006c8d034200c109554020b50341445603480b02081c240490380100e40d50380d04484884210a809446003c81c0c641014652a020580c020010107110880d40715070711041000740d4403240c043c00c50600b8050954001c10b1a8040c0d070520026466084000600610041c01c00c0000301c0041c03503a5200007107040240c008910802d0305d0390303164a0b2500081c03000f62510755491040e030000003115885001ca180c25070320007501422005143c0310030000c02d50804e040803203986444010035800e0b0002480950300031700b132035001004010700c2c24480c207041828039000300c1c2c05103040404002e1440f0104044070704507001610b01541c0c0352a205412400c04c940c00358020709650000620302c610313004d40d070808400e40e01c81c0c85001402d6680c07002006002c007407910004022840910019020900542030560b0100d009029240340100394400c590030304e0740b00030101010072a5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 2659243 1250 2657993 2657999
    0xa060f02150705090d0311010504030c0312060302010f030e0705030105040807030f0203040506031602010906050109020d0e030405031009031103030106170601020604020d0b06010c0204020d060302032b030b010504050d0507 97
    0x81002880c414041c401903490351030501e410000d20078410000b08502902005600314109032080c100185028015002048941002c0c0f03001014508a11030950000342c50b481032020300c0006200f20012240c5c161540d40404d61403120940107014641180c00040c003030750100003031540382070007518400c92142d0343d41c55440c03445182c09044036050003c0a0119130050105200544510089903003003515901091550000b92004074090320043d00700520160500c0000900607200340c003d410321024000003401044040000300c0c0c0d1324000c0d441100ea05074811010312981d20700c142d1204541703c0c00b0717240400d0700c100444011403959200781c0c041e00005a400182904640340e4246054000c1000d10180c00241001e800192481c10100b00251094a941d40400c840380e010b1500200401e03030180055460310000c034a510020310180c40140e0080c0101c11242c8810a81000d0448000340044010320308141c611008070010060750701c10743c0c10b0240410012405554945860040b107106800034070105007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 2660493 1250 2659243 2659247
    0x2060c030306120303070906080c0c011404061b091202031203070509010801140904021207090e0a0209010504140f0406110d0207050d0503071202090609040905060108010501140a060c0201030b0a060f 87
    0x48064103070050b0801d2041c01ba5003a4030640e628111421881c00707240d61380300c5040c01000341c40380b600390f07807201c1d80391002240280e852501d17500c1c45079001d0342d0108068142c82c0b400300c00d002107080d51140081c050038010701c180144002a03c00c030074005800c84011100d00106210560300c240d540d20040b80000c60100860740c1d21081c0207016207140035000072444194804236483c1c14010340001e1060b4110880c1c141d11080c20448603008001103079003400071303402500040d0344a160607e010713070065400c031002140a003064042c00c10b05e0034140400c4841e40e41c0300504840c0c03402026004035803064944040440e04421440540380180840c0c1740180d03100010303d4005e1405011700d07201c5060040074002c1003e07103a0849141c2091003120030000d0398a410b100002611032007088001540700e4640104070090281c0025194141c07803c0c50000c110a980f01c0c87d1403c500344c910341e20316511450014042c0074462081c01c850f90300a106040c04518005031070f0014400841c01c0e04103100059001c0442520700d0703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 2661743 1250 2660493 2660509
    0xc0801140301150e0702010f150602060c0a02030304080f0403020303030a0f050711060a09060b090a020a090602030405061b0c0d20060702030705040b030a0503070503091e01090905070302040302060c030306 90
    0x103000710000c02c06022100946101d5560314410407000200701400504c00314001c0d0410390b030000c4410000c0282d8100d02c440b20440c250705008407030041c031941c1c002070900500d41d800c88001c111650025815a43c8030750314020142e10030300d2040c161903402e000c0000103840c00c10146000300010304001c41d180e021003540074102c89000b00a0010042ea0468019034030501081c565000203400134003081880c19810101c002d0000e4145072030700400c030729082010b61407a40e070280c062414103a448184130750303407a68101d990740241d000c2c2c1980843c00b0446040506542204070058100c5070040e5407042e4107038030008a00080303092007901d0440780b107111105081c0c402d040c03105254030100d03401c44c01d2030140e40100307988028034003403680940d0381c4926080c0c0c955020043e01c980c0b00d45c042d00700c07035031601c052400e961a5005840014096000c407401c1040f600309592103d80c10000683d03502081514107100d003c003900003e040081899401c00010001d40c07201d0340100420031001006513a82c0c100602803191076 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 2662993 1250 2661743 2661779
    0x60603060501170f01030b090109150e010b01020601030302100c0e0402031603110a12020307050405031b091510080a1e0203041101080402030307030e0114120f0105010203030106090e04050a060c0801 87
    0x740c3c0d50300b04000c0200d0180c3c80840c1926048860b00199541d4544003a0040c03c10285c0a01030203441d0021113556800f5420007201101c0e548001c1c0042c540500043e40d03030300c20a010040150300821526422001380742d00034103a0841d240703010b50088a4140204040f41e00a56a98003030f550b81b0058180460381601520820180b140707907603032030051001c1c80107140a030386074050303120503800102081e1441e1180090302c02921008065400d220003082d102d400d25500342842c503000d40c110000280402102d96080c10b04a8009409555800314100040b1030b01d8900a1040a207540d42e0070070a2003e5542c0104800f01c0b4401c644016500d0070071f07042030000205100c40040c10484258204001a14080291540b140d8142031500d0410103071401a26980e02c6403151010303034000072401400c3c0c140812502d0f4024400b00044c0c0c803a99894000480c0c881c442400b5280200e00808401c201084042100951007070252003039070303205605c540c0d40b403043e0380b000260280010035940051010801c417840d01100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 2664243 1250 2662993 2663027
    0x706060b070b09030306010c030302070203070b0f0403050105010503010603030804080c1c050a120207050a0209190504080301090c0c0b0105010e0303070602030c03010e01121101030218030706080a0b0a0f03080f0d060603060501 99
    0x441c1b8000c400207010b0300500d00c2c01001c05801003008001c41d00e080100070041c101900d20152508055011302c4003a41141c40240c60355800c3c0400003506007010f01c11541034a17059910301c08a6910360301c4581d100e610100902d0304902c00d030840603c2c0b0100e02480810514415900d503551540141030040850710340c8107800c10214810171000c00001e80020f41020b8003681551007071115a81d80f030340d601400040340f010314a26070030041080b040042140045068807815001048800c60080c000c0b55032445031000203280445660043c000c56029444002d5200401000c5903e4120340c2ea50340c000346c1c0c0007622035510360040400140480c00c0884081400750040100a2403015115110000b11044c00f0219505041e80021038603900d807041303281c02104c19001340c11100d02a680700d20051034250200c410b0130101d0b2a003a0b200700300d4508800c2800c00c540c42c2c8400c0061550860311920195448501c40a00c020001c200445600960340503000042460381c4002030554039000014180d038800900d4885 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 2665493 1250 2664243 2664247
    0x6151106010807050d0309090207030203070b010e0f0402040203100504021303060608060903030403030203060103060b0705060103060501050f06090603090f15060108010e0702150402060c01020403060203100e010302130209060706060b070b0903 106
    0x400b00b400030300f1900311441100c00c0c0c9031840d000d04082e00d000b12650040c10b80180005520014140c0000c01003440c14844e040002c026070741d07040783c8016241d0036507000811908810104001d0301c0c2640241d900100c014080d44032460b503d20005080380d208030320112040c40400d0003001403100764403071000200080d00144c49a8604144159100e20000300001c003032603404070200b41503910070780c080c0015080030049140e880c3d11504101e56140c0c0300344412034045050100124507401c00031211600502e0107060281042c0f0503008001668000030310550107449010700660800c0b8041190344010040740c1010080d909288000520b0140140c211441d000145001d00091950000e030040d040503d95584461503202c501c00101c4502ca070041e400c1c295070000c540807043c4441c41c4d000314090303408064103000b5190380d51900f02c582c1e10240304c069072201e8401c1e141101301e2201c0d001400228002084a03103441c540c1c1d556a0101c40c840d4210302c85082000c42c3d03c400304032641c1044e035041440c100081d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 2666743 1250 2665493 2665499
    0x20c01150509060f01020d0c050a0206030415050a0b0109030308130c030f050124030605040314030a020a120c080601080a06050418030e0301090b06060903010906050109050412050f0901140d0615110601 88
    0xc3d544200c7d0414801c1081503410a900c203105003848800c0c21550700a000641d281003604142d04032603c40010301c0e82c09031030b140218a03203090500c24884100c506858840003245542c4069400d418002d2828000700d00c41c594903c001641110b07984082d610070034004202400034146a804c49405205103041041104240f000b0b851181e205101203030b40c0500c01140c2903440c0c1c582114560304054054900071400f10911070100140d4001d000388041c40d0b034403007100400c0c02411304d05071170f0943c0032800820045404030b0b40c20b52103043d072154481d246260110300c0982c0d0350046400c4644030381085070b21400c1ca034001b608060707106091031461001113009100803003003a102d2070b865100203003066200300c0c0c0004080e14281c07020b4003d52841601304004204546c0e5a00518010307090494040300c0405402540141b05402a800c6e168190f4000e8016030502c2c50202c01942c2d050510890003001c1c01040c070444419000a00410300a81480c101e04221940126030243c4013030045034407a051034000d50018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 2667993 1250 2666743 2666747
    0x2010e060c1303020f010302091002010506041a0a09020f130b040603050a050f012102090901050603190b0105040b0402090d120305060301020a1211120103030806100908030913020c01150509060f01 86
    0x202c019aa01219944c06100030300005038000c1c0b00704c902c1c1035080900300002841d44d64043d4440b5120314000d41d03090080b0002070700300103ca5040f406c03815500001410003800f4403400b41e03015040380c1c6503100c0c442d41340085103080c0d0507540401c0d41c0100c80304d100018013030140c1c95042c0a82c035007222a4900601140c18921143c0c0099901401202e0030302c088425054410f490100c90b40720200d4001c0c00300380140c20a1007445010702000c5800c50b00a1042e069541803550105681c24a030a80040781d4410b10307405c0404104c0a06070810480b0307800368003401842443d80d42d240008000c14418400703404104503154024066600c02859944264414820202d0017a0000041c00140402e120001810382e0395180003078660044002d034241c0b400303021002004154001f001140140400c4850900c858001d14040380d049410f40140c41094006000c501031070300b005040c03100c0c00c40c40f050025082c500d107008524210b03564100c10764102c40d00d100c000c00280c1000303601e542e00110103854201c0d0b45000c2e00c2c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 2669243 1250 2667993 2668027
    0x2030703030b0301110f0706110a05120402031f0b01020705010e06041206061203110c030c01090e04030306032a05030a030806120307050a0303020a030b0102010501050102070b0711030a0302010e060c 87
    0x10250505403902c58925107a0341c01c0d44038203035001001c06030907121450b4507681d6a0580084100300d486524288030354911101c2e62080d00c1001600da40c1e51480c101389010806280000504101c1c1c16105481954540710141c00605002000a200005824201c0c1b07000900d010184d82c0450306000100200360f295494110483c1c0a6039461203800bc945031251510350020040e5274800f0401d2518500c103c42003680c1f040b604801b040e01c15048440054846080540740e40400b071240b40824500142040306900b00044903034020b002e424002400e0b070f900c1c1c5a00c807403003070094090a04489902110483c00c240004484040e100c1a002001450380c990780240403004003500d03462113076031014230000c0c4182c03040084034061076000301507c0202c407140c500940039402c155040000320742022100c0c040c039481445518120740059000305446498400341401c107238852407055414503101145100e8a440400c003e0301800e220343c0c000a2040742c0010500d00307000c03018000200c0c4100c00c001c01c441600754021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 2670493 1250 2669243 2669257
    0xb091003150c0203040302211002030f270d0305071209110607020a090c05090418030804080a1101060b070c06090609051c0605100e0601050a080c030402010c020a09050106031406010203 81
    0x44001030b0440d03400c400b80d213103004540c40254440500c5100d050100d6400c0100e0071048006801c0b110a43e038810740e6032059010495480d1400700441000900d0b0080d40a0095034240c0e0020162442d00070743d06d82d040c1401a004142d070f02284c0c5620601100e00d6100a0103a410003090307008002814039540c1c0c000c0f5523a846400a071088a012510300309554034003220328000d08042404000d00700b502c100241582d080000325030f20491601111254500e410381d21012078a07490740c2c6801c0d4540c0d8580d02c400450700509501c0c0c0420a0b200d83c0240f0406007481090b0203000900049034540380a890300c1040226030ba0080420001180410009140c1205074401030b104101c40703442008559805041c084030440201501840c149000e100c00307081807107144405e480d081640014259103040040d1001c0c4959140a000250701c0301c0020045d208000c0a075411a1051400000e88042a000500801d02503042071460903a038078010010b490301882181d13030103120a0340e211010318216001179200d001c0d444d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 2671743 1250 2670493 2670533
    0x30a03050d0b12060106020105010906060504030302060a090809151c0b0108070509060d0f050a0606020105010f03060e0307050a0302061815041520040602010b0406050901051002030705030d0b091003 87
    0x503520000e0fa206940c14100c9103901003181c030305680d60340009029001c21b10915001a10300308001c607010b48603000311003e690305900204000e80300c6a030b40e000200791950060b1070034201031200c22020350300d03140d184d8004071078200d841d40c503004d10001d5103940003001c052440300c0307510303101c0c255403540d03000130209a20583c00d082031610341100c0340c08a2020700c5030381400d022a5140a07106100c1e5401e50344003c0c0a1001d400c02006a07a4030340344240d0880d0020b0113800c000040c18441000001e1268102054520400c0240c905082c815030341c031803601b05184001c03005078116008020b01a44148005004280d6800051a452210342d104612800010f00085c00c4440711074581314102c0aa0342251030380720b18111000511102c406010300f401d4015010301c50044d400d250f9a280b441c41d0a00402c0d068800080080c0b00344d919040822150400325150359043d40814042e190100d80f01784050f10700740c1d11444c00070030f070b400941e0704000c0707801002400c203c03144081d241c052020034060038541c0c0e41d2074811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 2672993 1250 2671743 2671751
    0xb03011410140d090b0711060c070206120f070810030206090d03050c0d050a11060906060103020703110304030f0c06020f0a060e0a0507080d0207080a0809040b04020405040911030705030a03050d 85
    0x20040480c0c91810503085182c1c10000000c000100342c040e41c0c0800041c0703000b0000c54a060311410000c03141c104140c804081c56a00500c0480c000024035001044003070710080140781b501810340c50b0141c410317004444e86090304c00c01d1750800040b0341d0041521903020b0311001b07404860b2400c503400220980580e5401c0c0d800303550031100050405006074101d4140c0b02521080711010000c0d004000c040354440340d540c80005800c4030924110030000265907000303101c40006010141d884000441c005e40003100180c041090515240443d17801c18002400914040c0c40911100c3c18a424610b140030040e5000f4000c55201188030640c504003c220640c0c03881c0d04c030b1404241d071318080500c0c91074143c4148028000740100c600005821000140f4040782c0c0403680c00707840c2159554400180c0301d40f41c403600030f0140c040c1045140d8032443c00c0d178021050643d00410040c20031b0340394000b00d001c445050500304c03500759001c40c12081c3c5281c108078a6005000880080082c0c49455800914501503002003100b41522 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 2674243 1250 2672993 2673019
    0x30a020a030908031017010e0c0d0204090b010612060f080606012001020406020105060907030903020a080307090b0a0e0102010506040b060409111b0601090b0303030402010f050307020a0c0605040602070b030114 92
    0x401c2e0480c1c6000781c2c0080c01c0507120700748070090b0350304100180b244003c4203031709a0740c1e400d11441c1809803900d15003994003d03016408500c0d062150305051a602264000d41e01c242c50000110f2080c100c6019128603601d9800281d030590821044840a4001c0c1403c2c0f41c0030802003000e00f400041150b41b2a02c2842e001090820328250080041d0741546404c01c02e5001090120711a0f038150301051103001c0454240407651101e200a81c1114030b00c0c0c40250058216881180c04100f0200003550010541d24180c1c808582da442284490b4102412000c002404c040401001e583d0901920350491002c0700d040185060f1000060500d100d07078416121000d40b211000098261601d05455144901c00003102d40c1c0500e9442154403480240950541c46251203030840d002d0800000f600c1c0300326410384521004402d4030405403441d420083c1003800f184603145042e000154030700c02c903200400645d1039103915542040700103414824581c111483d501380034001003000e1220b60846901c41c1700c3c15202c034040030310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 2675493 1250 2674243 2674247
    0xa0c0b0f0d0216020402030a0902190b09010507030210060b070501050f06010801060309020103020c0706050301030b010902070305030411040902030730150915051501080601020102030403020d110c0d050606010207060207030503030a020a 103
    0xa0000040c0d0f005c0d1020082007819800c070b4201044080c821200983d000c02101c4901040b480540210000b45a081c000d200195004200404d4501d000340112041c070740c05100c0c1c100590312580c0000c404041d0100c0c02004120f000d0252a41114061500765035074603000000800310601441200101a00c0c1c0b1000019640243c1c12200707078410441c1901c0ca042d841c0d20010301240d100b0b100864015000380000030300042103101b901c0c15242e240e0b440a14584ac0c2e174a402411542c0c2c6502d4a034440c1d500c442580040c0ea08114850042c03e8910091030022801003107800c50302c10b1903461a00500003032026a002500503507100b8428008000c00251603885070070f12404840000d440c1040d81403a00f01030005080140c5c02841070300009076030350386d2907940d940012800d0380002ea90040c00342e4030a0305207080850244c14020216404d01040344c40045c080e01c000f034540241814180c54580043c01403000c0380d64103016010203040340340001c0221074070790350303030b05540b80300040c10720b4080303680401e41c511418 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 2676743 1250 2675493 2675527
    0xa02061909060203010f0302030f031602040207080405030f010c0809070501020a06020703020304080303100e0109020f0d0504020619050702090f0402030d0f0201060f060203090301050711070306020313050d020a0c0b0f0d02 97
    0x990461011504d03503841d801100a5090180010b80c4248208281ca0942050010456452071540c0040c0b440f1035100707138280000303504251400c454460381030201203900e071420480c45c04140140000400c00e050808006000508007030003155098002d040103101907600000d40d003d600f54040c10059a800480c103041f410b5000d0360304034800e10b00001061200351501400024203540c8410412030069907203d800f201284074a400e10b50300b20a0034007040840c0441782d400b140d442400031b0a2949840020f518240801280c107002c200404d03004030700c0c9810340c10300020321607119403402c21882c560304054001039a105001c0c484d81d010041c0958158011503c00e412010080040001c03e1907050b40710b5001130340341c1c0c02c40d6582901961030500054505882803418600b507882030710280030700314115114900a540000c0407041c0c900341d01c013903a13000200100500702e42c481180c1e01070300c4001c2c2c3c4d41c074181100030400d510188800305d040c010040000e42c1902268603207000c0c0c03d00180e0f584104a00c0c080d500e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 2677993 1250 2676743 2676761
    0x50604051b030c041203020d110114070509010c05070605070c0806040f02060a090305070e0405150c1b0a020a030c0e01060203190807020c03010903030b01020c061e13030f0303020703140a020619 85
    0x81c0c2d200b00701721020981c0008400e41c03410700c5038a5002c0c501800c14200c600f01c81010580800b82ca01600200d000d50307000381c0081220720410b14200d803441c6469281d072840c0c0903095010030005a000030300c030001c0c040c0100c449405045200f001e00044d00f895100c16402e0b50105070041c5c8102c4000554400d82c50040c58424011948041542c0748039546608040243e54200d409075994000c0d10202050013410360507880c0b040c5000c01304075003403421000c003509201d4407450b005070f5541314060049000d030b070b01c07140c1000003944a414402e18041c01c102840300c02000c10303481801594800e01002c00b40000103038502400642c640f52018156650a008a28103800c0d000c903260554a440200000d05032f164000e0502c0e2402030302120342d11103100042c4992407246206030300b640b181c0745844000200d0220000c180078800c0700100c007405500c98450140f0031501c900704070042a030029007502019040001c3c0c00e29400605102c03801c2c04120a0065101c0d20028512a00d14042c00c0300e001c121640d5500c40034003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 2679243 1250 2677993 2678009
    0x306030304080601030b06040e0a020a090507021002031305151003080711040c091401020304050a090f0b030d03021201050a0b0d0c03021306020109020f0301051e0c040510020307020103050604051b030c04 89
    0xf203503528145010111800e445113800b85040c80045c5079441400542c241c0c84590103041408440e10700f0a40078018000648036500714050301d114882c1808250002e5801801508410003a100141c6403d52030b040b005240c01d500344859204208402140482d0082140d40180c1c80359603c400174585031948409060280e9841803074440000c10095011000c2d4040c0c1d07100c03012026034902c1003001681d69020f06c1c841d240d07000258040510003034007140c02c8100d0300b039118071000c03070030701c00f24000030f0f0a10300b00400450029501245180e19000070078170701401404141d60403400c403410600c91602c00c0c401ea8099041843e115034601b46c0480c401e034101c4810b01c82000f02810501c0d1201030080c00307000302c1e2000b64400c55042c07181031501d01c2c0c188180ca005980c94040901019040381284010200c014985904a01d00380000596525030b1034078804080c01581c007456460155200140031580007a0485015914140c100880044a801c1000d00c103030800100035169a100a015181407040b038100c440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 2680493 1250 2679243 2679253
    0x7060b0d06050a0c030605030d0516080703080a052d040302070306020414040b030c0303040302190b03010b030f13050706030b060c03070302010b01020d0e0306040b060102010e010608030a02010605040b06030c030603030408 97
    0x401d0003000e40c0b2050040700c0009051041d4290131500710240d035014080d917079058104000d60a417490094009002c0020031096401c451081038803498040d030030150302500441d075188100300c58107080d40304555004c1e444c43d15100080201d120440030440c44400c40540003810080403078141030007001440e00450707218005556540c7c85040903102c03c2002d908040c0264289040342403140750129078040b8803e4090300441c2018075607020801d00103801c0d46e030300201e03440307182c400f051502082c001507003c2e040300720200d0b50302e003401910750700c8680d0010a514004100007510100080c0c011038404126a554500030504a03001c90005509118000400d42144400035400c0304254041d000000000c800340c007542c075803074007104090321170105043c07665a054112030006000600100301c56a000001803000181454080101500f11030040d0072610725a4030104d918a452503090040b83c020700800d82d0f080c0243d00c0d032200410820f00000c1e01e0f295218034040001009610f0400c20f840041082008860f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 2681743 1250 2680493 2680519
    0x30403080a022505030f01091703100306020c06070f02030703020a030e0103110d0c020d09120303020304080d0c18050a06050405040b0103091205030601140304020303030f040510060602060a0f0605010507060207060b 94
    0x84516100c1c8030305400790080c0f122101b10f00da010b1050703003a2290030010060303501320440e00090b12503100901c2c04444071b10041020010400f0303440600b0140844100411140c24001c2000d0002800c0b000782804541c401c002600000754041044200580d047c03e190500e0106103005a000e08207010034044103102c04907420400442d1030f000501752403a50b80980d41c09134503070103040351148450701036180d480c1408000040000e02c640d001350781c000d010301b0506040c508007070407410a45510851032000242c0f09101000c05118a6003000002d0408864a40c0d20501c1c0c810003408034001e91260314410380e580d01c241401079000e50031408840390b002407498210074502602810f0390300103a8a072400500340c00b0781c0034441c6c030455044038040c45e0010b0041d4190780d14a03034010501ca00003001143c003030081c01d041d00c074810010301940d00a80040e4018100c20301d072000c1c840003110380080c0800c0302142444020045643c1090858140507086100503980e1030031800c0003409080c00603406a00090110144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 2682993 1250 2681743 2681803
    0x501061203020a0b060105190e030c0d050a0308060415050d020d17040905010605040303141e03070207060806030303010e010b0a03021c09060e010b06030a020c0109020a090b010f0206010305030403080a02 89
    0x2d26002d80309031088070302605e80034011203890051520b1014220300012400c6440303030244400024000c0c00804503590b413050740c0c0c0880d0007401c08000890701548070b011035604145c1c00024156010f44113482c1080441462551102c1c064510f02c5201d0080500510090554a03200743c1c03018400e40000302d15190144184800e00c04d0341c03040c81604a047c1c0b0f01400490401e104404642c1100d03099038940b58803072a01300410003207034007030120101550650580c010100452a01540c4210803513005031849510304180034000e1100100340d50700c43e4008100503c10003000200302815220030403c1d139a1a000580020b030000e01c6050200c0480080819980c0e10090340340e00201c001c070b07204d42c40500000310403d08071426103c0b218191030340400c040c00092090125903001e00205180000089002112758010a1243c6074a8006900442c3c85103600d030313a03a580010203214012054030042c1003039031454851030744034056800001c003048400602c080c8660702c20440c800141c40b81d80481d102c411800781c1d80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 2684243 1250 2682993 2683003
    0x307080a020706020c01080a180501060303020609010b060327031210030c05010201020307020d050a09050402040e040209010b030903040501030b0607140d0809010b09011e120303050a0605040204030f02010c050106120302 96
    0x34680144180c0101090891000c03e28001e664011f07121542d1640b20158170102401c0600c826078100e0000e800003001180c424003880b0025030183d00030301503074189001290300352440d45100e68040c440400512041005403658458490031000004c01980409c8041e18118807542184241c18080907040c02000c1030002c006d08111b9124488070645c2035614401a4241e020490b82d02004d0b23040007001c000c04500810050142900740e1030821181500c0c7c40010f0100d170800d0f008404441c021400300003c504003040b0507405070100703500b201e080d032a0400301a40e49119600403503040681300c200c0100d00e42c661809494469501c0300071205181180c024180c0d8820540006000148401c0081040503c06105405100d1005010003942d6030070f0082e0b0a60903101111100e0310300364a80000070715500e244a004e48028469a404201d50400c095950190358a54101c10322481c410801080091019a4805440340e828217041c0d00111140c2005801442c465006110450b201c82d859810580c0c0411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 2685493 1250 2684243 2684257
    0x80105010e07031a010309050f0a0605150105040506030a02070218040602070302160501090506030603070305030a0206160905010f03090203100203130204050f0606120a020910030209090f06090c071103030708 91
    0x16103002550b030b5001045040c0c41d0b001945620400000e401e01d901544240c00000c03009018404840c16182d00c40c0035503280030101c0b0010340e030803074ad210284082c2e20b24942c003d1828040901e40107040c603040c0800280c1030300c0b02400c0352250950020701501151141222a0f20841003941080b07142c2c5401d0400801035400118201c005000d410310705004145c0300d04542080c2c0d801a50b84901250800e070910100b58400b424544d0f15119043c400800110108024800d0110960241030142441608030020300d03000c2c1c4456041c000c60100510890f607101d80161030705021443c02056054040c00840d08050b94000d1340c45200707000000f0024000d9103030084a030190f04c259000c002c41c1c2e0f01c0b002003c20171181a508542d00c00c0081100e0b68640c0100781440390443c0a0090052501e15500c00295072804035010501c007094001c01e40d413540c1c3c07034012403039580703d15000061092031a128002401d0b120002b405840d00d03510110f50242881a402c0303600035032440c0982266985d0102c0e00303001790f031780d0401c0e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 2686743 1250 2685493 2685509
    0x10c0302090415080c01120e0607020706110d02030307031d0604120905030604050304120201020321040b180a02010f09090203010b04080105070203190507170d0e07080307020a0b03070201020f0408010501 89
    0x1450f9000f280d01c94804a0781180c41e4000a0b018138000d6000445440c1321240b1602000ca444105080440c0c0b414060301d4003404140c1c000f001d40c545000c10242c1504011505400550484a0307038400c481e03008000c0f2540300c1703032a240000d83c0c80d4030344851020b030b100c040c200b0040610540040108005100780102200c5649454031480d05680b20200740ea103000c100c40c0100a5007081c8400c0080212450b0309140d0745e807050040c0c0781040d40d02e58221500010342d41e000e00304030540105100c2408030044a10f0340101c01150403a5148040d44c030103507510204040c0080c108054188141e0f20036100341c0301417020b0000c0d00c105542d02e5a51307840b20306142d002405141055464040030403545400082114411400d0382c01c1d516480900c004140c0c0c0340d0308100d50941d210f070001c01811002820201c001e2124542c2c1c002c0000e0301c1210015030b640303040440d070031034000e95004008580169482c034140c40d040702d1110a2140d902d644190040b030280c010045504c25100380400c02050301d10041d040203048e00c90311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 2687993 1250 2686743 2686751
    0x3200a110109080706021b0103060506030c0304020f01030203070c170c030409050103050d05030106080c030903160f050d020c03150a020405040501030f0b0603010603030c0609020a0302030f07030c0e04030503010e0a0b03010c03020904 102
    0x6148058030f03032844d88101005030b4058200390b2420345140e000004803200c14140054900d44d01c00c003060080d0300c201c2e101104034800008000071450b00307828200f12071000f80380450552401600160032001441e001400443c904a1603090020200c0100c1d01596546c0060702c2d01e560740c1d01e180c20040c1a00380000c0340d50f8080c6030000300c00b01d4454001e590403650300343e44008094681d01402c4a140d4400b03080c03a10140810040900106451402e84003064840c110444c0841068100141400c1072400c0c0a81150095894407550350f40000d11803000d00d42c500c1400341d05482e0000320304000d10899003c90303000fa050500000c103014002c800c010825001c0c40e41e8481654601003010300301c4046001c0100820028020314000c502e00f6030080c0d0649101030151100c81d0749940002e8540240340403c102e00e940500c205208005404010740000c08003000e80e5140b50074683c2e00a4030700e0205009901038600303007400080b0011465000f900902c40054000c005991220a00401035171161030203602603410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 2689243 1250 2687993 2687999
    0x6080105030a11010804060b0406030c031506060509010e010207080d02030403021503060105030703020c010f11040f060318020609010212040303080f010e07020c060c071e030501110304030c03200a110109 89
    0x400301c0c401c00000e03880681807690f07100407401502c00350320180040d603040d41d45036203940031900c46100d06005940100c26064246140d8074107800c00014000700410030394103102007004210b810006a030302e10340090a1102071507010000407450030009a101e40300398450906680c00840d008002807040d207000b40c400103c80010741041804e05e01c81540c0c1740c0c0c0042c0701000010121842a406003c510089200108000c16160201c41c02d1361407090600d17120180002d020888441131640f56001885c442c2800e005003110900f500e08048022b02e801380c0a001d00280c13125107603109100c40e07409008100780701a1116240d0078000e1151000f19992140442d0100002c03c010003017065080c824001c55008184221205080c49400c1d0815803c812851207011004540503080045e85401003440081c1080c1e51403450070b00e28252100d080318100b01324070400c24040440d5020304891680380d0942003001c00b0020320310032454524401c034040e030142d00a55019a041080c7d40c0700040818100341d82d40585262 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 2690493 1250 2689243 2689249
    0xd0c050309150a0e03030702010b040b030f070513020903030a03020d06050405060303030703090303060b07060e06010605031b0c120a050306040606050301060903060e010b0303070b0106020d090e0402040506040b030f0706080105 99
    0x210a5030088400e5200710021207a640b038041c1070950181e0041c1000c9000b140741001c1078035503081a100140940d45581c4030040d24201031040d0012201c08030010190040081001501d03022a8000e040c003030203c028501075050a81d8048034100400030301160342e255a01d140c0100203421008541c2c0c01c0c103003000c10000340f81c94076014050180c03c1c010051461034490050540c0288111a800c5091503145c1a000806030a203002514050b401000c021480300c4030284028145030058001000b402018014040718042d00701310041c4c0c5400c41543c2da941e503030b030102c0460703d41014181c6410242c1c03400140c1e406184e500401940c002c2100742d405010490f19201c0c19162400b0034010000011216201040499020303080001e01c0081c0d400005120030a0902103170850748a04015100030041000420a8950401002d65465240d1802618142c10201c85410f50705000d00701a1040f034448012809a980c0c035404030701000b400400f101e04d903040d00c02d14903458040a200310750100b403904d80005810300b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 2691743 1250 2690493 2690497
    0x40b13020901090c0909050709050103050a0e0319020a02030102030a0e1606140d06030507060201020c070902040b0f030405010209040504110111060c120c0c0a05031801030b090402010e040b030303010b0d0c05 91
    0x240d0003040d100d090b0303091500300c42c028154000b00c00104258103100240c000d40d28419980a0001c84d07403500e40e02c03400c0000240c10354801422400c80c1c5803805504001100300802500c0702c14016102c81c1500c07500c4802c0c1203182000005000e94103510001c20702445806a50155003000c000009492112130f40c4010120503170603500c40d40010500039102004e42d0341d051401080341030307060080043c6143d240d48405150261780e030044030160f980024072003012041004003030001e01120f10254030b068248003072441c4034040c480c58501c14120200100742000400e4040e40d0300100083c00c204017910b0181817100540001425240c0442c10b10035088604100104480780b0035410820810b281c5418075034600701e010700080c01d007806600280082c00ba5440144105108a80101700a64403817500c101d440720040342ca0520039040c54580010881241c0340c582c038081e407080c1c090a005110540c41c0c00410083c00f06046140c2d40742c04000000b0401e020002e001d000f642c940b10204101c03842034042e080e60340d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 2692993 1250 2691743 2691781
    0x60109080c09040b09150a050603060f01060507020603040309150c02010306051008040206090303070f0c060816020a031103040f06050705070f05060409020c030d0504140c0a150302071406010608040b 87
    0x100c20140005000b150400c591306030007040d40c004a54500e250b51460868101c03082d10300c04200e5480b8028131200307240801485801c070b1900c81c8520001d51401402800724429a040203000700404000281414054000a401030000350300c40f02060135400c80083c0402078441c8100d000ca4684071000c40d06051081c0403c07551001e946803601c1549842e000c00c2025080760035003a50510040000c6000039031343c18080701905d841085201c00d12400e28501038807540d0014410240d200c0c00e040302000031580080c06d0000070750141003002c084503481041da82588119000420361858904000a40c10751000041c00303018001c805451007540c45403484002030403e4810207030310207070604c404c1c000b84000307178010448500f07460101c1e07240c011603140c0319003503034030403a81607a00d0f10050410326080642401040544041142c05114190500500d054040541c054035000c065000c1915000c00680300141c1242601c100c0c12a0815a174074200180b103060f08a608682c0c1002885c041481911800781400349 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 2694243 1250 2692993 2692999
    0x6030e070902070204090204021209070e0402010503040308060a150203070501110301080a0b07050909010b1209010b0a091d0609010b1002011802040203040201030b04060b0408010b010507050a030c0212010212060109080c 96
    0x9051074002070310701a401a002c180d0341300d55103c00104c0160703190b00c0204041e410115600c031440c40d10401c443d0924405a010080c020712202c100401130b82c2c40303403c90f41e106a0504240340c1640790304003c121968103e40001080b1070070300003031018694001010f050144e1280303000f80401d00d5101c0b40541c45010a02c12120254800900131001562102002c1d500c1406407424a04000792200080c44140b000c2e80082c1c40c4030b00000c0e9241000e030410349400d0b41710103104002d0203220304030b0001c1540440144110b06100341d403540c124001c0421514800b45144000003154814103190400500809440540610803040024040c101074018000c0c1786400310080c44040c0c16910940a1001030750000340304038101a51000b515505648911032080601072214682d0303220342c00c2035442421142c0301049907040c40418000d00c07000030000070348020241c1c0d043c030b0240509001c0f40f010035003120400408420a50000c41c0940400c64051109441183c09071b80c2d00101e543d4903003040d5100c0f2041c00107113030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 2695493 1250 2694243 2694253
    0x804030b070203120109140703090b0606090604090e01020d0501061b0b07030e0d021f02040308030103060207020d08160203070e0106050307030504080f040e040b06030606061204030306030c080a0b0106030e 90
    0x80030980c00c0d880154440e14500583e80b0b020352a8480402e158001d8000c10086981e1701440c41d1043c4c210140664401da050408211107a40c984410962030001400340d48a01c5001405010701d03250f520940d402010300110520001d030814110703e010750844003a02d038001e440c0000015005200d0200110a0f008002240301e10b07044070348031000902d00050041f010306480d00c2e0700001060081045400d60560383e409410006086460414110742c100300a030790960040c0424008154028112811241c0c082001680e4001c41d00c04202c0101080c0310141281d4008104c0003204d40074a10f085420030300c201c06032094262070712410060044203020340400610309000003000c090280d4807807604540140d40c428282140e42e16459450343c001c0c2c018820902d9071406210400c901c158882d170300188110041c015038504400414154020445001e84648400740400c00381402075009801030358110380c030081550341f90500ca6550f00114001211404061000029554424414508000c1030000a00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 2696743 1250 2695493 2695499
    0x504201807090b040305030304060608060603120304060906060f08070b07110904020a030818030709020f0307050703090305010f0501030201080a0603050c0d06020f03090a020112090b04020112090c0603020c190804 93
    0x100e00200c01000c000902c01c01d4000890300d90030b07500c0070700000c502c98802181e40c0e252901d8500c054881a600007900350380544c0a1041581d00402d030400f9401c24030032150303241c1d511410941d0203000e068030050101c5182c074601041c00c61541e0100000c0e00c01c81001c40b20019500c042d004130354031880e00040d02000203090309100034602007061035000f60004020300c006940b2919941440c4d80844046031941c2403c1c0b03100e03881c6084c00d00c0000010064070400314200110701014003990302c03004012030b00b00000080c147c000c042c01200c00e400034503000b100800880d4124000300c00185400c0c00241e01140e00e910005e811100c142c002d203c181d03a4400c019113044c510740760904c030b6615030038141114003036001d2046490f401402000b5520070f13001d9900034803108880303000140c01c0c0d403910b215480b1184e0a1805c1c8a021662045107070f60000d50a10300514052903680032600148200e441c0240500301060001904541c150054214140d072402901d0300d202d00c00840d101d6444880342e0040000760107010030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 2697849 1106 2696743 2696779
    0x90b09010c09080f0703030e010203070503040902040e0c130603050903070206030a060e0601090308040524030a060e01050a050307030b07020a021206010305120906090f010201061206050420 83
    0x2a1000710152088241c550350b01b408007400348921000d017507110364801c208a544079a000010749850b0354860815001039805441b9090840090f0004182503203c55405c84650503502031502d0b224914210044c1d028050003449031700280808d2000d440580c98510003144681c1100400040b042d09094260640d07003005000070741000041782003400020200802c490690300c00f199030002401d4903510034100394010540020141c1d9021041c441001e40c20342144040c4d440010310010181c5c2c8900038030080018900c80c0c80d40c5603010300c1c0c0400100ea86401425001201c40c0305603002041590040b8400780081814110264080d00c0100180082444140750f80300e01c4030141440c04e00c884002440c0b0f0700820024911500b00e6030040807240e0700075030004000b0420701004030858206810b04d01c004020441c4c058a40c0070305400803201200c0d801a0300d074001070000b0010300003102c070345040b = true := by decide +kernel

theorem cover : BRFrame.Cov 2517993 2697849 := by
  have h0 := BRFrame.cov_init 2517993
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2517993 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 2517993 ≤ n) (h2 : n < 2697849) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
