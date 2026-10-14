-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0341
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:18:30.261112+00:00
-- url     : https://prove2.me/submissions/186e774e-f714-49a1-9d64-66f803074bfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 61151082 ≤ n < 61330938 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 61152332 1250 61151082 61151107
    0xc07030303021e04031b051e09150402040315060f0605090108040804080604030c060510080a0f0f080d020306030712020f0d031824090602070b0309150f090d02030f 72
    0x164902c0c0d200000d07400c00c42414618000064001540146c030041d4500510305c072003916503105908101d1141c982088036040c0e0344000101906240b00a42e006001d540780c01c2188607041c440050340a620600000300030003000280c1c0c150041c400651030f0148180ca86134450f0a0030800039019040004609006c011000c0d803043d09407980042c00340d003040340340a480350040c80c1010801c0314103a001c104594131030020001c7c01d1084603401018802c071607425508245076541caa040108001d03003007003807040741d2000740500c42c010002d4041d070040d51195070b40c5141c00c1e030001075081103510394840d0098503400510b01c48261320498645034000c0c62000310b54146000c004100c0b915600903020031004503000e64111500301518806020628180039400111201c8a10700a0343c140c03081d000c10005c00d104002540d00003440c0e00c140c500003210399407260764203c801403408070070010044120200074280100c00800b503203020b000b4a0188103a4104c2e2082c0907090341d417841140d1280207124010040b00d0440c2c04d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 61153582 1250 61152332 61152337
    0xf040c1101050703090b040f02180f1b181207080708060702070504020901050313060b03010e101b0203030402120c060d02180f0a05040908040315020a020f0c0a090f1b0f12020c0703030302 82
    0x34030040a000c0001d861080c1741e42c1412b800c03500c984052114034140041100d9180c03080b0b542d1000c601d03041d40780020202d0450311151a10300000e016014191500411100c18800100075040502c01c4403901590b8105c0140d071340ba000d54880000d801001e03c040307481d04060003100c1c0c2058040c0c50f40e81c0303036880b14810050f80384800541aa03802e60b940030b4000381541c0a001d85c2c1d083c905418020b000103048a65103000320b80910714076600040b0701c1455030103200e4004c01074030703403054045900311034900c61810120300b803480c0d18034159404880000d03900300012050703018000054186804010b6072040e80180304845180300046c9501000c6140100001e18058201214a52003208a5814581d4940d210680000c0000c6648001034000c90840000b582c1009454056030310039008158041814002c152640113601a60360302035102e00711440c4150360340d0081c05540010303a81d007001002c0c07400340041180d419500344400050440e50b0000c280e6036107000351206099000060b106591961342d0640c02907 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 61154832 1250 61153582 61153613
    0xe010c050f0a0602030a0e070305070b0903070e09100c0e01081f09150305150103080316031107050f01110703120b0d020a15030c080403021b0f040c1101050703090b04 73
    0x34822100072081141e000c1c0040401d80384200c50158503410704410a20a50746c000007500c18990008000b0800700708001490011921080003807507131600444003181c10f10016400c150800130a4500380300a0b040006504901400c5c142820481d22840c1d0a045801b140301c00c40c0c050004841074081a181c502c0d840e4805070030b41a07850400d61031991103419009540140100b00703942c000945041080c0802405800b441031100184a080d5604560300c154080c08064443e240342e10101d000035910314001d600c6035441c420340c181100c1c0c0301c0881e4036201d955080b0811400301a54281000b441c044443d100030303034041503810b4680704103000307150407041c00074603840d201c441d440b42240c0d100202580320070395020040c1000c50105e0480c0c1a00d10f1015013a95107421810041206203800c00c40429802300f14000907580d23003200b031804801d0020004900c0c0c146005c50701d030300504d4080d1007030f5500c5c0c1100e046910000c108009200c030f551110410750440d0f0100b80c000d04060181000500000c041070401030b40d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 61156082 1250 61154832 61154843
    0x11010807020115090207110f0a03030c080412120f021f0f02120709030b090601030809043611270703020c01060b07060b0f060414010c0602071101080c0a0e010c 70
    0x60114140e10f00d4004802030b80600c9400c0e6000403084140100d010552070042001c0c0c0e4140d0201003a940807600903a030500c0090100901c01c06290b00700310040044800602c1108910000c0c2032395800d05000180042d441c0c200841c020014458042d07002182c004480c201c0684240500440300c0307820300c0035065500300840941d5003085045400c000840c03256008144a660701c55a690540c0360406852a003c0d200c4170055006800410014440004881b00c0e004203030782c08216825007624841c0303400c4005401aa6000142c050701c0030400d03401c3d131485130031030041102000c00e0315481d06004400300c081c2e04822500c0100c16492460780940e6990540112080c9801803a01101d6023065085882c0d582050703800c030500181c1ca5080c400d032030040c50700c01d07001190b400b41903440507000104a4441d62081c00884124404001282da00910b070982009400500a44d629603a510b01400c030b40f020082103602064401c00418604030181064842c072412540354a40040700b0000192100540400100d41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 61157332 1250 61156082 61156091
    0x60f16090911130e0f04020d030e0d03051309060b121f0e070917150c071e03091d2a0a080708060303090f1c020d080405010f0507110108070201 63
    0x11504001e2054001c2d030010168016143d07404058116044403695210a0300011490240009800510900390300154125042240721019240580301c1801c00c903034090344160803035114401d041c0c01500402c0141031a000c440000b075141c0901400700c810900038500407a10a000c1c0030b110f014074ac1c014a402019a4142c520700003550039a0110710101c1d6040001e451a00c00309006205411820a201800c490601b0322400b00ea00e052103542c2e007603101d0440f406144ca690124110704007080445140380d400c00c05603080c41e100e0068400c900030707080c8411000036001e5000041c4141186400800441d81866020365949599180a401e0000c0310100d410303415082582e8814001d8a0005104060440d1074442e00352412044c00360503200c0c020411802900b08015032051643c4640f81c0704001e60b800c9030119000328401c40c52944404071180004c2d0080c0500c0c041000340181d00d000351003200c400f661a118400c90410040306e89000d44200140700d40081c481120741c0c1c2d8003405030b042d40508103100005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 61158582 1250 61157332 61157339
    0x2040207050f070909031701080309190504090f1101050403021503220308070e15040b0c03070f05030c070909170304020d06020409091a010b0f0304080706150e09060f1609 75
    0x83c2410015400045401e80e201541001c00d030b00503001c4450100221852406513140004454591044015480c441c144841d4540d070704042081d008405403102a0082040169a142c2840b025200006c1990100a40040078501d580300c0c1040310f046d254050301185214141c040d42c02c84070b42015000880780780260300b81d4030000d1800362954a1080c00307075a55410314141488080d050b1049141168080e03a484043c40d01c1021820341150221401c56040c00d81d80c01c0000c28850544c00750a0008020112555400050003400009021203071142c1c1c06403600b89599800c2d51040700d16640f0001c0c000714074150080b4003c401580556030082c0040c0c4040c502c10b8459460034201e9200350042c8403456074a82042080c805c01c1c1c9414001c070851a60100259414446840320500030700c8464041e21314008005010480a03800b50f90b040c03540301ea02403042c10b62807010003c0c1c10040380181c490302d4140800241503403d000400074003d440000e84441941c460045605100c04464511000e00c104d036074000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 61159832 1250 61158582 61158613
    0x3030204150e1e031207050c03030d14070806030a06020a02030702090a0c020f0a0b06121002120118180b07090e0108060105010f020703030816030e06090d0201110a0504030204020705 80
    0xc9409860560341c0b065545031034401c1000420203204114007554011006410f00d8a0001c1c00006580300424200c2d00c40103545030081c9000c4c015009207406000c0450400e0341c49030300360003d0120139400034000340325a07a40f034021140c1c030404031405d81d45507112103d6140428080ea008005400582c81580d1920001ea00803c00a01065800302182c0e9550300d600e072001941880504444181500030b442084003980b2004410786c009003015105480d04512015040c02c10801001d850506210540d15101a1848c80055810912581c40d01c0b60b114140b00f0100300d664800c40110704540160402110220b888a0f110f0714001040c0d18180300d2241404103e05900304041e900902c505801458190b04200004000b00d80d01420700301554000c18081c00043d0700300300d041d9401507500750300c20f6001e40007a00480150600b01d100c090300f40146810b02080306c0c2c0204001e9546a0b640e0002e2194105110f07400c541480794001000001e281400700744010703d059001031100794010000c4417500152580c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 61161082 1250 61159832 61159859
    0x406020717070c050306090c0105040e0709031a06030613020915010513081006050901030c0911071a06030601051210050a020d150905011e03060c12050c0d2a0c03030204 74
    0x2034443c011016403c11961404115480d40000d80341c0c00707800c4001021001030824040c41c003400a012100786d0005090f14450440b03640115004070030902c159203401e01400700400d05480450280c003070390000460500a42c20641c0d200b5501801000a07940c0d100055925041031440f21410000c1c10080030008522544115015094139005861196080c0e65400e0440e03080341d01c5640250b0722a0010804582125110822607000545c041032040c0034408004640c410240b0051013200310010700d800c104000c4096511640d1b0a8084400c240d80751020000030f00f0403807400300041d0380120b58840f0b40c5000d5030030560700050310580140c10041802800b07010b80350351079441d0f0707120b02103140104070031129401860b00400b918080724501003c1042c0f172403042001400050006601d8040700903060b4411514122020303a07503c010065402c2000c90800c4907031002c3e0760300540a02f06814503060500300824107410078440011814074188040b001c0d201080f0700441507043c07550a1100090708200e5540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 61162332 1250 61161082 61161097
    0x117070c0f120f12062412060b03010302040b01020105040506060d0c08100c1e02061506090d0b0105040b01020c030703030e0a0e0106090302130902030a02060c01020418050405070611060406020717 86
    0x1510f0345400d4641d50700400c0030705030882d0790440ca4107102007040940244204003d48011070085030b842c803180c80c0e40650b9140514160900e011740340080000d0741641c0d42001e1410399208450621052032414012030990704140e5000e080c0d44c010001013a1113250600f426a030292280c0546140d040e5240302c1d490a00e0908905003c081741c54810340230f00554003540d070700d20811070a0034030a802018417000035519440180a0f00d00160030080020f41540c6420503941c00d01c9004000604c510a18500340e0a9030701c0a100e028090790602d980712103158000702c2c1e45030020b900076000784401851a10211001e04403100c6264003c0e400d110040360b10308910308464083c210544410519901d50700c184584d402000e80860002032170200c001d40140e030041043c50392950122952a2580c0102148034028030a550201c100e000d5001c1c00c0d400e001e14140c001521541c0100706a9003900c1d503960040d41c0b0055424110085500001e0000300040c82c554050306940c4d008183c80e003045038403102c0c034103881d901000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 61163582 1250 61162332 61162337
    0x90c1401200a0308010806010e041104090f03020c040f021617071e150e150603070b070515061507080706020702210d090f030201050c010b040507110c0117070c0f12 72
    0x220b042040c150004811801011b40718010603a641c980040010740010240c8002c1c1080d40e52407043c03110350341b15008060160307081403c0c0c2418141c80d02d80a99680466042c45005038180040c050483e1220f1094076a031100c4443d5220506181da5291101040080d8180180010a02c89680826429090800d80d080341c1507480c00f82d0b4032241030100704183c100b00c010850a040c02e08040354500e002c1148800e0195241010b0303256103031140000d0802a05070810103007900c000c24590188600000c070302c0c0c0c217240c04103065406912410180301012180d0f0000c0c417102201082898000b81744480207000d00e038000c240040c01c146440c4c0c0010340380310b0030342102d280c1080d2801c00a860003205000c0c06c40c4681450401c58000c03490501c021020f20160321001c1e05010010481180d07503003007034105284400c4000c100300a240f5111a000c0c1c4022003410b031172003c5204514904226500400803403d200c6c0c1010802c3c01c099440810032121110f00b8841241d40d100d0041c1100c1c00605848000a8000765a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 61164832 1250 61163582 61163593
    0x50712140f0d1404080c190c12030e0301110a08130305040e13051515100905060919060309051605030c0409050c1203030a230a05070203120a09030f03090c140120 71
    0xc8260314117501047c44c021b000c41082c104000040e1035515640445000c000f0036403003401603090956200010902e0b10360507500306104010801240c80040102d034101761100512a100c0c0302e44404c92018840008001c0342080209210702c2c0d0041c008940e110700c3c802c40942c200f4010350707115410070404030326014805403602d0500c1400d2036420078500188a0541c0c208600101ea86d00c0107210b00c03003030701c5914000e400000e9121f00ea13454260314580107026002030342944603a070311401001001d4000b01960310b8081e4041c4030f03510004900e620800c58000900400c071034040c1504200040ca80024101d0360384c4168202042152250300b046215880f140c0302464803441c14101c800d0039103c0001010b0388101034000140d0510f5801c004203904000790000000d01c581e9000350a074514071549004482c42401e98041103465510b54009156507440f80d510080c100460807002e0b001e445021354020880102403105000c1000c0c050900d04000c40b051408420301560b400540018614130076914007541c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 61166082 1250 61164832 61164847
    0x506012a06022520061206040f020705011505010e100e040c1b06050a0e01020a0804060507270303180620010b1011060601050c0312060d080307050712140f0d140408 72
    0x1190344c941002c640a85089180050480c0502c50844004009903ca1036968450300c1c42030040c0d5058030010b90703112008104a407251094107481040a10405000442000003850341382082040400c00710380c0da480d40c04000c0742180400004d840c5c26000e40e0100105081d48001119600304884504c0703000d00e0000a203070900501401c2980d0300003a8400032603004001405045500c412a07542c0281c10407000101901c403480201c1c0d4061150020b800b000300c04c94000420400c072803016500b00c03442a16a0040104095881d0017142842c1c4141c40200c1d002421100c101c14072501e0640d0301042d40c000008004003903000041d071082104003e040020001c403860414071000b004501d4005201b400c1c10307070501500c0318010381c0e01d1040c030601d56a51000100404c005890f894002c0d6203055000041607201d00c0c0014000300281c00c0044180d03030508241000096031801841c8180d40c2c0000300c000c49181507910382c03034681c0700d500441d68821601c0e600c400c1c068009100800040c01188038612490741c0c0d428 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 61167332 1250 61166082 61166123
    0x70b070e03010c020703020f0a090c120c18031e050303091b0d08040303052104030302070b0f0c03010902071103030706060f0602010b180a0905010507030506012a060225 74
    0x4600e00401d0190b80342800c10707200316030006a0302e41242d6040f02c00081281c80703400807078080040383d4070400300c16050005c0d0010842d00181014104050103004010400d8003800c210f421800246103451101c1180780244080b4020900c4103441d65100d042d2000c8505080d42c070940b4550088840c100c16400000500c1c1d8509482c50600c65040c0c0100c1d185c00e60840c3c9512240500d11403444011b0a100340003504403450103101d24881b04036032116084001900d0903050140103540b01300700032151075281070000f8681c260308001e0103008182c0802c109086130700f040c107050002d52120030250380c000d00f00d01c49040300d90f03400c10082c4080d030b1003a5008204145841c424019840c0540c01640c15641020300c0c2900b161990603c41082c1031210030440e900d0744451070b801005258100c0c01424950030038003000311598060b0000d0340070351001c0e40c03820014a0060310303000901140d40316000000c0c0000d4018404505260083c14903410501811020390100b1841c80081c01a070007812503e105890002c0c03040880e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 61168582 1250 61167332 61167347
    0xe0415090b0a051f0804050a080c0601050913051e010f060803090406170c011d03010504030c11060c0303040602070c0f060207060306050409050c090910020f0705010515090a05040f08070b07 83
    0x341c1a18044114085000101c4019003a5003c0908004007100080d003403040230441c020b080e9401c90015030390780c0380c100203481e1034080c24080c140c041c0d00240c01180310441e8401200f0601030b00700d40a84440c407200449042e420b0388a401d00301896403140c500139120042840760800070010480111b56900c0d0341c006110a80b040c60307024111030182d124200c80c0c20040800c1d43c030b20402c400d280030001188544140a5828503200003503401d07619001c20002016045042914124051031414101420403410040d291041514807507540c0c10034404200002c0d20ba8000d007100c06c1c4103150800740303e5144e04d102903480e4115800400140d100340ea00f0402541c03d031248001404090720240070185142e200c0c5035503103405100c034500808002c4005040d440040c444062000c01c029015540c0d038484042d1402d070750700244800c2e01c05500c7c000101d101c0200c03040400041c1e4101814040c0c0390340c1c4401d0010002c0030020300a540020000c0341d00400035040303a0040c8003003841141000164209802c0042008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 61169832 1250 61168582 61168589
    0x50408120c101b0503040201140406030b120c010c030309260a030e1b0105070c0906140a08010212011e03060f0507021b01050d0e0102040b161713060e0415090b0a 71
    0x9241000d46000c4003e0b60740c1c41070f003032521421301541c0c90f140c6100494103000c00702c0c1c443c2c0c0c802e40049030200c2c2d0280d06410446040700c044550040d40f89010b0001d075214500611054081503a80e054100024003940101104c280a010450310606000c512200304610741c002d807500e07610b0002091400700d07415104018580c8131120080445a40d101d0149510714025800702d81401008641c000c108503401d5400005400d803a102800056034800d5850850303074031080ca13644910352065001c12a41414400d40d0a401c000030045042030741b0f040d1084400c0c41d4000d0540c00c900c40d0440001c0081445805820700311070000c4400240381c541100300034140106070348402d50343d0992681e4280c05a920200b904d00810382140001801000c50360390900921071a0300448400c2000700300240c02580d44001fa009040c0505403001a80c492650882105d200d0580001003c2c890080180300051140200c2ca000710f5016100140704c641121141070007000310345c406c006980d2a1441c0c141c880c18a892401c004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 61171082 1250 61169832 61169863
    0x3030e03070f0c0f0312030b03013e0306030604031808030a0c1a040203060402040b0d02120307060b1f0c0f060e070302030705010f0c0609020a03080408060f01050d03080406090201050408120c 84
    0x5402c5d9694061555010080f050801d5121000524181c6c0d0030340c08910300905100e03140043d0408452054620f20060a5a0f00750b41129160160011152001c8900c918030040180210356107036541036a15180070341013903080105100c40403c05060410041c0003000c2c4644519072019100c0c90110450328402501128800d844010301c00143c03000551035402c19811100070070320550100c08a801c40200c904044c1d800b41c4c0c03010a207408400088014030b201805000c0c2805088070101c1405444000d80051800390801c1140c03d5155510a0380f81c08800c42c0301c1c0311007410003d41520340205070385802c1254806900300100810031071404000ca040149001c0c01c2010443c11640380142c8080b2038050040c091648a000346411503680544803006141e204154a0b00c90b0b46803081d00340c0e10b443c1110700c1150a41c43c030b00042410301c3d0031100d14102c0742d49503484543c1d6036260342c0da0b580a08201403007241440010300000c14000c81c1403080444004500c0e180d0ba86403580b07504624601500304110608 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 61172332 1250 61171082 61171109
    0x3020a0503040201030e0f010204030609020901060e182703090a05010906171005030d0203030a0507051306050a020c040e0102070b0a0506060f03131505070e090906070c03030e03070f0c 81
    0x22554100c0250303540b0640908000940e184248040d07400c040d01d5070720341405d651000078007000b0001d880e44800510760080d2405061070703807619800e85442c0c600b40103031940b0a400c036460b56020440030900c2507020000b04c1005029550310303600b298036000203c8a407401ca40000c95110301c6070a03c9116000107020034a414441140307000e201030000e410b0010500810406200082c60300ea02c5000010300034200a0204c407945804140025100c9e00706030380000c00b1a0602c0041895240f0038429030f02e19406c10034500e1202468800c040e80c1c01c4c0e1003500c950007540a81ca5043d010b541c3c4500c10380411036060000541e45249601c1d00c5404090000c2c2220305540c540818041030f92200740642e01011980100d03a5503d403264003551181d029501001400042c0010040c5c80c4204141c1001780505c42c0c5031030f2601e401c90140300b080f40781c0c40b044440c40030340d074000800180d0040c03049408081d01402410005550100c01d000a8119841091f080d5400803590b401042082a40002c510060036007040011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 61173582 1250 61172332 61172347
    0x130303080403030f0c050f0c0a0516030b09010b21010e0d120e1605041808030a09020909010b0d1106040f030b070f0f050306010302070c120f020102010f06140603090a1209080d0302 79
    0x9200b03001f14003005940c01004201c2d101403940800407401600d4000c4100c0c0d1085007450040d4000c40e889000c00c072007030084000450840d040502514480c2000100f4021010b1070248003010201c009080702841176403109c0c1008011041070125404030421951610400d00701c401e106d81c02c0e18407460003080981e0213041c0308840b40d04082405010b48034201da011a00702d462800c507240604244002409107500082441010240740e0b2007082007500c2034555440d10b56070460903a0817a260254200d82128650b0510800120300c200c240f407080f84010002d0b800d09441d10100c02e01082150022510110f410f814059015000031160780608150b1400018021102070700502900003d001107040c582c001c91813804220b19100b1090281c8403000c0d001ca130034441800c215150103951641a07004d94030b031015202030131415000304819a40e0183c0d8103c0d1008080b000e10820b5030005113110030078020001440002182e42c04a1108078007140d80d5001035a0a14407031500304409000d0030b00070f00d4410031540d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 61174832 1250 61173582 61173587
    0xb010f090b27091008160b030402100201060b180f0316170c040f1e0612030c1505040515010605070b01050d06061e090e0705010c1403130303080403030f0c 68
    0x1100409954800054501c00e12100c4041000000b4402c60344641c40a0421040040c0f08081c03804684640b004c4602c0c007190b41d06124a416603a008000d02a00300b00002405824250120a13030000184000108160303902e021507001c1c0c110101c050000701c920403018040703140c013142c030a0f20380c20101c001e400c03110040501254492224440c40c1c28011400400c032425400900c02d00244c41e6000c1d20034042071036141480c80081c0460709880c001d0045402d2881c1042c201d912403a02920074402c0d000400c403045442c00d84480d00320450440382040740e003898000440759405254007840c440c1c00206031408492940c10f900d01d030142c1041e41040030500201c004501480186c0d411501c064950740300d802da42e800c3c08006410650010003984c00c80082c42049282009503031003c580790310300c007085480e01d5034a94584a032014400e150006545080202c0842c4e10350641401103000003040f60700d4080c9990100c40c0da003081e98800c1d408038200c00c0805c41455014001c0d940e02d0302e20f05030b04000f00301080c0c0c1e01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 61176082 1250 61174832 61174837
    0x40203010e0601080901110a030c030f060b0418330e0c0a0c14010e06011809050a020f01050d0e030406080a020a020601030312110c01020c1203010303050913060306020703030b010f090b 81
    0x5030f810050740e0741c04101000e00a50261841d800e0741c0e01c500b503480140c203a000d0090700c0c1c88950400002d2800b6100d1a0340800e40c072405064910004201d45820329054100000c015200130b00714403141e46507500304a241c1c03401301861248440481c150010481041012002c442d180d1200518551000411189100181c22202013800c0c908004404c00210702703003000c0b00c050603000d03000c1c1580382611000381d18074000343c0c4034102c9100801402015424281035400e5600e036220050a43d44880f02050061414030b03607a04e0104818074200b42000c456602c0300094030b1080c010010640c000040602131b460740b05880d242d000b00418802c0d0715110984030029030b5101d0520015040080111002c400f14049801803140c01031041021520342c2609a1194001e40c4110300f014818880c050010041040301c4040e203040341d805403500307402c0c00b0160050080f202003c0240000c41c81da90300300400000c0591014140d424020703500054050030410000d0074402e07042c4030410034081e14802c10050348c50072008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 61177332 1250 61176082 61176091
    0x50609100909030e03030706090b0105010c03140318030418050106052d09030f1b010c03080c03040302160305010c031a060a030f0605040608030a0f050406080612070f0f0302040b040203010e 83
    0x80082d2a15841c10b040f50b07074100503081d00794940400900750b4244107454010700490390190004000c2643e03550015111040c00d94401004100740043c41d031030445041c00a10381c06000f01400c540400c3e40c030300c6000d046901c00d030051000400d80b0040300f664005940b10f480e0240c140c1d401e000b0310b0000340b54903865440c28958040c103640b0740300d0001d6082c201c0e00a01951030079680a0216419165a041d0568688824005440c0d0240d00d0b9070110b04c0350340c403661280e461184c06484482e940e0700c6444018010782d20082094042d4070410303101141071648500984020360062000060300c648490005040e180700260075401c10203000d50003241d56880d0011500c3e04a000d0400140040901c02c03040c024050315403006500a15101c000520008044018000300a8542e80c0161092030701c1010b5034940141d001e281c002900e03840014065040c1026100c01d440d0084c0c0403946415030b100b01d613020010706030700440a1484481801c0045080c40c0c010392036180c000311003d505641c10542d405103082d20090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 61178582 1250 61177332 61177349
    0x8031e0c0403080d051b18040b09151e03030a05090306060a080d03020904090507030c1802040305060c09030a150f0e0307050d030b061c020304030f080405060a0203150a090b0405060910 81
    0x1001c0341ea032900700305031407903148a0050996101c001ca0601e40d07d000203c510180d01407414141070351200c0c5482500207101c0c003140c2c4192400080220140f12007038a900d000e60910501003003941c05940d030100043c0505104554641c1e0fa54615441814108400a4032641c0103006805080c002c0500c045200c09411f411460016110002100040c000d4116900c014065004828020003400382842c1448141c07081c50700b44503540c0c038035025050202e106610010307110386c1005000c0740d02c059140b0003d0035550030060855251010030703114442203102032412010300a655001c400e140314400d000d40e007407044820f000f442c10040f840e00c40301d40700d1aa242d8000c0800d0343d5441e180d6001c0c3c0d2a9015a400c661003000035103c68003540b00f00e0030080d8016281540420800025145100e11414074244a0342e44003000d0001501c0d001035484c040d41014007941c201c0c00301081c011031aa100d0041060040410322030104584551205000483e003005e0281401540c260701040411000d1028002c119032590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 61179832 1250 61178582 61178591
    0xf010633030e07051e01030507050301030c14060d020a030618110f09030312010617100803070b0a02091c02100306050a03030e0303040510030b09090607020a150908031e0c0403080d 79
    0x22605041c100c203600041c1e8417200c2045140c041601100007000322080030b0300c00300000d88036900c0540300d502091000400c4080044e805006100c81100341105560020b442c250410702c49030504000c5c1e030080250100002d9803070808002d042903481814100c4603040d132040102c0702901c01a000d180c4540c0d0000c101200c00016400c0d800d40341003080711095195140800400e503141d0b10010041c1d103a5552b40640d803c600d0700882c5102e120082034000312602a0019842d0800513510101e01c43d42c000d00c0803001c107500740f10354101c9489502d22199091102690020060302510420404652844600041510b04002440b10f0340780c2000510680350941007074580008101d000038a1840f0320317040300c1d400c61040782d0070307220b09901500001d44010084072000e0160391303803000071a03445d01c2c200e0701c88005a00030ce03c0c80c0c000c00d40c842030109140d4510300c000305205c003503922944401d034000c0d03800d090580b441c54080d00e01c0d540096100354200c00040c2d400c600d820700cac54807001c2e01406017421030800f00382c2d603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 61181082 1250 61179832 61179851
    0x61e0409020a0915080111090a0e040212063301020d050705031c0203150405151908070b0901020d0f170c0d05010305010c0201112106030f0f01063303 66
    0x40c1e4154200504821205010350200062400c041381c1c000d119640103903080113080d022000d400000e0b50584a4058a074207221440c100000d40c00640280c016a00480c0420308071114080c2802034074858002070304400031b132550b440401c400e120740701451900c1401c42c000c0c005906a030b0119808551400c0d520b4001d44451035401c006095100e6002c440b64880d02000c403540c0710445d29005144104c3c80c03d580c00a10001030414841a51011643d0600d0f241035005800344510740384840500d025192408085919220070070f0514000c0c8540080c4c030403c07808143e034116503034104415500440c0e40e1400901500300b0703100203000c0403c1d010b14041c0030304130000000c070081441000c0d5905c3d00d00840c5c042c0402e5039282401c07402004080c205200550814110303181c007410a008a81d26200f403422150310596060f403c907101d070720303006e800c07943d00d4000e0b1400340340d00c260108044400b901080c07000050380ea00d004080550540701c1c0000f08914005c00700707400b164150319001c01100100501f0080f468502c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 61182332 1250 61181082 61181089
    0x170a08030405150f04020a0603020a080105060d1409060a0b0d0302060610050702210d0f0c0212010b09010905150907020a110f06040602060108100204030807110102240a05061e040902 80
    0x6500383c2c100000c10104407021052015090180b4029102d03d070245071142822401da10601141e800171941304001008103080c410005c00d15000841c40002d4051000809145029002d40300129558000001c0c000340c4820f61245103401c8108603100b0542e0601a43c010f926000002c00403845507040302001c6280c039026a040f01c5810303500400d06d981c3c041c507400c020344a4000b541c40000c5c82d8403c150040c00c42c0780c01840c1500d43e000a9441c1d0090301101c41d070130008140e46012182c0065500d5032444602d5880ea001414081c0c99040c4011030702d0f00e0110f944020196403100d100b441214040180700805802103560b01d10642c001401c1c02440c500080483c00316145010025000f507c00100011880d0b40459282d0503a2605415038155001c1800342d2001d9010714000505003400800452000840071902d10b5440d00041c01a00c0a6580902180042409441035075940489050401101c61900d20a00350f1001044500780f041074507040800180c040700d800c0c2c0c640910f40d9440c5100a558 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 61183582 1250 61182332 61182343
    0x151204080306041506020f0c0108220f0b07080114011701060e0a05130b0307080c0609060a0306080a231f0207080d020708070c0b0c0615010c0507090510170a08030405 73
    0x1028007500e902da003545d48800030354900e034000c1130004a00901504514640c483c1a216004080400002080c00a00140d10b2100710066034101d500c0204108141c00144441074650300c03505840d100c030321140d0302d040d421601001581c01c00d02e0410000c00b0340c0050b00c502c105a0729040d5403a510700362014489440200340805840d0300700e5a4003001818000607074216682218a403803a0a07815102c03601d40d600d10003580c94802c1c0312650b174004400c0c440601141000d5002e00020000c0345000b01e00310f9500c5110500f0496040429100d03060581c485001e02a032140c900501c106880d001401c0b209c0c02d60303e106c50311551a21855011a400080f15802e0010000540d00115035150f821503803400503240c40046035020140440b80040143c01c00940d4103886001d6030000039110000d05500d6a1b102070b583c034800462440030303041c80070302104c00b800300b401004000003510000e075000445082000800c200551143c3c00320030000103003000c0c01c02c1c419000c2000d0220f6540240101c0e00d0780c450303181480c00c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 61184832 1250 61183582 61183601
    0xc051009050d0914060301090e100615090e06010906030e010204080303180706020615040f06030f0f0c120305040e040501022206080f0601020d080c1603050915120408030604 76
    0x2909221080060110200e410510860603480e0312402c2c964500e424510100d102e60322507840982400100554800c030740100c4c103500c400d90183e41c11104140c4022040b1036580d0031041000c00300660702d00101e41c01c40c82810250802e040016503c1c034007840000c000c001c01d40604010103484400c10750301010b00350151400703030440a0a41b0b4491a200b0b00e081c0c5c55007040f520b40385680c07140c040b00040540c0003080341405681d0402d55440318024540501c0003801403041c0210391a940d604000004c12038040745060400d10400a28a00703041e81e00780138002c0429600b00d0700c48008941403040002c4d412908075000c660881d0b100c042e0641e00e60070007500901610080d1840101047c8000c6201421520a0780945416403903c1001d03032111182d644840c0300484400303000d030744030001c0e260b0840d0003410065405403011140b03a14180d80901d1130700c4062684c0c2c9084000c02c07004120349001d0f10b0596a00440010f150b204282411018100b0302d80041c07000c0c0c03001e4840c040000200301e41d600c89400c040c821 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 61186082 1250 61184832 61184863
    0x11061302060c01060e0a0f0902030a0807020f040906050a0e010506010207050d06020f130602010e01020a050d051812090301110a020307030f02010213030c0302100c050304060f03020c071e08011401060c05 89
    0x200c5a0311752074031402e1101141d031220b40c01c2c41d202446100c028940705070300601d600038000344180e42035907072450790383d6212100503a401100d02c440c907000f541d0765009540b080e5100c0c00c80804c0b2801e1078446d050a4881170780c00c050003641400c003000b50999000480710100c50302201d1001418041e810307e10000d21910b00c030403100e8003000400700c6408940c407007840100e46d085e0f030080040b00203d00100e401c034003400003404000b50781000420180e45207504401e4015030203400591b010350301c07001c1c000d00e8041d190700c445011040209401d61685428402c1c0d14804e120a03682c24076115940100a49070b01c6002001428850844a100c0440b0300c00d41c107580c2400b41500fa5618616124200103000030352a1000724465514015a158840e1007100e8296902d94481d00031801d250508509a410f41e6403c2d5102c0101982403150f514914000c124500040896900212040e0501958107800c90401e03003218115070304100745005042000001c0038110b1340b1510303004404404628086080c00c4204a4403000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 61187332 1250 61186082 61186091
    0x1020d0c08070f0b061215070c0201030e0d03050603010b010201060b07061d0703150c0e0a0e0c070b0406050103050c03030715051305160611070602070306051b07080c01050711061302060c01 83
    0x4022403220381c00d0041d074085504800c1840d00c000c035643e0751030b00487d4215003102e40030b0128100341c0c01984120700161050401291a42800d6900c4c1e00e0311b072000c0b2034400000d0302c9034180555400c2c20721801d81501e03801e20080c0541401d00c140810180700301c002c000e0000395212601242418522102c1141c00300080a54010940d0390400ca10b2a8010b00070319014186400501506030780a5450642d686201a101081032890101d1802031107000410450460134104100000a062481c03514880c030f11a40c400951541181841868500034484003800ba50040100c0e0313010406518001914034002e15003c1071907622010540741b5001e0300314004045100386101d01181d02d500701d0342c00040e910f00ba941d881c1000310202806a91300f40754030845000d43c110f60002c3c070206001d49c2265500c6a0740a41c507460450101d03c40226942c064442500c50a4020070a00841c09080c080c00e500054140f406a0b04840c13010842a2030f80c1000d841d51441108a124010842d00c0304000e0b0b9a440342107000810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 61188582 1250 61187332 61187363
    0x90611190c0e07022503030816020102090301090305122a03040606051002010b0111060c0d1107020303040303020a0c0e06100c0303090506011203081b0f181c03030b03060601020d0c0807 81
    0xa559581c00700b01c031180c82c1e0744075170180d81d440b041c03003113400440390117a03070301c044a071101061040c520145822410441d5020000c071001c60710240942c901091281d601c417513507014501510514a8030160052039400c4442e00c103141300d03d0000d10585c0100203058601503403615a4607103540202115803103503030083c15489080701040c1d01035011210410003030301c07403444440c1e60f003a510361078010071150200604011711100b80c190039558480c207880e15102e261246008501c5d000a0f01c1d58200d41c1c0b0480050f40002c10b100200720f8803aa5890003407a00003649070442c10a0000600303440501c8840d00100f10310724000f142807500c00d402c00d294880c0c0020541c6d02658442c1c1c4881c0740c03021003000c00d81c00708103154081401410030442d604540d034041c5100c00e081c481d860182c1c100c41e510141c020300003402040041c2c4410781c2c4980340c07007840300c220481c0c50340107128510700034040e29141c0d840c05119400001c1042001e903004696080308111514091076003241501d406c1d14140a201c1024042100c078180d1304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 61189832 1250 61188582 61188587
    0x1e0203010903050408010507030903120903090302030a080301080f0a0f140a02041a030f0303061e060f0d0213091a091803030c040305060c04030f030c030909020c0607090611190c0e07 80
    0x200252880d010090155564540c016000d5600ac90f2008000a07820a041c411442c1d4030703880006084e1103480c0004955903280c0000b4a05014642d0580d000380300000100441901045014010030840c1d0250003000e0194854a40035001d0250280850b101c6d40c804903503840b0140000d0700d403254001d01c10844442d00c12040a900008076550178041e10500d178051940c9039000003501d208110042c90034990038451148034514035240c030405c0350080d40c14403020b9400c60306040074002c0c05112810042e250145401901d030200c6032984030300c1c10303603191010708079036040f04035003040241e681500c80342180c0e00d5080120024641d00e6000c1076803400f01006000c032111808005008603402001182e000c1e8450303400c2c1502d1b600c074a01c0001d0039004040d00c0080020b000e03c40c41030720746002e41800c0c214030740d03103a8091b000d9070b2012103c442250046000c20610bd0340004411000e48041c1c40d104c00614400951156180070145d0f1028480c183c40120307100f0004000183c10241000e180034503c0c505101901 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 61191082 1250 61189832 61189837
    0x50c1509090901150501021b040e0f060a230c03270313090c14180609130b010f0906020d11010605120a11040b01090510030e0706020304030506091204031e020301090305 74
    0x2108a0400135000080c5940c0f0003d03111811007001d5584041340c0c1440410040240380c0c0000c0c0440e240640a0890340c010001c2c40058401c0d0803121000c9118642e40740403480380d45a00581c0304c8008103400921040300e0105081c0c0780d004c1c0003252172201c0c2014080104001d4210407611100d00c2c0310000320180344c020000c040c441140c3c922081409000300c1c81405403017110f01d080fa24004d120003405040c1d070304c0215090030a00302c58080d1205140c03002c40d4000c52111a01c07195154825a140d00801506581c090742e500c2da07035501031600d8001141400d9000f521040c0c1140034800300403940c0900301000c01d0030b601080c0100002030084c3c040e80701d011021511107001a9003a10390080074840e00482e400d160041d01c0861030165101103045042c1000c2003803049940b40300c441007507603030703484100345040c00c000c0c4902621180c0c0045445074a14504540303040300052880c005034010440c4503461402c8602901c3c2070320341c4110f503d4085115490145200000c000000c0c0d415030a040c114024035400900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 61192332 1250 61191082 61191101
    0x5180a091d0c06070305180418030f020607021908160605070809030702030606060307050705060103150b0406050306010b092704031d0d030e0a05060304080a030506010c050c1509090901 81
    0x3015810388950840c540d203580e1050070321500f10300d0821020f0300080c422401800107030f00500b81a414048030030049411650744403158100e854071a100c4009060b000607808980c1841c42c03008149a2600c03c0009494890581711a41e004842c01c8011342000305c410262051500a800004a40d12490404501030b08060ba40100486c480f0b4000c207802c1c0d100401240c100c280c0281c0140001c3d01d480c8140103030340e0310041c40142000000c1c401200058010300c10203001b58003800002d4001a00e034030780901100c5513200d50314421850080100705949010450a04542e031407480303e1744030b140032030129444205c0040349116031128070591000f6117116226082c040c4d4042e03a02d5112081d8142541320b0b5a070801507170b0650004c0c4501c1c054001901c107100040f07402001034287c240141e514000711f14280c200b514100c850400110b045142a41d05104580d480802464010070f4020070b526900d45a0700440c88403409824041c14240301702c0c0740203084551400019000025514008403600d000300328a01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 61193582 1250 61192332 61192361
    0xf030402120d020604170d09030206090705040603020d0f050c180115030207031b1704060201091406100b030c0909011e080102180d05010e01051f0608040f0305180a09 73
    0x1124042000340050341e90b0140781c00b80c004103503907141d079195011202510340c3c2280d1041410810811a43c009010b0006046e11a8000700540c0c18900c1b07038181851410740210307001e103160170780802c007507030b00d42130000342441e00f01000060b00e212a00742581000c1520329240d40007229031201491447d0310b1201b090407105010900100c607002c50f18101c06038459402c0180005548001c1039282c160b580c00d00c06501d600c0751000019000f4200a0740840780c00c03d5000d030740580d644103981018000041d07407481c60700400c54050141d61401400c0c1c00d68100c140d00541e07013115004000a050040c81400b11624880010100c105079a0344071512049000b141000c1d601454000c5400204041c050007519000c0c0d40201341c840c3c40c0364041060141d007110511068805640343c4c0d00c42800d0101c20b11400340958103180c03090880d4200d040f4441006001e5a101100300b0080c401000041140341c06030000d4503a0500e4a42d0703580c000e007841c0501d1860900300b456407102e003518002440c3c941903072100322415600f8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 61194832 1250 61193582 61193599
    0x602120106030c05190e01022b090503070806071b05060f190501140f03100e01090309060507030905010302030405031e09101b0605100f0803090a0b070c0b1303080f030402 75
    0x40700441c1d041c011703039240d22404000e40d1501500c090054055050486041c0704840d0042c00c03807107040604440680e4a82110410420028040c41d0b02250401c00b4120580092101c180303070240c3c1654890004103d4001c20054490480441c02c0c0361888075811a0488212011421701d41007071640d03080242c8036144114071000c072200c4401d505020f01030480b41820011038038001114203100341145620045581340c0a4030030703100001e100d20b00c43c084140c021000000359110305440e000d40003080c113800600c01c0c018180440700000b40c0c0100aa01950400e1a0144e1aa1139034581285540112210825a5200425010500d405c004041c00c8560411285c6a080c1440c1c603205444000240914a10452414180700f020400c0c2d0380101e40c0090509680c0d00025503136516690403d821900644000d400c0000c5c00081c03032800c403c150015100c02c20070103140489550710000c4da5800d605c20f94242010202d128075145150b20130740705c010343e009a5a01c0d034030b510202800c040c1d0352040720204c1c441d9141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 61196082 1250 61194832 61194851
    0x3040e0f1303080601050903010204030f0311070819030e03030d090c09140f040507030b1f090605130c030605060d0b03070b040b12370501050301020901050f0d09060212010603 77
    0x8002059006005000792115020300e9914200d80381c80005159034103120382004000314a071070920082c0011800ba1251704c10388030882c41c0c0144949424010840d5561042405004001d03000c500401c5044065143d11030651040c5030039075460007506140d552600000c280d5200d4101e135600081c0d011803203150107000b15a100c003c0c103000c840b030940b8440368200040c0e0010704113203201841c0300d40050080b8100c40041e6130320b81c2c0302a84220f084a4040983e40c0312004d40c24118201ca6440307018100e0b1903c2405002e00304408648010042e6a000500a45030310741091018080e601030b0000d8070025000303c0e650030000d21041c01401c001c3c03800038040c0c801c5c0b43c0700040f000c080c002500c041e542c10401291802003450754084090801400e6020f55040000794040000710000c0048414240703200001039408038a00c100049030016440345000c0c0e40100000d0441c0c0c2ea01030103d130305549810041d10f40720125007104800030840014000c03c03241c0f00248408000e08110042e5040742c0d541d43d002d000d5211f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 61197332 1250 61196082 61196101
    0x506030702010e060901110d020d0212101d070c0b040c0f06110709020405010206011e08100e0609010b0102030901110f0d0c0b0c160b040212010504120914181906030503040e 76
    0x900050221a8003040c0023082080f002c03a0010500203410a501600303048010700d44c2482440b058845142403446880104030301200204018119015001003000074580000050003d0340303900030042c075201c8550001020044118590006400f152040c0c0809580f613142c064007510486803420a2440703030501c0042e0440090007158195003069000c2c1a190740380c8003251505000006101948100b9039102280c211420080b58004101c1c0c90b80129640030303c111900d041c04005088044a40d0403c0144a106d0760000201d89082a080c40e1050010070581fa095040108032010fa002501940340207120042d03100c5054464075002d810020000c2c0c90711301c1042c503280704016500c213150b212002c4c44400b040b08003080036032150000e07040100201500e10502c0c01c4800c00c882c201d030030400c441c0308403004540c81004100982078002d440e070a500034500004030140607a0000c074010000c10000290306150a101109014200d00b00c14080b95840385043d5449800034011040c040c81000b002600025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 61198582 1250 61197332 61197341
    0x6090305190917060c090103090c030b0a1e1503080310080a050d021606020d0e0111030304141605090406090f080406030e1002180f01020c150306030c040203040218100506030702010e060901 83
    0xb40011140780c03904030f10301b0040d00503006840050310700e10800840080031a034400281c501c034404880e4000b41d0440c4103a4141614504250350500b854645251001030740f85812405080c2d9800014482c1c980c1c4e03c10800c82c1440e01e41e81c11200450050064090401c0b100150301c280c2030700d880d025503140c91081142c02003489a04d103e5517005030301684000103041d0084010380000d042c180f400e0300d40c035020a00036070325641c0162400c843e4403550b00f1081140038018002c00d10300441031168401c14514000004002d0071020b80040c02c110354402289080109001211aa40780e00601541e2540e80d905400f80042040850549040c0100807003640891981d1084502c05007a03e044592200c12071403d00c80f04900088801d410741c071034404001e246544200752002c050b05041c0c001540ca1401d103082c141450190b45245010b2401841070200582d24800d1000260403946070b0350001c0c2d6600a440362203948140c1c08142c00240000c2072052595041d0400001040041d049075169218140143e0807078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 61199832 1250 61198582 61198591
    0x50f0105031e0a0204030803010e100f0b0703081806010803130e0402153405160308040509150409030c14060405120d02070606080a0b1e040609030519091706 69
    0xb096009289402c01800c0c90269400800040b00141001d450b075032104810741c420703001040d001420720708210540d405190404054003e02210034074141c5801034840c502c1c080c0742070050902c00c880c40000c1000c2404080160b084142000316041ca5075610300303190700c80d4001d0807920a0147d40b050003080201140310154041c0364085c1007040080c182c42c1e00315405800c0a03102d1030003030036088440708108010f20442140c04004035142e6001d94010301e0002e2611600300611480c41c03034440020008110400f054900b22071050700c40754010394440c070403040420030103040e159200d480d0181e00d00c02c0c940d0201e4041091403048804040385000025603e0b518035007150002c0065221000b486024070740e542c058640b00684442c090304140d500d640d100107032121030b000822240e2215041009110494007840e070000310700c3ca04034240c10082c86c3c905019001c0200090035880e180c41c01c2c0010584940304651501c0c001740d88244881d584001c000740190030700e00c80e0912201200c0454030440d4408150b0030700a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 61201082 1250 61199832 61199851
    0xb13050303040f0204020706110408070609080601050f01090b040320030c09061002070f031505070c030c0b07090905180f030903030414030a05060c0d060603090803040f0602091207050f010503 84
    0x540e42d42d59280050116030031422a04150240141d00000303180e4000c12030486015071071182c03074500707045c007070783c9808044d0780031340c0c01c03c82801b008001040c80420110b0549800b604c41000c0d0b132190b000162461040d039807101e07003142d600160010905c0290000407148030001c0012038000842d120826a440796280c0107554060342e080007103502403800007901c04039109940191038555913562101d035112241a4400d035078104420302424403070881c510880da031140c0b06081c000004003190b10000c4c00b40d80f110b80300070006030b000b40106542d1400750b010800140b514407020302035403418448a0010701e08081120009101d4074401ca00310401c00710030b840e840000070340210b05151800d060b2071040c40703403240180d130540203045880300400c00030701c4070610484509074010342d02c1d40b40c16402400c550752503019034100340c60b06011030001280401100c0c0c01030381201c000b1426013054104000244102800158040600100c1407d0140c01151140880b4012a10f000d000070390000107507014401100d24025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 61202332 1250 61201082 61201087
    0x70e0a05090903031f0b073203040e07050f0f07060501050307181e0212090d05030420130c0e0f04050103080301060c03020f0307060b030f01090b010504020a051201090203040b130503 80
    0x1111785419010708080b803007031904101d181e860b40c1c54001c42d4801c0c00142d1360500c20141c9040403860801d09090307046044201401040d0003000d01c03907103a002c4c902400b6034a41d40c10001c00c5040d4401c800751035400f00f0400c02160340d514490380c052820381c0400e0085800030f061600001c5d0a1070041038003801c4440158049002143c1050741078010007001d065840f030030701c1c0f0540d6400506224405444a0071100320300076402c0c207042c1c10300703403400380301000795420402d080042100080800384400710851074810440d11104410002503014400c0c00c40714030005282004011100742c1c00140c800c0303003803019507641140c10142028081595024040981180c404100410403644210580760b1040e003e44151744c0c407001c4c5c041c0c034242103a01520040c3c410340d84851900c10186024483c45035102c50300b000030132031a1042d40e42c61905040501c6054840d42c0c1c0401d0640e1f9507405901118240302e02c4020022496850714a50b10081d041034500780c421458450010760180c20a041c40d44a46400800550 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 61203582 1250 61202332 61202341
    0xc0809071202060403050706050306031902010f050c01091a1801050c0f0c0a140307060509010b01020d0e0607020604090507021903050922020703020a12020c1503040501090506070e0a0509090303 85
    0x1218208910000ca0f000b41c2c040000101088080c06044098040d03952425075904000c02054035200b0140700e050118200302e01038074010707a0080e07500003040c4540c1c189541c4540180c0384407401028401c1000c3e142401c90f001c014004441404500c0c869450040b00b4480b21000185c2d0600f210b0b4210766002802d141004030084ca8080c0c0310103480050440c03400c03100b20080c5036551b03241c04c00f10045040784661001c101c0200b08002400303010740c03041000008000d0341e4003441c0000d41d03e10114000c1c900344100343c40b5004564a0303200480d0115500501a150340d2071313030703464004000c10045441c03c0040c050760f420b0405001000d845054000e400da0f4840e420314413204104801e200041d1203500e8500c1c23224248182440701c50000e000854083d40141c141469682000b103032000d00c03c0600021904044201d0780340c0d03610483c3e2600001c0c0b0600c0031544a541c0d52829500400142602902501c035036820003d4090b4440b101e28041402510624442c9944001784024000192402c9080e03400900c0000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 61204832 1250 61203582 61203599
    0xf0c05060103021207081c082d25021005070207030309060e0102011b0f0e040b0303180303070501060f140105030103080409050402010309080301081006080c10120b09010b0705010c080907 82
    0x1500c2001c62100360b491503544c03686ca85140c5440503c01122440e10303440410724041d001b5003000d6000d09112080b1408908003005030001e14140e412009000c901c0d04086102c21001c20b281d81c40058039440f650011000ca14400b030b40e10102c0e4a0a1401e103818000010921480401d07420212681919503182c1241001002e480c400c0c441190181159a5403d8545440200c2e046002d49040d140d12283c4041d0b044010080c0342c8003100003103901840c00e168a01c1800d071400800c8600d1004400b071410021004000001d066100380d9102a01d25824039102042d141c2e9101e1910085880302003034810808012001544c11b03000904c006012460706100c00c10141010360080c82d4010710524001078558030b00d582d2140c0c0380d0000e80100303045a22032400701c44004030900c03880b80a072001000030246a03400b0000034800d03001d82c1643c0700400035400032144910f03400d5081280741c5440201200c82d90741e181d1603807500d1900200e806032030640c00c01800e2700b040d0f4043c5604602880c2810041e109403420a501d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 61206082 1250 61204832 61204849
    0x1305040b030d0521070f0e010206010501051801050f0d0506130b0112090302030702130b0a060203041203050a120929040f02150c0708070302010e1f0e0a03060903030b010f0c0506010302 81
    0x11400b9000b901c2200040d01c4e801c480c01e2007101d090700c5d5012051035240004148203040c43e459410f56101c02c0c01440300f6030308401601c10664500d91203120070580200104d45a00a54640803090f090209464a4804403a000f9601c038290944083c80c8100c160300448059500b410300d0ba5012902c050310000e111905a0442608a0300900449203045116401f15620740a9040e40541d0a69a0704001c0220f207001d8140030000c14a51000303506180c1800c03a40400d10010300b80c000c0071300c400041d03102d03036a5008803c0c900340c0c403034121800c129844007410142e4039604160345040601d41f0060034440064440d03807002d80030765080701440003802da25a00340240340c3e4155000040b840781c140a0102140401c00002010300300325806005813030315510024080c00d44c03600010780708291110b603c0c010340c10f00e503000140a080c18074158103000200c0b4003080c85210681c0002c0d22075420004081c080c1601030b00002440502a41c0301d400035a462201192200c19600c0001d0140e080703200104094902a400d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 61207332 1250 61206082 61206097
    0x1407020d0c0b0a020a05070f0605180120010902040b01033e0c0a02100503091504060f0f02070c0f08070308070206040807061101060f12060f0b13021305040b030d05 72
    0x2000001a150b0300d00d811140c110001c008016401501c02c981003150501c043e400400305003034040c42e03260401c100a4054001e0700901c2c2d80c41e500751090019a684100303116005501448040f49603004c0014031640a40000760041c0d0055051500901b81755200344101000501c00301480030200a16005140010f600498a15032803c00c0120910114007400000c4ca220542c4100070104125144140804a00500c4000342400303001e004100b40d5090214008418459604903e0303071507a2a440c15070b008298000d03180c03c106150024100b64010b080d40105000340c040e80c0c81c0d45815650300e800e000503151078060002250002d900800010711000c000e40501440200710354103050712191120715050b12030780010001100d680c003160480340d0030702c240e50140020b0303022022054184200460a00000c02c0c005242c141d5884d5003400030301c0303640c2c005c40c0300d881d00074003094089400c80c1202001c0e4101060f041c168401c0030310002454902403245503283d20015007e4480000480c07000d0702c040d00316a2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 61208582 1250 61207332 61207343
    0x10905040f090c14041112071407060906020a08131502090409020d050106031e050606130e060705041701060510030905031306031a19050415050909030a0f1407020d 72
    0x244070400040c2c0f0800a8009004071070600410802c0032801c1000f955030000010307000703500400446400c011203960290b44001c0c1420400204101041d00740040d120f001000782602d403811030b10604102aa40040250701c1c0340c0d40d01c90440b521401c034002c03541d05071008010144c41e41c43c1d1680b144405c0c19000303440141d200400004050030503801050140304004021075072030755284001c1c0100b000b50b01007440c8025400d03484a0380c003052650b500b1341c2c442001e0045441070030620707140700407034441c0d8100207400c001d401b01703407a9a0308105074040e0558100c0d000360f10348040e02c6811500e203120144542e400300c0e9802400c0800e042d24160095006003030702c06080d0781a0008000001295501d080e412004213a2a0b60000d00c1050921000d007030440c1aa000511849000d803400f000e80c2500400322050f102c003110700103841000c0d110710755560039065000c039811888140c1000100d64012000c3d00c560807250315204119000600211200c4006407240d40d034070b0300140591000b40c2000d40c149454540b00c5c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 61209832 1250 61208582 61208591
    0x30709080309010c15090203030d23011a0706111602030c01020d02060109090c05060403030f1407022d0409080301051003050601022509020417010c0e030c0402070219080607080105030c010905040f 86
    0x58000c03a0655112b05107602500b40c56184241c4601008104017841c035021842004180d4146058a60380070320200c04203805800100300070f400e003c00e42d0311407610480d40303010240d590000340c02003007143e100104080e0310900512400102950000c6000395190100f40d0181c005d0780e0070030f5910802061402410340f0f03401d068440c046415100c0c0d100400140d4006c0d01c0e0280e0340001d890004012101144410072102020302c01c08005861b205010400c504948c41110809100200c141c10300754108041e0307942c002c0c01c103000c0300f00384034500340294140c40042d0750710011140d0000c010f50a0b81c8003950f11900603031000041c2e00365100c040391000f0710101081325075042659200c4900059070010382103100d0f0410f0030350124803946000d00c41d058102c505070801c1220394050301d0000303845481540045002d1500010118115030f550b14030514203c1e10f030040c1c030190300c0d01c41c14823030ba55413405c882d04008a00e0800c0049400d280000b140c2c01d60a070142d40300305180741041d042c00080d051820310030b1300309901c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 61211082 1250 61209832 61209851
    0x70308030103140d091401052b0b040f0902031203040309030804171605060a05070809040603050f0709060503030d0c12050c0a03060f0b04030f0f06050903030709080309010c15 77
    0x9400214002c500481030056080c41034401d042c00c103000482071a090240160007046495441407072106601000d00b005c1b0b40b55440741001e1301450588401c4407031008203005004005a199611079281e001c0191400c01c0f01c0c1017000941c1040b10015540a540f503805612007405018240c0c0c011030b8018807c6c40c01c401c00c6640c9580e5482103401503008130700c0c40707142c400380084410003c00103101814038030190607480c40c2c0703004042200c611074076001000300600018100b050003c00400c540b10b0610140c010040c0564a013003054660f9800c1d8040541030196040014925038280603060654100601540c83c20000b900c0007401001000c00910610088200804280080d8032485100340381104026540344020704c00242142c0664228150841e038001c4140706072580c000984040c1c0768402c0b04034101c0c02590501d1380d942c018683c8001d0070181411300b085151100800598010240b5407174164005450b41f038241d459004129030b0500081440c403010000c03803040c1c418405a0500c1d041c00083c503440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61212332 1250 61211082 61211093
    0x6060f130303140703080c030603070f080106030201080603070605040509070c05010c08070311120103141204030602090405060d021e010915020303150f010c0602031b030f09060711031b0703 83
    0x2160a44400148039600c0c100103154101115650710040d0b1841c0c0d03840e0150568000c1d051410191a07640d6241c004030010300c5c2601c1c104120400b609015100186050351216028042e04160200f00e00054070324000c10228200040c41106481c020340b0340070300b094202001d03c403500d40000c0034030042106000c0c040020490a01c1400300c4000b40b6983c00341c40b440d020342c2c054241d401d03031807890115220410280c554035aa090440b03044d60392044400200c4040487c00a1070b0440081e600a14000005000410404c0c20340c0100300d103072402d50f410f010715170340c0341c0810101c1d80604101a4005890030320203e801c050120312011002d5050418620194942c08000301c070150110150004d03a10000c01e01045009040110b000d004086440180c0c850f10400000c0800d084514010a5141c002c80401d0402c0700c11041241c0e8500c1d142c03d0b05440317180031000d1068028003a1140c4025025840105010354442d194161900c24030710011803030301c1010b814901841c9102d1810318490300071070720080000361 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 61213582 1250 61212332 61212337
    0x907030f021c0c020616020d08040804170f0714090402040f110a02011e0c0203041206060806100314060f150409020d0c080613051c03150e07020c0612010b0306060f 72
    0x1100140024600c5000307494008050200100890b0306c412510885da40020084041c81252400c80010780300c0b840e00e419280140d070403084201d8000100312a200e240010040141c6141c1000c40341c0c46076441254010503405000401d0b00300041100042c050b042c0303504a01c0a01003840740008080300825005801c507040140d0280050351100040300f030030020240c180c04440c40d00c11003080442d00c8030070040c0d81c0e0300c00d42c4150078030031650480340d406103c541e0307110100800b0710009803503841c5803182010148103458007080710b0000c0005000b009103100001c0251003180c0e41483e0141a480301001c10b60011851481158000c1d01c481c1f0000c0140c46010348842e059201c0e440b0041c4a509208041e8100417000303203c501c03d50300851291010074000a4181c065031091a0011040700c8000c4049000d0a812040f100071108007000010f5090b0307401ca1458840e1240303030b007038076040350b920000c00002c1c2c41270076044680c100b10400140110711080004540241000b4a0b03140380c0134078074101c030540c1d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 61214832 1250 61213582 61213627
    0x1020309040606021b1801050405060a0e010f09060b12010b09040902060706020712110a0206030601030e03031f0b07050c12010212010b0309011409061501050f0c06150109050907030f02 81
    0x117800c40d49901c140b11030052a40411901e080764070758a0402881ca91001201c414131540d40f1458480b00420009c0d110040070401510fa00f950752059582c40c0c80174036414241c28170900c520649070160001c2e001c170413081a900c007a000001000035991925501c02004e8101070f40b520f074015514134990b00181d13501c100070300c07007140b04500250325102c050034030610070302044d8a5141404586084c5039074800d40419061407403541254105e03283d4651000482c0240070321448901544400400e0001300c010025420300c03c040c0c1180b054001d01d8039050b0f0b0b14068012150000e065070f009004000007031508683d864900005440014101243c0f03412500d4240400c3e80b044058903030000c1030061105e028001e90b1360802c43c030500c0e80e1007418601c07945540d5100086c440b10780c81009102d0301c0b50360707841035080324000b0110b240c6094480d8000051561902000c0e40c100500c3c1d034114a540c10b507540a400840c1c1140c41c01004013986907200311301034000e041c9000d40108510307420420608450340c90500e07030106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 61216082 1250 61214832 61214837
    0x80a08090102120c19052d07081501211410050a0605100804050309060a09030506010503121204030e1f030e0705031515040c03020903060615040b0a050706020a020105041a190b01020309040606 84
    0x38141f013801810f0502c140c2000056400046460b0026448544018111021151001550280350703140c03000300b07031041c6001441d0b800d4690313600d624000d0005401740e00e8510301c80c0400045c0c030740c502d2010403180940b207080d030440b4400b4640240d99000d24035032035000b800340342641c1c500010040054103a82c0141c0c207070004900d0040080c810702c6400c00c80c03280034040c143c0042071100d509a0255143c2d02a54001d0302c21032295400240030184550514501c0100c040c103072a40603100c0859444121240307498000009203016261804000001a64011900007601030403410602540030192444020a1940008407030694400d49442d18030516110000c2c2e0303580141c0f2460103404143c200000909454451640b140340124014440300c2114125021600030356541e402d140020fa8181c000c0c2c84010300800c0c03021a042c82d1250301900710920030391040300907210f00150b2048007d10950b0544008400c0d84c1c00c0a0f1040d000141d65010803611801401240e01f0840b00c80002001d0301c005405c401c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 61217332 1250 61216082 61216153
    0x90601030309080c01020c0607081908090c010201050c0307081305030307020307120305190c0c06060b1209030a020709050411090414010f0207030516020a080a08090102120c1905 78
    0x745580a5000b0001d441c03014041c010206031940000c1d6141740c030000b120f00c51000004c01c82c00708440801242c00900141161010040394210080d088400031685201c040c000c04411040940c418403400d40b00d415070440c028203640fa01101107481100044c0085182c01c00304081401140040018602c6002c071580110740c3c0e85070b1468503142401c1d01300762a00a040c285414401c0d41404030300d080031607412400000442c0000ca0390101c07100b0998400c042d102c1c601d040008100d95122900400e8100c510441c86a8540c50307400440303589126148158006810500d0180241103043d04010b421a00490100a083c4400d00004038007580603a01150301c40c8404a540c12008401c0c010320b4600c02403076030114201425620058440d104e4107981d04468110f21a52800710354649644401801c000d0044030f1080308103241040040d800005000c0c00f5208004045541c0c0498404480c0a640300b10090f0a168068099810301ca940003c1c3c2114240a41a0a26404807020003c060340b040e15400b4002c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 61218582 1250 61217332 61217339
    0x509010225120c020306070c03120204030507150801060503040605040302011d0d030515010c0305090d050a080a080c09060f03131b171605130b030d0c0201030e0106080607030b01110105090601 84
    0x40140c00c0d002e5031409004000c294030026a80100304250b20242c2410300c17240c0d4442c5446d04a03490350003e420040140d10224011003405030000d440025203c03842c0900801d00c45c02031080c0c0b4100c000744a1b8100091081001400260543d080b894026200303000204406080b1841c2d46002c0c1016503608241c0d910a0622160b41c652500900750004841007841d500d0000303440009215003008240a0140003001994101c95103131051240b000c66048000d8030802c00702ca01e450602680024540c0000074984c0c004901da03040742500f22500d081d40149054540000b05500f010780e5000148042d280601b501000c1012500082040610000002c228070883d07043c5a08154007091815503400241d03c29020004022400144007003600c0044070307103100441a07204003001410b0411400e54042c0603940f03056000c0c64008442552562003601e003404039003516200359003203031428403070256a9805a000f00e14100d000340c2c444071400728103150103190040c08001043c00d5440030380b80103c06078070040040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 61219832 1250 61218582 61218593
    0x2101020c060a05060f01090b0f071703040b010305060106020601050a060f0e0909030405040e06060904060e031308010c030b040e070b09010c020d050c030f0d021f020d0e01091511030a0509010225 85
    0x1545c1402401c064a80c5030600801c0700e40d82c0116107400c041e102c4001810002d100000c41c070215406295a1aa03070b50349001d142070340708602c0030702c01200c041c41036100205500307001169145c1642c80140400b14110729080003103e03000707454003040040c070146000c0608030f42c40c0d6048803841014800300a580c0d82d480d1209100841d0340741d0f00c1c0c07504a40c00c09170520225a44690b44150080d40154001c40c080c81000c0d682c505501c2600001400f401101c8030006140310107402045084002c2d4808003c6603042034148070603190038070245501c0b40c0010340c0c1071250310f0510001d00110030040c904000d9501c65940803d0070003031101c40c16613007684000c2d41149103107402c003c0f144519000704040c140303504254501a43e141c442d60000360307141c007920718060138040440c1d050380c42100409506001011407000c8481c02006141820303103a0b8055845000e0030044c0d54041c10b101010f08443c90361a69030742443c903100402c00a080340d2040d540030003d2042c010001c01044071400c00d64403c0c100a0072451914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 61221082 1250 61219832 61219849
    0x70e030c030d121d0303040606050a0b0301052101150803040f0911030708060d0b0f0921040b160606030302030a0e0315040f0507080d020705090a0b2101020c060a0506 73
    0xc0c41c03107075110b51019100154400500700703031544100340101d10b10480c00d04060005096800400042c070010041209021460300100110751064030f414040304c1d110030605540d417200f40507c54100e01c000e81d03c2106408294402c5044004150000455001c80d0071001c0b16114161700c1104a6400882d0a010541450382d1100082610300d504205890502012803828000100300070f05114144000502d543c4840c5803100005a01810803070152a184480345003810003a10700401354820841000c264106002e4100e80b01840c088401c1c0c1450b10788601180f890307004800c001041c0d01003591450010704075004000103140f081d00555200c400c40c0c00014001c0020600e0b04d0311a600000001c00c03070072031042829401a4228809084420703a50911619080310350703204070518458629200029503010842e40140c030001c58080c410382d00c0b142500301c180c46403605025400480002d80a09100e900e0154a0b4006a03c00015080c030000107041e82c1800e008aa0011071709031070741c08002840c81c12004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 61222332 1250 61221082 61221103
    0x6080102041412120304060203010e0f060901050f01090b04060203091509060d02070602090316181a090601111b041803020a1b09050405010e2a040903030b0306070e03 73
    0x85007810b1500c042c01d10349492021005000760444411003408801c28403c12501240009602d9900c3c1424501407000b0747c03091003800d1194440002182c101443c410803140070b004000d00000b070b00d074242420080121490200e0b1414001e06a070000780c4e02c0b0f0403101800080c181e0780c01868580d128002400308100741c003960301720620b508010b42e03000380c1e8896040c1c80c2185081c000040e20792943e1302d840390091041000c41945807103005006000c1040311350801054038240f40811046046502c0080182c0d000012103405140c02d81280c03561a04290140661104052500d41705000300e440b17a080c100700000d4100c035071081f6000705500c114203260003001100c03400502c100311b900c015510005d48030702030004000c0c003016840c103018500040349181070019050180b801c0169040c585030148c001c1c03c00c0c80d809240c2d8003c14100048031000c03500003180c2482500c51044038801108100001010200d2084040c142d1310a05403072145c804002d443d102c0d01541d00c80d40142882c141c200f5240407507012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 61223582 1250 61222332 61222349
    0x31c0201060614030a02030c090402160302010b01031a060903120310080d1707120e0d0306090b09071d01020a0c031104050c1608070c090c050d0c050f220506040b04080106 75
    0x714030502d04010b41c411640d1020545e03c00507202e484190303202d03296100d050046644240085295030002500c050001c41940c840e030002c01088910b040150155049542c1000540442001c004410b0400c1402821f803001c009058907001030003503d41c0c0189820544400040c040000b00c10300c00c4a104000b1a9101410303400d0a08040e0b03d000d04002032084010669404c205440c8440d101a040c180c000c0e00610000c1c1081c0c4110000500000f401040d142c07064030303089400d02454445504000300000c1c003070140703907031002003010036900030414152030041d456045114010004010545070b841e9040130318400c903426041c541004080005907a405000800a510100482a5101c5d40e6000050b0300315030066041c0d80302c40b0303039060202d6900c07143e03803180e90a241090b01b04114a5400030091030403038a00c16042100840c01c0c042290b0301e0040c4848111000300401600400c0110414000100301d403006884248940740c1c0c001c0360b19034225034010300300d40201190900400c6c9080c01010040c1142c0ca = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 61224832 1250 61223582 61223597
    0x60921050708041e0b041d0c040501050a201c0314160c08040806010f0807060806011209020d02030a05010e0c03060402030717030c010c0905090115120507030209031c02010606 77
    0x3519500b05601c03da114110b00308011007070340410101028040710080c204a69407940710741d6070f8040c8052010810b1101000c041070100041c82c2c00b02242c00b9034042c1c90040e540c02c0e08060a60740107481140700c1030400c4504422511300004c00103401c000006000c11014140e05d0345852848000e0182c5204000c401d00f107054080030002d000d100e10b15242021f03200751a01d0003010040742040c004901c200e40186034240103840001c60880c03041c0329a0402c41c0c14210454250325030350002110307416410b46681c0d001440c00b01d401c0420141c203420103155180001d18409400f020750340040d24102c1c1c0ca4a0446c0d05075107400c00002d140f00b090103203084401080c1c018082c507151590003c4d40710074190180b5124406094030a003000c0208109032078070401040000c22580180c50000780c00c003100d51203040d03c00e00c3d0202c00816460302c1c844041c3c4906510f5201c034881a250f81c4002c101401c8000c020714101682405001400d6500b00800d451001c40c1c0310601ca61041314020003820b549441c3c00c40018007050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 61226082 1250 61224832 61224847
    0x207181a0d0b061c0602070506010302090106090b12100803070506060a08280812010f050a06030b100f050904020d150902030403020a1101020106050907050a031b090504020702060706092105 83
    0x1600b00140c1c42030f0121402c0e031a072000396100201d01c1800100c040d050603c04074a0702d04205000450300c0c1624000c5603080c06a0781c0c3c0d000c08a13500c80803405003264440050062411800c0903000b0345400400c2c100c0114605a19880114615084030350190380e150300000c2031000a051032000d80010380380325006051010282500a1200103207003c19442c5402070410900c2440300d07807802e07240703001e498885011072075a5404490074610101e01820340700340f0302400d00181c82c034042d205801c141d03040900800c2e80c2c0c51407030b90181c0e0b620001622070300c00d0080c00c00070312110360342e0741c0300400100c8103008000442c0c0030b8107006061101a1900060100c6204106000219400242e40f0541e83e501ca0003a101c0e0852150040b8058003195201e1f54100d042181400071440e08040542404801c982d0100030400001c8582d18032003065110034408144c03030b058140000c0c10309400600032140054442840c0416540d6070304105c0d182f032001510070050014030074800d50a500d019903048a400e250a500300a071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 61227332 1250 61226082 61226093
    0x948031501030605030f1b0a0b0705060f060102030712052d04031505010302031213051c1208040b01061d09010906210201080a020306130f0204050406050303030c07030f0207181a0d 79
    0x720541d07800d100ba00d00310b14a03820f2380c3d00400325000e8002c10503815298111450302c1940e400080d03541104444107440001c155502c000180d030849034002000c5141d0604041c006d990550040b9080c84681c00350040080c221210040100209510100401c0e951891401c00040001920a91f490294100801003007d40d50000703004c504030b211640520b9403003203040741d41034215505501032501308100f4201c8400c801400700c055100030b0f02507415184185101041290030010840e4010200b903541401842a01d2240004141c0b00d24520385150152128000003501c03000241d015420342a2036030030611001c0700710725406011070050720440e0241c0d11140d0003e441407100030721601255902000180e600c0e03a0b010440b40c00004140300801405500c6203100b00030754000d0140900480c1001d000003007508000040380c0c42900003a0076070f424591940d0301150082d07002c0c0c481100310b200700c2201240001d4066450202c1c41c060640020b001c510b0f440e0180108901c5102d0184612507041100c8003086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 61228582 1250 61227332 61227343
    0x4050c041d240105040c11010504060504020f030606090a0c03020d09081902030c060402060f1c09060b100e040b030a020604060801030318080c040c0327020948031501030605030f 78
    0x44048170007240d420301c1c1c602c007290720500420501d1450b600b4802440b00b402040c2d4081c034012802500da000512a840042c5941c0d2030044d505a9040040c400014068040540c05100c0c000c2541c43c000d441e00c003010220405503181ca074800d60310300303000150004001c0f0304c80010322010051b5002031b605002e1aa000c03692580f0700204060301034900002c54450780d501c11030440344840c0120800020740ba55508480b0300400c941082260344605d0413600c070203286480c1c00360440140655559080d50744c0d00070306000160018040164040c815180c182005a03070b040e001e8000b80610390f54107542e07903145082c010504010721400801c031112150b8280f001050108010003848401e55010444840000c42240100940d02c03030700416422a0403601580c014210a100045000f1150542301c2e4580c0c002e07168201d0a51184501e0282d001100c40108600e02c000c2d40d079103094105214944c0403002c0340700060650007194600000c11490304102c88075030300743c81184041c0c0b800394010424120f25034846503466 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 61229832 1250 61228582 61228589
    0x10b040504230304180506040e0c100e03010209100c0309090603020105030106081b0a26060604051e191d07020607031812020c010210110406050304050c041d2401 71
    0x141100c66801908100820480d00203010817120b03c041403082c1c000c00c3c0000c1c007055810521940c02c12103c46022a000505124101d1008000140d440c420b0003054400c000d81a1820341c00d55003c0c06011007955622080c3c15170b5445648424040ca440c071724006002c5510b0b50446211207281030b40a2000d0303684942070301e06603140740c2005880c6842d00e4000c4200250304003001390b81c0c0b210000e4010441a40b240b1800c440001500744200d8040311280c84101d1500100d0b03400f50013032400d12003000a4500400c00b040401201800314165a24100c0480c0340c0200c0d002030b506074000d6a0720100320ae0700c2c090b50010140000788030a50124205800d0094482d003000e4160010944c0315640669101b00c00c000100901d640040c1141e9038000d0154081e440b021103507640703405030150482c8804244006d0090045101980d900c162409040c10b00c00d640c00d07000078005403014410400405550740326481403d080490281180304011407002c0c0c22032500c003407072044403409482c1c0d05070000c19806158505054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 61231082 1250 61229832 61229873
    0x305070b070501020d06141302190318050304090501031101050c0a110f06130f06180605070303020d0e0109140d08010e040f0f0c0807050d03080a110c01060e09010b040504 75
    0x4401032400e02c1c0c3d01a00800c0114560a407611000003030070b0010785918000c009041d50b54810150340d080640e41207010310b181042e51803000c46054644a4886da1010b42d16002c4024494458002900c4891030b54025810070404552f4490050050001600d05c50090440903e00303149001c44160307000d03880785841140246002c0c1c05101d07030f0403280d641860440e43c504c0701510300c540703541070b1141003510703142c0e240b289000c0274240c248081a800c2c400c5021182403034070300010f20511889e0000c00c035015840301e1026410164207002040311040705020303034810980c0e002d001060420040c24412004c0f8203503035100d5000c0d40a04490846650004070301411200300c02c0c403072407859846090095440082c07c20041c120300d1036401d02010824068004800c0e146800222103466450310240041c5041c004005000300301503200161940030690460000030014802c214240f442c10b0510600b900e20700e400c001c2d000d450248c10842221400d12540164120489061003241842e0301e0f0701c4a0410102d005406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 61232332 1250 61231082 61231087
    0x4030b010e0a1a0d0201080604060801090506040b06010c050a1502130303050a110102030613050c070f050a120503040812090c220506040b06030103030f030e0d030e100614040b0a0308070506040317010305070b 91
    0x270394407548140c009001210003481208918a4940d4071558101c4084407858940c00200d01c095225012001c045a4014018022642c0c243c031860404490780c090084001d40800008695a10000e0007000441c807135141c6644a01c010720740540303915800503c80c0126031050040180c1070b0707540b8010b096120b640792000205a2600078815845124545c0094607415080700c1220401500040e40c1801d9401104c4a501003000e01c07a00f10b8151105440242150f44140210208104a0a140d9410950000403a1000c0c0b0610012030400307141c01040c0c03a1031841840e003242e01c65005000b041d60001c2c0403502000300501c4000019064001800041d0030003159508070759945019500c110300c080c05003170840e441c610117494000d016000000c80006a8003c040038400040124010302d000e903a412110402a204a00203000040035040030240c0c0c0000103190000114001e4401030040318064806000c09140504016140d25400052000c560300d00b4001040410004039402e010341e800b13101c9090b03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 61233582 1250 61232332 61232341
    0x501050d020d02040b04150906200a0b0c0309010b0405040203250b03010f03060606030b0310111308030c1603080307050706090b18060610080f070504030b010e0a1a0d020108 76
    0x240554080b10b4030240c0f0000e004500c1103801800341c0700700c4520f004520680b12543d4021210342140344104c1010824000c800340210b044580c8031a11000a801110038080341900c641030310540540303000a130900c0020602100c10801c1c02000d00100080d00c040c0701a00f41303640800d40d250b083c2100192145e003000c45034a140c0420001100040600400c2d041d00c1e540c46102402c100400e62008a500c42d00c0c0040014165009001e00300d00030500801607c0201030118120010340119000812400410410103103d12440554040a0002940116101c5c52441c0300280762880520301d81020080d032007000c000184000c0101c9030700c0000344c908030343c81303115a02c0d101c000f403c0d45100013800007502804120800b0b181c0c1c2c0c48090002d280d80c003140c01c0c503107515083c40b000c0300d006245200000c9001c00003036001e10601003940d400484d130340fa000780740030303640d451b1141489404e8000b44165030404060000c01642c6d40070700c1c6c54101061541c205c2e20b000c15800a010b95554840080c1401820030000c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 61234832 1250 61233582 61233607
    0x60305030715110d0c0e01080f0411010e0301020d0e0105010e100317250201020c12030409020c0c060a0801082a01260702160806040309030206031f03081b060709050105 74
    0x1800e400f468001c50b45613029a100c9074007a100c2d0150140008a00014610456225040141c003441800725640301d244c886407030350000c106406803140d06014803030070b40b000306d500c0903c01041000d10351200020110142c02142d420f40e14107900c403440034072030300b800d05c9031301440012240c044a81c02590206c0e14000c8009442c1d0a0040a804da262120864540300c40070b041d01c02c0c01403003581300341c1c26509170020a40c1001003422145954100e180d01c01c3c00207008004956000b4004100c2e110211a5140c1145001440314ad110404990005901100401411000f0031a5510784125400e0440341806070f0808160b482d02000313500c5041061254003070a550003550380940c4041c1402214090030b145c02600a942c0310440f8501240300c2200e0100080c50b4180441e103107008644c1075441c55401455502000348030740010b03211030304445102d045c044210101c0400e6000851260000c00d0722051030001d0311070000c0c036140d0041c0d00b0b900300e0010440b0b115441031402c0240c48c800d00317046885000c0f60048 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 61236082 1250 61234832 61234841
    0x1080d1812150c020a03020304050d020102120c0d11010b1309111206010f060201060f1a1902060a0b010206060d030f0c060e0319020d02030702060711030105070c1401060305030715 79
    0x21a68000c070070364194180030050080c002d9040100d1400d10044120a004a036510101c0c900a0010381040c8014040c81c80d100115010041c0144126a40c640c00308402000c1c590000710300c0c1d14152702c42c107810940d06803c80b0703a001c60091104002c01c44000c156011980b40000c0d02610038401b0340d900700110070001035168907000b00320007403d40c40504540c9500e181d9101c60078001e0700074404d106070700000c60f10310501404c800e8a564100b1700b14524580691191164a000002c01d11528280009980d0021200c40141c95080c00c0d401811700d0704103c510740e001c88464998590464020300e04001443d00d8515500710b074140d0524201c2c074450350b0b042c8100c03252a05241d00820b2181460220344140100201802420700001d405122580c407468081c0c0e42c0c6c0841c4982071026030001d0001001501d0301ca405000038038000e9031541a5074070176500190031110102da410010410807001c103803e00c41400d0590b0036044009000700181c9046417030315543d900039a24000c0c400e41d8075110490420703029401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 61237332 1250 61236082 61236089
    0xc0b070f05030309010906052a0901050408150a06060503040b06010c1112012403150207060902060403050d030f0608070504050a090b04080316020c06070807030905030613051501080d18 81
    0x54030f449003440c030144c82c06000a600113803002814180490707840100508a100d9032680c809a4034240303c0c14140f201540c1c1c0040c0352250501006000002c0e4028083c05080c0ba00d01d43c807089181a071070030b802c55404440d504e4000d030007002000d004010000e12010340716900071000b402d107a40d19540c0c91034500c0442aa010015401c00701c0740c4021440800d0541102c041903503108003050230002540c1c66000c02e2065844050040340c1861080400303c000e03540144660350140801140018481e00818802c0d030081e80212411380c0012203440e40d99030705101e41400030300380104c2400243d25001030159601d20174003030988241d50b02e0004c0380b048102548600c00480c2d02001a50311480c26003003510301a0801c07076031040104080ca41d9019220301c04105800441d1004043c0c43c01c2501c15200d10423a0b03040f40d00b0403818001c803500c1c081401e640410100344600c8144030140900e90162404034105044244924192002280184035220000c151000341d000c4501e4000d080f4406c207000c10302c40c0d010a03030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 61238582 1250 61237332 61237343
    0x180b04020c0d0314040302030712020c030a0c0825140109030501090c030b0a0b0d14012306010306080a0804030b0405160303030506040506010804020109171002040b0d05010503030301030c0b070f 85
    0x3030220180c1004105054510b425032004c01c5110040810811804001c94004006070070400c040350004040b072521310703540c0f4668811200c0b4609a000400c0c0b81c0540500291080030056204014201081151503001905004c0428020710f613440c1c0a0b1104505000c2c09e02142d10103100c44060ba4810a8201c00030b41e0890700902100e8007a00384a0907030086804159010320003040029105c54590081071541c00c400350003014a80c4951321403240c510659482050a0b540710301c0d1682e42c44880b89a1203040b140051141c61803410000005001c0714007943c000c2141350098025140071816110a40d400c480e004004030701c5540d00c07480c1c51802c1403032001e0115907030189082c011061589c1944000e20406055408002c60346402e80155001c032000c0713600a0015120540130b00401030090754a14480030a002110a90700d8240e0640341a0b03085900410b0030f082005ca0b90b850005194002d05004180a9001e54076650458480c0001c0384100e0056031001400002c0d008108040100009182a04403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 61239832 1250 61238582 61238587
    0xd05070905101a0a1b050f0d020d020a0b15040917030403170408071203061a09130204150f050f0307080f010501090b1b07051207150e0109180b0402 65
    0x401288006010596020307003500e540c1c21010600c070040b100000d040300c0b0b03841116400c000c02c110701117035007800d002081c81d00301604440c10000a0030803c800e4500c0b4107100302402c0302403800b00c4028542404004660110341c0a01402c5012030780c14018075400001c2d1407400310ba0070283d42c010801922503c030000b03200b28031209540400201c9000038600480c400e503618051903111030307007010103c902660081c06c820b8080148000050030645800120f030f40f641804140c260703940640030b20002d00003d05400881000506406500d4405440d0f10000305024086007041c0c10803008000900c05075549005101d82c03b52106a03a60268065800d8182c4001c2d02560340d10381820010450b1130f0659158402d81084030003ca030940c0592489002c1d03a911f000c80030300b0901040742454413900003042c2c1074054090480c0205643d102c2020003465040703200001c1580b80d2822094100b0102d2242c1c12004000002071204400c4ea80410a1021a4003282098058112038854540144403040000c3e6005100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 61241082 1250 61239832 61239839
    0xc030303040515010506190804060b060a030209010215040c15020703050106180e0a0b0a022a0a050d030501060c03050c0114090705100306030807020402030c040308030c3f060d0507 79
    0x4604100c0d600010305401c0f9a41c0e02c0c41400740a000b00108034440302c0141c040450030520621034158028040d210114011540c5408a5000d9003c40501e0f000240c0015890300156010400c603006c0c41c5441240100e10f2800d03840d05480e61000b80100745134068070440d00d41a4501c00c03c01803014640103002000b01998a1064200005070300040440c120704281c00d010b10000003007460b940041c3c000140c0358507070350f4050340f8800a5100341e51812450b51030301d41e140102c2103131300500503064039900c00503c0c000c0b0303403800d01d07510341a01c0384907200401d0305240c014028103911007104404582e041c140540c4500c0614091030150011055003801120040c0410010460001e00001120b070180c4001c407050320503800c101e0a80e452804041c01c1601d08001c0c80b001410070354000c2d903000b040248000d003415142d98401d03401d0b88c13050326104030004011071080007910106034240c03090b1003541e01106410610501c0c410680c3c1090041d00f150100b01c80018010340c884880c010b032103d070b0010595510544 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 61242332 1250 61241082 61241093
    0x90609060d0803090d121401061107090e0709050609040317060a15080103060c09051c0203030f0a121401060f080a0b06040603050a0e010b1c0309030f1104050a0209010903030309050c03030304 84
    0x2031000c3c03400d00054006c05540e000b4203007031107401d0810f840801c5400b613070b13030900fa41030310814099402c1290903c0f850030300240c0003500c1d01c034003140101c006000d401054030340301080040d00c2c03002e08600d2080380f44c0c00a2000282d000100d800000001d00091040c90f56283c0000324800016030109010940d000a0200550360041c05981628800c0c01c0070403200c07034825801ca071701c0003003405200d40006030a04c6203004080356454543d42c1900c01801c40e49000d81e019105903032074200801100110740645040d1a120044d40500885d05403c2610182a0b6143c04401800032403900c800b0383c10b2041d00000301c0c407050500e4002e69105070f401303860700303965540d50380008000f80340c2110300e00441ca1412402078254401030050380c00042c03005003201a42d0068040c5108401c000050403020300c03c0c2401c00000285128041d1100c45000390812420030b62000144000d8420090440d0400340c410007104046a0704446000309507901841d00280f00106450f2540c60521204526a8188000b0040008204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 61243582 1250 61242332 61242343
    0x6120a021902010b1e0d020105131a040f120807020402130f08160e0702060c28110d090b1905090405040f031103030106080703020d0b0409050d030b0f090609060d080309 74
    0x13500380c1e01c4400502000054462081881d0103280d840103400ca1601d01645c03051002c2d241200020a00b080c4090382c80c0e00b60510f050858500e1f503c910310114080009200322000c66005015146155100d5407295456035054400c600703000340b1070f40e408204441043d0902c816503000d01040780f802401a9210f201d0141c1d00d100d80e15002d08041ea84090214205001402c424054a52600100400d403221592914260040e20540703a803181d207a01103141514904a142d1085213190b00d50300d02240010305d5090416841d00b45000500c1f603010390801c40c0c1ca04200841e620410000c40e540003092021408842510983c1146030f07102c2c1c240b8052005104c1d00d0040700b84814842c2e15407012052046a54948030f000910a4074086a540000104114041d40042201e07074900d10303000564590010028013101c000220694950f80070750030010a440e014419007c620b04111485900e01103c0b20000c1d02c0d100300245180d0158160001081880d2140445850710f207510000030340d168a40078080d40e079500c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 61244832 1250 61243582 61243601
    0x905060403090938060d090b01050a06050901080c0a030e24090d0f03090f02030d0206160504210f29070c05060601082706010512010b06120a02190201 66
    0x340e1400e8409070541c3e83c40401c0c4200202d4856513040b440394100078070305994001d40c000c640c1201d020000c039018190281b19000040e840381c0c01000c05541400c082c400640141d03007010083c0501044441403507030b00700d00c03000d910000d0114130341e50340c1a000804174081d042c0070340b240f403051252004894519201301c05034801c1030b5113a40144100d0755000c48a03540c80d0300003030100012850110100c18800c4c400d8210b00d1a890090991070030500030b9901003840c1c8031094900c4001078200c1428441c03590481c000780f01481d40c080c40c2c032504190038200a071000d0011800c10a40c42d41c04607801130100800300541d0107280380c2140e04402482c004e1102e2042200c0d9603400c165100324540000b54001d4000c2410b0841c02e90840c0003000bc40d07403144019a40c1e41406450b40031300d444002c1801d020f0303c000e480c1c554048005036003c0c0195524200500000300c400045050a5034102601c4503c0c4e92a810182c0f507508204012201654440c04c0503440244120b540d4480c10300109456901c0c01a015000344810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 61246082 1250 61244832 61244849
    0x907031b05091e060d02070602040b0301120605060f0102070506070611040605040801060801060e1609050402160203150f0403140c031902060a05160c0317070801030201120203041113090506040309 86
    0x80d5848a80c900f000034254040b1658003400920100981000c240d01505410b4407070540140340070f0700e903404041540c1090780403100c0c2406140b190401c0104074003c803900041300f9103032900c20342440d0380040d486070224011107000e114049541c006010f49608015008030006001c5039640b6102c20008105074014026002d03150300748003000841800502c2030108036281d4620b822600e413100b01801b014003811050140800031640404105030740d5501c02060300ea00c202c944c1290000080c0306060601604030341d00c0b4088168802008074035198003590700c0d4000d915207454410300040e0301440c038803805840c10000c994400803825807030030343e20b280c104140032849408a4100340e072140c0501c4242c0b9030880b00092102103004081021501404c1c0d10120103101e4240804040b20a544804c03490508039000c078000781a800c010130955801c80300d04a00b100c01c0f69020340c554946501c52141004600422b140a5010409910011080d691054050580c00800e031600c0b03040c1400c005240c0e91907030090064 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 61247332 1250 61246082 61246099
    0x40c05091e06070201050901030f050c0310300302070308030c0409060e090706030c17040b010e0708071d0a1d0a1a0a0e0402010c0203060c03240f0907031b0509 70
    0x407820a0050000a41c01c07008060314030304580c1da8011110307038104400403814940c40c1c542103a0348500b0350188504c500c074003916079503da1420030303040082e0f42d4269021074030328034510301d1060940740035000781140302c0740b85201c000e03400d841440e040b03181201c260b03c050130481020040c0400b1801d800b00a108568040340709000361a15500c0b40c000c07880f420394000e18a83d00000c000c1001c5400f070340100840001c2810086004075200c01a128003990445e8110358040501005000040c40c8129442e084001d0740340100882c42d18000140c07600b903019100181c3c08280c2e203500d034050f030343d640560b07405440700300342c003030600e0340c1082c90401440f6007900c05a98040c10102da007000380000b1000142240e20080c80020410b142240c84940454058005c2e41080017030002140035071000c001240c045c129aa030354668078504910703050701c80602070380c2807035400b91000c006645a990ba900e840c400d014080305c080c0e05035190364070700342c0040c80070f080f03008058030040d18136245854000c005064a28001c0c0c84182 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 61248582 1250 61247332 61247359
    0x71d06011106070c061506111005010f0902090a05060a02030a08060f130513021023070803040b061909090308060603070f0503040807021903030314010509060402130302040c0509 78
    0x481d000c14403840a41254400400648101e2240c5041c10f2114081c0000103101a20102e00300c04e526480c0c0c10032404100e1407202c10340403074000c000c0700c0991480c0030f00402c680c0d410302c240404220014418040010340100b6280025991441050300805004000340e035503010244029441c0d4121050300408200d0401c0042c00b581080999039031441002012110f182c000c00c40314070010100a4034000111034500e655800684450985021810050701c5038642001c0c41d481070300c0a850000900003011009100090000b03c46005a80d0440d030f0000c10810701d41ea030007001c0303402110800c05807280a000c8440c006940510781c1c0c000d01140d40241d4660a45039580824800b451000342c50f00b20024402c40c51b41345200f0f21440c0995001403152541500d48903154001440e03044209100c0c040811000508008040e0140700f4420454203d10025a156250000041c000360380201800c1c02a0707000140380000c010312443d10b9001d10b900a00030441025560070080c115008250a64001c446c12140078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 61249832 1250 61248582 61248587
    0x21912030806031b01120f06080a0302060108060108010e0d030203041113020301091a06030406090212030f0d0b030a03020a02190e0a0609141012030c050303090c010207062606030708071d0601 84
    0x4c00b0030300181c46220000030200803e2000300302c2c44585003e0960b8480021519620a1007021130050180c4d00400705541050852801d145040c0e203c1d0100340e152140c1c001c10300c0c90110f0100159100340c100140c0300d99603410600f0040d070059501c0c60384616407118401d1034102ca540610b0507646c1c161001c100c040c48656581c1d0411054405e0240d00c0070301480001c001070710b80d400c005901d52001e0038242000d60456442c51441e0401c1c00e1010b812100400c100c00d1a06151107000071503e0203e00501e440c4100f600c0c043c0d2100d501c0040a40507203095682960a10283d4044100070b00c03c03544200224a00411014020a0300d40542c098107800e000359295000402d103146070044100d40d15030083c030b5141040b04181000c540342d007203048c0690502c3c2e4501141062010350310600f40003010344030240d400c8000a0800d0410741252080c000554140b040000046009011b10324844075a00010348070880000d18118880d40204298840e4000210715810390000740c0d0655401c00d0b081c1c0b1041e49554005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 61251082 1250 61249832 61249873
    0xb0103020a0c08070f150608010506010504150305090123090c01080603060a050a090605040b1e091e010603170406140a050f0306010903050f030717090d02191203080603 74
    0x1403000044541d0801c2c00412000c0c002810301d9072003030f13584102e03102090780d546c504003400040b1000d03001c0d0f449204000c529428040c541d800282460458502170a081840400380412043c443c00c140d95200021004002503018404080c140207100c48030382248160100d40c3c400882d019040350080748062403a80d4051034046009550040c0500000e58802071100c004100007805008850780b5000c100e4041803007489443e008034015140d5060b0341c9090070078100c5006842c500504c420411800f0420350340c4002c200c1d07601c2c2c22103a04868001c001408011400341c4056000544080750a22800705d1a0384071100800071034070300351280703031101080c1015148240540d510b40808248200911b00303a01840400031644001c0504122103e42e0301da407109441c28440c40f03940d0440d6480002c20358240509840202e010981010300c0a02d005403200100c1c0e440480140000d006041602000100184489000c0098003460351404000034883c24000c1c541542584c2280c0640202c039450510225002c4c3c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 61252332 1250 61251082 61251097
    0x905030712050c09070f050307020312010914161d0a0506040605090a060e010905010804020414010303020c01110309100c0302120a020309010e0405150609030c030304080a0303050f0106120203190509100b010302 92
    0x1251b041e20804120156250b80c401004101180801c010550300614264600c2e07001c4c1646e41300010300762480b40681c0e4845080034213084051203500e10b101c05065481180d60f0410200c142c0c480c40c0085901010818104041d00981da10941c0800c6c0490025807040207401c65032011500030240316554101900c1c4d40c2c01000700640051030b480c5043c0400d501500c0c0a98005101400000f07941801c80c0548031000f0302a00101c0058000301d4131000c0740e40c1d0200080d00c40e9404180990b01d802409400204402c012000700f02c244055070790300d801854000e020010452414120306a501c099183c00203403258001d056107030104400340c17400c3e20107081330700c681c40c070034804400450385441c084010401c540d0003103286160b0504c82c0e421602c0d150b89061000c4c00092040383c008105011161502030150781005000b800b000c44000010841c841e4040501d60710a040660016500e4640340e044400c03a14485800000043c108028401e10020004440b0351584814a040007461039410046040e03204000707 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 61253582 1250 61252332 61252337
    0xe06010f1a16050109060e011d0312090c0d110307090c0f18170102040e0c030402090103030513051f120203070914030f06042003120a0509010905030712050c0907 71
    0x40e84800c4445501c01810300e40e1400801d9200c40c1c11560f1094207590b150340003158044e4641d126201040024025000300e114082c042d20312a81910844c580d80740074144c2e42400284c120380114404040c00c0c040032243d424098801280300041e03080007050148844e10f014000c1c800c0341c5001405495920680c140c80350346643c0c2174445215204122005106000c0d001900c0060328030010b407106115200078111182c10380056111480d21581c1d48940000604170303020140c04004103c01070b60b030821018156a41070902c0d9031100c040140200c002c0b035640d04a290404500c1d040009402d010b041004125200703a80c034550100d4400a0a000760b0006a405402003450b4040078801011769120340b4480e02005007c84804803c1155000d20342071041c0d40a848000221a40d41103031256011900720900041d002008540c95240f40300c0c01c0d610420006200b049004200351002e80c3c07054441e10000d02d001000c4940d51501d030f0040198510030f0000c1150b0600c03ca0800d001d00d820300c3c503405440b902a40c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 61254832 1250 61253582 61253609
    0x3010c0509010e120105010801060e090a0b0601140906040e04050f0a120f03020d060902040512010b03030306010804050a0203100509012003070804030504092f090d1b050d05010e06010f 81
    0x80191020b4403001c3c90503500c50203c3d800d80035091424800c203070092007400c1c00814007620344031111452560203802c68000b500110b20490108140c041020f802400c2881d0283c8100c03500c22035014103009143c51240d1101c0001380000c0e00e820042d0000c0d0055008200751028045c1220f45103607550701640006211640a550040d900c90151071504556112401c015140c03d5010000908440d665048040481e80c08a002d1000d07051110200b05021400c000170001030403500002581c9000007010141003010004c0014100a4140282800191702800300c07904004038184860243c042210824001e600e8981c01801800014145412302d00442d210300380343d610b82075402c84540c41d00500980c00d120782088005550f1400344204202070101150629144641021850ba030014040554540c541d0505c081a240d60f50f498192041030b92001c1c0001003883c80c800f0360b49014280e81e2209030307c2141d6180760f2007440410b400c4150b2088069054903256038a078600303031281c04518060426800ba00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 61256082 1250 61254832 61254847
    0x10b0c101a04090609050d171501030e2a0d02010c0206070f1b0515030105060a030c0201060510080402040b01080103050d0804032109030206010b031317220e010503010c05 75
    0x5590000e041e040c541d01035041010720090119003910f00b445022140b1665941c20741080c00b000303201500496949140031302201c56100c02d0000455000b40003540c0e44103050350f8a42c3d49a003e41e00a0100161003015901c0c0204048418400030389109100110030804e81c00190b01843c20505900c40c040d4161503082d03d43c8826000c2c4101a00450411201c103001640b0110110380c1500d140410032030701c40441d074882d5007014180503124984004002600e0400c0c8010700065403280e0942c3d0744103440340717000a030740712892400328054a140c1c0c0c001500710310000d40f0405070308d500c02c07101c5102d00e00940c0c050101c00c5aa0b401110014402d00c80940660070054800c4040e9114524594009000e45010428503c42019041070003560b044429003007588d03804400100b58061103072900421101c1002804c501d001c001e442c01c900c01c2034400800c15901081c00b91020303540c25041d54000ca01314040e1a80644903080502e1a450701409440703160500e000000546141c140140414101165503071400d0000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 61257332 1250 61256082 61256113
    0x905010c0807020a0807081b0904020904080904110408030c01060b070201091e03020301050f07120603170a14030c0a0801091514030114160f0203070206030411010c0602070c0e010b0c 80
    0xb00b24412640484015400074510900f040810042c0600d800070306486002e0040c40c08603114040a02805190500200005a07a410b1b00c004d92107504120619540c0300c1ca4070004004100d1111822117104002c00e010461900002c050b2103101c006000821400d621791440c03803d180248500217001031181c55090000741892116400d50440c28460403e855840f58000785c00d407141119041d42c400000c80c200884107600031a00c031120310104004002c154110b07140c0100060742d4200c1580000c400144540d000b40c810088075503040000e03200c1d940c6a04144000e98059071003000c0c8140011070100011070002d406126864044080040c150f000d00d103441001d03050000c41c0c0105a83c155600d100502c0d5050b0100c01c8036204100c0c0a071501000015514082c09042500c609a0215403050144000680351081240e4102e50856285850141c80b00c00490700c8000c00781000f0092800030504c0e01c2000700000c01001500c03030211200c2c40d981e880e403a0800c854060141280c00d5179008204d1851581c0c13 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 61258582 1250 61257332 61257337
    0x203010b0f0f0d18030305060907091509080111070201030c0206010b0702040f0b19031205090f0906040e0a05071d06130509030904090b010f050906030604060e10060303030e07060905010c08 83
    0xa0441446060002402500e0112400b0b1326809a05084000c1d8203002c06030325100d4640d018000711101c0580342446180201040060b00907010602a80c00c5003100c1d05004882e620010035590009000c1d01e40c2d100d48444580d0007140089020a00780103d80c6506400441c86078143e40e6060074060501c1016000c100c043e00e4a03840300c0000316518031100032039842d1a01460885030209013402c40c0b40d8598540300c54164007506400c0100082070044103250ba86408a0b2441d0180c02c40303603c0184c0c0c803401c0024004000700f181c030660611803600c6220070010040307036543c102d41c41d0010359410031681c10184103168174116000b82d030081c0709a240c9001c3c003005901007500914180100c0e410410400042811a1030117041552320703282d90001044507960381d49540014100c02e0b10000c047d410500e000c80e035140000b0304010150390f110000004612410080341070301c80700d4a034040c481c032603482c1001340c010070040600b0907443c041c991000c507805029401407021503106039207070b2100003800e498514098 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 61259832 1250 61258582 61258597
    0xf04030311030702061501021c051305060412030e09010e0123130f2016080906070c05040e1c050c0c030a060608070f140405190501090614040203010b0f 67
    0x150351a0300507545808110042c0d440303605981c006101a040c420603401e01603800390802411036104603042920359040b100c0c00316419a190510303d032506000000d952035401c99400c003c0d00000042030005242c2200440c04000314060340b1210324601220050102228003401004842c0c400f9200401c2410604001511031016031000c3e819903007001d8000070b280030a00e14503200780c191076041c0c0c43c10600c0316110740000009a60381102c220405a84050f0711802486c2141c2c10050300303507000c0028018000b00321121004002c04090b664a01d52500c199820003900640c0e014501e0803565400c001c1c00084d00e02c07119a403131507d0240074000e8400407a03181e8000e100d0440d15000d09503102881e92030421401426920920003c984281030410091034445260301044000c0131080c400c0250b180b804001b1060034506541c00720701650743d504c0801da80c80c0808150500f661601000145d440000ea12000030741b071001c02d19034186a0030790b0820090380001e00510300500c070108910f0001c0c02c1c0140007031120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 61261082 1250 61259832 61259837
    0x61e050c010608030901020d05090d03180f06120e010507080f070908030706021e0715050a020412050c0102060702011e0b010903020d050601151403040f080408010e0703050c010f080f0403 82
    0x14111408211800d581d00b40c3c0c000c9900d940b011039170250942c2c050218001c80c6000b4034141e4244041e041c002504494080005818480084001c0b806a01d100540d600a82030803038005012640da0a00101400684501807809600c3c1c802d08024198040c003d0f80e001e8007681d0346102064840c0c841c490f118100103010039051040c0c0c0380c00003450960a2015004941c019040142c48100d45403074040c0e1aa81d900d112480da4200f0400f807000141038003203580e00e001800800080039075800340c265009105e25048500542c0030209000100200000d04507142003003a0b00703440c02600c0380f85069080e03418001c058481410181c105031868403903540440144541450f11514960b0381390003060030f0a22507501074407070390402401131042045181045680b80014074040841501c50b480b141400e000180c00100607008003500503003481117020940307000c1c00c070110003044000c4116540340c1c1e680c0a6444116410b00810f244507049600030403c16450551079110f1200342c0c2c0e90701811b4400c42e14010011410b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 61262332 1250 61261082 61261087
    0xf1b020f090903311508070503310c05220207150c0f030e0303040308010308030a0906020c010609051312050c01090506010303090810090309060e0604090f020301050a0f061e05 77
    0x30520400380080003004e188a000000c2c1c0902c01820f18154035050700b04d010300040f040700200c2004d6104484907400300d0303640380868a03921011907110132148009100c09801c0704120071403a00450740e001c040080c80c8100720803400703a079440050180c1d0f5a11041040d8a408070724007920150f14558008040103031040114801581c020017419007180c801ba40d4440001d500c803448605451740610900e111082000021411458a03075001890898140030092480c600800450900421508102845940700d50b084d5226050308000038020000361058003180340c1031101217151016a40403038403000f81c0080000030041c80440701070740d455000742c0d0014450b40d078416500c1d012481c18440c2c0c60103940310342d440b08505840c19203030520300260000c4d2260400d02e042117840000390000050381c110340703140c10314608012021000070303901d02a40c1d1108241c941408180d01c4e125006900850580f002181c0e441c2006031141c07041d04031a420341c024030f0041006550302000142c020000c40750400e50f40e140991 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 61263582 1250 61262332 61262347
    0x50a030b0315010e07020105010e0403031d0609100f05011d040206071b090506180106080903070804090501050418050c010e0f10030609180309052701060f1b020f090903 74
    0xb4909014070740c100c00c0b41d2990b03070018442562100c9540341c014810f403000740840d5060280e012004000680007c00781503071036210505a4089094504486041d6070a0321002e00d0045459612082a40208041c0034940321540007242c40d41d00c90541a943d038240214210740301c1000c82d40c0307202c002030f10603644414180845000244880500040400c00d52202010b103850224420141c03500500107500c9030b80e00c1d0403030301c1c021030a40c907040d07045a205103003504194890480700f506611958401400b00500010b01140c54902030b04810304940f803d0720200500f25104405011850f00301a00a01e02d42060010150641c46a01e10440312400200303010790f000c200c1b000180d02c21007581d5080c80403a8540008215103013281c0f080118405080e40c49403410041c9a03070090990001d405400d100e40c1d00e02e00020351003d02c1402889040141300d0345d289495840300b001910455505080c000040da212484401500d940c1000711401c40d4045c1540d03031400ca24404000d61540018100c0c06584400c2c060307035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 61264832 1250 61263582 61263589
    0xc09030b18060c0702040501382a061006021203071b0501050f150a03020d0f120c1b06050301060503090109060c09030b09030403120f030e01060b0d200406050a030b 72
    0xb50040700c104049a0341c4000e103105000944070168400103a02e9000b40342070b11420000c0c060a145508002458000d045407908002541d0003030b0102d0034640e803030707131844400464071080d0461440600701003122055a5622b03048291508240501401070b080880d60700329801145c40076582010040c10640203840040120400d00340d107194050725207039124011b10041c095002c40c116001070b40c22011550100010020030f480404070300c0028040c004000f841c000f402007241c22401c145501c950314201c0e00c0401c00f802400182d45c0c42054503170403140b450711243c3c1380f001010303581200c0881d1601400c5a2034841d0994094000031701c650403554070317101c500380015180e12504009011a440702010171341181004200100c1c01001c504c02a07004202c24404115808a0b0384080441031800901000b0300c4441200900858604034070290b080c0740303012549021100180180081c116030800490f5140703407540d0f4407194010a24104001c0402081c40820710420081c01000800d0501240302001c12020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 61266082 1250 61264832 61264843
    0x130503030a0306090510060e060c031204080310080115090e03071203020a09090e191415070e01020a02210a0b0109050405010b030f03030c1c020313050d030c09030b18 73
    0x3501d00095840300c040c440e422491040c070307410517420091003e0090800b04060101000703210f125120394030200e4070546820041048940f107804400841080341032900d401042c5070001c1c4c9175403091114215000c110b415051089214040c02200c2c110541e41c81c08803048010150035110340b8036401708015003404200c104103c40c1020035903590060340c401840800405616880c0c2050207040e04100d460712001100080c602c00c501051600030303038014280e1402010713281d141108003d240c058204419450b100e40d4601034030400464076041f01082416004a0b01c1e92496030009510400405c43c04071442102c841c80c8000c0707c0c00b03508a40381c0ccc039190b07200c2c0424a4400d80c03198000c9601c0c7c2040100b041000c5c000d000c0141402d40091040b0080340080380e03100d00005100080c10000441d005060703041c0400b003248d4482443d0021592420304142030900a440301c0e009039a00e00c1000304070318420788030307208526040140d03030341d61f001c910308564800401090140100d469000304d644840380d100e1081c0003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 61267332 1250 61266082 61266097
    0x13060c2f190e01150804060b0303090a060306030312060e04030c0204020d0906060305070503010228030f06080a03030506030d050f0d021b060117060f070e0111061008100204080a020613050303 84
    0x4500c0101c0386045800950080140c20a60130720703c034070b502da1480e01e4010344410b801a500ca240481c00c010f404000c6031031401040c2c0300300d50101d44c91f20300188494150780f001055030700030390341d65852003c100480e070140c4025104182c5030361031040001c3d0110380b142200c8405644000c2003d131400800300c400c1c106513030907044141d0f01306641e440204204002003041c0390090400703400940c02c00640340b51850820569100589131703030f03641c03100d0400c60622a80c401c00c0801c2c000c075000c208a03500c46140d241c0d101603044044000c83e01d004013044141c07400146002082d250782d51078520340042003010401e04c6c3c00896140040c19001d002e8145a8410354100e82c042211440c024003c6600d00800304a02001c00316110580c0c0d004241402590f44a4000c4194002500d040c040c045141c98001224212040505103005008140a10041c0345a0114000440d054bc40807103c482c00c401842600300d1065104050316603004240103030050170040d01401081015820b01c0090550703903000b007801c0da0b02402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 61268582 1250 61267332 61267369
    0x60a0e0c0c0c04090206041505090a03081c11040501050a0e0303030702010506031209010801060507051e011a03190209130b0c03070f020a030f03020309010605060c0313060c2f 77
    0x68807850044104940080b0000c200c60038007039413009402103815841940120814095502ca441103800e020b00111550800051710303014000e980ca051440d116040756048441564052641050304102c5000e28814455003c0119240c43d00d07040040d542ca91040001c44180184004401800c0c5e5091000c0c621401c400c0c4c001003043e180c0b8000f09810520708000c0c414030a08140866242664080201f605482180c00d11075a1250319042107450102500da94100283d590f01c03010f90700b08419004070280802d9010494410b0609500305921032059101c150030a40704001c0c140c0161401081c5103400070700c1c02a10340c0001034191039400d08014200c0310b0200d06880001800b1a10ba80404004411841480644420300c0180e800810380003c64144200f010707008004102e8200742980004010140208200d41c1c8400c034010300c6480f9044680191840c1840703100c00614030b40912444003030b5640c0700c1000013000c003000b00c41032860840c84c50a682080340c841c1c2c1139455521010340b5096079501c050b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 61269832 1250 61268582 61268587
    0x402010201060b0304051b010509031605030705030a17030a0e1501050a140916020c0409050a0b0c04080607050c0c040606080412051804090f0b0106050706180f0b060a0e0c 75
    0x1400003a0035600654415281a841001040089040410307000c00c941456091000e0a20515004035420700400801952601514900100d06d03900380d240c80c0101c400c20f0741910ad60694420416803101041440a4159031444102e0290680014021507220907200c0000500d1950300035080e2800408021640d0859005e10061160b880c1c040c03814401081032100219100340c050001c2409450040c103e424151001d40c2c0c0381140354020300040141c0b130800fa0003003020310000d040080c0d0302d155805041d01d14554440200c1c410000c03040031070b01590f90f614014140c07500c41520803509641b000a030b1004038058603691304400d40e0380d80500402071000d42e4a080c42421315081c4810081d10582c5040140032042200c8003c1c00f1030074980500c804012a40011002010304013140314800e00c0b44001c2c030240505001066058001000d01101801908100901802501400384808000e080a0300c0850300c0c105a030001004469403a502c61001303000820300399a40c3d2000202c2480584441c007010501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 61271082 1250 61269832 61269841
    0x11070c03081305040204060c0213062312191b080102040603050103030f08010302010207060e030c040203040b07020d021209060705010e0714010f030209060706230a050f0f040218071404030b 83
    0x2d50100340074140840f01140740c60300d0040081d01400c00207800134090a9010b00100340680154040c2d402040e010780300301907401170001040c0c56129888400c9200e422000101d000482d8002003019403800c0041049051146544409005404c8651310500100c498100802c50341000e00141000703041c41c0d2404616035045140c042d10a490164020080050036001000543e030700003100411200941040801090007202203410401520142a04130b400013090200300207484003124821070b0759500f900d5090840d040c04980310160360380304843c02d5506114104103480c0c140020711040d840b40c400000d40045540c00d4504044d41ca900401d00096000441107155030801070f595194511898118a03044502c000a4071038002c80074040d00c0c00751317100d001d825050b211500140607000100026110f510744148408060002141c01c5942a50804041403516010480080c02294014082c10780322403125190600c00307200610403403c01044520112140d14101d00600145005030640e82c101d290 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 61272332 1250 61271082 61271107
    0x90303250311150703020306030102040e131a090a020f06091c05010507031104090c021203010f05130902030606301005010803040305030706050403030609050a020c070e060f0411070c0308 82
    0x100b4102100003034200001d4060500301c002460b42d80512035040045c3c0300d456032000709009020701e030000000c2d1120503050012101000c00e02040141c45000020041d000c002d00000384000260340303807190395000c0c41d06c55005140035103041040c03070405090103040002e603d000403038030007008001c5c1c1d80366072202030700d070b024080300b070007000e034010340c103040900001c0d840ea00404094860740c80741c0e031100ca560b01c4038154041e10a22503508154401a44603403a540c40e19000d0704100440d10a03140b003000e4259200e8204c050310700900200680041c00340040d075560400b801398010307040c01300c4095894000d030300c1c0c1411421015056800600c800041c00122401e110110031244107030010251a4018401040040d8001040350f81130340d484040071038291680d01d0250b010700031517002912240e0504040213800e09032035000d000000101011240c90542d2403170400030b030320015a021a00884041d403801c2a6050540040310141101401c5a190204030b84641c01485001e40046074801c1002071130294414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 61273582 1250 61272332 61272347
    0xf020103150311040e061522050c031e0103080a080411030d17090a050c060a020f060c0a02061501090504020f0f070c060809070e0103060b0f0a030b09120c120903032503 74
    0x20301d030400904042c100801f07044020a044458980305070844610401c181e650301480321104924101c05100e03505002040a02c03035003080307642e49000c0b011a00e0710b8400070b84690312141240e420900300383c5449006001200c0d480001041981c8017400c0340300000d15502c041004030b88140c0c041d40c0314103511103280301c414880b0303802070704000c2e10354400541400070510101d1481c15110085850590f1080e071074800303904100049000340030f94080c2504101d040700c9000018024074a2503400e850040d556410910701c5080850761941c006211300c14140700e41e0525034000c040c680c00384900641044200810b4032051303444000304882d000e68800e820070906400071082c1c1d4008600310094509139081c0100341c00c8040e814070015208a48650301c2501503101d00c4c0e65070080c0c0e440541840c4289441c0c0c03d050241a0303059070034003018480c0a1101001000d600e007a2203c03000c01d00e0140005400d54001e034102608460b10040d8140420401e00d10010707211032061031a203940d020102283c1800d0f090107807550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 61274832 1250 61273582 61273601
    0x41e03080a0f051501080709031a01030201080c19050a03151e0b04060e01050a090b03072c01020c0d0c050607060902040b040209030307021908030c1b0102070b070f02010315031104 79
    0x180c185003c1c80001c03845545003013080d0ba8280780c1089507a0710034008448000382c1e40d101070b00a0020344082503801c0900007516060301c0c001e8880d2441e580304d041c0503041611495020502c0303165041c80700d4254922443c02403020840900d40480e1880312842144a041c821f07500c000c81040542000c0c0c5d84404140040c280108074502d500c500b0035141480143c006804a10094104076001815905070307400740210300302419418072601d44a190141000d0910509142081e03800155031315040044c00c01c1c24021074800c441a405048961401418400100394440c4102c0c2c4224140742c010445131106400383ca0314900403c030101e10600103006210494221040242c016801006619241d49001084071b100c1070703041d2104264081440030804140342d413a004801e150100003200c01c500d82c0c0c0024605000008604028014111100107994443d0103100780008071000b44105404a490803a901900768010b04000c40c0c81440d01402100c0050b55400844007030f82c0300110780f1348a08092058880760f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 61276082 1250 61274832 61274861
    0x9120306030b0a02031e0a090201020601080c01051b1009210201050403080105091003050f0307060b060c070303080a0603020a09020415090503120a030906050702060402090c070b0609041e03080a 85
    0x15400e42e151a41c00100c01800e44010715000000306525010440d0f0082c1c032001d0b2070080d40c9041c01d00213070319009441d0321401a801403050030004290700b403001c0380300341d03150384161219450000100c8840086010a408a41041c042c1400790a680440340c0211451188500f0001d9008a11041d204030303482c14038031160f401c41e8500f00410002076042100281511001c0385c1501c3c1c15900e0780d5014252964030b410060031070050784054074015000101400003688940014441541a14140100340c02030355003200300c550101604102182c050b048a54020111060224130309443e0f801246031003080e603000340750aa900081c10041b80401c182880411044c0303146c01000d603890300340000d540d88251a003841e0051000141031800c40e0182e4850020550b1048040c4050f18240d54040e484a00c00c4600b680155038910001e1f080d07942100031510000e034030410307010080e1102c0c800e005804070000e1044440c1184100001d01604103480e06d84000c80c801e545407203036881d0521050041d80c1505009658 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 61277332 1250 61276082 61276091
    0x90706080103081602030a03030b04110c1b030f030301060807080603010b010c031206051302030105090c0705070e0c070807050106060905040b010e09042f040c0906080f04050304080709091203 84
    0x465401408203044030b80107070300507854001c100d14013141c13500d41030307002981445403142100400d600b640184010440840e002c11003140310400c01c0d801c2c1e02c02c84a03d50030319000386043c8640080140760300d00c1d50305006800c540f000125814290701d558001c2e00f0040104020a08102700e4070f6208661640c880400d038001c0c00038000d100c1c0041c040030a0a9002401d200720307104079100d6001d00d13501801c008d00d001801d5411154039151103c00a60080c0141c602900254001514400ba40c4040b41c00071680000100340f81d81c5408140340e40d41d030740a402d02c039101800300040030100d00171001801c552801580002261840e150700039004903d10340c03000f40a50300700b00780b410007607070005201c20544009886c80c645650b201c1ca041602e420665a070340d480310900d4081c010480b038000200380b11148041d141048801c0f019103040e103911420b8070442001500440c00205c8140515003500d400622030f6040b039003455294210203080260036081000196965410a000d22a11081500480d90142410003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 61278582 1250 61277332 61277339
    0x706171803070b0c09030a060603120e01230d020a08181911240715050f0103060c03090501230c03070203091e030102070818030c09190207050601060906080907 70
    0xc1d00da00449034060700769081a40001d07198002c41c0c08585c4082030081c15190b03404050718080005100c0c501007620001852060b24815a008080f18201c11405840d102a032080c0000003c270404240e000c030035401e2400340034028910b00580003410301e901503500d40808519001c00901103031007050000c42c0e070a6120b10410121140250344881c0c6058003c500900d040b0001d0300400c90b50b5000010054002808040a07007495900601400701c46200c1c4d0f071a1030940019400c0801034a03c2562041c0700304034010010070010740181d120b03d844810604000c12071070100c0c0c403200c2c21030303c215881000c031002c0e00c07070302c9204a030820203965480414144080c1c19400c1100000303681c1c2c01a04402801540c451025048003102c2c00c0c58090050030050080d95144554a402c0480390818813070f0344415088494112203510303010034100303c601c0024000c117140d03564501d0748051075035840551000003542001101c010580600c6480e002c1c14075034403038802840c50298020500fa800070982c400c5600001c5003072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 61279832 1250 61278582 61278631
    0x30b01091104171006030639033201031403181c0b0c091003020f070b060105120a1406010309030206060118091104030515100506030712020d05011e0f031b0305070617 73
    0x8c0d40315140518000070300c2004240900083d1100441c940701d207042101c0d40040036019656054160b92296209013191548a1075017617076070044000000c10783e0540d0a0321015802c2000c1d40c0c5006100e01c0407502d0401702640c0768400c07443d100b0342e078284c050f00d0001600d981500b013880c0c0341c0b012001245011860b28a00001105250241400c002c18420024010032166032141055134216840000b000180c0c0c14a071290304c00400c82070f6640302c0c2c00004030000901b2580a407280c0400035030103030081c0405980381e00044070414420101015042480f01c004600000c180c85420001c28540c61020f0756a81141030052400701d0340002000002078440030085410340200f022401c0310002c1d6001510ba0300d80c0c0c441541c00b400e0030341d0303074007400d0b88007084c00e040800458108904842c8501e442c80b035581902c0d0000014500c480c05041409404140c08000081c201120340190602a08000040035100d507240e0b0f00307004a943c002c0300001c00340d04001c5100100d82c40c0494026440c083c40201d2240181e07140d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 61281082 1250 61279832 61279931
    0x703050f030418090602040b030a0e070636080709150e0606070602030c070204141803041d04051e060406060503030406120207021f09030b010911041710060306 70
    0x2102c0c0f19a00e880000081003c60b80681d006041403c0a06841e4582035000c28020905e040b004001403041000019040740200c3c68292007410120000101a01c0002c0c050050b0b0b2402001c0c28000c40300880000e20604144000f40182410410204495085d210500c011400e10b4000b03503070401c011418440603541b0038089440a69222802589070740e1000104419400b0300783c4065007250500d403000000f800700b034441c1131040003810190100c031104011125624042c80c0142d440451588a0f084000308102d40035a82c024070074021504080100b480c105503007805404201015402a010b01042280c1c0d4010180a010140c0045081525200000304644110450390400b164005455815520b8040495070a4030314100c106552032400c03032000b80001400d200a94600c0400400030a9883c040c4c003c0c060000c0d03c00345810708090a2010031088400044801c4078184604410005a003001d4084c600087d4010030000410618003041134505403000e031603070354840d26003508050309120310600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 61282332 1250 61281082 61281119
    0xd05070209130609080d0e0607050313020f1206070f0e1003110705060705030106020d0c26130f09060605071203020904020706020409020307030e0f0601090c050909090703050f0304 79
    0x21507584a44400c000b50030041e1030308030301030145401c0c40414824404241c006255242c0710020400681c01010525501d4030b60903101c00340007a00030804542403400d0509016041d60005080c0300182100200280354699442d2600803541c0003001008011078010000307081300c0c2d4590800d07000010181c80020318103211403c600c0f0a15545203250b0032001400c40980c1c4e0700381d40c054121811800c20107000b4103541c0091152000502c50600d07180f0742a03103d1400c202d070311603000701047d90001800c03001d81c43c00c401c0442c0242411505104500642c000700020710014800c3c004521459410710b08000182c80c01178102000f400f90030010000029144c140c2c800080c80c07207140c0181c8403840c4a0000b40688070b400800b5109074000714021841911a038015401401961000c1181413840d501c401e031100084281490036801000c010003000c0c955030843c50f00b40a0134a0020f1030240d43c0d4001502155080d240c107550360b404600c090040240410107201c4502c0200000e504141c0341506965013202d0409 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 61283582 1250 61282332 61282339
    0x40b03071203030c0c0f2a0e04020d030e0a060908150106051c1503060b0a05040e0a12030906050c1b0c0d11040b210c0406050d02010806030c061908090d050702 70
    0x2050554141714050b0880708a9020441c405282c501d41400f0507110208141e9017003103030110200384c2116600c0b111200494110300c80c10429a03507540c00300140d900f00000d0640c103001c1c900c244207000b030383e980308040003610b05500d4001c406428079900600d08001c0700d103401c0802d042c0c0c3c1d005101c080d0b0000295940c0840124801a001544c0030f030240c060085616503000b000c400c0c81002c402c00031a90480f000e00d8005139000900c0c01d41e140b0070003003134840e00003100c0100d420003c03103440441d030f1000c441c0c103600300582800701d5018016a5140300f240c0b8111200c84100d00081001d00300030325070384450f51002c5203140007805102c2c0c9031000201949403402c80180302c0349140e5814400d5880315005082c841c030006009000c10103558000032400010604418054043d034810110f40d0b10301445a0404d560020305428050000c95005540740500a00b8440c0e00d88900d5003100601d5aa00b401800380f4038150140c1c004880380d00c03074060560840a44600c0c3e16400621400c9001540541624506178044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 61284832 1250 61283582 61283591
    0x705040b1e1503090f06100b0703080406020c0a1101030c1e0c060603050613050f0307030c0f0809040c18210209100b031501090b09010801090b0103020903031206040b0307120303 78
    0x3600040c205070840e010400b46880c003c800c0103250f19000c00d9040f0400700e000261655513642c6107000621251a0260300011007082c462070000c13030304c100903c40d40984181801490300c042e05200d2849e01c600e40754221183e1094000345212964580140c031b07100c2e030850512108030210102000c0c0c0741c2d2520380000c010000d44400070742c24081a50049402140c1060a640d8141042001c0210181703082d001900c1c1031007115031500401034000100c502442c6c1642d41c03881c1c000129660480f402c2d440301801d4801c8030051046034500d907210b1144554011607901c0d211142014200d85070245090b0754442034083c121301c0b460845003000c1c9000e0340c5070582d040310102020f540d00c408141d0241f0440e00b288140f017a0100400100806401c101c0c40850826201d07811420350b250081600c034440c000d80381d400904108010017041e04142c1281001020504015082c50000c0c2c006c01d03d141c001710702c0b11002420352424440c050a06110b2010240c40913000b40c40164140700410135901c0c3c4030385008040641d0b9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 61286082 1250 61284832 61284889
    0x3020c0a08030f06090f040c0b070303061502210408060604050402190e0108120306031e01111309050c0c12070f020a03060903030e01020903070b07060b0402041203020705040b 77
    0x14044100e11035070154060b41c403410000c2680700c8540d01160540e00a00810300490070807a0b904040e5442550320003c000c48181c01d044000005820822040303007407584658001c900c03911105840d1030306900704e50042c24080003880c01c4810719400301e0850b5014400400007070000580c049940d81d4890003c0c0c40204198466101084080c0e0360301c5102007241c0c8202c4404107060048824050499400c442190380c0900c100d0341b58042444240c800e20350640c030203185841007480c3c1c220303a541c2c3d1808030000000d10003840c080d061155030000c40342d90b01d101c0c0d180c035081c415002c80d44103e603089084441260b05000c1d40903e0f440e038400d420002ca40660300c0225640c8100b0080c40b414045e07565001d0002c180d8aa40c80c5400d002425462104401090a0010b0a01b80380414400c1c0c40a181c4010002d24010303290100100707184d40520b4068403225140d602d254007075182e5000500081c05d441410049404243c01e000307003440e4060304014440c3d410245004055501d0f15140070920940b18000c0c01c03a981c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 61287332 1250 61286082 61286107
    0xd080f070605070c150b10081003080d0915020309060609041407030b090606030607050904020c032a100603020a14040f0c05040f0f080a06020306010207120b0402100e030606010302 79
    0x4090340148018107020400150a07800540c44032034a1252440d01030040300c0d44401d10a88840e50038040c6c220413020010784001d80f1402c1020340040e241d43e504101281c6903242c41d1070541c002080c6204960b19000540c1c104000f1300800749900c1855101103040d41030401c3c07061741b1004007818240c4140040808a014488000a180202281c0908803050302d42c1c4c4c0e203021035803d10304441d01001c1d4062600010070904011031f00c4c81c466480d80c0d981918001402c0c04200c0250401c2410150911051040380512080038904420451844030307030700e85158005a00e1880d0000301c20040351101c1c180041000141c944078400c0c801c1c0d40c901c11101b007081c25403001040060102e1400c0e002c0850525002a100c1504100100309440010310241d0f01c03642c031070101401c500c030240704012041d4030000100010802c0e40e03010319002101441603400160f85e4040800c0c6404400c5801d41c1d0442b150b030140021464190801d00301e01e1030034141072a02001070700c00a500d480004103000d041c95000200e541d50001d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 61288582 1250 61287332 61287337
    0x1e05060903031b011d150a0e0709091103010c02070b0d2a20010b01021002070611030115080a090302100e010b0402040e041509050a03030905030906040905070e0a050d080f 75
    0x18080a0200c0000d2a0f84c0c06003410002000c5481100c028650b207100c00403c0c1c2901200d031565100003d500d901403120010040e8080074419406072603004101c00f4004d0044d1801a805480a003c2c0c55882000705400c407041165500259840304c0d800308100b00d240c1e070556558014075000010703424184959003400c0600000ca00b03000c240b01c00000360b05980c12501900065404601080401200080680c22501c1d1000c120f03000d82c2c08144000e0041d85d03203400401545109030b0002c10405020118556503800a80000120005262001036825801064158001e4003614180700c1601c0a0b01c01949600c1c41904940155031034040391a80c445003500007981070100075104640e690b558111048881c801035408442c25041c2510080020004d07010f0a414190030201602c440101c42d5404e030700528400d0801c0350580400d01034034010703a403200c000e040203000700e00c1c1c00304a5142c00580100040c0080c88117921032525010306011548901c0344048080382e010102941d95024032a00e0340950 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 61289832 1250 61288582 61288597
    0x901060507051c120c0513031401020c0109080309010e0601060c02010804050c062101050d081603110a030e0f0306190f0605120f0d0302091309020607050106030605101e0506090303 79
    0x2a07028020610105a2000118001002c000b04c10004529841011905803086004078412108810018804942c61042000c42c0d01265000145003812103a00f85080d01c40c8601c050303405000200400c14108001e00916264101510180030150f042013006041d0644003880641040726610005040190800032880c01c1000180350075114021303c1840d0f110184038140100c0481d281c6400040c043c18010055160710340d10800007414003404001090400e000003034294104040c1c40082410204140100960203020365a06848003002e00c062201e80300c0030504c818000d07842201040304030380f111000184054024200850701c5030080340c41c100174140d9500226070010708400c0c1c0b0308403500001880304000d2416000e86e02c00080c01c03070064080b03005464101e500208200b000502e801843d52009682c148010411800c1100c203848190845031150412541d00d0350311802e002c03018044c506c000c00102020f030f525010224203182e0780206d4607000e11900707008840c080f81d0318070a590140b00390b5003030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 61291082 1250 61289832 61289863
    0xa0305040303020d05010b04172a031606051216120b010c14010603030f0206090304050910170a0b16020304050d0507120506060103110f0922020c010603110906090106050705 76
    0x10b1b561141306a24960740b043c46594441c0101034110307414050040b407051400f142c41400f1803a026a40c3d2401025408074106150345030186d41c00740c141e014691a0808060700282d561540c0303030103c650614008a4020300000c2000f0344904650041c1030784444126208820f000020071030800d5100180c62011002e4801042c036103100030003000f01c40f0154010402c49002c0d0752000d44a078203804050ba1038460948681c1d103a03400420081c0001d040c0340c00741a0300901909401c2c0112556058038054010b03110884034120b0304074580243c1808076100300e954110001c070005007421004400c010391740b48260320515000c1c1000703561500c140002444098000c0000007a041080340d001d01d413640c0c9803502140e0760760109140c07118038143e0f9a01e201c1540c0c82c0c410040c290310300d007005900810221070b04082544d213204145142440440c01a40090141c800e481000400e401d030540c83d10313031070303d804100c9814011250310042104e1592400360403411540a410000e80d103054a0416904202400030b502c180d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 61292332 1250 61291082 61291091
    0x20a08010e0102030a0b0a1203030213090203180d050405010e0f0406080d09030b010b0720041b0509042a050309121b060601030e070501050d0e10060302120703080a0305040303020d 79
    0x1c1c41d401900210b1081c420030000304241903405040003c450098042c0b000d5004482c0c0400300003e0207640200003a21514014044141d69103159a00384d9008490b0040e000d000014a61701d0260104102c40c3c001402d410035500302401e10000070080c812980358144114010040c0107660f0b201c1c3da102001600c520801c0d20350380382011501401c1c43c0040d00c821510008410700000d0003180c401c0942d206c49038490401010304415419103600c8124814020307500a546100798181d802c629011040c120b01035071642600c800c943c008200807503c41751120448648032017945442c0503a03c524910030071601e2b080072602c0e40c0303a2080107460003400c042607100010340000c0c091004955400c00d00819440740007202c00c3ca9496200440a443c0d41601c1b800160348040e00074000c96009001901c42d0420500001480c024082e05403498105985c4402e50a646d840900b4025400c2462061000f680d110b07004206051545e6680301c503c0c458000305808065945010804040c42501118a01c3c0c05200c0c0911 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 61293582 1250 61292332 61292351
    0xa0f020c1002040807060201050f06060307031404060f0c05040b25080304061e0903090501111002031e070215040b0a090503070b010602010c0e01081306060e0903030402030d090308090d020a0801 85
    0x1c009510a020307440710ba00c100354000803028414013869215401810408100c0d882d1034084c005550006400c1d08181615000316860160b00b40403800e2181c3d006000200744200c074985a58201c1d80042d8004c8100001000184240781c054411036044100306c2d80c908009002550441250515180d8002d020fa00d00006100500200f0740003000c441d40002480c03900340109007440002c0318142d0800a02040b00f1400800c12076018822542d44407804000b030f2000043c40a1042003241c0c000c4420101c081c0d01000300c80d40c044d09500078690710040f0f60001b003104003100c50081c0c41c81e80c0024801842c084083c0001090b21480790800100b081c1c0c0201125182c0c4040c0c80c040b49801024010100151318007510015154820038040483d21010307100c0720042c0d00d51040c0c0c0f403030381508402c0594000c1d460307031400603901041c3e81c141c3d0b21a102c40d10240d038583c1010301c101800c10f0501405241003011800c01030012440403021039842500442c1c4403c2c40b980e851011407803200c1c8a40c080003580d4a4042c911 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 61294832 1250 61293582 61293613
    0x31205040e1509010608041a07020f0a03091d0106080f064501050604090e033a050f0109180210050a260609040c03060c050406020d1103030a0f020c 65
    0x5502c2d140040340d9010840c0c2c0c80f00c00c11654601d04032130280c0200040e0840c0c00352062554405508528207105803059911507025440c50054004402c40010f2010b032410003940c00140110000c1140010490f401c03035150400c000c03d0180c0c0604040c150070034903c00b0521640d00d94038513009031908201d016040300c04403c0b20845a40a0400c142c10030540030070041800b9448070b07002c5058410052100341850308050205009000401d900e080b10b10042151b27641266000f4510385080d03800050300c0d00003552401d028140c0075100b40e83c8020f05130405003404401c2000c0c81050381540c1a0b50310009500c0340401101c1c0c008401c4400282d00841c01e84144000c15a0140081842c4c5c0380a880d82e185000c0c1c0f10300d40043c2c511218a10321403504480010035064541001095045030042480700031461300d82d100e00302110b542d803e0140101c1c400060810100d6010710080c4180c0007139080ca40c8006640031610340c1c40c0c0c0301c010908498203580d008180c9102c0034940c1070300c0c0516040e000700d411240040c12003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 61296082 1250 61294832 61294861
    0x5180a150206070801031e05030d06030620090105160305070b0c030a0605191e0b030f0106030e0109110f010201020403140307050c220515121b01020a050304031205040e 74
    0x2114010b008810015a21501a090403412a03501c00c0400d0102505000110f60320031203188100c800e0b000400411085034200c2c0a0800038501a510004014ac1308103100d03908030403100740103410004240004003c50780c02c0010f5860010070700301c01006030b10f500e00e81103d940c492004020010101c4e8028414010344400c0a188a03e0007800e003002416290b508104103000b01940c036451043c000354080c03140054070501c8580452960404e10f01d020b44402e20030900d9001142c0038020103a0b600c00412070268075008900c5103062a100801c0494400d403100075040e501c0c502580c2c01185020302440d45a4403d42c1110011900282c1d5042e41e105200e20041d22540103030801d850718071400c80108500c1c60030300d40c44245281281c0140b407642c20540c45400c0a4900140f00b8111944201d48100140e151800e000c90b650340d00c07802a080740d0727002501420400444810840c1194089104c001c00a4400011034007a00c2d0011503488000050b0002100c0320720464001c0315000400c84184051921130740760 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 61297332 1250 61296082 61296119
    0x151c0e010501080708100c050f0a170f04050a12020309040c02160e09030d0908070b04050102130902090d02010e0d02030106170607020c06090f012309030114010e0705180a 75
    0x81c07125990310444242d07201308901810701d80740c010001d580c104000782c1c3d100010f074140b641000d07401e1181c5844144c1294000303004c01c0c0041001c0c0b1900401440310f1501080c6d101110a41026440c2441c1c1c031000da40d2242100000c00c6000e212140102c5940208191145000d00402c14041c038002d800700292910b401a00c1c2c500070703425020004ca021102080c24900c5100ca410080d0304001d220309100010b03004081040d18600001c005480200703810580701c030300c500c0c080c20003d607444545803c40305200d60310380e200303051107407040c080b2115999803807074906101b640902e4140080760311200060b5802d9080c01d8003c1d8958038003000000c801200c0120720b44400082c41c26100e190360b40c4401a80c44141e00e8400d207510150070042c1b1071041c50400c0c2141032090041c50219041c0100e204500c0003408011000d00c0001030104590006140901441c1005503442e0281c0303019515041d001c0c4441c400241c1510103000c0041851906d00880c0207144101817002851000010358070602d080040301e0944 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 61298582 1250 61297332 61297361
    0x180b040b09090c01020c04020702030307120c0204060e240a060c0606330503070e01050318120d0f1b030b0312041e060201090c350d081f05151c 63
    0x555410f01851f0071302c20b60310403d802501961500040340e0720700810200c0c0a6101c81880042481e03c80540c0b0344d0302c5140d000d89080740c600905414400c071810000c02d42c1000b240172180364611a60080e84980510404440c0700f420301940c0d03c180c91911030f0182a032500001c9102040030342c07080d4482549640070090210441000504005101c0c0c221386600c400c541010104818400c804220751240b070046038482c0c5d800c0120240740720304040f01c1e8141410050441d40103040440c0b1150012040d105090281e0202e0201300807100e00401200900c8003600c4c0e0074400d00d90784910310501910244a07101c0c40020840d03245568540350440c030361011201c450b00d10741b0240055000700754240144140c140294000030310ba01660b1030308808070600d42182c1d041c00000c0c42c42c24000301d1016403c5400050348220000a000b5880403003800510b2142d004103468050b1540070240008240c01c0c503051420b5420660f40000c08001c4031411a506201e10351000c0e0b5103800c8284e0186141c1595403200048d00c0da0203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 61299832 1250 61298582 61298593
    0xd0f050c040c110c0904080d0c09030c05030706020c06030c0702090903070c0b040b0304110307080d120c0905090a09050c13050f010501021b010809072705010609180b040b09090c0102 80
    0x35038102c0f03001d48250110a103550040003008410324151072603035803007442400020724281d0030810800a41d00c00a40000205184110a10401c5000020351001d480305800800c0300030724080e00255100304c09065030f1702502c000000b0806600e1010101c94400e0740282403442c150400d01d030619625440104150391520035182c000c41c2000c1e8040803101159000d40c00c450458440f80c84840c004656520900d0385441000b10024082c202402900002205516100c00310303c8000441c000303840b80c0e100a0700030071041503420310650341e8152600d500030700b000034000391005c410714155181c80c1140e05e00a90040c0f425002d80f0002c07d203504014401d0004500d541401e0340da4000580e0f8614040c241065004414000002c2d9544106c06055000038844112141103680e80e80e00a942086011800d4590303600d0242e840d034030002070090600600191405000152a100c0b0b02c420660342507c883c0700d05911041c1c9481103a407980c11200031100024038081241c01d0034810b43e662404180348607409401035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 61301082 1250 61299832 61299851
    0x601060503070e0a030c0302040b040b040e0c090603300403150603030f02010506061b010f050c032203050405060a1718071217070c080a05030a110a0314090d0f050c04 73
    0x1162084085a41c0306c000c0c00072103070130343d4200005080c6c45100c5582065440503001400c0d0707128001c3c51245d290800182c884103001c0780901030900f07401041540264410307850750320b5142040c112880000324503208591801c144180d5044648038a60015060041d11002250b884810342d01800840f4402d072100702c9182c0810f20b01b40d00b606c1088580390740c040414400600080e0b03408846c00020706610f030001656401140314142243e0040d15000b2210f40080304004001100300d0703050301c181c184940d9805020074a41d07001003091046000703c1d40a01c03c0440c0d40c1020030300941ca0114002034151140103c0c0c904552a42050034008001b001580b0079480e0024084032445c03000300f503613500405040030900300f4880c0e184c0307294403020040301d100d111003078005001c4005000500c1a24131030f40285545150011008160b40d00c00a1100c140d90004a007510001e80c2019200e040c40006c20343c45901c9107001d100107808500207420284ca01c0180e07a160382c00704200440d15150480f07040f50104505d841 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 61302332 1250 61301082 61301089
    0x515010503061006050d02070f060614061204110f0306040b070909020903070b1b03071505060603010e060d020f0a0b0c1213090b0402130b07060c08160c0c05030601060503070e 77
    0x2094a0195004002d24801e110892080c40103000034107546d2009490000380d0b540703094101c86091401d9800d11341e070703680601c80300310b4800c984100740310700300c2e115400c0c4031817001c0c1070814903000b4100030620181000b80e4041034440542c2c0800781c0c94001c0c00d9415034070303203818624402c200480b81d020018142490210324507844d0301c2030329542d8201800030500c0c1d60134240341c02c03110351003440e000d6001e000b2610303c001c00041c10001020080e1144d55006800e0144081150540d64040d150034030907102840188621102800100e501120407a0245210300880c0042440050703004807081c0c024103070120215149811400400d07014401c2c80031100c07009001d44814001c2e028031244c3c9400a03a01600c108400500e50300206e18112000b4030040c981248100c055021540d107a1044c0c411034008512003041c0413551140100c1400507081c030340c0301454074080d580c403210203101088050040705c1c16118240300315218004c02800019080303034100d503155030000d00304c1e820854000d000036220ba00f8840480c103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 61303582 1250 61302332 61302343
    0x4020f09120601060207030b0c04030c0f060306060c151e020406020330040f03180f0504180803061203040b0a050301080d020f030403031b061b020d08100b07080708070515010503 78
    0xb0145d602030111141145c0d140e4807034550141c0a202d0882090201001280348280c2c00c5000380b000340c65881c1001e10308a000307419291594800814401d04505500200d0410744404000e1b8240410000f68035582100401851100d60600901584081404200b01d074000000300b6a02c8800c0e01040c0c000510b01050003120014821210204141c505c003203000501da410000c0c0b0b4040c0f01c6d040c60f008c03146010032480c078010401d9102d000c100c0100401001141490b00c280c214508255420741980203860300c414a00f4807000c0e010900400e0a040480c00101c404c0c07007940c0c064400e1103017040da260705581009020790402c0c041c0746001d010388589040e61900014405030090034940207141000c3c034544050759082d4004002030851200c0e401a20300265891081d0b03030824600202041c2a010038400003441e118503000003c05000d5403a050118000305070041404031507045510680d541400e20703000d5543d000f00c0000422900010403184100240425481c400c00340c6c1180da0401030ba42e900806940c4e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 61304832 1250 61303582 61303589
    0xf0f1e09051203070504092a0201140c09030c060d060f0b04030314030604090f2a03020d060209040914030c100203040b040303050c041701150609030309210204020f09120601 76
    0x19071000ba52030700d034160b0b00000745030b1028050a100d410a41c0c0c9814041c1601c44109544c0d01045c526200d20001d81c180a01c0f905642c00c580c0b0080200c02c083d0b0300b0025030a00d01804540c29540301103141c10465604004800740041c0280c822a110b00141900902400c00c178062003c08000510020400900542c15507049982640d290403500082e90400300580d40007408480d08107171904850b10109154101c001d1000780701d52031400384002050401c0c10091a0244804440004070800700056561600c50020607a00100c0050341d843c1e14000140c010090038074000c0c0070202c940c0003204d0004010003e03250090800040e11007402410150108a202c00c80340140004044408180441e10a503c603d50122280044500c1d0940710100090007242e80c15004450383e441d1005001c5900500c4c0c2d0480091160341814200d540c1507540103000000580078076251410105100ca091048403110901f1064000d08110b5076840d24500085140d400b00c0c244500070040c031401c404001100113a000e040307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 61306082 1250 61304832 61304843
    0x80f010b0a1403010603020904050a02030c0a0605040b03270703170306010c080a0201091b0f0509010602150702070f090504060506010810060311090a090507091e05130f0f1e09 77
    0x85081c1a4102c0395000d84a40c095015940c9003804001038440c4c0d40c4203805a40984020b210307801991040614140720301440c24025174554504010b115004002e41e02560810a81680c43c1d23902d012940380221480701001c0603013a4440703080001d001d0041103510540c0c2c040c2348102e03038a00d030042d1140801e1000303407159800a81f1703540e0100042034007403000d8540d00c14188004074503142d803900c901d112180d00c03181c4404401c42045040000c000740494903c01088203940c40f03400342d0b1620402a403100030000a4280c1ca802d584009980c2d907100340720130070150442e41031a103459502c8104000040c481114203da05a00d4840400c59660047c1c002ca442014003445118900381400000c41c0580307030328100c0c242d8a01050200c074440740e8904041002901c0303c140b00040903e84194010010152035101c00280c07040750605483c80b040c4045030070140c0750242c8142460342c2c24030160900820703004110b400c4051420204102c0d022280d0880c1245641c100d14001200c984d10564008903003040000500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 61307332 1250 61306082 61306099
    0xe0703030e01030b09010603021b060910150308070b0412081b0a09030b0f04060507082e05030102190f02030a0503060d03030e03030106080a05150f0d061b030204080f010b 75
    0x24840d1500c003030340700018500451405828404903017170303c1d402e070020000301c0d4010941d00360511030980483c500311a800001c00142c10014500758031000303140701d09120380e03482e40c240240205c0e04181342002558815001c0f5075511590800510340c0c0380c150f90440d60900034182a03014684200c003010b0040c020900420042c9d510120303103901641c0000d5500c0f051164a000000228072040d0b044c51050100904884286c035003840e1840c122000206070000744806102400241c0d1005d01d040d12402e03d40048080c01449013416080c00e1030199800640e2540c0005107084101a4801c800010600e4603104d05100c2c5030034030f0f02070b80c583c0150303c1d821000600610001f1560b1030001035110015001e03080016056000840c410f081d54000d81000001c27884000500926824600c9040c1e4800125502c1540c0307082c0100005216074030103071560303104000e4896002c040c40841e50003105c4444d0315212a00042100403c0540a90054898800d0500503060030704100d5406000d105406c5200902400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 61308582 1250 61307332 61307339
    0x1030f0506010e1e0a0b0408010f020f03010b0a050403060504150506060406230708040303020a120306030b07030e10061401080f010e010e1e0705030a05240d14060c1c0e07 75
    0x4242081da00600050090105495036440c5c681c0400c003d032410301280c83d619801d001030380d402c2d5142924242c580b10320405c800c1e1020b50300c035029a81941d42803405103a542e85280e00480782805030b60070150a00d840d00302844104800304026402c0c01100342000e2145d90b5800e02004a01e00452103583e021850071030088606c80c0f45444003450421208119074249481798503104502e40141d0801c60140c0d02c0000f0340d0060110220803030461b2107441c0340a03c1100d06503650010000c0c4080c00302c0040c0f6440f04000e10b1644024003c02c601244449010815681c3d1036400481d100f206940c0c01d4042035020010a642c031107607000b000d043c0c078150001d0400903460b201036420510340042820200d400000c012110100350909468080c0e00545d9400d071f05c81c01d0442d84074049541c0540303119219092600b034041d541290011342d900c4040c080300d01007a41d034418204482420b4000ba0050b913070307000f20b50800c00e044005030041c0408007004221340404c194400515400c40703200700070640d8a50711010b000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 61309832 1250 61308582 61308589
    0x406051005091909050a0503040f0b210c090409051c0813030f0903050a0b07031109030601030314090d0804060201050609010305071223010903020c010c0201080402040207062901030f0506010e 84
    0x240c50aa09242000a144e821a04d480e411700a0241040303070f46401c00a01006a017080074141c501800403440390520700469000e20f140c2066202e46984003c422003000505110000c505948401c503000d402402202c240d0325040d80c0342d010b400046050001022150700e100c0344190501d42c0718941c02c2514007150181d035107040d05c0b0220781c100700f4000c2011681c03003c000241c00b40000790155104644c18092130a00e49405800c3d10805030520709148401d100d9000d05980026099044a400d0b0400c00c0c103001d64071030048298491010241e03004800c24030072000b00180c002c01402120120390007040581c40340c208002035620700f0310000d0950ba004d035070144255000c0314031403200301c2d2007a4661021281030110020078810813580100740ea035912074881d01070640501c9801c1c916902440e1400c0f60118a40c0080c0c024680a00041e020340d030b0204100040112507448101018048400517144615000d0307482c000a146140b5203001908004038500c04a0043c01440e0142c1c105840300040761900c3c9050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 61311082 1250 61309832 61309861
    0x30702010e19020117060301020f190f08040b071809020a020303040203060a09020303040e150d0b0402130203011805130605130c050a0506070201030902011218140303070906110703080a08040605100509 88
    0x10161f01d95070810000e11130040b140c000f8003c4001540c450100c000e40c448018000707528070780340c41041c0501c4808100001d41e5000300726038041103d0138403850740d00007160b2503000c060040d046030180520000e031004805800001941c4a00d10840480c2c0c0c0b1030707444403c44000c0d109542d0000790164000c2c0001d102c6c07404039071205540000d07140701d8058030411030710003d2029200e8440681e0141c1038602031005505205411134802001070100358699490308540c03960400c0102d019818066803600410003200c0050010080030780c0202040c0007500b001d0082e41c4040c0e8a00000300e54602503150001000e091440e01802200c10003000071742003420700c0d0010360291042c60b40490410031014145082c0c803859208100140d002c26276803d0710f4040741d1a04180c0340e05410060306540d4414002c110103a64006540c0d0251002d9142058000105074156803500c401030300b00404050003c10440d0b1034542c441c0d1040e00c602e0064000f4445034a42a20030703d49071b00302e40a0380f80c001a000001407414244da010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 61312332 1250 61311082 61311091
    0x21020a05061602130902010215160c0f050a030f12060303020703060519091410020301081b03160b070606090b090c1b0618060106080c070f060e0102030702010e19020117 74
    0x1a00c1c00c04020b160b000911005041440218040e070354484541996810044c200d00c8429241500341141032141003203114000c0d07441c03424200126030951504200c0400b00d4114040da00104442210007146800303813541200100c0f07400000c1c1101c8140740c10b03052500542c021a40c01d0b070003819140c1c0c119110407014007001448407004549444041c140050b09209401d2000d003c1e940603040e05501520443c10100c4481945401c82d005100512101c0760204855803000194101680d8480300c08002ca414040d10900d02e00c4200c0c000c20000400340c0c9214010000305114510401816848003420030031a20040041a04087c160000409070403101c6d0042c4441035490105090360503d2600c15460070804580054011052501c105104601040254050401410282054a0b144481d05001d0044500c054802440c192814050014940c0900c80512182d8025943c91a004101074040d000785038164110340305401e0178090b40d002615020b0342071541603581034408440c40041c45181c000103130 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 61313582 1250 61312332 61312357
    0x504140c0f130b0a0906090b041809031103030f0103030e01091805090304080304030c030c050f01020a080a031b020c090a020a0c0f020f04060303120501150e010809010b150421020a0506 81
    0x800300342c000158014245103203055441c2d585e01400c000c001490714200b80e22015000b070043c0414081002007022070000e00d0522540010055440d0808a450416600542c00035010010500082c0407030749035160705072800707a10ba010301c8510007070044501c05281c1c400c4081b00a0120700e05000705c0d1081d00125040700c3c024080720300b025220320240b41542e00550044030130101c0c1990030001c00c403241c958500202421100a5050a00300b40041c0d19040a1040200340402c001040b0751420302a52286400211041a070389140c44204006991041d204040758442c5407448001809003215000300c4820703071a5617543e600d0a8070140d0754200c803440d804908136031160441402c40c0b4940c685200362270003140a41e0399401e1070303c00006d10108881041e00314120002c64030741029020703038002c84280790301d0200f03180c2030b2056030b42c8800e001d00524180385c0072035200400c40030304119602e0880150040c0c071050428901d400c41c408a2004205e2099480290030a03c001c0080295113030020107081d0003507942 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 61314832 1250 61313582 61313617
    0x5030a1b03090302010c03170702070e060a0302030c1012092f1c030c050105070305100f06020303190b030d0f09090b1003020304030207151d0f0114090a030b100504140c0f 75
    0x40c030404d23229941110716500503804800304202e07014503010345507000401500c22a0b5014150380201e51031f07490302d44246001d5140b07000389001e02d0344a031181603001e04c402401000f044086191010030401403400084046010084c9501c004601e01c03011680210020058501e22500190688282c0200441039040c01f401091a001042c0c0a00503644035812a03500011a8608480f50307440d00c2803d6007040d040c03032010364410320515400100726500450100d8404242182500050f000741c88120f11454060040318a0490350740d030490820b05440609450ba9681591292030700c2044403144074503c0c3e03100d0032107601049024000d500035038002d8000e106507180c0b03507114064078100c90300c0245440700145923444d1480c06610300c00070192075010211048820001d050000070002c00381c004002c1801ca600044608460352940c1182008683c0710b19076501e07034903040501c06100c0004d031003810301070380c14a2400a060608026143d02c144840040c50341821034504206505410aa030144000501ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 61316082 1250 61314832 61314857
    0x609060d0c02060c070c1404020f0a020106090506030a020a030b13050a0503031b040b0703030c050418020702040b030105040b04060b0a0506040b0c0c01030b010f08061c05030a1b03090302010c03 85
    0x8400003400c10040c0d0810108141000d00402450700d040140403401c0c02c00c060240100041d8a0f106075002c566244c8a41050768200700d000600a200741410144070107000110113141079010742143d003c4031000c6904010315950311043c15107941020700002c0d0b11084120303080c40044c0300740700c030360b504030b502011111b89095096860701c1c90302d02610415aa542e00220403c1000390314240e1402c3c6800d1124a86400e09260080c100c05034050400000c05140e01d40e0262601d00f032160042c1c4d0b0047c0700102900100301e4120540d20b000354060704041e03000358241221407111317040500800d4040e55121212803001d41c1c454540f08000c00b1903c3d09194080707007541000800365036a0010f440a0446010b000d5950303880c2c0300340705140030800307001c142c149402d051001d103080ea040040580700300e5403801d290031030350f85680016004405c0e10510102100e81505140c0521000102a22601c0c80d40c0d1904410380000040d4485015100840100001c000c48014030040d48580040c4a41c03911a050448207a40da = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 61317332 1250 61316082 61316089
    0xc0215040b070f1202031611010c0b13170306091b04050915032a060a050d0c030606080705030c0403080d14040615061103040b0901050409090318091a0f0609 69
    0x314141c603030490141a1030184541d18209914501d0540011071905141c7c00702d605925211140140401810800c03815081e4007a90400514651041c001179281c034210000e0f013040700c411070080d100014940c8854034076803180070490b03010f0b25006000942030743e9000c401c00800d10242125801b5900c0500c0b00190980380e005843c0c4c05031188922080044040e80c0c1031600d42080c01e143c40707090444406081000648000c071825000c41305545041d50782c100341c1000c2c3d4a9102d030180c0d85030f40500e000d030001181680b6038410010745065542c0c1c2c8a160f15481012101030100340d86d0200301c0c7c041000100001208200141f442908892010424464400074152403c00455055500903200e1442d15501265401100b014000740d060032500f000180d05800e41e6405280941d034548003001507034814503030241050390000e10b1100002e00c911091031070000d007040c0c070081c090300c4480301c41d03d004185c00d50140034613000d00c00121415054403090300200304000c400581c12940041d810404d07240caa0703d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 61318582 1250 61317332 61317337
    0x705040e070e0708150f01080a0c020114010e04120801140f0d02030105040311012009090702070b030a090c050a0518060406090e28030203030a0c020313030b0604060b09010c0215040b 80
    0xc0d030f240c4a180a0785030851021300d07246030000c50b0b01e10400c52512404c44a0b80c101c3d4040350030006120001840a00c22641a401082e095840e2108250075900010f00a600e001c0707005d100d2031103101d05603038000b801d100658401034207020740e0100107a1400000100e050100c16400d1214000b010001c2030241c1e074000c00c0c00c450f0b00341c03010350001d084c91840c81444e1209010fa21001021300061450f0003141100c0020b240c090410302d01c0c818080c1a0110364000c0c0700f00b1451002d0485160240c0e644c0c1800e4849400504460208442000c0c0d42d0000248920300552040115580545590315000d0602c44945e800ba40040c0481d074400d9030b40c94041038440c8244925401000650014268249002c1d840000c40396030101c0d40c200100300d1500440065400310036a0780110030030002242d207850701107041c0c0c00c602a03a50350426011105d10f000003403100c5040081d00940c2c0c196800c020050301d60350b02e40c4d6148102c094039404584001542001418200c0d2044000350705c082d02c140c105500c56510b1203281c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 61319832 1250 61318582 61318591
    0x40f0b0910020d0b040c09080714041506020a032d030917030903040608090102040515030403210501030201031b050a0509031c080718030f0f0219030302010501080f0a050705040e070e 80
    0x455a139222030001d0f0500b485515604845420407160b46403521180c0c0c2d5543c0c19500a581e07100c003400813000070325216030300086818068442c3d2054200c0cbc072104000d51340c030306125040e000102480004806e210103004050409941c010281d681070301c0061042c1d01500d0282c00403100441c44041c40a500b000c00009140520306640207103580d68a0014018842c0b1406000c450040c0d00c108170030445a6114a4110241c440340d50f1015140c1d41c85044c10748180c401c2c44500c20600c21a10781c511401041d651100b4180c80c400d803010449000780c102c0d0180542450006c54001c100104040c54025001d1800380190910040c2125443c000858418070014940030900000c140b0a006121045402c8500134590403003542c83c1c00e0b116803554940d0a41880350181c050b0640301e00252920640d29502c503141e81016142d0361b2034010603a6864028000c0a003442960000d0191401c031801b000c0c0c1c04180c000c0c1250f0800020042d450501c82080000c00c5d1001e0005001d1046100c00900f0000f80c1d1401e9201c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 61321082 1250 61319832 61319857
    0x30203040f0e060306040314220518160e0409140703050d050319050c04090504050a0b01050102010e03090f03030c0d051909050112110405130b1305040f0b091002 71
    0x240d0786880c1c4001c4108540e5080085824040e4040064076140001d0840d4800d8051801c1d070380040e09030800d48007600c03403c81e060080c4400422400b10349a011a008030489005450641c2c429800d0b8141140a40c4192180200010074003c2e40903024415a00c050040400400010711041d10340d507441747c00c5509814203102a0010394040042c4402440900314043c01400c2040c51450f000e5081a03401d00030000ca0100380e5651008140700d0302d001070660740500103c0204000c01d0a10b0f0402d01ea41c0d54a643c0e040300c200440f00000700302c951040c05402c600c5441203006506250950301041060070105200d660907101c01c0c030000030180000c001c142054811520b0751640c0d80e07045407543c500c010700c044022080c841036002c01c00c0346903484550032115031382c90880002c07028400f2240c0907480c405c561201e68419900b104084481000e9840326820304821100c0b00004090038503000c00340c80017120040e1181101c5065000810704420601c0c2e48408030300240c584041c00010326200302d0b00b10740100d080c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 61322332 1250 61321082 61321087
    0xb070605090622080a090b030c19030c0e09040f02042301061718010603171c060305060103240603030e090a0623010302040807060503060a140303030c07110409030203 73
    0x1104042400b4480c0c2019000842c4038201c00714020040114000e64002042c00b0000510704040038403a01180000e40482132403156207040007800c0c110503400130b14280b690903441d4428500c80134041e2240c00d441003282e465110801a00e00100300300000001d0003a50b80c91011150074005a8481c0b06100b0719669080c0141d00b80d10703500c9140c0d221200140c00090910401707549024503110761185a40d403060a00080b201e082442d40d90719805861584d200810400342100b540501c80c0c500e8000c3c0036910401030301e040388050045440c8040d12281c2c8809070080e0000401480420fa858044c1140c4800c8403401201d00340402620314206c501b550b00640019030040c20b010745900e00001c030b80340c01082c90308041c0011414007d91540c8003c5843e01d589401e002015600110b03406038054400822071a016601d5081d51460040e0443e0310407034515110b031035075101c041480d444020900c85002c0b405002541940c0d075003440c4001030390100a0a40e0141010304544046646a0003080c603024400c0d4050354 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 61323582 1250 61322332 61322341
    0x50105011209030c0c12230303061c0b1810060f0605030603030f03010902030618070e010305090c0405010b03010906080304320d030c060c02010e280b0a050103020312071e06060b070605 81
    0xd504540000087c20242d202c510810060200109880c1c00040c2216540020500c40c80500714500004500a25503140d20082107078691420002103407000d451802d965102410b02c00f8042128000e000f090f15145e095041071000f98454005140d0010000c2c01b240d24107011865040180c0c0c2090344100000c40c2c00004102103810301e4801140e16900c016400300c520b08040c00090a0503038072441c05810569105c00103100104104002050340c0c5000d4001c10155844008003c3e259009001380c120082c202800021855000000c072000c543c40c2070707070200100c1131403d10035204c00c07a80440044c150483c1d00039041e465030348510051900f0f109480d006044641d507d0040d00f131300e402d040b00a096925101700e0749642d03100420b01603002629a101e803802c4041c2c2c0b07604543c124242110151070030303e41404000050300703903034803190689008034100c41001d030b100358424105100d01240244201e603018681d4140c6c546401d0141102d512401c00414290380395400c1903c0d94010351801c0d181e01e0313215000d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 61324832 1250 61323582 61323593
    0x20405030a0c0501020c1017040c050607030e090f0c0703120f0609020319020405240721080610120504030c06020c031201170606091806150310050105011209030c0c12 73
    0x8441e580401e840c0c1c4114509441d1025080c200d0362203e40100341c0c0342e10b00149c1000f00c0c00d0500005401c1c0245865200d00980c1001000c2c070b94600007050280d9465004035241040c0c00040d58810818036940e2032a01183d940c00311540c0c0b84000c0702450b45038941c1d2403161b03440024095040542200200142c0300e01e082005610620380d030070f14440600e4810041800301e5240e030490b0040c5008585441c40c505140030709201101e21070750b072001c2c2c810750383c5800704e100d40c0c05a070343c0580c035564040c5e0340c6094a44491007001075049004198102254491131010401501030700020343c4079009080031317003a00400d40ca900059070f01490680100c2e801c0003401032030846008110a0140a104505403020308501c8142581c4d4000507103000c1c8603020060000d83c2c0403001d090400c8101c9004000d442a60a100c0040c204480e0071300c541502c00c0c0150490854070398190310800d81219030580d2a64401c04250032030000a140303143c800c2d02000700b000305100c0441d041e8174141004084444d9004400c4407641001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 61326082 1250 61324832 61324843
    0x70e0403020c04050919020d020d11012606120f0601030b012603040b03130c060201020315040507020a1104060905011404150605180f10080402010e030c090a0f020405030a0c050102 79
    0x1010300c01d030b01d4001800071741d00000540c042081c0200060408420742e9000040041c140804020b6205a80030040c0b01041701c5404015822a001e80b0381407150240f2440b002000c80642c155500c0d00804000000c0e50f030300c0c11414500e04a20a44180e841c0110314061050401030241c106544584140004004111250fa41c681c6466801c51651030b1480e0f503550700c1d903103a02c0b60303100381d22002c1c03804008945001e80480541507580d9000e0b40280c4296561803005e4081d40040700d041003402148203103a034040c01d0500900b0311403001e0f94050291003200b5654110b00d15030244210350096a103082c0070a480945100c3c03103019020f40c0848001646034042007105840c0300b01c4011480d40100e080400c240d0350803106460308440c13a5001c0050440e00e1202081c0703000f1962000c903074402c9101e5181c43c0c025400000e03c17400741d8000e0340d0306901d140140381403642d030f08484110b031900f0048003000100119a254414030124041c800701514141c1d07642c00082c41c01551940070307200d0b002c42c60420021503804024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 61327332 1250 61326082 61326103
    0x1203030c020d1103120606190305010315050c0901030507021c08040c081216020103110a050304060501080304050a06110c0409050706021006050d02010c0213020a0309051e0a020d030e03070e040302 86
    0x2089900c42e42e03182c0f0b40d43d8803401201066003101e903038a40413603520356603002a40c064241c5039203840c440104100000b005000d080c8401d5a01039580c500c0c005040175280a80d0f07104001013003c05107000c440d48011070060800a04030400c501403442145881c0b10401425440032140d550f420030a0700305400c0200210720303140d01c06001c56111440e00d0318082c801c1020f4621038002c4101800e031414040c001a806818001e04a5854000002c3c103041135540150195018500440c0c0c204000d80c0c0320f42d03400c0d9591049008460340480080300800005101d258600c00b0303480c03144140c488000301705021030709541e0900300803035280d00041c1061060b554104441210900c0307404e024000c2518100100e4140741ca036902c06410842480000300c195225100303e03200d0403171540700840d592203040d07500400800d114602101d45004a14244982c03641c0d03c100403062002080282400c03031116420801400f01e207070004c4040c440c3c0e911081225035024811080240958400d00d403c07403a041c640241045401074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 61328582 1250 61327332 61327337
    0x30206041707171507090f030804080c0a061209030c050d020d1206060813050a0b10150e090a02131518061106010905070302161a010f0b0706050a02041203030c020d 72
    0x70840001154005625034450005082600160719516411201b070042a00054035141000000100700b201d010000c0003191504001c3d58448a00c0700d0070800c1e5a0010710078000048d5115901251900761540480c02c2d180c800d08003204100400d558a604181c1403d0340d00000d604004003020583d0380142c803011003c01c5034403041000030300f403044c042c0c420040580280300312099200e9203c2081020882c24400720380100042c001454080320a0310054a030b400f07035008140c21124075032001c030b004000c4220040c0c0c00510740c224a42d15882c0e10402501b1011001c02c0038401540b0004002206d0070180a81450070f550303a0312980c1030000c203c50880196071041c4200412007880c20810600460114199081c001c0082035a40f501074013140030f40940e004a07201c041010070203804200541000d072900c10740c0c08103244081d03a40c9030560352500c60584228040c0c05420000000003a589902075940480100c000600b041d8440021f1f0b580316007580e07021401701c0d680e031007080c2081c0d030100000d84285e001072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 61329832 1250 61328582 61328609
    0xc050109050c0120100207030c060504110f03010207081206030304050d0c050910030218190612020907080907060509031c1809020301060c060207050705030307050304060f050a0504060503070306030206041707 91
    0x240c0913240d41d1020003019400a51340480c88508262080381240b0b080c0d60071450920a5007000d08107151380540d141c0304d85224000e0b08511150504040c02602c0b01c4581100c512070070111038025003944500300400c280d46c03502040101082a03034030f142c080760a581c0980000f081c2c0303504007004e000784100050407030100d02941140820059960f610190300c2c8254110040c4031644802e0407842e600d04140d020340005038104440420303000e04400c4581e0342075000700d64050150701c5a1b003080e00c0c900c1d820b0b01c2c1a0420307004a4410311019025a0042c1403018002e02111610003211900001524000b4070900c005105015000f0400d10307401b1100d030103031600312411403a55150103400390582c0c03240c00c4018040c90300410020140a01408401e00500004c0e003900c8d5100018903050341c9962060050b400030409031401e00f21010301c140c2c2035070510340701a21824981400c140302030701c490708010724840805488180100058880328003600c002d00400d034040c0d484a40b48045281400b26903000201e40d811003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 61330938 1106 61329832 61329887
    0x17030a06060309082704020c100b040608060c2206030b040e1b120c06181c03021f020c01090503210f011a0d0516030605090f01150c050109050c01 64
    0x240c270b001c200400082003048102c542501070351041d64460400100134a619000030000705a29501c0742c00403070009004002c1c481402d40102001a49074510100380e414140900c804482d10f981c00791042002d02c00610544110400215101c0d0b04161484441d5050510109401103805031546aa41540e4424417641340e1212030351074040e03500000c549884010344100510025403660182100340d901e40040c0d10341008105010314156400c1000e100c148000b40b05020710355100d980503603106c48d0740d04254005604211240302c4050786907000c2010001c03c020542d0f05580c0400403410f5000c24200c1c1010081c0207030303c94920824688814400400d54a000301c03004410140d80611205440344140a4540381c161925030f9440407080061080c409205503900c0c22104919198121b003005450301800e44000c54815210340d00000f012034a1568440100818040305a100142c01e086 = true := by decide +kernel

theorem cover : BRFrame.Cov 61151082 61330938 := by
  have h0 := BRFrame.cov_init 61151082
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61151082 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 61151082 ≤ n) (h2 : n < 61330938) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
