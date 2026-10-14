-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:57:55.509322+00:00
-- url     : https://prove2.me/submissions/16ccc349-9db6-4b01-977d-28683126a12f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 186870503 ≤ n < 187050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 186871753 1250 186870503 186870521
    0x206030a1107050102040e04060501060c0c0314030909010f1a0a0203030c0901093c050603010b09061201030b0403090b1206040903021c0503090d08010302011409011412070816020709 80
    0xc66000c102c20000900248000d10052184e10381e545030074a01810400c08030750059101c0401d20440d1001100000c00703c020040599a02500d020740840410030aa880d500410984c00c0e00061224008035100d0340c1010800c0484903030b0014000c3e402c90742d07a0748004a00815450b40c0c050781c13052021451103070805015000c165018504440110303500c00c8a14083c5400640303c1801c25046030403078900c01c5904e450390032040340c1c41c0d0554910900c1c4c60702013401c521051080311594000401c0d00f900664a181c01c40e1442d042502c41d645076940c4a05220080000540307084000c140c0e02880090320340b50070410340321120785100044d039490b40c0b04000d01000e0404040114118094852582c00250b103140200800c5812031340c80303d8503440c14200513843d00102c84942c13801e00002000400041c0c1c3c1c0a0000c08a03283c0d0b803100ca5480740c02840040e0b0303034500c000780f00328035407030010030503040d15a28000c410f0b208012507602c0d00481d88039914540882d020a00c010760058000030018402190f654012406d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 186873003 1250 186871753 186871781
    0xb10050a0804021c150b06041809110a1508060f1c05070801110705010605040515060f0412290c0307050c070e090f1605180a0216030f02190206030a 65
    0x4110040300500b039007004a804116403468007400f42880d545e00034490040780703000660b03101d440e0078200000308001403124074104500f00c0e15100c2c00c41c1041440c001ea180460300180c07c0180300358503079082045415295042c807002480c6d0303400042c11881c0045000e9200f98018150200311b940d0021142d03685041460107030f031540301d0b041c1e0020704060240700e400c503c0702090031015255000d5190a509590707a5138410317442203007488107003d460700c0440f00134540c4240803214035946808844400c196405250b000c0082d4101314800342c0e080c407010a1454844040c3c50f0030745045000549694180c0200c241e550031038001c814000584040c0c0520014034403104030104a410443c0d0320b070b04c051748000003244c1c0c5060603004500f01c0c48250404011241c0d5003c0c2a0b0311401d101070511000c42c4003409100400d80741070071424082039082c10140d04a800141c10012840c462050030306002d0983ca0401c030a4100500c42c0881e21b000e422106181d0b0900c4560003045a86544c0301e8001c0080600b07001484002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 186874253 1250 186873003 186873019
    0xe0703111308011b0503040506070309031404060f03050f09070302120f06090a050106061103090103020d06210c060504051305090c030d09030c0b0a050702150d1e0b10050a080402 78
    0x500c032054110607100a1110100100e0742c50400d101d00030401c0c4004143c6820b0103c00d1040c400014804290154004610300c0c0020301c1843d1400d00312070111210131200c061a00020300406c2e40e07a0721000404066401c1c1e02c0920035031721101018151648110355400181d00440d500744018a4003c040d40700c00c1c46a002120391007141d030404a0304004058030340d610140c0c4044080410001d003801000b0040400307080510000480702c54041c0c4912400c103000341050340c0001c2c1c03c3e0f901c42c1181c0c00f48010746800072010340c0e40c5401000d99806031110090603290000c00c401c0c0000e0142c41001210252031000d0a248051a01c3d41d180301c0c060074000c0c1c000b5800e401944403865168808110410008215540302c6a249185007400310075004a5003103000b0300c6c0010400306001079004021202101d03030641300c1c01440240c20750050018002c0c8440070401e681041d1000042884a80c0660b2074503140070701c10801c01e8201010011030000c054070140120340180f110010303060188180310b0f405800034007101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 186875503 1250 186874253 186874267
    0xf0210090807060206042001020d080702010603080a08250c060203090a05060717070e0109050907120c03140903121303030e0307061b0905010909020a020708010e07030b0a060e070311 80
    0x1500705150383e001240140e000e001000140200b2a20340309000907403040e0344070084078480000f51075851060002c828480c1e10408103890b42c0c03007544104000c681225209445403030300d0f040180901825500002206503948109220005e13282d4282e1214219898401405003642d075000003940000b0090b030858081c52404002042013840f200f40b0803015070785c40002750300322608080704984001d45038004215824a000e9030590b00000030105070351089890229550b49c40303000719281d0740d185280c0d0885600b05440a0700d115010303007004d00941210302211040e95110300c0c000e544c0b80120302d00b64880c20400c40206510f1850031304018886402840c005c00ca4901a003405403840c0e200d45001c40c0e00641e10307030721544c0740500c1003003140d1110300b54900118103e00e0310000800c0d0445600400d100310394001100e2140da4000c100050080c00b20364020720141030041407954440d80b00b880281c5184245000180d444a890b00c188801d440c445c602e02e00c440d40b1100004c078020820907600e0a00301004100403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 186876753 1250 186875503 186875519
    0x309030d03020702010809060c0a050c030c070b04061d030a0305091314040b090d080f060f031f0b030d0f051804090f0201030c031404020904020d0c080304080c0109030f021009 77
    0x1452051215100560345005504c001061b010009042c078030380d600184240f21115499504503a40746482e807030b2103034403100324030340142c00c41c8600f10481c1814483e0110020700c241c040b201a0045503005d0301c034980c04040c0b60200740101180300d4456585900300f441030000290080c0c001c0c3c412003074080c050500800c840d551010403910b401031102816035001c01000104150910115480f05c089000303000d1401d4580009015030360003900d130600b1101c2d8000000c015450f0549004000e0a00070121050800e025800010550280355542d900074100103000d0964140018041c105010230f60318405144401507081b51190403004009002c600300c0c00e10140c003030380c8502a510341e45000d08071040500c40184005400c0f182c001d4050ba00b4142044040c1400300186210a43e019030140c03544030182e6100d00c0000c1843c1081d4200038450903240802141424000001d4000d6640e0041220840444400107454584d01407000400c0e10807000707030f124014142628080326400b0542030801c01103840e0044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 186878003 1250 186876753 186876763
    0x6010e0703020c0d0504030c060c02300a0807022e0f0909111305030c0d1b03061b02060c0403080318010f02182106071b020910030b16020309040e030903 67
    0x1403c0003e07102140030f1040c0050741072346000814940c204504040e02c1680800c2c25500c407600c041da154040040030036600320b2982d400c0c40410042500340c175451165441c0ca90034a03082541c0070307401400c409981601d0880c2411740d00c007000b41c01601148078150320040486002004804040420001200010340318009000302008240c10500c00d40e00d80d00e544542003d64181076000c14030a502c0b1498440054566490400d18141c220903010a02d516040505c5812070803230f480242035a140c1021003900c0500e00d0f981d005190016420303109251140300d040d014902480c080a891850100041002c41d2850b0f00c200d5082003109c0000324503180c01d1240710301203810042d00b2240d041d8004010740d0b07040c0f0380580301d6040824002030403e503014490030b0030380e6144070040810f0113010b0754400481000d44064902c0c101c1c40d50003032410140740307002c0381001d8500055200803652107221b027010800749544103010703003600d130510740c000c41c00c00b40c1003020040a84a4100084030361300081007081095102849 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 186879253 1250 186878003 186878023
    0x6111216061b09080615010503060415080d05070b16050f0c01230a060e04050a03050313060f0b0103110702010f08060a050607051e030f04050d030509120f0c0102010b0306010e0703020c 81
    0x1240c1c81e5141c604401303c3e05103200101003064101402c81417118aa0700402135942101081d640042e0500c0c01445050905040c0c3e005942c961207080c0e4840e00055110b0010b000c1e107823040820116a45810252052a0028a1511010840c28481306c10000c90440c00b030120541048004104480034002010307520010303107a411603c1c45001c0030044508400d0045030010640781400401d245002d4450300c1d2601e180c84002000c204001012940040365220b140f0907080d00820200f00303000422800070000d10101c0700550120342416480c0c440001114140c544458040e152040121004401202c80d00300041016600c01e1b1f45103030200b4a0746440700a402e12512680c01440c41c410214070348421110008802000b50b4000c102b5202000114000d440071288103030781c801310600003032405481c3e90080c0805250480340b2204131080004c000602032001c0641031003624400c0c100c03500120b080c0c8400807101e0750181d001c800100101c850301030440313034001c94902c1c005081c00f017002102428441d00003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 186880503 1250 186879253 186879257
    0x3030e041b0e090601230d0b06130810020304030e090601110d0e0306060a03051c030f020c1506041104060c050a08220803030708060607030e030708010606111216061b 73
    0x30b01c1d42605181c118990010800d0030701d4504504046148003003001300880f01400300b04007250a4006e0791554020080e4180e00070a050b45550354021030751001c2c803007440303010494451200b4032002504a4406c490040e41c055803015130208040d0f05116076820007821300d9041003040034000d40d141006020ba1540ca484555603000d440100c28105071030041d010700800d10030b502291040001420006112003041103614800c0000c190400c0158020405e955118203040d0000909500404000c0350840748000310b10350882007600c80030144804c6401c104e5401c0d070710700401c110600030240504950208944100c0c02c03900000c00c07a81d40c0c45219000000306449038a24515031a116508a564000182c0643c0b4002c50561400103801401c071359010f04824080c00c80041c0c002d06043c4070b030003000d40e0104040e049070005c40d80e030301505000303203003910500c00058524002c000d0020703000b2031390039005160359010724141600f8035841d1140718402907040300d8096540c8111a0034002400c0440c0d281440381d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 186881753 1250 186880503 186880517
    0xf130c05061b0c040c210e06460b13090b1014090a09110306101401050405060301030201080601050705010504030206011706040f140a0c080d0314090703030e041b 71
    0x840b0b1024a041020074000b8851801c2c0142165200d50000c0b002400c500d001c000417070214051140c3d000100010001c4d05080e014400800080c0021a0361117003540a40425a00400100c1d00010602325004100940c00544032220b0044041311074001442040d8020998031040101a1049089a0f00e045003140d002004004000301d020498001ea0000c00c04541040d45045041f400a02c907000c0041140c02c0551307032480000184280c0c0d010407202c0813070207011903400303040040610007001a82e2144c0c04411101845030021544a075064070210780010740202d0550b400c0d50300546044600524650401c0010310507040811000d0007514040ea02035005007605504111616942480300c2d5000121a44000309010028101000d00490540c106140130300c80762000e00f00703600f0040b10190240a580200b0404219504003140c1e0042e84242c40c0c0701007103051620421010068000c980f01c0206401030724080020900411881c0b03004a4000c0000a10710f0240d814007102403450010040042c2c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 186883003 1250 186881753 186881797
    0x1107090510083d0222080105060111071a0705070b040312080f04060e03090604060305010e181e070b0409050a060801020309030414040603050a1401050109050f130c0506 74
    0x50000140010042c040c0700e2071803c45410030554072a84200703002004400354510304140750150705480c850b924500b007284410400780c04030246007060b0f00600c0030a521b041c02080566008000104d0b000005201411085244c00c0318200c883d5042000b03084148002c1042000207202441140054021750a14903111402d600301400c3c04140e0005d89010703c4000010b2140d813860f4804000d0340154005c0022a146881034625406d50042440c0386401a40215003c5891600f5401c0305050300c180408888503943d0311950042c2c030ba01413940000c0240c1100c240038824aa0000343c0c0c5004d4034034181160951543d84030810240c0c0d205500c01c0203203d55032809d1103d50046030107040001c10300d1000035415824402d100d562280300724800c040381d4420784114500c1c0f9440e20703081380b8011900a815181000040e04101d0552842140c6141c5194688000131540e4076440c4601030040241d108120450b81d0b44603415200e1001c0c0c408203480c81403600d500002d1720f964071801080d41c0d1050202001030000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 186884253 1250 186883003 186883019
    0xf0204141017070b27130f050a0507090501080c040312030c08090106080d03090303140103030203031602030304110d0201050c121b0106050d060b120a0602030601080f161107090510 79
    0x254040c05004030f4004400030454039200000381c950343d803050040a9140c0959a04134600350010030011a041a0b1a448458200070158840c5c0700e0141c0c850000e1155940b584590804c80e00101c6072880843c0fa0304e0403d0003d0f51144954580c4200b805520354985602c81e01d4017171801c0e540c0400000001c1d101c494000d91541d2151400780c11041b55802886058108a880e80c0c49540e0450254201070f0f603940305006140c400d170400303401c5401300f18040e80c81d0358483c18003e4a03a80704403400d89060b0fa1a448030003000d80f000046a01c15900b003096590090414001c100c003645e94800142c3c1044028080c4c2d101410040c000d03a004080000d004555650700000e80202402aa90005c00185d00d04007040240c0d880368000c0a054a520681c009040092480024001c40440c038001d0301d1031090300220020080298029801103200b6224604696940b0440e6008031170116400302141503114048200c41c1d00446446030811542410744440d203807603404410403500210b071040c00d20079001c1000c03c1801c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 186885503 1250 186884253 186884279
    0x150c14030a0f0e0109230406080c0117010b0904020315041a0909010204291303060c081321051b03040312021612080d0f0f06050306130f02041410 64
    0x3542c1410315034142c06020f000a440d07071600d403148031540c01c0e03801c5a142c450256aa18494001c00041c0100440d5888480ca1942c035211440114085144a2284a03c021500c0b14490484440c00c80207894201c0310418030002e500080c1c400300c1c00c264114146811030741c55000706182108540400300c001c001071020810b080101230600e14032b03a407040100b401207140c410440c11810101618000041c40740c540400968403902c020340c2d0102c2c14400000c010000c0d160006aa4230b00c00765198a819180c0061480041c4007844009011829609501124504030324450720300040c607040483c180701c0540329042514201e00d64118190704009000e0003000740f6007c1100c25036880d440201064001e04044c01300c444802d00a140070100800d101408122207042103030300d181e040c84c60901030014590f0044c80903003088401c0c00556400d04c900815a4280003410511844100d4641901c02e03a00d525061402c18007580181d13006030b2181c9a001d03e100000054501500c040104d400d00c05103040d41c80c00f654 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 186886753 1250 186885503 186885527
    0x201050c160f02060c070303080106020c0102011401090915020a0309031416081c0609060303020f06070504090b0d02060301030302150109110d0c03020903060c0901020712020a150c14030a 82
    0x5000c0074468800348111081505640c59402001810154080d000040a5000e504001d00d001d1060440210415501501d03150417034199400322001c20075820016070030386858942c00d120b040340f224010803400140c2e422101c01607000708000d5420908010305001647d105074001c40c0403030b80780d071041000c05900203004c0c545442c58150f11414500c54540a80325130205d00005455014045205501d00406481070816071442880403c40d29940701852009000c040c8001e401600400010b0f900982022070a244242c0d040e80d505c0341313030508020007140200079543c015604500c00c3c210b00001a2074503c000c1d03003c1d6010b070300204075200480c00c80410a490503003004100c0c601301001d1f2000c481125080e14a80d25041d000840e400c550140120000e00981084581c1441448280003803140708100800643c1e02c20389c207444042d41c0301c42078600802034a600094000b226000700704600742000d52000b441007150300d002c4c050a84181c958206181c940551110305401c0086c9076006540c002c0c2d000039032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 186888003 1250 186886753 186886771
    0x1f09020d240e0c040e030c0a0309180e0709021803060906151e0609010c020d0309051e1c140a03080a0b010c030f270602030414041119020a02040204080d020105 70
    0x340300011030b911900c40c000b03900c000b40074a4581c03c400c02203500070f00a5540c0c03c0045411a0104101410001c0ca02c0105102c1c842c010710713410340742d880a1030b0940a00f0300404030440042040d98585030f01103000b540884014002c01c0f5a29154000c25a0203000040c090001c0f14010072a40c24117203250500d04100b44403041c0b142c24100b07036400104030a0b8843c007008603000c407952a1074480307a20058880c01c0304103c00943c0400b4007443c800425403c01ca0450588074140c98011120a08240031528402900316407a80500b0345c0f01c0d400d80060144490001982c814041500000e00c0300382c0c490700d00203078840e0440205060304104070403c155403040c070504580901e4524840041a180500039030000d072044000c006000454504c022456011010040c0c40340c0c0245009a948001c025101d820600604200002049060f901440e050180d0a241c2a490344041e28186180200c15104045100c004007540505100c3d06c015907140e102900052070f03114050300110603505002402c4070320003002d80207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 186889253 1250 186888003 186888011
    0x140f1006090605030a0b09010305010c03450813090f0506060a05030406060305030301180b0306011508041103011109011106070e04090201090510030e120c1f09020d24 73
    0xc031859102805104403465814072550ba0b4a56007500805080007200c1d103500151060000420024154041f40d400c0d00d40342d50402030041c480f4020f29040f40003e015003003102c100040a07981c03102d000d10b8840d05031214001e0702c0e22005030b81d03114142c0b5084542d01003c2c041840200f0404d00c40b00340143c200c0c10b9034030340f0204500c1c94207400062407801620311030002c01030040700180c03c00045503c480c0255800108403a12580c1d9035002004240035a038091140794207182ca04d071464200051568182d5001e0224015460780b150011141140020026941c144a00780304160b141c40a100d0b1149080c05140b01994400101001402c860080b500050807944a2010070240c82d600c10240581311100b00c03030100d00130380d1030b000403160001940c0260340e021b54041c0001820301c3d019032201c00c40d03010344420f481010011140c001c603940503900400b8807581100306010760704041c59000218140480100082c0c100041d0080b07410410580400c03146009400040c802060620100f510300c0340290340140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 186890503 1250 186889253 186889259
    0x40201170f010b090102030d0603060501050a050301020304080a03022a0c100e0a050402090607060203150a080703050a0312060b0d0c08060d03090e0c072004060b03040b0402090603070801140f10 85
    0x150007040500c43d191442c80b003c602150396030300c24400c460101045a00a1007c20303101e0400100800d03080c8100d92189054240004d41c0d0304060017542e01c541d0704118824203098000310240c0195000741c58040c00000c061801004144013100c103048803a09e030740000d04210710388109020000c43c2d551004000e02003aa11707841e113030703686a200400c15120203440140e252120b80c0e0208945001e0508014503035400481080048094529020303087c00049603019180c40d620344520303444451500020f00540c0203800d01401090149004074003280405e00000380951f50fa27200009160000f07021088201d44078a503024166500024003030f0031100c100c852040c110b856175005004424280305240300f400050000502c000210010f8a2400740c001418010750070480240d001d681c41c80610781840b1324502400402c0304040c0205492059a00c84032f520902d4a803a002c01845e100b005001030303414441d40001040b172030004c0c0110012075243d20060181814118444600250300920310032024918006c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 186891753 1250 186890503 186890521
    0x1090e07140c0d03020c0c01050c07120503040f060201091b061710080a03111c090b070609081305040e0a08070803090120030105011818020f0903070e04020117 70
    0x1a0084203906002120701c103401202185070254002d601401d0082c411110b44441e0160020101104520f096902c0071001074019100350140d00c0d810340d402d0788000c805210710800407410f480294001d50460342416550318039081c8080168015600607512200301100300000c9515181c00c0e40082001c07541284d00380107000301040e54409049010244000205000c4c01c204503901c405006c1240030340311012130b00c3c100500744046800f100d0b0350602c0b4165150f90703a22040d80c98040c0800c10b581d01c03400958648403001c68150003022090302c0560b5a0020800002d41c900c004000b0b0b102c040c3c040d481c08510b05001c2100f1a0a8045881c03002d801c01700d0064000b0310f1130011900e01940c8031041c0358030b07900c995800c0c50040c14007250080c92600510840380c001620000558120751003643e6040d40c6241c40d841055481c1030620480e00c10304807100d031810200780a90050114074440349095070800c01d0240c00070717262000c01d0b401145000c003e03106110135941e001e044035400c1a2441c07060000c41c1040c17215 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 186893003 1250 186891753 186891779
    0x180504030807030c030b04060b030118060b0403080a0315140a05040605030c040222060518030a02150c0120030103060506060c0c010c0f021914100c060f021306020f0c0109 75
    0x40810144d940351400708042c0203505c01c8880000240c01049001d4490201c5c5ca4a0b0b4001e026111455072503402040e85a081c6010f2131b000d035030742c03040d425003070a02d1503603050459040f403c402c10905460704409650004030031480c0700145403894416405c403c0c13070001d011001000780c11840c0107605001003440b0740e07140000c01044000095500503561003540082050304001000c06c5100d03c40c014000094155000028210520402100d02c0c1c00c02c000e0400c05568003d8010001e402c4501001f0f2154099184406400b03090090400400c6144a8094103c090344850030380b0942c6c010040010300502c241841160352250058400703c0c070f00701101e02a42d5032944c0180c11107041003109400d481c00c1044014004189590160480b80380f0810007080381503070310340c0e800b4002c2900d5401030324075464503194015100520007038880d5490403000b03446107000f4100f00014407072003030303002c211301c0a0b07088000006900078416a0b010705200704500c01851b041141c40c0d4072880c10419181c00921500c0401c3c2c3c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 186894253 1250 186893003 186893011
    0xf0a031e0207050f0609090f040b0a05040308040f030e030106120506010603060b030406020a091d072d110102160b0a050c12060103020a21090b06030a0b061e0303131805040308 77
    0x3131382100d110008070029202e0302c03880441e41d421035041801c0c0151540c440b542c040c010340c826449040141d54414001e02291030032100500020402070104011400c040c204045850292a04243d40740340f039008642502c42a601012851038003040a00a0047c01c1c00441c0c0500414503003403080c1c07841d00840c03450500002d040641a6a030010300d401419000380d001400400080568160b240790a902c0540c0700700341203400070007003000c1c0000a0308003030351110342c1389086d48a0b40503510118038510086880074500c4083c40303110340d820001d0701810300d48140610340e000c1c802d485030002c5240c800d140a0035500050482900b40f001070201c40740200780a82c181d6030098080c0303801a201c40001100b00daa490321940d45060b071a4080b41d0400300c61100360070400005009240d00d0391a5160202450b686500c40c0c4d101031b0406281c0b9022408500c0c004030040e1580e010741542e011801d10711000242164401e964504207a0703400303036003003000b2004c3d02c1800c50070104184c8100b00a2400d51406810010010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 186895503 1250 186894253 186894259
    0x1103030f01150c0b10150e01050a030f090803090703151505060702061b1e060618040311031c0c0e010f032301030804051906020d08180f0a031e020705 66
    0x80322810b20701d44070750050850309800080850040c1055018007801c00300700d00441482481c542a131003000342c090241344668170010b80d00c2c0351a100150030120700812120740117008054a448142000c85d4090000d0340c0540c00700d030050b0111514602e0800310354403408140c0082d1508006231001c9481d2440d60010441e4000d540459680d5113030b20024030741d4402e503101c403810003072540c002c49190300740040d89110010f5410904070a9a0300e14440f55a9000215000e42d8007001c10655040011602e8038210b40092103418070b64a003201a9a4031f41c1944c1145250035800c4070310703084800310380da214051075190707010034103040082002882c0000d00401c01024004207143e20354090300000c490180b0030320400d04c25003140c020196113900d001c49803540b2900c544c1e44901d603d05035010511900c06084001c5440c160000c1c0641b40ca4040c080e108250028241f4040e044203004e880c01001040c0600241c1124541c0600f49441051502602c2c20300e0340c000800c940a071008102c48401d0300012a542910411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 186896753 1250 186895503 186895529
    0x6021305150d2a0e040515150a0306170313060e06070b091c030504050709020f03040f08070b09060405160f05090a0e0d231603030203060a05150a1103030f01 69
    0x21042c00c03220f120409990411503003035450030a41992100c00d840002d001114240303c241c94801b041030980c070703034070041c564810078000701c2101580032000100075080c5941404154242c0c1c1b4500309800c2c030440c00140300e0341e400001c2c0898050800040c07401c0030b4212410700800d100600ca000c42d41d6802140c800600002180000c582d4103c3c0130401d5140c3c540c001c407120002c00041480040c007a00d416a401c8030325110709000030407c000316001f074030302124500c0151800c0d51341d40e0321030380d172041c0b040802501c2515041000b0408500100102c81c440c0549100801090825141c11482c1865072510506121551041403044d9104c8e201c14000b100c1c0200c030802e285481c0c2094600041511400d42012407040a01804445400034044800c050800701c411403101c1c20b500d0307008694407911286400c880007032108100001d010394080c640020002d041e2910302d68443c1c001c184445903001c10140b401001007500c41c54254420000f94441040c007000d1400d504040c2c04500411906003e00a008203030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 186898003 1250 186896753 186896771
    0x6010c031b11030708010903030515010c02060a05160804060809011e0c0e031c021c0e040c11010e07051201020c0604031b08191101090308010e0a02120406021305150d 73
    0x140d00c802c2c0800c0740c0c004003952000e55540721141c0c000e01c008142200401c3c1000001003154074504040100c4e00d1040c0c69007030164040e41c0c00c111682d80303c000c903942230ac5400e100e882c0020158034045200b040c4243d0903103036038078102600940411402080034800c5c0e810b0081c03a9060140101040c0480113080c0b6010441c002c81007001d40c2c2c86032440c3c0d52250540325484021f6140d5032180341d4032145800075001d440141143d10300c5007000b100801003003800304804421261039403e15912940c0300440501e0081d144030303045c3c4002801d640107907980190a134062201031000385000d1801d00c8001910b60021407410100341e081c41e440e4075000308043e062103020500c14000c040c940c450300300800d6110050a5882e55032030382850743c0300c4060110000051604040440d0110148545071801c2c0c1c01d0f480d0300702a6842d2066008800710000c0883e000782d0b03000d116103081150980a211b010398414440562940c56031000444a06400e0b84218032511003191030f811950701e40c2045580c6003400344404284220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 186899253 1250 186898003 186898013
    0xe040b01090306050f04020114040b03070f111507140403050714011103070b0f100e06150c1204030212120f03090a0f05063918150403050606010c031b 66
    0x807036072001c0e00581c2084200102c0001141100f03100740c0c400d80314100c0c1403040100200144c0210b0180200a079401c20211b1056405001d25004084491400c06021a02d0305201400e040c48040d502c18924000001d004606130044c682144544061306403d0829256803601580e42d143c03407050035244080c0d0f400b04001c99118404201441e460304080b20754030304481c41c0c9140000e90031104001c20094100125040c01c0c642820f803411501441c00020803902c4100800620401034180b112000204008000440f0000d2103000d0141d5056250207440ba0710718010301240d4110001c0c035001c1030304a03000c00c00744440034605540740400080030440e1681d8421003460b00e4092000000f03070943c2d407070708000800c000c00061070700c0c860070b401c0c031032001c09032003515414130000016503030382c040600050708034800a603403040903240c6a020400c1a50001c03180d4004074051510121241111100006050040c000200002c0350845820310b00784800150a4074028803102889a001e01703014441384171340d82400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 186900503 1250 186899253 186899267
    0xe12041503200a12021216020606010e0d021c02040c090e0a090c0b0304150908091c02010915090306050906041b03050307081605070e090705120c060c0304090203070f11030a0e040b01 80
    0x5000c0a0b01b189007030110901d06170202241030040180b040b5000544154030a0b044144802d80140130803003000903903800c2141e4290030810390f4844035a1110440d0260351240100c840c4a450703034469840700c80c2480410350300100d0042c1f81280035070418034081d0000b00300903007110441e07207a0b1014580f6522103142034600d85d4010880105603605098001d0180040500148000041202c2d41885810880d40381d10120015400c040c1c0807070303084141000344230440007407510004900d26041003035a441e0380d200011994190341c516080d070700c260100020400c0c03554601d0240601e01d14041c2d41c151566a40179564824001b00400c040004205052510840400089456031200641c1c421540b1010403001c20f100458104400b88191000011282003580d0900b1120411070b026084c206a00418084141c4c00381c984114944420840060103420b6840034502448191361034034824a4110740041c400703100240f140e80e40d5001000316000c0c40c0e4218000b80d0b492001503078003050021390140180d40030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 186901753 1250 186900503 186900517
    0x6020a0f030e03190b10060c05100b060c060103140d08150f0409050a122a0f02030c0a03080d06090509030318160b030414120d0e12041503200a1202 65
    0x11007074403240e0303104121850011500c540b503d0b003104886c0c0c07942c0d0070007100e41040c104405000340d003003080e0220304d0304900e8111022099024210038070b0800c614205500c3c00100340c0c002d481c4003d405040340e201c0c03082840612244503d900c5c10748042d0414589090b0400d009801e018801d041c46e000b40042d5442d81d81125161a4100d0240d42503e00103043c020644840070607007400080f4000744110540700500041d80114200040c5884990f8040c2d58020490100d5a4160381c90301c50401c50034402c1e515200001c0145124081d03103500c41400c5003052003500d4480d008190b444d4101350410a00b030000105a035480f101c0c1c800750002d0000c914119509003007800c541070710b108031200004100b14807103000440c0145e1041c4c009180c4038035840e10103611042c2c81191b80b035502d00e08120100d90f100315900602c142a0810b000e81e050001000f079141303a217038000d034032074811a80c450498507900351b0544900b01d4101d04c5046152440c10341c281c06022540306030340d032200503c4210060703407400c100740b076041d1015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 186903003 1250 186901753 186901783
    0x1205150c09010e010207140d02150712031503030c0201180f060f020c3304050d061406120c01050d0605040203010902120115120209040b131506020a0f030e03 69
    0x26061880c40400030350700c12240c450214958000000a5500c0083c0490440f5858446410300074504010801d40b0422904140da000380550b4110071401d903c6001085014400d10042d40d460180c1036020f81512882580c4112140c80c0d220200042a0842c0e800e0420540c2481c15803e10f020008910007c48030a8008800c5600c90704030209100760000c60108070800385408403030500c4440c0040201c6010107440c0c440018510800d0842a40036000420050f121104281414a0781715804554080780004080d2102500e039008038210100c660205a00200140c80810000c900c50f02e0541d40e405070030704420f0400c507002442102d15882d40e401000680b100900566503941d5464008001c3c1d00450b2407004603103410300c00000e401c0d04480c45c3c00528182625090080ca100d03403102c07002900002d40030350704291255200740003540c0302c0d04000074800c0e00304800a04442c181e046008000080d8022100350352003140040d02240000c15850821a0b0500c0c00c054006280c0d80400d0521050130300c2018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 186904253 1250 186903003 186903043
    0x60522030305060f0a15080601050c06070207050a090b180c07060501080f06070809060a090206071a0912070b0f040c05150c120f1804110705071401050309071205 71
    0x10805a041e0880b6004110444074080000c940d00100410342c0c4103031040c1e45006000003054600c1d00d0003601035030ba008070b050626a040c0314807404418140032044403003030b006070040001132025103400701040001d00700300542005030406000110314000c002841c4402c9040c8042d0000342130003086012200401d80c05841800399595a990300d87e522107001469000038040e400015840030b10400030180301304101c900900f881d0710380c1c1c0b8110000780100041640c000c0b40810805011446c510b11031072140306030381150300c400c1c54503d00c55070a1184100440044000811040c0c0114524080c1581c0091140c1140c1859840d20316100c01d00d1421588455002000c44003080488000140680342e10480e51040e20110080c500c0c032040d2901c180300c00200307002d81c20b02a140300d103031091803401c248180c003602c0040c1840c80340303d40c0980d6400000c0200c800d036012103824000711100f0810600078030f400b03081031b500303604027650815150300e814000e43c4440700b14500081c050113410001040c00b5668014000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 186905503 1250 186904253 186904321
    0x60e0105120c0412061b050310060f03060b0a0507020f010509060904050c09031903020d0215040b18011a0103060801060608130606150e0102011d0601090b03070302100e03160b070605 80
    0x201a003000341440e0420300c1d00300d41d138004840c040c004427403058403905103809011342040010307078011030f840d1200d40406555240114210920400405d07403103803a600c0d01516002c03070348108280000a6560301d8100a01402210010784a81060321410041140e000c600c65a0341c8450150a0188421140d81880381840c013411a00600303041031140ca02a80c2030351304400c81c0303410a0340d80341c00418028004d50b608174001000710741e83c2c100f00394005030418120300c208083d2040d010709448035014550b2940380741100050003076030540314000c001d100034802800140e103000c078090b00302c0d03c0042240768214039074414001046550360040b0003400b51142986031281220070300920b5410701e0f01d00d288c00f540c606008600b41941d20b528a6407200340c03910081c082682850089406807001e03003074803034141c441c02c08007100503601c003082030601080701e40c2d8a0914410301400c141c0b03810004000b6807000e06894200b4402d901003079049880403a0848408292522207607041c03107540c00102503010b0041007560461b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 186906753 1250 186905503 186905513
    0xf060102010c05031b09130c11010207151a190602100b031e0a05010203010f030b0906190b03011d0a0302120c0a0210090e0f0118020f04090b01171906060e0105120c0412 74
    0x368070361000349c0d584d641803400422256080348202d02c00a00809880741c840c410350b20803038102d250400c1c81c20207440110004480880e06d1007a0540322081c460285041c14044554100030707000c0024031140d010f10a210a182c0420340342c3c02d802c04c554410000000d660050500104100f256496000b40210b40d0f96940d041d103818080c0c818081240d0d80103640f4081080c00c00c00003140740c000e66810010f0300c001280090701d0300007070210080e2076400d0354075001051408034410310290200200c400c003a10b017a50301c914000f41007a01d04035511459030402c2c081980703010030000d000d407003460341620060068a03201030117540000d41c030713486440c5094071102003040301a04520300904031403000c0d001c0060129001405c10988c054070f5000c0d2a845001d10040040c05e40c180c010455105040c100000018a40520304c003400c5c4c0304460040c031080e1703035242106210100d842448010f208500e00344542c008540b000030038500c980320601030000c28030008034002003013200441d0000c0c807400084412490841ca04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 186908003 1250 186906753 186906761
    0xc031a01050f010f02030901031a040212040b1602070b2503020307051b010512100b070b25120b0f03030d0c120e0a080a0c08070b0f060102010c05031b0913 68
    0x182600451560000100303d500901e000120001960061030408213100700440050901540d041c04190141e010201c0d1511244010600b41100c201c40c1c2c512442d0900301410a03060242180e03419001c0c0360600e9030300307a50110700780c0c0c1641c81d84c1da07415650301c007952080ca8a499008000c0202c10404149920801d038000000344111482a0107907010510804450960404004060b038080303034003007011440c8a08540f0034640d1042d210845400c025403501021004d5400410003121a09010b000b440a40c0d480c1000d5032489251540c500040807281c040010094004444500a01c9450f41050015039950f40b11103a00700c3c6024040741d0310358072150400c2010b081115496000b2410a55110290b5216030184800400d42440200150300107580c8000b0554440c900000400101068601c001402003005200440c010085407006d8149005c03a540030b008060515410f680c9400b405c41c3d001500942540e0f40048a69040c2c1268071100104002034400e102e0b00e2540041e913040350150b201000d80c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 186909253 1250 186908003 186908009
    0x20a170f010303050c1516080a050108070b07061b030605031207120e010201090b0f070e010c050304060f090e0103060b090106020c0906040513050105010b0a031b12020706020f2701050a08040803040c031a01 90
    0x1423090b0b080c1e00c8040b015000c40300280900101508070940c280a031400030070042161900c551400154110780042c94070009400002d10400a40c40d440c0420280c542006134038181a00710043c28903050041d6621500709080145600a2004142c0c1041d01a8000e5003d81c51407500070030160110310b496400c10700741c86400c40e50900030559030000012154480d0b02d10040c100d6022000303500c2d00d0300342001500c602c81824145000c1100c4081b011403050641150140254814200861081d410008004940350305803c04011907111408814487e03445a010680001041d00c00092503212070106550f05142001c1c042c15a6082200029182281078001d03c2500150ba03410400d051141c84044c01e072212100d0940d002034010148410101c409a00412081d441000014540014031100c401c030394203d1f9603c0e80d62640285550f416030300b502030703040c105001d0900e8101c1c9840c840040180400c1d801030000340103440e001c00000c2c100000d00d2999009190458028042450616499803600078240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 186910503 1250 186909253 186909257
    0x1305011a12300f070c14090705031801020f0c0c21030d0203130f1a0a05010f0306020702040f0513031418010c032001020a170f010303050c1516 63
    0x564035507550120300c00705041106550403884141802404521401800d0300d03040301d120401c502810284220001c024241c40f8002940e001c5180409582614202c00400c6014100c3c14003004601caa004041302c0d171040c0d821500b0440080803c50b00d40c020300408030502e8424900080741c5400c46030002e130100c03403401c0854180d0001d0180d82682d0800520a0911041d603501c00e1007a200803070f03003d4001e141d002c400d007003458003008451384900401c0c283c8050305660042c20314503401a0300c040400c0b0a60310030f840c09824082c9501d0111245000c0000380310141c84258081002800c40d5501e401c0000c0780d0343c88010501013403c140d81c1003a40070182c00000ca01280c040705003940034400e5941074404203811050b4034003a4210020046d80c9105400000710700304854042d0800c0c0f8503001d6001e4441c804024400180c44130310702400a40300881c04210f10300d6908044041001d101c8407118254107480d40361405603201e81207402d0443c5811801c2e600034000441382420009024030321820300071018526 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 186911753 1250 186910503 186910519
    0x1806050f06040308030f04240e010c0c0c050114130b0307020d0e06030703180611090118081903050409020f030f0a020a0e0909070305030d0501050a061d091305011a 72
    0x305040103414451407100411000c403e0002414906282c0d1425074400d000f100d15002c0303140329001c0e81c007007124000001c0d042e2954403103004690030350034840c0d4503500740c203401e05050b191081e840749082c448580c0700d500d0400c058462801e030010000c20a644105000320200e00d0b030b2035158550000b0315001190000014401d5466030743e20300303114005d10003004801030036440c511b4441c205c0c01c50140c0640841490880d640f20002d2001400d144200c1010740781c450310035130b01d4103407443c0010507400c008448440c00d032846000c14041d45901252200000301c0d20044e155156045140a907018000d60740f10342c44086c40410060041c1480e10002d500c0354402000d002810350f0351002c2c10b000c0340940030102d000910201c4008d0014100042010f4021075482d003140d100329542d1307590f2072440c2d0200b0708052005403982d00402c0707a418109a0400138200c1424000c09011010080e543e4840040301114421800200440c115001041e0792061090b04403009025034900e944001045170bc04c0c0a17094098041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 186913003 1250 186911753 186911779
    0xf043e090c18150f0d060e07021f0c090803160201120203090a03030f0b042301270f02040f030f021807090501050708250b150604090213180605 63
    0x107400c11640310030744a1070003407840c900380b80500480542e44004105070305410004948004400c4025050a40306202c0c0880c4030b500380800d0041050000d81600c0a40d40300d8144011a0744010b082c0400b11440c03641d00103201c02d140b070030480d2003951030f13401600240400a0503025510502d0752020201d0300030b8903020300380f04008013030700c007280300031604c40c20036800c01c0803010b0000e0f2013a0484028910500d0340842c03803000000000701100c201070b4000340c0e204400d800407058407800340883c500400611055000e01c02004881e02003801e410a60f0180441c1c0d0790501e50702400300340d41540c000e4001084040c1c41c0300d48078a0400b000c1000c1c01e009070b10883c068440940c2c0034040c00303101032040c207503540d40c100d92505e04070040d078041d0495041160000c1080c445e0046400740c0111000a10b1811440d40140416030300f42144140c4000d0a002a40c0045c204c41560f01e40301c400840c0e0072101c400d41c00594942c0048002c07403030420140c222441c418281c542c0c0e8203e603d499040501030340c804640340e4040b294 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 186914253 1250 186913003 186913021
    0x120e0a020d0809031006080309010306050906010c0b1906060801050319030e150c010908040608090102040e1504090507080c0f040209280b160b0f0f043e09 68
    0x640002588060400071000c005a5010b000e050781c06409001c58130011003a1004400356078072604513480070343c400b0510305955a4180148002480c0a0700c0041d40340c10004002070a02c03c400c0005003201d02c0d4040800c074200c5900b07003c2105000203500c104075013911124000c00c242e10030302c2000c3c0f081c0328a101c50126083c40025003148290305840b50302c00450590244000d548540008a40400040c4540c099814081c0076602096104903d81a0f6a40c1442009440c00e00040e01000c25603105010030b00040a5108006404c1484002070304203d845c40f0300003c0103801d500074028464025900700140c2542c00045c041451441201d170356450328110700500c0100e0080c81183c543c010750000d029803480c8a19910031500020610075880040d440e2200c40301141c0c8141c43c02d8001e403404055180a01c0041c903070030303074101c401d60403061164104003040140701d01c000ba0020f0a4580351841045019848803142d0a15408000e4624600c400f205840300c05646410b58040c020901d00c000981501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 186915503 1250 186914253 186914263
    0x1020a23031003150b030106030c1a0f07030806130c030e100c0e06090301090b0702210406201e16080106080a03030f06031707020f0603010b1204110d03120e 69
    0xc210312500801403459501d420369401244010038901917503c1c0010f03400e5480a000c1c000284d809501c8600421703141c02c1c810018215172540240144800f84520b06043d000c0c8000c544481e6051b24220304039171a28400100040d060b42c584416040c40d04800d001003e23090b810680c98020f4441c252005914007901400580300060a90800103039504100c444510740756000d4075601c54054000030340300301159a0980207001c07e40e4141c000d40c0c006201500268850701001030300740ca4244400c1e0505103030044c01751a0aa500107100082090840d07219010201000f580354900c031420310005040d00421046030b10f94a0107882040c080c603000b1000b051241050294104444c3c1040091070544400d4800310001c02000d4088043d05440e05c1001002c2a60100c01c0040301404098856980845d481000205481d07001401d00815041c801000000c0811041d1248134000b44241080380d03071145042060000c2400d401540141c1c03403080d000505a00c41101448c12403051010000c2c00c0c11030140942d50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 186916753 1250 186915503 186915511
    0x11e0912050a09050103090f02091f21021e0406170f210a14030708090c01031109010c02030a0b041a0112050307080a020c040509010b030c010c0b13080c01020a2303 72
    0x108010f400204035551103a440840c8081c010141d0351410911580000d4001c60141c03070341103046182c034064010300c02c81d51740490300801d80c82016201a81441420035011003c01d90060711400a104400201c00030a221281c040c80f001041041003940710808030801007880703c2811b01505c02c0c140110b241d100700181c0c04012070002c505103010029030040250855000e0700da80c0c0b04000d8680625025014580050350140e08662991045413409901487c07800700c0071411207041500340501d286007031016030704940030702d0002e00c2c01d2040580c140c0046450000a504014a008008030030007003488001c3c0c2c0d000d050308000b00c42c0c00c001640d0f103d440c04a4030104003c040c103240c20030005038000452020042030041e2040c01a80e61003205800010221036040b11500e0903a515000302002a1409110840b034408003400c0201400d0f506443d4840030301c100800c0a003800307003014400024454441700340c0b5041d07040c4a00948d80c56507035120082041844d0810f0600011030485450742400c5164103503481 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 186918003 1250 186916753 186916757
    0x30c01060b03130b190c080601140a0807050315090a0c0908030c07140d02120d020708071a0a090f120b1e0601120b1309120507031e02011e0912050a 65
    0x16010300c0d841d50111602c0117040c00b40e0b03030700409041e40d11000a41c054589403030480c0c1c4072402e00e441c2030000549a05a1003021824900e010070640320030b10b41148005402403000c1c0381c81d50b00c0e0740d560754081c0c8100e84550783e401d9020f90003d04000105e1b4813500100d031700c181250303640c40e441d6560b140090b030f60340103d0f8480484c80d00705502c1400711804d48003401c06401c20040240c00359020540200e000110910780c094206e07004001c00c00c0019404102c01340003805400000e200031442c0c40c4019030b1070320020550750303102e41000a0120070240300703900c0c040c007a0246048904119075030318440ca07030542e03103190212134815410300011342d0340e01b5505070200750750550280e507240341da0740030011908214019040380c00030307664042d022020340f00d81074003507030240f8401c071700040d40241810b00038400d1401c9a128002c000d810002c07800000d50020881e50000022911740d00003441405085c1c0c09003250f500110007601c00c01d011501001810b40140c005035005920300c2c2020348603804211741c980304956072100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 186919253 1250 186918003 186918031
    0x50a0b12060403030506040908030403170f061005070203010f0e0703030906170105041806061502190c05060c010605060f04061214180f0102030c030601020613050601060e21030c01060b03 82
    0x3001c02d01175000359501c00e0004000040400e181c0d50b4402e15030300269402e500094043e01040200b034448031400d50040050400c050083c94802c00040002c400c9850040400c00c000c02d42c181151025000700014244103103050010b655000403140e034600b0280b2041e0001303503042e0380001e1b00300d0241418510445007446184200d070309050901000c0d004000f9240005d500c0300d0f01070030100703403a8851923018014440304400c1c4e9406141c0c0081c6404806403000e654080800c2c40440042c03005100c4c1e004844045d14059183d820381c1d12082e005001503404039801c400300284600000350703e20010019180f40d52500d07050001d4190780001207640c00f2582448551051010960080843e01030024101c204402c443d20085040089426a04107840030400c02c000441441041e68042c007104c4d0b40016180c04d40414080d240d1207640c3c4e6010103114000078000c103030f54426000d807100100503200c0c5000024400030703200d441c0340d02590b907403003860300300304a51070841d002c180300f00b2130800c4a00900000307644c49 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 186920503 1250 186919253 186919261
    0x8060106050c1c05220e0406050c120f100918021908070906080706021f0225030c060f020f071202070e0a020c011b020a240906050a0b1206 61
    0x1451a5209024040c82481031800f41d00008120b41d240c9504a00a5515152146403196581d20085403007103500361800c841d22001d00c1800c00408110781e000b40c200401107400d8655156500140c801c003000d0b10000c08040341001403c40c0c943e42801e0040209241c0144110760354110741c0c0498100034104070032102104c4990025180680c0c4641c14525460207c5042d96943c0c50014980070341c903030041103078a0316241c0800040c90300f40000002442d070350001c0c00300c2566440700e60008601c201c40e00c03004258042105111907524144600c0c641804a282084070180c40c14003408000b181c84040314402c0c00d15542da505007282d03001351760460842885036410018142e070340d1400003200501140c11403007001800a52a6000101d042c0a00442e00380143e940c61943c240c0740c25034034200c5000ca840b0b05013558882e22180d00143c0303a44495004240305c3c000103079038440c401d001c61407108800641d900300741c3c84034180060307907019074084c0d49204d4040181811040510540d206020714950282d00110009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 186921753 1250 186920503 186920507
    0xb0114190303020d2003040909061b0807050708071202010e0610060903150f0c210209010e0418060c090609050a031a090c0402133311120409050f070908060106 70
    0x801740001c0d07507958445003500200d03285c5142d41c000380e000315402d640342c20070003062000718810750200d50408030098201441245015040003030140c503420030401c00103114014005600191003c541e0701900e00c0d10f01c0d44403954024040d15104010150350301132040810300c0003a42043c10303803c82e83d0075140e00c01903c0c0303961590b00107100c88000c0504141d44611141d5001e031240c0c41044402103442e00d94181d400c10b9260301d002c590007590282c80c00c00744104000d20301c50381c10103034001c03201c0390441c1c0114030520103842c502018000610003d0495041020440419030015a0001138801c240d40e83c02c891652001000792242492101410b02c0480106904440c82c144040b66405140102207880c81221040408c0c100e0740494282c40c004440740d5801d00803403285910004060720181da110506411080c6d9010140800480450500041000d510030441007480030349404284821243d07207856490080740040c1000301c45140b000300542c00019000c500880c5032000f551802e0006090513801c00b002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 186923003 1250 186921753 186921767
    0x5070e01050702040609060e010312080702100902040e1501050411250f0f060615080403020d0807120f051e19091a041b060e0603150d0b0114190303020d 67
    0x580c0c00c55240c040114000ea41b6024041c0200544c0c09460501d600d141040c03018804400202010804003e05202c200c540c0000c0001002c00707000400558042d40d880041d0003403000d45c0c005445030041503140d4440c201000c000301e040300c7c030964050040c0281381c5071010080c4906c068210b5005a1000ba614840f2003804502180c20b11600c00d010001c10103403920030b20500020000c5941076200c001c01d1010b4500841307041e20700c1040d030414800c941490703a80651142c410715494420090400001161140b0070000c89c003000c030002604100f00418140d600300a000100c0e42407441d441d0351442d0000000c0800d071240c1c400c40c03400b0503088515000350b041c1c00182c549440161203d40222420410481c0d6180b03c0c2030180b0700ca05604007400004909030102010309134410004e000640100322902c0d00c56078100d82c0e000001c031784901d08910098002404908600308080e082c4c030803d07c00450b8904e0b0083c50705030700040407500d440352a058000250100601c80c00000c0058200c2a8864021805044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 186924253 1250 186923003 186923017
    0xf0c031b0503040302180a060603050403020d2f07080f03090612060307030b0a1d0f030d05101703041406030105060d0203060f032508010509030405210d0c031205070e0105 75
    0x4180d901d800e90745e4000592040b12003040c80c203140c00354024002910f245104032401030805d030034140221314050300c019458207408203144007445001840c0d58800b0359034501c1c1e291810a00b40c16030740700e8903a452042ea40d40d195806511420700c10a07850500701a400002e403081241c0040c2a20714103940d50000701106940a40759541500c00d610380440005c001004103407288200050000c4e10900d000d11785050348808200c4040fa64003c444140208a0040100c42c210315000700040707401d803180901290500e445038014119914051042c06408801200a000701c90840500d11610020701c420003149206c00c0c4900303030780510f00304140708510805402a46d0706c040300802d4001403200060109007040c030707003030014100409000c5543c03c00101d03210b220000b900106000f00a85c0c90200c0e2540c2e0f880c4540d00500303125002618a0030440f0f81b401c640713401410300740800d40e504041c02080140c01450840421404200e2a8560035900c001920a5030305c45d89003507982c1d1028071100d600554083e4003c0d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 186925503 1250 186924253 186924263
    0x1110c0c150c010c0804050c1008070c02010c08030109061e05030d0e040209040501091d0303040b011202190e07030b0102030a0206011505090904080408121216121406010f0c031b 78
    0x400082d1000c8001c0c480c0c070000022549681c0c200b86894a0b10600b84810240c031031b48181020003800c500607038000c40140c2d0045040c281000e4400c142e000590b040f2495030001070507060000b00201e151301361600208102c800300451441c012400101c004030080c4203006043d051f5001c24004120700f0702c55a48400f0501e0003910040c94040c414002c58240d4900740c1101c4186512801a0b8255448408298403500c644501442c1141800e540f40769840d10184542c0d248800766110388001d6545a440b100f0f4403500121101420941d0303a4046c06a00344116150340229240051003245540003104664505045a01905440c0e0a114030b03030307030000740c0e1740d802500b04039090008041544581302a80d000c1d6025039800d03030321541340c022244d2504891004450700481e007408400c0402c219035156541102800050540c0c3d070018100c1111250010341d140c8210600700f04101d07003002258083c042c0216001e030389000000c0300220082d15015030401000b0001a540040b00f440801d0b40b450b1b1003c1e0034450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 186926753 1250 186925503 186925507
    0x181002030a06081b0a080c1305060a15081006090503060f090f0a05010e01050a1119051315090b13260f03031f060f030504020a17030702010201110c0c15 67
    0x100c1e9141e180000c5502010b03aa40021307030140609180c90910103008100c010010722035140c6c40d4002c41c0302c45581c5a00c24080d0b42d00c0714045282503485810308030184c4102c030002000f01614807401828298160f8605100e942e0403440418501c0c440d405500030b40d50003400801e443c1d180e501584060340c0d8001c001c164140102a5407141c5602c0038000e1300240741c01540046440703910001e5250071220090210703400307146800c05400c515582d00dc1610301c45c600203204100c3d08040150151001c4c130803207945608a04c020325021070066400d60980e0704245590b501c00006989611151030584280d40b4020007542a0903420451401d00800740d0a030b00f0000c03000f000703404013030114080c5400500155941544c00200822810140c0d0742c0c08415141a2160f403455602c0c640700015008040c00180c403001c040d11f603000501552282d00220004000d641881c1e120403d10f60700c055100d40100744203d006500303083d03003041d00101140c00d40703104204640240404480040410400d10511066aa2030001c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 186928003 1250 186926753 186926759
    0xc0203030c0a0c0f05061311060403030c0b0a02040e0406061d0403020712020a0b0a050a1d060d05060f10030507020c010203032203140c0a03260106050d091e0506181002030a06 77
    0x510460340242041101512840083e1902d5103060070308c1d06505024200502c010000700f680400d260003200e4001d030324a8048c1e16004140c6020b44100e400c0f00702c01213040d00608c000c110700c56008900712030401d100a940c0c20710030503008494842c103031400390040e4410403007031104049901007420414401081d5010840d80c41c000d1b01d00c5604075100c8200070540128041481c9034001d10390314104200404d9054118031150000b81c601d0144904500c402682c0b8800906191070713855a038002a14000c03c602207208605c40028040e0400711690801400350013641d0a0070350002095901070250302c40310a1020524440103280c440c050328065007080304103a02c0d5010b10669000501d84500300101400d40c5072a9402d003d4031400550261401c04101c03200d00442c1302c861001c2581c103440703c514000781e03901307034003903404000c1d0051000203850035002c3d08048000982041b0078111040c416429221f030b0380e032072902c1c1b4812188400c1c0b001e02541c1156141003680049c0764015a030003000500d000442c0c2e51 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 186929253 1250 186928003 186928013
    0x6121504050c01080f1b1813020309060907030807030318080705011a010309020d0609020f180f060a031a09030f0a030f05130503161a09031c0612060b040b0607080403060c0203030c0a0c0f 82
    0x80711801d505084ea4000306200c0a0759080c09818de1241c0400002e04241d499555052800c0c41341402c003a041683da101782c0480912105544070400742c200a400c0d844a009090890091079211188200b0107a906409031244d4000c2c003641900d546c000b0240140550681c60300001345c04e1820301264410811f40a000039541c03900c0c2032210000b0410300b131000d5884d02445001551002a11052003007460740030400003c7c64190218040c0c400807181d1140c1d546543c040075180d030103a1121809100c9010580c00802645940b008060b04090007050000b9250480041c400f07510412010780300360410007110f0510800b440505541900c80c40031680740f80b0300c00600d40041c6000351072400c000e03017002581030100808040c480142c20110481000114075040044036030b010304000092105441d942186525550f5520a22581801a0071540d4a001c18031306185a0307070040c04212185460480c80302c01180c07000017a40d01c240e000c0741b003403442d03d4075210301030ba620f18984008491544050013240300045e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 186930503 1250 186929253 186929269
    0xb0309030f12090d0e0a0303030c090b0a0f03050a060302010f140d0f0b030d021b1003020c0609060403090e01050108070e041814101406121504050c01080f1b18 70
    0x900c92000a03014181403e6071401d0030300480d008020030603451305240c61540c9540c004030440c1d50504000401c080320010980d4a00307410b601034000e0840100c0c00308001c58020b8820b0f840108107a07002c0010350307162034170002200d01030700000e40000c030325288210300e00f4000d2108003c60304401e0b150303030b0400310721007407803401d95811511182c0360503101c1c1c04081036810100031862003540355002a00c6819030007003907000c0700064103140600c20000d414540c01c10350300039412180340494210a8607828039200e001c081e0f5428043c2e50480000328500c400082d842042600d080c1624ae050f0b482c000561610402120031011202c01a03901070b50701d8858440d013044082003901c103544039025680602017400c625500b0824640d0541c00d40707600703000e07004030310304507550740d4650180e81100d14161980455520300c1c584201024540040d4250100740410711500044c10b07030340844241ea5142039640d40e800f81074110042501c0c020b4403050103400b07440410b9450000752480c08004420414601040d4001070710728 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 186931753 1250 186930503 186930517
    0x406140a02182d1c051c030e0d03020a030e010204030506040c050108010b09040c050906070605071d030703021306170303010e10050f0d020102010e030703051308010b0603040602070219090e010506090601090b0309030f 95
    0x35a200100440920821b90038640000c00d031410104110f46103110201c0d11003580c80c038560105a030004500001c1402a4009400c07601500001c649a03034403444c11070760701d0707034259000e40e150307100b0081c000360540c800d01d07410b8103071480c060b40c86040c006924180005400070010b01400d02600348600b00942d2220300190284a00413000400d8500786203001401080b02910740302c00e120302c00da12015241c0c60000daa0411030341d058482359003c1851004410042000350080a01c3e104280b10f0302101c4000000514181c921064064440d9160746100b1108000984205500300f010203000502c0c0b03140004aa03c201e80c0107000128804c3d100d00b80c0035055a00c00b150441c080f80c40030940d80c801c087c01022907006800008000c121a480c070f00002500c502000344018a101d800003081c608545442c6189200c03212444044002e00c2e45801c4c0e000702906041600810641c40c0200160380c81c9042d014050040b10181c545010349414080000d540d580000c00540c401d120030400300840d06202c800400c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 186933003 1250 186931753 186931763
    0x3130b10051f0807050c07030312020d0e0303011802040f03020907090b0c1605030c03060f130204050f061c020105030a110f0316020d0c11090406140a02182d1c 70
    0x5045460380003d4070944001c0e000c1010000144054100304a00103181c0040d240c00d400c00b803543c0041d080555000e4071a03003045565032030070000f1407c810304000010358140c500e004502026648060901c00403801140f04240d170301c0c4507085041003d03041810310782e500032099140030200d1a0f00c45c602e0900341c1c1d0284030b040ca41d6074030808d2103092014085050314080c20044007d840c00072035901c00a982d940000d0186240d00e5441000b15180c0d68541040c18540c03540640180031925040e00121090a022148540640c59020382c94010400369940340080a5050312214190307121649504000c0110811000c140c103020064407081c1c400306c8000c1d601c1140707105080b101a92407040001c1c18a40c01c076000a05020b400c1c603100c00015848266442c04500956110b15250b8980c02d0640140002035144118180440c0034805c40001c0354000306000070782c483c07070b640600503000c05001d106400b500690203124495003580c90115000d10b00341c0c18411004001011002525442d01900781079220103c5d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 186934253 1250 186933003 186933049
    0x7030e031b0a0f03360902130e01080a03030b040203070815060d050c0a03200711270105030d0509130b0f10020a050111160f0206040f0311130203130b1005 68
    0x2081d40000e2170300346200101d9000820340454061406000001ea4064040c4164001c500303820f1000440c4401c5001b03254441e00844156540c1482648503a2111010303070020342031052521003800d00b4000c8074080d03200b581d1044c0047d03507080310b50103103aa5540030140c0d008008102c0a00807042ca8001d2901541c1c074640080d03030b141e0b403155029007103d0300340000b24a41c607549003045031070803600c8056801140c0c00c51107000c2c10014240016400c148030803081a95403664240c45001c20601c0c88070760b03060b980301f03808031030f2001000202035640380107504030503901000e00314034001c1c03440450b001359800305405400c8419100381c00b40012000031803034840000584c403458400052003001d00540110700400c0382034600e0070007014500e003201140c401006d041d606801c1c0e445021911130004540003000c41c4040d0b4502c5d0380c1c0340e20f0300032146009220114410701f6610092141c1e41c000d4422640079105610300341c60624015980d0381401d0320020199002a44d14000000b41c03900c89400a40107034802c041500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 186935503 1250 186934253 186934277
    0x3070b09010c08060306011505040911090f0618010518041b0e010e060922050108030d06050609061c0207170c0d020d020607180503030d0204080607030e031b0a0f03 72
    0x5030845040b0900b00003080900e030107002854602081d032505440210003101d0000c40d03c0340e41980e840c4581d5000b0036030149008000280d10820a01400b542030044a41960040022041111f9401003040c2c0007030310b080c200c0300c0c96059805000240083d40d56588901c00c00d52588002030116080b0505112072103010f8021442400e0740b0809400d0014400d08001640d510b4060100d000c078000d070280300e802404070340d0354040301100a014440740e029146030180301c11340c0c5504c1050384a030400c2140c01c1d4000c0c10b1140200d038a240980580e40301d110003600302d9040640c051100c403060040803c1a60741240d081180d0804614014880305419044031442582c981103081c199141c44000c054400854100050b000c40e22a40400c5940e000a6140303801041e003c84080b14140c1710815600c40ad900d840b001401c01898407007030700a48211846802581c05c180e0300c084e003c0d02600d004014001140d0010001445003401c05011040341030b940714219241d40040b541c444195076540e4a042c2d000c104500d102d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 186936753 1250 186935503 186935521
    0xd0302070512011a100c0b07020309040f05010803030408130f06090e0105010f080f1e0a060e0105090c09010f0e180907050f030a022103030f06131107020d0201090803070b 75
    0x104940342c0840000300a501940421490142c01c903184451042e06284081c4603210712031100f05007425000740c01401c40d41032150000e03540341c0c8420300260149017481e0541c0540001880348034100c1c0c0a04001d9851aa21a07a5100995019085094401c1c0b80781002044820316440000d002c2c140d25103487e425541004110900c1c00070582c4014100480440d040d41d01c1c903400f03a00c0540200000800740003a454a40007050020740058a81600710701c0a0200040d503060390b00031000312103075aa420a01c698880017408081341040715481c0750fa0804028a0300c1c81c1d40b1402c6070000b1102c0610b000c0c8071451008000881c00d14849000c44045080e4505001c00448203001c0a0300420080340c450641d99890000b10f51699020f00700079201e61181422012541520b180e40c5101c402000c1c01d40340d0307900c2d0510841c55180e405461140c0961808007100c9270019851043c9002c4c0030204041e40d040000540c20440d8402054500324100400c80900241640c07041024140b090b12564a80d10b203441c0c22145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 186938003 1250 186936753 186936769
    0x1410050106030b040506180606090303070609060c0e06041205070509130203010528111905130e06130b0a0801020408030a080f0f070507080c06071115040c05010e0f0d03020705 77
    0x845200383c4c501003c0c081350f690f0341d00141c600401d0080038100389239a4403000640c80e009803104103405000001c5c2c80c0b401c0104550040300720754070484041021184400d0b00300ca02101e11540765070801010002841076111903841c190040d0f01c24812940b000c4c4c1c403240801d1a1410965040c1e5105003040202c0085180a000b00390740301d040403c103a062840200e407129250080458155402640d9941c0100c2400580085420304800d2500001c0c90303080b90807008182c0e90107110205481200c0c00c0011404030b100c402c00c02d000762402450000f24840d0040000000e00c01c9501c4182e00080104000980341d8003030020300014000c1401075500d400039440b002e03200c500014003604401d040100ac001c031340e501e5144c00742d4104130589420398840343c4a14000c1103620070b2200d620b44c40d02c0b403c17040110140d40600c0503010301142c5401c0c3d91038004a042c204544040c252001400a0000e00302031000e1b500ca1a0509002880102440580c04034040404c25480031984260016040541d05004c00d0900f40e00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 186939253 1250 186938003 186938021
    0xb090109051b0102150c03130201030b060a08091005010302090c03070c0c0b0a02010e06010f090509070b0f1801110a030305090a0f0b0f060102030c030304060218031501060e0409030e0d141005010603 87
    0x905000d030f0b24001c1c6d0421024440140100c000c03400a46880e010340e4407075030010310800c401420350703596a254200003811115040301c14054600c61000d404840207258012281201e501802c10985621a00313031250141c0c000610410800c00c2510b003000c0072940c80b00c2c10100820180156540d035030b1250038001e0940703400c00300041955118600400400d861881c000040f600780b12400145030b02c8a4003120b0900040303501c04005070101181d2f520a0796003c0c80241a6441c1020010380c484540c130005642d1500d801002440a0f00862000303030201c4e01940202d039000c90704070159503000c099a40e03001003412025400390b400b502044104442c00707501049a68000704c003400250b00306a0f1508009581e40700c0180002d15054001c070396005025000412203d20180050544101c1c400a502c030345002a024071884002034401d052103040f509052007009a92070b01030340c0b80e50701e044140c000c0c0000004400d40c00c94401c10706948030440e0b10307014409620b00d0203281d9400305955140800013010f40702580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 186940503 1250 186939253 186939283
    0x3060f040501061208040302090403020c060c070501020c0d030c141009080304060506030a121d0a0801050a051803040b0c0a05010c02150601090e0f09071e0f0e01050108040b090109051b0102 83
    0xc1c90140214410100b51b43c202c0b941290b104650703998030b1400303e040951448240e9044440030070104c045520110b00113094a00c01e9007101c1103d15800c0810007095501113000c2d0100341c44010380380100351004401b1b84203409140071942400300a41e454400c690b880d4905a905180200c2404200b00395405050b4000a00b2070041100d00761640703507601e8825a00386d00c0002c0c009280c040241e540c6284004004001e0000d02d1019910342d110b146e076000c3c000c00c031800e041d8a86000000303007440b0200344444000e8940d078001541400e04184181103d07920440941c44144100140e070300010368240030390b000000c0264050040021240314140c0900005400c59041c8951402c040c0000214146506d41c00b0081010025594a03103150440c00e201c3d80e41c120440c805442d0740e41841c41d0070141001c108481c2d07205070341142c181d41e5141c110792075030081c0500340c00140080046800302c0c100801194104040500000b0540c7c1ca96481c0c600d0b104682c41040c0c891541028840c1d640d40c1c041c401c0b020000c24030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 186941753 1250 186940503 186940529
    0xa06030b040b03031b0f030703270509040602041509230105090a0311030706050901050a0c020111101508010b030c061308070609150f0c0b0714031003060b0102070609050d080903060f04050106 84
    0x186e030b0054402241951010401c0c8a900e044450001144d8002b0004050103412011582031904210f0040e501c98018200107490000d40c5010042c07050418400302c1c1c1034ac05400740d125480089420b15620030b02505030400406202c2142241e4400100354003c501c01c01c3c007504044a240300b414244070340c66210000340301081c0000134607a60081308980c40c80345245041d014415541c801661400f051040c05455407040080704442888194424180c103c01c0e46a030402d03460ba40d087e070a09030743c09540280e1f0140c01c80b030a004c040f4113110780a4000d02c22a48180d079109a04c403c807003860142d00d640b101c0000750440504000584400444914041c0e00e031605046031000c0d40e00142000780e103441c00405d4420254001031000d8486c3d05010040300d01141c240c1e41d00c6c200707550000b40090440c0400d4814a00c0c0200091080d800041e082048400030f07100c1c107826034544000c002080710125404d54080c0c00801c42c6080990703060000c2c91203103912076a10714041c2402d003800b80c00c607119504a00c21602035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 186943003 1250 186941753 186941767
    0x705060703080a111215090c130b0c010e030c0303060f0901080a0f03050910081006030219080702070909120305010807050d060f0f09050a031d0a06030b040b03031b0f03 74
    0x8099440359100129040c013145003640c2c08103081e040c1c4120f00b10100482c1780d07102480b4013803402030380c882d04180c070448128035141c88075100300c1f8a501c504021401e91307103a0710740b040100010b01e0000d0402a0344510001484650700c8825a0542d400800d901c4a603410000420440c2d103021111914501015982c0d0000341d81442401992540709400103030021079214806000c00d407140b41100c0420902a1104000542010303000d440e9071410b840d50a08018203010202e68584a4400d480076441400c043d80180144c003d011348a0f944083c0810045009508000c40c211503240079000034035100b41c9a00c504e800c070141e0b00504640c810381200e4800c1d00929000c20941c0d80d02e109142d28142c0010b400603600100024075401000604803240940782003140c3c1805101022400c21015400780d140c24007500300e8600c41605415602a0f600d44c000d10b0008140407480c07195004400c4901c0180000842440e40e8000074a15082007014110141d04200c801022002c2400b810025480040042d820010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 186944253 1250 186943003 186943007
    0x10e0c040509070503060709081507120b130608010b010e030114010510050408070612200a1d03070f03051903020a03050306180f0a0606140307050c10020c0109020a14091f09150302030705060703 85
    0x281c1ccc9031481c040d443e00d50740030611a81d10301c5540c6001c10b005c0303403040040f1a076030013446002cae144003102140814143d40c620a220b04040c040c0d000c0c04440d20340d4840c0c00e80e00b00010800d0402012644808220b410b00c0b010603080000c004180140c22079031606019840c0f0740c11540107446056040d20b0481e0280e03800100f142a1075000d45005c18104d04105403031141c0c20b003481c240385000ca004a645445038400000b0741e103550142c0d00c03003902c2c080c50607215046640d01a0a950111403a40280168844048030010900c070301c0185411102c018000b44100290030b201c0000840241c1d00f2030010046035080c420501c1d02880f136900200b000d0f041074a40080318990074005400000c00d15000d0140004144000d0707441401001021050401c02b151a84540320106000304003540089000383c00308000490550031100045a0240c2c00811005841c1d035441300100030100b45040b4650b82004856001c00c0307100550182240e21a4441071a408803480c43c0101454491540d0005004003800c00c50340c0c020035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 186945503 1250 186944253 186944267
    0xc030d0b0f0a170a05010f051006050301030f02090606090904050d020c0a030b0109180212070311040e0a032d020a060c0e060a0311070b0106030f060602010e0c040509070503060709081507 82
    0x302c401114200700c4411000301800c0440c285002059546032882d1f0100f280d0b160350000780a0303500700d035405402e01d4840c00c0944241c48207010250041030840d540900500d4641d00b00b66101101030051070509178140007154110006980444840e0019200b50000703a03410804805003200454001c1501890342d100d807000d401041c086c2004464680340301d4400321004e50075144d2101d5000d40070207840010900100d4480c1e01030700040b1103039200b8002c0c00100385064021000d21040c55006071001030103659054030920803180c82694001002a0290310000c090b0700103d81d0545030340c01601c4503640600c3d05e102254180d81100c01401017038030520b000350310740ea405d403100003c0f18100051091507080b1803154601640400070322400307440c0004982e40d03504d60000074103645086c8040c001113443c1e503026401e80e5603020300c2c0c03145513105c80320301050b03498981c00441e0000c0c103040590701c500352074101103030800303000300d0307100b008621035000070042c1c0c00042001c061040000d4a0102c960309040234024901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 186946753 1250 186945503 186945509
    0x10522050a051f0b0d020108010b1e0a050409050a05040c031407030606060c0201120c1409040609020a020d1e02070612020d090c1a032502030706020c030d0b0f0a 71
    0x641a5005102003000400c080c090164109084030491604891070100358140c410340b01c04228204603c085150402d140b45c0102d041e0305031a0001240c1c01d28941c036102c2d4120250403034ae03a0840e030741581c0c0c450201c00c008051450169170348564032070524040c80c040d10f0003e03040088035840d0504020120304119481ca003900d90100075403010311801201b26180540765000640707150300c0c0c2000010780d10b030001d6003094010b20030380f2500c40c2c1c00b0400040c8411125212021004140019540b5240e2080f107002840c50080013800010041e8603017035071034101c0c1c0241d00c0c2c24026a020420503410144c002480401d50344085000c0c544c03480196100a481e85524481c1d2b100b413142030300c0d030580070b0000d07074064031004002c0d0141042018030a0070001154901c0b841001030003054004500c0c17480d40064107c0344a801d000e121f080700100b50700a0303c0302508160314244d0844c0014450000010a00c0c001000d201c6a0000110703120750000c4616801c584814404601c1900c200704100d00e1038550062210403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 186948003 1250 186946753 186946801
    0x40804050d1406070309120203030421020f07120212030a090504090305190206010e091603020d03180311100f08070e04060506070b0108070506090a140105070605010b070b090105 78
    0x107070300c2524280040d031003400300705000c0d4040c22082001441d8581d00c4170b400d0900a8400680800c0302e014243d0301da120a640c00f914134012104906080050340355610014801c500c1120103101d6003c1c0d00720304102180d0002140d200706c6013074030300a6160030618a803454650300c000c3c1d858610510720107416140b903031003a80c0c091502c83d0140418540a101a02d04046003590924501c00082c50001c4d04c8210074000c0c000116407000205151044c0090804074001e416103484151608607020092000301244040301002441500f210100301c4000905004600c600c145038440340f900800c001140c6200006401003240d8140c2c902c1d5032a40c0010800c3e0000d099061036150a40d0300000300d8003400c00c5801541c0c000000045030000c000166890740c0c12241e140d810ba136059030b1030301c0410000d441101c0f24180c0c421003110003480502d2601c05012201c1e00305042c907d00d000c00340d0750b0300750946200741d02c0843e441201003200c1d42800203120000c2d50160280000f08513503e00750281e0401d8500020346050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 186949253 1250 186948003 186948019
    0x402090108310b0f16020c1302072a050102010c0e01030902030a020301020c101512080a0302041509030b1e0c090a05031603020a0e07020d08060f0d120e010804080405 73
    0xc40812542d40c1c90845001000350000240c040c2007946441c10140c880e080500d00082c001001d201031144003404610b129405009105920010441c0e01c04030b0300920050250308000071000030b441045584d0340c81c40340074243c1c0c03141c01d0100c0f10200403607a43d60185065904007101700c02159071092905103183c0007420f0000d0900824000300389170080510b4003c1d0550302c0010350801c48400040c84114122440a0601075101c440000b444180a18485c62100402d5000f4140000b034240b406021110821301e0014109030359109642d540c241400c1800001c1182c610090040c04030800701568403100714001e280890300305942000e52518002e1800c414680d01240d21001c0d0750b508682c0780000d1100904458a03484001c00801000d5500c1c40304921804d9a140f0004803000c0d0031601500c03d400c3c1d0b0300a4007220060880544002c50010a419409490150440e4071aa5060107900701e841c0685003440d02c0000000c0003405403040e1030003c0341030106040070000010050710071202660000e6540034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 186950503 1250 186949253 186949291
    0x12080d0e070833090a0f06021305190b07080705070e040c141e0109050307090e010c081b030411060703080f150d020d030302090d06050a060501050702030d030e1009050313050402090108 81
    0x80d0600017030240080411856044c500284040750300503000301d12440040e401082c0d904c40400c485020380c001c1508510000040c20041465a107002d40025802400841c0c500403031076a92608100d01500f01e00c0301c400c00e01040c80180070100201101414070307921820000320f06040080c80640396600c8065900100c030b801c9524503440b4041c210010b0070054126002c817500d51070091701801008682e80f01561038000b0031320141e440340132021b0046c01c61600100f840c41c01400803041e25840203200343c50540c180482d10b0700302e0301c504004290850080d030341d04045090000040c3c4a0401c0a400d2244c80820620400301c95a03909045464061741254002e100103d6031409034040d0007040d40569100c4400343e191400d00c0f180340c024910519616400300583c546036070056506024040000e5090307804240400c01c807034041da001e0044060084116010071600c01911010307030380e200a045440341c00c045809564811a00074600c06450115401e42c01c0110f11400200001c5006001a0781c0e00000c82d010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 186951753 1250 186950503 186950521
    0x6042a0527030c030304030c09090203030f0412050d091401211b02101401050405090109081321051203070c060c1d010908030412080d0e070833 63
    0x442441082010140880c01c444112030201400200914000c1c002c55035044110719020003180c059a0f401212161040d041c002018010403494808030f0305072004002050540da5184050801445060115544500a868880c1c14200e4080b805030a0010f90314050001b4000c207440242c1e4030000f80f80104410340d103050000c40c2801500340d500c032030610300300349402480001e20036580b42c010150212101502c1c50000c0004461504080f203004210140c014451454540c0206030010300c501c0011410b5540e81d165080d02e03a0101d1624502d644d541d040030020030103e03d14820303c0d43c0762030710040f0001c0099201c1c5511060000220084044000300203000b03140103100043c0840c1d0850010401505c440c1805040141c03081c0e10fa07404108403490000c5903602c107017049400c0d40d0610707001e541054540240181d03c842c03e150112600002400001b800102078800c160015500500405c44c9a181603e01801c04490078010090070040941c0519500706c039490f4946018000f1201b01a42d9683c0016 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 186953003 1250 186951753 186951757
    0x301061b0c05190306090809030616051b011e022d07230601080a0308010806100509070203210105010e27070c0609060c030b03031626040801060e06042a05 68
    0x24080c900d0002c21b80d050042038400b401d0302440c143d0440d42c1a8458051051410144031100c0c03001070820010221142c2c0002503030f006140c004000411311454607808111460b400841c1040c250b40c3c0800d5026052130b40c0b40b000d003016440d07054400b0600c0d4502140380c05520400340e0103841940d000c2ca07400801454601008004014401618415611a05156158000c40400b41c3c00100c0c05400413441007004908240203003200b14600401c1860401448110b69005280c0d03010750105020404030f480c0002500340d42c42915105d180890360403d400541101019450140141c00c0030304008149480b1600303422101030955400b03c810303981c2000880311071400101c020100c6040c007056030104003ca401c2a0754400aa860900072203035141c0c2031503901d02901c2c80c0e2004082c00101210013143d41200640000203e5201031281403600c4c01c1e800e11298082e50050119a40da0321082104001c900320b8a900418220360511404001e8032040812440050305e2444480a10200c1c00305180a141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 186954253 1250 186953003 186953009
    0x31b07050d120305060f0303030712060801020c0c030609160b030604200309011a0a09020f0d02040b0a1404031a06030a060c0c110d0c0b0a0c0f06020301061b0c0519 72
    0x102001c0360a450303140c41e405100464034402e0201c0e0502011072403030328000c1400d98540303030064000c504507a100030302201d05021903105581302d0f075980c110100d03541e01c00b030009048200140e0001c0c181d094898041c18038044004000001c42d41208031071845501014121804903500300c81d03040d0720381e00c90100207001400c80d100e00c191900c00c1c0d0b21081710003583c81d402079403013001c01c88020890100c0000c0c0020601e0700d00d600140e400703c00c40340103101e50445503010f00b043c40c00c1c0685043c1000c000d0407241c4126030040e00000007a050209a0121441d4131459001f041d0800b0303038846052030b14580c0d882d070300c0c040346895404840d1500d2000403600e4070b0401c5600c1d15150804010712542401160140422485400c283c40241e481950030b80c19040600d0364040b0150311040307500580340342c0a02c1e0407003a0021030004003000702c408140000301e40c1c410b42c44504036000c1d070001a96545000005001f01c11000c40c1101001c000300d00031000704a441c0d419000721507041e12050010144503125910414641e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 186955503 1250 186954253 186954259
    0x10030224041208160606080d0807082202090106080405120c10020724050a060611150415020c16091503020f060f0403080c19111507050118020120031b0705 68
    0x2580213001d01c85c142c2c00c0101266050740907140e040c02c800c88100c907502c01c2101c1070008200494007044154105102000103801c2d903ca59a1050256034000b5034441c10a902190000e07440300107100034820f041c40124140440900640d1501111058480d107175418a21049445039021450308140300c010114134210030150030030506080c0c2c425405c903000740000c0e504007880d2880c00d600491082e0240004091140d44140181018800d4221012184200610440e60600c0030403284d06500d1407070005e448810407040180040000400c500c4030340d6889640000b4240b42001c1c92505c00090740c07402982605e07010350b8001035030340611020455602c2080084144144001000000d0103030300c201030a41c5050103001d070f030246500ca00c0c12403800541d141c0080e02d250329414810040b440c5c010160f9181602c6940003500345015912918215800010701301400e5a0240c030500c11982e1000900741c0241c030200113581c10b580300001c01d070303500e000f4090540403110100c0301c100381c030503003c12008004140003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 186956753 1250 186955503 186955537
    0x50a020d022802030406080c0304050f060c070201030c05031e100b12060a060e03060703091104020c060411030607050a1b0b040f112205060f030610030224041208 71
    0x145000b4120303144a142404403a1007450070b00caa595201000711070885406503103511440d2a440701a800326800a04201c680b841022040b100709403080c0b0066109581450055444400900014050700c1c004a021f500f003000c1001007101000a40004132060071850000c1100d541c1d07030500010945a19030044c0040707400c08030351000b41a1075030a0307240c4981000d1b00c00c4503050b9138030001034801e070aa26268a52540000c0c00240c20903120342c0c025100303140110012100c61130614049012a4490000c0364020340085003088103120182000340c2e44e0072000c0e0014241ca18101000034018040d15149008108180a034001704501904d4820070b0707190440c00668050905140c894405c1450300d8041f81d034002c00150321829458150f0f10f00242d614818203a000c0d400341070206800414000705120352024070490321850981b0308101c0584642c07941a85c4902050441c01000100034807402d080c56a8011011000786080008060f1401c981d070040700301515007898030308030b80113000d0340d001003401901c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 186958003 1250 186956753 186956767
    0x170901090503100e010e0109081e0708030a0b27070e0621070f0201090803060607021914030c091b0f0c01050f01050a0909020306010b090a0302030f0109051e060109050a020d02 77
    0x3c1a403100e0811224403000b0030a44140e45000c90036a114010301030035403801444044941c0700c54412141e0390904500b405460090941d4680c0100d400035115035014030b07603c04846a003410407182d0070302010701200c205040c1c0202d41d2205005010000c00c45410803415011410702d070b844007400d9a041014101c1d180400720040807160710101c10440343c01001544414a0b1740301d00e030040c401c1209039074001c1c10042c61607641400b40006540700c00801c0ba00068480303280c1c84950f02d0700c00c5640c003070036407100d034441d484014404140c0340c40c140401280c030520307c010a1004981d0006200c0000e202241c40b2542c8401507840d03002102d02583c203851603d0b50902c0d04001000000810a9043c0c410440e20b04070b01c07039103540080084881c0450000c4d0582d00c94001405540741d10000f4049103240100032407415a02d0b503012a04090810f9070305141603440e00040800c00c1010b00480104d415400075213000c604c007041c52240da480044c89042816652100810010600d036011100d400e143c1c3c940955031406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 186959253 1250 186958003 186958033
    0x5070b01050625080d06150207030813031a06131104050f121b1305041e140703030210051e01180b04061203020105090102190302311e03170901090503 66
    0x4410601150745c0c0346480c40109101d11200c6802c6003029a03030707005020b81421aa50421158010728003000c040e0100c210000001d18902c0d005003c0e030b058203101044c10b00304a42402240d8101e0205041001c3c244480401102203030b07401d480c21200101c500351024030403003000c00d1901e4081c0c5402c816a0203680c5080e070718070080c094246600d92094406030195141041218219030b010343c1c004015200b0f00c0603646881c170844103100380d111b02546024440d64035003038a942c5002e00075401280960030030310341080801c0c0c05108480e84417070041061221a022048103800c2103034140a20500390320703072100d0141c9000b295440f001c0c0c800c0014008101d0700792120b20b41d02c01d0070030400b0101d00543c2004005020001d041c000d403a4055013084260000b141185002d41c040e42007058001d039821220042d0711310003841c40390010400c1030052120710596007014001a554030700e894080780b00151100041001400405c0064000d5100c0c1c8403864030f468000340121102291ba070b01c416414801e801160300031074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 186960503 1250 186959253 186959257
    0x5090a2a120b061c12110607090f09090b0610030b060301030b0121032010050a020403021206010602030f2101180c180509181006030b010605070b0105062508 69
    0x50007420b03840c10954922080100303208103e90300c40b00020b48070b010007000410200c001c01070013026080042c3c42503e15210701d86400340c1254041b0000b07101620070091f501140203104068190440144a07054040d15210641c0703402034020741c090741c02e01c0d10485600348668400c0e50f042100815540da2941c1d07034104000641c00c20b0254084600d059080c0544081000c0020880720754581c40702603010b03054243d10300d007024641459400324000c3c0007150102070a40d208241c41034041e20300042e100da00f0741c01404800c5c8800180041d403940054014040250004203403079601e0259502c1c0780e030390040d40b110428407500c0c441001c8144019800085044143c1361800901468950020800110590811070310700011860001d0b400c040b2440600990900e4421268403034155900300032031002c8904414545406e4003a20f0f104c9075a100010f208022640010318014903451402e03d0408105458140c040700c018071480303110381c100140c61081c131740c1d2a403e50f80480b0500019090341008a040c140c1c0c4076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 186961753 1250 186960503 186960539
    0x160c12080115050310091107060e0a03020c1509060702180403030f0b030a200a0f0806010305070905220c050d0812130b070c020d02130c030507020105090a2a 69
    0x103010b100002120794420301c1902d1285070b00b00e0032205040d01e4690a0340c001d14900f240e1100044c0f0400a001c0440c01c50b010795051032030705000800e462026401c0003030030000715000640c401c1401100a40b12340b40c0000550304a170b1811070760f07196902814800036039415110500468612004001c02042c1601039000407280c00c0b0a05003404800c503030504050302d49030b0700e00c1d0042c4070b07500b80d0445081500805802e810885000b50403d20702c2d0751200620b0564420302d5002c004150701550042c0100302d401c1c0080c50040505000501080c20040c4d00ba1320b90713060003001c0340c20703480400c1c00740c00c1804500200c40004003030180101d40001401d05080c12103903c00c200c0b100240b04c00102241840c0f0320300407540e5041d80c10111407241504c4001707044a00201550302660310010401c407480160b6540c03800e444245007135400000d00300440103800f80545030000e00c180300390b91510042100122010980c2c00000b58440350b9212203022019040f01c541e001d41d028000a4142d210011480702c0640b160410742c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 186963003 1250 186961753 186961769
    0x501020a090504060b0403031b0501020403140c01030506090c031b04060f02070b0702010804020607050106030b0f180610060c14070305070303110303040320010209131a0d0803160c120801 82
    0x1c807640394414030003620414801c01c40b48030020081000481c2c1300740070300c0b40c144102d0310390aa00111240c036810300b641c00c142c2050741c07034861003071200074100320820001404107428201804581b910400081c51500014000c4118900c0040042c01c84903550044101c040c10503a026a100c540b100782c001d299000c5421144050b21903c84003042d20800b17102a54036140c0e05946080032540e03030340c2c240040c41d00448000c85580d9201c0c13801100207820740300094407a52002c0c00c3d0a01902c0d218520305410394035640351070040e800040602c41c0c8000c0134116601a074410381018400c0318210f10744541c0486082c0d03900150360113030380e0303011080201c0890b801040704e01070b5a6030400b105a002c49213490348020348008000c103014003035a41d2401200340c5844a03044408000504140a80b004100b095500e2444182c50340e62380c1c144030700740030386469142c00b4003a4250b8840010b03c92a6440086a1102400003921001d01140c09001c15100d0711480300003e034400820030b45200c10400260079070100f8000c01038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 186964253 1250 186963003 186963017
    0x21020705030717060c0c07030606090c03050604020309120f0405091305070b0406050423100c061a0102060c0d0b0d0501140105060309030d090501271103030a0207030b070c0f0501020a 80
    0x281c901c200314000450409210f0207001c0a488004690445601816180c0301c28051148000082400c3c0d2007884000d224401001c00c202501440040440e03000400741c5108034814800d10181107c0001d071039038000c413401c00e003a035549413101c6001030a0007039a0006d5401629001045050741002402c00000c0b807040e1704403030f11940c03114005095401280244400181c0901c410020b022451203200000c11400d20070cc01844214404220840c043c3c142640100c1c007124814400c1220502c03500c040d901303251040d103196580c1100001d40b01c132406490ba108803040800d201511102e20360002d144540d0080000e402c01c0d4841c030308a4081d114003d030b0445060070302c4000041c207042c20030441788a84800400780d440c001c0da25000300c009160400d003e0b521507590385003019240c07440b443c0b9810400b803102c409012115642c0b4007501192807000c1400e0098000f40a8030300000d03000074030300044e20751040550a6a40e82d100707013100c05415002002c0d001500c144440e0042c00010340c000c105d4012140e817900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 186965503 1250 186964253 186964259
    0x60e060a060e0c0310090606050a0f08010b0702060c030405030109051b09010312030e01060509010b070b0901090209010302090a020f03101d01030b01181506081f05100309210207050307 81
    0x500300c1e1203900c510020402080d00140c0c100f60804029507201c040c0914820030304c0c0c0c03100c02d81411600c6540042c0041540058946503c6c2d420848402040c41c0a1522100d958141040d0700c1d99030190410080c01a6004950345290f504203000303880191801400030084050f1605199a960b19038100588602480c5240100d1030b080c40038907a8142c90f0488500c418141200404a004050304840084903550780d88021a49545059056001301006101143c50303801905048403141006414400d01340e1501e41d002c80103859584240c3d044940444400c1313840c0d40c8110311540a48291612201d20304c000004102141c090901010203960540120080d030b02c3c01401d000c40000401e02018200122150041040081507192814000b0300404003060f00240340b1a10444000c50340c00c540085802c003c200210000401000c51b10800c081070b920300a03525105c085580c0124100020041540310007580083c003c0d26816602da0840705508494040d070f5131600291035100302e000d85417107401400d40c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 186966753 1250 186965503 186965521
    0x3141e03030f1501050d0c110708011a04150306020409021c020a021e0a0c030b010305060f10050112111303140c0102100903180303090603050c0705100522060e06 71
    0xaa4420310b00d480340c0e1034003601d0ba0210400a040f80d114100e0402108200d600e283c10700d0fa0051101d40da00640b1082003a500400006003084c1250304600c0680e8940303201c280b101401c10074160500c580607600041c2c1c4103607611003004454007541014000070300015000030019981d500902c40000081e50b0700e80980031400d0424181c0c13003078103500f00050b031040c00c3c180e10b0ba85001759071010040484007151144c0d11039580e1181010156803060b1070b5200c05000400500400380b056641c880460b2002a080d403400064640e484c0e02035008880c100710880405001b0014141c0c0402002a102094113848910130156400c0c003070054002120b10350943d20303004078810000662580c0841058000e01002c00c44d14210600034503140000390300300554840d00085046c0b1034101000698040d581c1c1106c604c1c2841400b03001d030b950242010345010000c001e00c80200d00003140d145144e0001080c00b043c50348911101d03012032001a43c000100380c201c41620010420701da406000040083c0c2d060360007a45d100014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 186968003 1250 186966753 186966757
    0xf040b0c060603010b1f0e030c0a060e1008070917100e010f0f0c050f0310030602030c03090f0d0f030c030e030a0905010e09090a0305070f0813060e0a060e060a050403141e03 76
    0xc0e480301d06e80842801c2c40840c01001c0030401c01101804a840164951002138011201544114081200e100580c241d07804c00b00a43c03c5038010b1402d00c013a15040219006064402c1480323016103c1ea58841003880c1680203209803040e5001c82d03182403040d40c04126489009106120450300000e1814151400c05a1140030300c1c0c01c0d0302030949865040c1003800c2104002d540c402003204072101d0641001000294085c4040c500400140300d0cc3c54591422983d21403400030700e882590700c141c3c444454001c1c1954070070860145131220385000f08000c2c0459000340c01408002007403100d20b010204d070201c6800d82c040c40e402c3c100c9800b45c1e54132603a503041e00c06109031034500369040c0100b03811040603c000710f4001c80003081031a11803820300b07801c445603440e000d80c00d4000b2a107142014000702000c0000c075500154039000103030101d5819040714586500602100c43c0c0c468401e000d4034003c03c4172000300d1b00520944008542118001d00945c14507502d0790348a2040000c00380300c03400c468188100203800082 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 186969253 1250 186968003 186968029
    0x70206010e0610020a05010f0b130b0d03030207060b0a03050313050603010b0904050613051e0f100329010803120916030201081003060e0114060111120f040b0c060603010b 75
    0x500141282c40d801c0500408101650200007544144001940000e80c00d200e00e8560320440d4100140040700c1e42c0c01c02800f807040c0c842c4902c0c12410280d225859998180c640a83c0c2a490700300103a441c0d00d1403134a0006007050550055100301c00000020501c0800320050088486084c42c550003151a6010045603000c01c2c0181c0c0420001404284600e040c5503000c103800100c001c2c0301120b240403078100784003640d00807901002190307646005a040113465200b42a00940041b1802c0440d240c61031500c0200001c62001904944c0da00d00c5a1034092028000420760400c1814092100e603160002039980f82e03c0590641f003181c00020024002507008100e0040004414520710344c070601d0b503001100d00d030318040d1072058500ca4081c00000081c103140b10341c0044d49090000402d5070356800c4a03a80181000811441c10f00006c0b00c004030400d40c001ca520f000d2910070b41c90880d194800505240428000c9400905450703000044012043c500003500d54404c031000c80090015034140e0090090600c1c7e42c1c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 186970503 1250 186969253 186969269
    0xf05060109080c0d030918020a091406070f020109090c030203060f0306010302030601060f030f0f0e0c04151a0f13170d091215150302090a0b06040512030c0109031707020601 76
    0x4107060b8140b806400003c6002d00070711b0060300042d22000380b03c40d00301c0c0251203442001d5001801600c03140d0450580341c02890f8407243c402c4121f45520100c0d0843c80f41d0a0010040c1e12a650b0385821a03000c2d0412030f003d4082e4035410000e103041454068003e510a07a00c0ca48529850986400c652600007046810b0760750103000341ca600d07446c00070150f82d14803c6030254000d05440d003e205000c6069031144aa101c22442404906500301c0268a4203148140c41c4443c0503504001240900c0d1684000050441c1c4262040030740f4071500780c5a49490740101c0240c0290500001815050310740900c0448042e59900d1000021040c000125a50b623140301d0320821009ca20900810004450010248040741e4040c0004580131082c0240c80300485201c0c5410b0307480b0440d092818015400e2460180c0d5011400c214100640c0d0f1003000020302c0c6000b20b10800340b00e0501140d908408120034805d840c02048a02e0091104030307840d10340a0306003918044a944540100b20000d00490301c00103100d4121001c030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 186971753 1250 186970503 186970513
    0x90209130b010f080702240a150503190f0c0803041703091e030a0f06050907050a0e060607030c050615040c05091807050c06130c0602060408030f190e010f0506010908 73
    0x503100343d6184e4001400c00081d4081c1050041801d807441011005010002c0280901450320504450032190760f107808800030070710400c090010352400502c40c00d4a1400101c6e07902d10780203506c0c00b07030701c25585003100900c4500441c10000e5203c0001018100b541e68181813083c0000c1161240ca5803400f9890a159100d1001c0c1c0c4000d1241011340b0744490b034250042c047d5000302413035840c0c44103018140304007194180d982c0d0040000560040c000c2c2c40240a049a15042e0145000c3d020b14058002804017442b035000002c0480030036006507411004243d006040d0f8905141c4500380100c415034041220380030f0360403e200c4501070361160781200c02880e1700910f405a06012107460740b030100c200034010014843c0c10014045400010000544119051511101e0241680c6030080003000079900240543d80808240710004026000f42da5104110b0071a074145981c8500c0c91a8070740041001800c4101c1c034101e0340c070b01d201e141034100c10418041d038034007801030782c98020044800070020312461481d0703004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 186973003 1250 186971753 186971777
    0x30c030515150d0c05030118030e2e030b030708010903090e011d090c1c120503010305030d1a13050411100f1b060e0d0207090212060111100204090209130b01 69
    0x10883c1c0d152640200d034000c421680701d1010908603000300c01030114128020780400105940a03c80300b003c20020b40b4980c0b4000080c1402c55000c200520701e07240d03d00d02d500e40081000384070f07600c0500c00100007001c840c42140d4402c0000d000704107450083d00094503142001c03601e4045540501d04031307442109030081900d051210207000030f102030030162442c054040e02d913800ba5070700010080001244201c20900d10060314040480d002150002000c0c8402480100007042c3d021041e00c81c40110603501062101e440d0725004000c4007080705541d4401c0701100d407a0ba81400650001307220b01e22881442d2100d200c600c2c20007000080241d0003800007000540800c426034461114100c00c0c141c0c0c12031001d1040d5071980c1c0c050079510447c00c042d0065001150b50400c40d50304000d02c0f8001c010543c8114134081403a40d101007030110091403181400b100010100a00804000c0d4626011013140110744541d01c560041c00a03500c40704185200f450045040010110103204001e80054142c44e4a00c1280b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 186974253 1250 186973003 186973009
    0xa170309070306020c010c120504030503060111210a110f0303010909020604210308070507020a050d080c1c091d01090b030a0506090c1201050f0a05100906030c03051515 74
    0x40014005a041e0180703490010000344140080e080100d540000030841d2074060790001e00c0380d0b540d00e08e8800341c0341c00e060501010039044002c40e60401028a1304040181c040c50003146040100d030500c0090381009030403900b050b14140094030302038902c0d540b854a82c4001a03001e55880005c50400011070700100300401c00c22425a1000e40e42c2440038048a05180d0340310b11540b502104c002042c0030310410381d1054420580d100e008030340d021840f0b041c41828001c0b0390700411501001401402d005030220844002880f0b41401598840b044442c211250031005152040051007000604804140c80c0200498520b180d034003090100030010801d80311903172a00a501d8041c0800780003070390301809040e00400214500344a00c83c818503043d0010800208500107008941e0a5280c04d1100c0364940414401c941000340e2000340c20840c6000041426214500c0340440c0d05410b5001d100c2840c40e0905c00000c002260402030120b03409601903485c4506906d00e50300e191a070407155a00708440300d005400143c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 186975503 1250 186974253 186974257
    0x80a020c2e03020a0306081603030801170d0806010c0503072004270201090e0a05011a04060f0804051c0c020306070206012106110d0e0705060c0c0402030901140408030a0506030a17 79
    0x400c4d81c607005c1209030f034544400c0e060071050300340307416184194442481415001140c05004103020702804441d803504000154950b01d40c0c0089800f04443d16001c07942c243c0c0700d02e0781030440d0381e00f007020741c0c3c0d60303030340910f0003126400108202a90f03600035507229030301c6450940705401c0055070b4080403031491043c0542000c110034160304101d0500007a040d000c00c136921601c25161180180b0240016194146210304101d4684030004c0550180c04200034000160f00c121000303604103660500500b541c849241540c10301c2e03068002c0e10055038400680d01c7e00b8071791040c401d6004074001c0c2d0940712541c5401204903104c03902409090816107030740c131059048120001c040c6030b001780908400035100c0c80902580b48180d000300d110107191a03c0d410220103000782401098010704044641501d8209170303039080c944601c42d07404014402c3e0783c040000384600d0303001e400c2030404081d801c035900040d180501d0451416003040c1c40d43c021007443c03e0300140a0781000203108443d160005218107160a0700354002a1507 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 186976753 1250 186975503 186975517
    0x4106030a030e0315010608240604091a120d170f130302100609060503100902090c090301020d1404050709050403051204050c040603350421080a020c2e0302 68
    0x1071003155007010200503030500c40740c042e186c150740f0840e450600000c900240320341d80700d01e401602a0064a04141c3c2d486908a400302c42c040f020100c0e0041b00503950403441141807510607080007290342ca0000c04500400d0191000009407100c0c00e0700359402d4502c1c41814400c0b15030b03c480c00600710106940031454071114007514400ccc4101d4070030b420007100010590309180d00c2050703081e480b0344003030116180500c00080c0d003e210071010082001550002000c409001d030803040700030b0780010101d80035202901110301440241e402840480144880300c10300110840e001d03a610300940360080b03108600c40c015140030f00d8050b41c03441d00304401003c6150039188060801c0310749100c0c90071001c000d5103c0b070181c1001140280201c8803c107031070f072110345011800d9010aa0f4950310111004502000200c00d40f41a80c122556403c0d0321b001020741310024002204015190240c0410310385007003a4000303040603503c00d0a03038907207101509411512505482c0d0b00380e032041030884060f0040001f03210b54007078215 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 186978003 1250 186976753 186976759
    0x80d09080f04030506010302101d040b010c1b030b010b0705070306150504050f04060606111b010c021c060c1412090c1003090c050303041802030402044106030a030e 72
    0x38041c080d80a03212958456403044603550000307001041036260020590700d01e6411403c1c48040c070204550702002131603d11200c0c500c01c42d81c61500c0d842c180d1091081800c0c0580c088000c002c56600f01c04503a03841c00c1a88011141e07404c13000d001041c10750b003410035201140d90080040c4441e5003560b40f0440602051a1035844000e170f078001c00200c0f907640d07004071801007009650041c014201420100c09a881c140c000d4014806a002c20291038030740000c0f40702441e0b0203940620801c00c58080101c4030b03580d44120195105400c4450417541041c04c0c006c3c003491911803c810001140000401c1c0c80855800400d11010340052025480c03d503c0c41c040380794024402001d4490584070f45001512907000c41c030803100020f03a500702d28000c12212049020160400310021420b152800104100421806030b840041c5600030011400b107480e683c001035040c1c0d0014856481c00400c10201142d2148034400c11404030b02105851102100c100341542e0080d400174000e0172800080341c0301580d030810351500e82a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 186979253 1250 186978003 186978007
    0x612110a1403060f101d010e030a030809070b0c06010f060801030c090f060b03010b0d05060a0b0304083702190309050f13020f09030f06010b1e0702040f020301060210050103080d0908 80
    0x510b6a1004580e44010071759444140c4501014620321100b40c3e60fa5089a0501400106a1000ea0780000310065141d034540b80c042011790710391214a04022180d070110402d9400420101080c91001c03440d81d06030744040f5900035400d03550f20400c90701d451081c440a0031180b2003840500c04141d0f2900140903150510b03e000c110a030303803041d00802540c426844141e5400000c00c50780940e040c3c0c1c1c020300340c11160454a20134071906012102429200240c00180104000a00f1692480200407921204005003090801c04003030b031031110a2403407442c031402e0014068644140724411a0304c10030710809406540f002811410281442154030088848641c04411000300c0450240d4600040082050145010352600b2840e0245464200740c190f902c81c003074000c0401401040b5201041e075000e5905040414007603c0707064900e0f6410b00c40c8800117904903003082510100a0717150b800031410ac1d14103170708841c2e60019250580e03044500a00000308606c200b00a490400c002a82080c414140201001e1f4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 186980503 1250 186979253 186979279
    0x7050109020307080607030f0b151b0106061701150c02040c050f0715060f080c09040f0506040506011403070b090f0406050607050a0b0a05070206070c0c0503070612110a140306 77
    0xa0310b0a12a51310181c100c5e4044d004004845030326020b402540480045c1c140480d06440c2c002860b030301210383c038640300380e2004a00b03000800300070410540b0695690707000300051502c600d030040c00141c0c2c08218a10003441c8038000030b030324642e10313100c10380c20416a80d40c29030991841d82040040e224010200003081801d00c0321401c00980c01d00207103907883c4903640c0b42c600e02101000c18426201c1343e500c812241030500c0e808000c2e5000101d52049401011a0340c0b40e0143c3e140d243c03d258490240f0030103851440752504000410600291890685140d1010801c146516504241c1d48104038080c01403011818040c0d0b80603410000c0c000814194000d2011a506072a203000c034880f0b800002c0d040c6c0c0e40b80c0c400d81035441440120100d8541040c8092024041c07450320f00e40181d5210005400101040088603a1809120b20390701d0942c0503103c0201511203c03581c41c0c07001000d41904600041015180050703c03d604005141120072101c826180da9000e8161290644c2090304001c16081c0c010315481594 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 186981753 1250 186980503 186980509
    0x501050c090f092701290310050903070804030803040302060105100f1d032d030a0507080a02072103140301082505060703030e010b01110613080c030a0207181b050705010902 76
    0x5250340e08085000044540d11451200029800e044040400110340301a00c6c00f1624003003070583c00713018400d030003280381d8035544022880d504ca0040f01500c2208082004030070800c00e0001580503602a60807070f00d560340c031082003042a0452030ba112010070040d0713084407071490044548014952041e61904519900c00d40440c2c14a600d00403170311181d441d81503040c004108004c00c000032101500f8002c6003003190300103000d4800d20072000060030386000810b24154991081203158041e0070000000c50444001000c04c148007451010100d006c81d0740b0721080c5e64100c0e21201600d048510f800c00400b41103036540d580c5074000b220700d0f80c03400818500517008102601c030074008062680c800e54000582c90081e0440d9401c4883d456203036070400402043d10004d002c80001d9458100e01c0d40c0803184110981407403c0030302c1e4814215134070903c0c080450715111194010034840215030200c411004e400428014620840381e104000e01c14000801076180c1d0031030301c14006008100e01c40d50001400e00c0d419000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 186983003 1250 186981753 186981811
    0xa0902010e0339060301050d020310060e16030917091c0302031201090c1205060a050d110405010608070c06091e050f07080a020319061b0c0501050c090f09 68
    0x29030407081448043c00e5a001c0100382112004107400f40e40c0410340e03240b0001e0414817044c840c051103401004020000d5560a210303482c01200403020402600303980f00c0740c2c1345003d0000c403078038802c034544101c11804044c000e01030780d01c02590181d2401c2c00c2c4c981d2000301b12926008105110b070401d038501c81d0341000f08296074110300551301a400558445146d1b402a4581c610140c100383c100508112000120540004800040407034121010170b20756078400c04178080040326400650b00000124140003841000904561500b40580741840356a0321140280c1c3c1d00303c000d581090001d00340000100220318264007902002d807180700d40c0303a00303640e50504104100b0140c41056680341c0249034400a50071080220100800c84440501248805900040e80359031902c0040b0000b880300315a139104010b410b5000d507141c1003892089402c0200c03068401130480e01310380402c40f0b10303610300004141c100c014002904d85030040144184801011041070245811016004d40c03204400007e510f0908004000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 186984253 1250 186983003 186983023
    0x2130b06030112050714180a02131205010605010c030c0b07050f0a05090f120706180503070f030501050c04030c0501030f090b1e010f03030e10020f011509150803030a0902010e03 78
    0x401481800c1d00c3d4101031341410403a5110044044910444040c0d50305e40301d03000d80e41c02440340041100c1e540c541d06044d001e031141c000890240000c0d01400300b000101c40c01c1d17012103580150000c2040e00d031244019640a0707403500300a408100540600da00058424214660142c4180362040c01e02510401c10001604040c00340c101080c400304040b0705c207041404080120207021503a110841b03100071806030703c68205006140c100403290a030f42042a1001c000c10380242405800c41c0d050316501e0411017401021400200c0700c80d420007001c5503034410140c040d42d0036250440400c0c2900c40ca040015402404440c1034420384548441c4210080340204401c240720707103440c40c12580044481203131000350500580013150b01100c0d01800f031001c640d2049024406d08000d82d50fa0302c4280c01d1144c1640780454441c00c0014640c00c152400742a0403004102c1000c642100ba81030200544006040b458000d40d03020325041c6500c113200041848100d03400600c8003c1c01030520a07064032031500401e040900000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 186985503 1250 186984253 186984269
    0xc0303010b0a0318061e2a031b0c12030515060c01150806010f08120315060c030403050102040608090109050a12050d050901140708040b0403140c0316050d030209090402130b060301 79
    0x184105000c411103101030906c40303c00801c03040c8403203d81c210240b20003c001c800107080d142100c14001c0d020307a00c90070360f21070840710140e076403d68480000d106504008084410310030510b0600806402030060b075004000304220f03909030039541001d00000350031a020340c4081d5900c078080c51900000c444507500243c1070040181089604001c4111000c00c11540144510790010300c80754400d0036040240d90300140001041c800b40700552000460a002e0005508540e000c00100002000b00542c002d0044880c035031108071455550888150880e090103801070304070342000321103070001540c0904903180682207081c0329041c004110008011240c0888a1241d160341d142102605840803800c8103070300c46207a10f00366140c0c0c9010703500c00700e011f00d000c1d2008061081885070400b00f03186807010380c1d40003003210044907102c03070040640c40d040d0040718005484501030f50b0710202d01c25110740200d0b0352052010b04103001c039032290340c240300c0d840c5001c00e01003004540c1c84a003100c031b40e034a110003140205054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 186986753 1250 186985503 186985511
    0x10b0a141b0105060303160809030c1807080c090d0b0903130e090106050f03280b040b060a090e071802131220010e060d090204110a140c0303010b0a031806 68
    0x10079821500d002d8480392180e03005004c42e0580004840c1c0c0c91903200c3c0d0044e861900d45503018003191030020106003082e4020342e003100f20240e50300c00104030b610642e0b050783c54546c2a201d840886945104946001d50410b11009101c004103201004103a008521034003105e191402c0803035001020308158002040c0c1d449000148910300c2c109010b401d01604044400e0030f141100e810001c0d546040c00329034420688000d056030f01c0c0c552546000202e08542004140015103498078282e07111150480d9140e2062404080c02b00340d020240c0314004151440c83c0c01003821900b441007241200d042c3c0e5039400785e0740c1d80801042c441420300401ca0401401c502c001c10420014a141c100035006115106481010010180810680e400300308400b4510040e11650354460b8a18020700280c0280c40010350070604040703060011103104402043c607600c85d80c0e200c425503990b5100d401d107540300760395044030503600a00040c030502e2403070801051065901d01300010000103d1640c2c0d00c0d40d80084d1001c1d5a03583d27032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 186988003 1250 186986753 186986797
    0x3040209070207212a0501080403020a06090c0e150604170a08070507060f1d09181e160312181a0a0f1e05090d08030f040c050a030b010b0a14 62
    0x100307800c0c0e0203001001142d50032004040c030056150170b20309206450400c070f035510100d021301d8024001d0451098000c0d0042c001724a1504182043e0b0300340b1300c00d103144155480001865500303900b0031002c6000f030045c000740c6414644a8203800086007032001d010303140628000c00d80040c52400003040f0540c4174a0180c500d09180000c040c2071845400c2004041c00f111a5550460b08010603400f60150350072200030315192a200b002e00c046101d0811804550311a050b240101c11034100446413104884000300e4165a514015482d480e80325440010310310001c40c240e10030000e000322160a0300d4001144911080da64a02e442d20b4a0132800c0043d840c41d15001900c441655031103404403140d180309003070821203007481402c03203400c5168280020042000c040b41e01d121030790301d000b01c43d8405500b1850090b101c1c20140c20107101e0943c191001c0b100c0160170500042d0500304405800d08607904450603514a1386080035070482c550151116500304031842514500300c6418a000d00f140c8100c40301d0101000703071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 186989253 1250 186988003 186988013
    0xf0e0105190510030f030525030c050c040b0a0509040809030a0c03020109050909100f0e01060f14030705091b0702150d0e1c050702060d0c111902060304020907020721 73
    0x240190a084064034a04824400b049040c244d4031105c41d41454540c4ea1a101080d10313480c420300c2805840d03816407155074003400b855881000c11002d01c6c02034065904900842c003c202c1114801d040e60b60700076402c220200924600500d100b0740c0075000b03c000134680502d00000a0030014046402c841a8003108414010341d42c1c05000f8902070001a00c10f480c140c200443c0f440c0d0741c0d5122050389100191240e80344048030029801c40781d00c420000d4001d0113030360388a4030725050070880e40c000c046007080c005900b001c2d103207000282c00c0b04640000c2c1210115403100c9071041805c110100042c2e01c00b03842088407800580301d100c0040007d943c82000703030b6280d030700043c1803605a480c03400414185511101c1102c0150b51072499078541c1035024145540c1d2424036201013801d50040c2e00707010101624144107191421b0f048222014180350001c1902d10102c912110081c3c05407201d10065003240c024000200107041c404059900701106004580c072840d5120000214210640c0d20941d944140060400401c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 186990503 1250 186989253 186989261
    0x601060813030c060b01020703021917030f0a08070e03070611150906010b070c09020d0504121803020603180d031b020a12030c170901021801030c120f0e010519 70
    0x8009005010004559480c020700302c004850001c1d00c1c80da55100c0b0170440e0b030700801903880203650140550002c40c1c40202c00703072082641442040c5040b5080d1042c8525501301108445c07101c4070340346d0f40e903041107400382d0708864001c0010211814060000d1004880b41c0d42001004c1c0201055034488890f0b500f24610742e4100124140030b09582a80402880030002001c9500c90540d00c800010540311000d1741001d013110441b0740d0000103e1307440051824150402c0d0b4101500c201d005444401754044610401c9410b00c0f01c0f515041465007802c0740600041c50904001c58002649800c0d0460150380c0910b15400c0002d0020b4200110b65101c0303d0f150b03480868001d0000000c500c0c005042c40b001c060310740303084058400c513840003050756030703500741c05180d000d0504a154000c0c014542c010a20f001c0401a0003903006445032003004041507450b6a4540c4607005d1030704992810717610500b1561301f480d16100581a03c4060000003a10b5414003500040e0034401c040c8030f801c640100380d00039210b80e40c42c60122 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 186991753 1250 186990503 186990511
    0x30d0501031e11010e03100f0c080f042111010e0a1106040b0414030a050a14071a07062031150f021203010305060f0c04060c0b04050a1406010608 64
    0x2001c002c8850b0b0012842640c0030680c91042030803c0340304c1c18a40c00000e401c144222442c024114070340300c4c101440603070aa0144011101c591504501510350b007004c1c50b00d61104440007006400d01d90700c4800c11218000f00300e600c410940c2440f028054035148403c0c01e40e10784c201038207031982c820040351082c000b10881c001c03041c0d503060324007030314003810120200c20303503c101e003e26156241c0c0c000f468401e03501e040081461041c0c2060136640300c03075541e14145010300c40210740d40b2034174400c0d10f80205003031a03180700c1904d549110701540d0307140451036a2070307802612400070b02d0001861007401040c0f642c5a0f14006000d40d910580c0340d60401d11005800030141e111050420f090005946810b1000d88807100c41c8000c060000c0c1030000c0392001250049141071031501e0443c0070824044000401c000300082c0c45401b0340c0b6012000c01c103955650403014918000d03881000d002030081c04400001c142d021030b09030b4220b0301607802d4601c16802034451001c0e04051031075001155201100402019500807851500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 186993003 1250 186991753 186991793
    0xa0510020703060908041509080f0102040e0402010804020111060c1c060303023708090418020f01050703030b030304120c080a020607020f03010b04090804050a0b070b160908030d050103 81
    0x15295000399a5100c0b03010040807207a0b144080c00a200e040010f90300103206044002015110007000101400c101d4482d02085100c0c1c0094080d1181c011b009440a59000341c00720349040c2e82e2030300110f52110002c3c0040c2c0c14400e4169a19804c0c1c9014803219110b101c0c10424a581d442c24241401c1c0c05c440d40b07589441003140340290910020b580400c1443d0556030700907042104042000119804540130420400983c250241b05400c0064404c080d0030104400c0701d0401100c1e80503d50b02c00301401803a8003d61040780d44011406541c0101d007c1c004040c0a0b00e00050000001c0c804a403450740907420611b440382d0107001620402c02d03d0041003002d0480765003d049888156400700346203000c1c82000910503e0408400d250383e49003580040c03144031005000303000381011818201d0722a40240512809210500c4003c202d0481403000c807060b0f664861454501907813001d861801c403448181d021020800300c9040020a204104007504c002c00f400e0b80009815451840c10b82e084429101c01420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 186994253 1250 186993003 186993019
    0x602030301080d0309051f060f08061005060c07120b09010c051c091a07030605130c05030f04062c1b0f040f060f0902120a090f030c020105090d0b060a05 67
    0x801e5010a1003c0000b502e03003400324402505151031410601c0603c1c10804510440c034010800c0001d5410030422100d0050703414442c00d4580e4a071350340302d6070200c604032640c005420003080700e400d00a008001e00c0080d1815101070070345459580d4040345421105440205c0d504042c0a040032007031107002e10003203050410500d0100c12a0210711009400949120803da4400068060010402040d40d070a01003c10402c05444c0c80030000d4020400c034011a401402210000000c10445200e84013143c981601c600f42940d4400444000c40d04005004498442e198114900e03080c091855001d0b0210f1007003100c2d031016182c040c225141c5540e1140040003600d001c00002626160f005400e0341100003036a000c9083d01900050601501c4598082a0110100b8000080c80c1d030704e55000e400030020302070b4600e4458641d20f01441c255031207079002401c0701e06180302410009004100707240a40b072040c1021400e01100c40005003d2800b4181300b5607030b0405074020040f440c81d001380140e0142030101d13001c3d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 186995503 1250 186994253 186994259
    0x12010e061801120503040e010902030702010e07060504050f0d06020f0703020c010201050f041b080615010306050a0608010b070c081b210304090e0304091a01021203010513020715051503070602030301 87
    0x82603800701845403203684040400c210341406030600c1120090510b41010400c5540d450910800030350044a00b40011352038002011802d0801060308022202e2964480c1e003818281001c00c07112a08041c145684490105038100000d40703940094010304680c0b41e80d0039212009401e010f418608184240d5045900d07000400c010118407c0001e900190084401610240c0c16140102e41a015030000c80e500e201e0081000f204600c10142003480d0384080c0d03010311945907a0300a004140015021f01c01c003161450006101000c13031ba03406850100d00810030181c141e036880003940d00b002200e10320401d1484000071080002c2c00c0111900c0480020800a40100c0a40c440c40944a00543c00b0b41c03460305841c0d2142007088081041900c015000600c070800030701c42c07011f020040a000800c10700780940140e150600941145000f42d0f812254050302c1d403c10300d150307008040000e611110040301c85900415045510300c00a1041521450039a5284054402c2403810549412150340c070100842d0300800043c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 186996753 1250 186995503 186995539
    0x9010b030601060813050105100f14211f0f0608060411010513051203030f06012105070318050c0f04090804150c080a0203120c040b07150204090212010e06 68
    0x1150444409113401c40164031940c411030007a400112020b0842d60a103000c0c001c1000c40721b0051000c94101c0c0c8850030400d42e880c07818041c00c204201e00240d208450001c2da900701c184092082d9a60307410791090f192100f007011400d40e411200001da012140e0f550300c1c03031141d0303e4016104030b030085c1100a005010920b8207980c4c0e00011190903a24504200001c0b038074103a03403900f00c1101405400020090b486a55032041d0346540c0390011030b4110040344a00d000304025500a0490001030304d82540458100f0201000441c05020050030100402d5901c50622011429a50202050520403409000c405030310004000c00006480d640b10720851405030705000240c145000c880481d0318520092032002400c40090781d984820141c0a81460400528030107010b40c040001c298280d00c0d002c0c0032020761144100320b0494015406101010701d01000000f001c0340041e2215510084a0708015181545650703222060360824120391400e00d144c9001405151880c1d520180d01c50b02c02ea03142c00c641c002003011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 186998003 1250 186996753 186996763
    0x1203031f090207051902130606030218010f0906230705251809050703140f01050c0703050a0e22020705060c160b09120412110a0303050a110a060603081209010b03 71
    0x2040c0780c05d600041400454031006d610180f040301c5031400300030559507404090080d60003120503442288440c41c19280c99801403103890b21382001035a80050090400078103850644207846400d5004400e84502c510181d06030303000742440d40c465005400f0400b0411405540d000b11140c0c46044400c01302010b102110010a00d00d600908904021074034046a042c00350414207650070280c080b04501507030803038213840011000e0300d81c1e4002000300900c4c2c2e40d151425041e4040c0700f1004000880400c0640c0700140302d005656000350000740507124513004e80d581030000070150100151019004140301080c0002800126031020808400c28607019021260400e90718101d0802407400c031103000400c1505100b00110300401e04034004460340c65490308403031110f50749240c908580301c000c403404e21440c60074048550700c1104c0c5d00d0345945081c140c06181c2515028610301d034091303842c0309014590000c90201d0240100450240c0c0c0040c0c0c0e1140220b0110003610801061200070b6030508460304000e407000a9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 186999253 1250 186998003 186998023
    0x1b2c09130f050105010b040f140d12031409070602010b0616020904030525021e0a090b1207030606171513060e03030f06040b040905120304021203031f09020705 70
    0x44403803a6000500d03100e5040166050302502540c039100011440341100b0f001401a1341001300c0414516aa5010712600459240c14043c1c00859082c1c80c1000135481c0f0107510400c1c0150f003004074800c14441c4c03420740c0c145009c440d00c1c08c1907440300a040203071035020f1007105040c0744d096031220300e4420b00ea81821070008007503c00038010036414000a0916206001340c58106e00000d00020842d50504101c0440d04e0841c80d050b0f2048403030440b4416481d100c201100301481c80034103003005151410071080001e04514031490b4010b0051031070000c0022040c4000b00280d841120000b50b030354200140203c924180521a04081c1d00640035045141c102c5408103a004809a01405400c1301902c0c0c00800307040b04501c0811030380300c0032043c060b050a41107400ea20900e0700340c5080203210800c00030030003500c914210151140d0031141c07080403a0801200159880340c009401c119002d440301d09618038641c021a08500c2d2030050303400c3d0401c2c8825a654a030000d002c0b101095003007104e140c507900d40f11a0703401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 187000503 1250 186999253 186999271
    0x302060a0b030d02300711010207060305011202040b060d0f060e06090702060f06010c0c0b0a02210f160c030f15091515030618140a0b070809011b2c09 66
    0x1200321180910514003200340d194240030000e07120051403401003061f1805407a00f5015014a0b807003c201503109204960482e541001020b016100c1902800000d048400116820001c20443c07105024242d0052103c52900000000f90003071410302c0602c0c2c050307805030405100765003000a22105990000f90a40c01841482800349070741c407040010b0303440e110440700060254042c20400581600c04070050054050307241c094911586242d401a5603a400c030101c6203050540a0144040d11558080034117820108183c4400b52007419407102c47c00c4500590013250724801d002001810040403a041c0c07480c01c040031805000300c0c0d071560748013040c460046180700c0401e40d0b07034800800d501e42c0100c4000001c50300403000300010410361086080e90881c1d980296410b507d800c0005224000000d0f084e100356070090309990603500c400d401118010300c0546804c220750348400244000c0c25811410070392035052616002000300c48008041217640c03a1940f40140785403000b10b40062525560f0701607610003021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 187001753 1250 187000503 187000543
    0x8150402012c0901060503160915031a090901020405030f0f0d030b03160305030c010b0d02090708130c0605041815030813030b010f031103030f1e0d090302060a0b030d02 74
    0xb2040e10708065141e030381980200c4042c000604c0540260085002d840ca1064003049140c40200642d8071542c00d105141c0e02a20240791020418860303030081d0ba081741004080904e08902d400001c1c4141c10036506028941d6000a0400c003a141c1008003541c00710940e00a041044503035580c3d40e846080d0070610303905041c1c441a07505847d903401c3c03243c0c994601c010101e400d00e0366180d007410f90381d17500f241c2d180501e20340c601603240d2118501019000c800c554020101f02c500e80c0c6021089400c1300010300b05215110030704074441c000a00c1000c451026162560380c031615540342104c1a800014140c0e00c031401c803454108450740140d082040d44084d20b4110316090f9907118005885010114580e00180449100c20000300d000d1400410000850340a60f6904400051034400c041d00ca1150646c40d0151030070420100b10a180c02103122101c13540b98595190402401e903180000762a00358400320016080b4408104e1a02214400d03c400c05000b81c00400000d40800c801a5540b40101d00700c082c90079003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 187003003 1250 187001753 187001807
    0x70f1d0403140a0f09051c12031508210403020f1020060f010e0106021902011211091302030903040303030b060c01060b0a08010b03070504030303090515010f0815040201 74
    0x640b2141450040400300241d44801000c0b0041040d00504c003030800007014141e0025080c60b1681128802d00818031119814800c41c0d51042503d03916800c1c803400341502c0d41c0c48200041000b0064400a1081d040034041500500000005c00081021280b01c8140c0902080c1f008d41c5602242078500031040d136a8424003010b50405460880c1c0126034002103110b0342d41040314480b00420f5941c09484c0a0020f15070590729044040720349002402034400692020081c024000b401e1295034111034018100444184680c203003400036640200f004421543d000500080c80b41450043c0c1c1c0032040c0c9080086055082100680791640314512001d01015140d003078550703080da00e1500702c81300c561981c00208507060b59540010069004040300401041f01e0900008420104004884c86480e02d65103203407804e403c0d59030507001442144400d4030144510380f045400c005050b40444c0c00380c480103418401c414500745685186c80101c0003900541d14044c0f050000607600007030300201c03418082c4004114211 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 187004253 1250 187003003 187003007
    0x1d060406031502120603010921050d0227010201090b0c0f12070309120e010c021314073603030516050604150c170619050a1502070f1d0403 61
    0x2030150000340c030441c5a00811140800310b03500419090308004100c21107992607800301400c0380c440d0103001e00b4008040070300b40c001c9820f60140c08001220750030312606101c2d0302e40d0f90b18103e80140000c03200c40ca0705441c040a03840480d60310024000320900c0280b0102c411950f40514654020f0304c45504114042048403071844481c0688a00c801000307066202ea191405005001e000c3d10070085d0346000803a0b0030b01000c24407031001c0201c1054182c43d216075006490b424407200c020880506824191b0b80c007000b03c402c2e0f0380240b030039015942031703600c10440c00760285c20380c4404404c51001c0b0381e48a21104460b6800c9426000d0041100e415007003190316040b8406080107102e11080c0001c0450060030100000c10803455866940d071b51143e102004040c55581c03040d900903110700c0301d51440c80d0042002030b000d8a0700c144c42070840010044200c2081d607481c00407d0202d1400e030002c60b500c041e84841815010b5040103104003c0011003120751050345005440c1e0500c6820b40c0100550024000001e81894 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 187005503 1250 187004253 187004261
    0x150604090f0b0f01060c08090603060117041b06180e091507080106081005090a050604020d060b0d0e030f1603020309100309020f03060702030901031d0a051005070503011d0604 77
    0x50304890620754410251512500c2030b03404562101075606040300115403e03100e20684500254408200352804810400b0044a078000034005070412008985041070145116100e5004910860f0a460811220108142d485400c0d4100303808101e2002c3c00206107144103a540d5003102c10b216284c400913103a41c100a82000d40120300e50015810050510028581c00b080c0d00b4100c41950341c0d42c030420b440340341c1100341c1007125110300b83e400076200c1e01080070300d0481e1f84500d82060004100500e441869248541980e54a501041d020030022901c51800400341c09101071201003035024500c0c00b107007990008058000c00c0900c5070140035000440c1c2c2014000c004460010800804440041e26415001000340c101d001c0124054401040d500c25142800184c45000703030b45923000340d030030a400c400044004002460481c51085440e011203a90100180f1421400c2400380b0060030810448401d100d003581c00160426040080400040004003076842c00100d86440c1c8d0a805e55068039a03800040180c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 187006753 1250 187005503 187005521
    0x61819110c03040b18060a050405060d0e1c02011505091609080601180b03010b090718050a08030a08100e04060f0212180c01020316020d1505150120150604 68
    0x680b000050101e10003502da0302600320562841401c42c001600d180c184486405100b55035004110300340028482c500c0e000740648804290700800164000c0ca20301d8652400c190641082c8081c00d208280182940e42800340e445000044100700c046607244c400407507010800202440c2c001d003410110304a11500c200e01c6d0000804610044070782d6542c40e003210b01c40a501200036440310900d4038010000e2803c042c080c40014000060141c9103680e201001540c002078410320b00b00d01300b600700b40d021039036580c1c000095028196134001180c4580c09500c01400340b04024103407a03441005d044e800c0003440540a040e590080d441440450b0710740000c800c05001c0e0103100701d1000000038010412415a103811f014003034100c9940215a001200c0200690b1248580c010b01c0d5412a069100300d0050704054407815080340c0306590585034243d02594003c00c403903003903a040e04000b80c05411102c40c0c1da40034080ea1341100704098a9010003560741c42c0340d0394415200d00c00803201c1c1d1a07240094090b41c1c1d0ba41c058000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 187008003 1250 187006753 187006777
    0x105071b06170f090c01080603150a060504060503070311040b0402120f07020d09060804060c14130801050f0112031d121011090315150409050606181911 67
    0x595070711000090b0881030728001c00c05004a5510000f1050741035855081e00a1004102500e50a07032202d00454030030720000d00254041c4901c014003280d04803c00c92480c880d0040c1100003e2403400d1900b01300981c1c0030340c5d0005129501c4404d00340041005003c0328418014120f4000070055a0600410043e00804a800140403440000c0000164422040c90b05c58940b540c01c0d200183c2c035000043e079540140380610400101441c3c001000100c16070f02602c110f903624145a940300b0000d090700600e03640302c0311a0800c012041c00c003c00100c0c0c424098ae5400030500b900402e029030400120b0303c01000c42910180401410051b8114004a00d100c80019014007400c403107004001c18031166a00d4001d18070704256185010901010400d00100b03884903500c0c02006005082003108680d42511005042071a6004d0007074041c05031540c442c030561a43c144114080d2071903244c07110400c00700040512580c42d0401008080152740c00082c4491860340544240003d00c4c1245000c04048034083c50164002c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 187009253 1250 187008003 187008053
    0x1f0b0102150c0333010206061c080d06170a050c01030203040b13021f031514060403030815090a060302040c2a110607060905060114090f06040e070b090102100501030809010507 77
    0x2030136600201e2020900c100a800700c8000781c03a18014000100d4110300c069503d015082d4030600045c0e1488010126000031800210301c05407501c580030814012204520141c0e030040e03c424040000c140521038050500742000c502350f1402c0d484541407400000d0460240050008183d8115624244040c40c0d10141008900c000107030250058010826160420b440303041c4100b0018a00d0400c0d031443c0d104101c0502041e00b840c0c613541c0d094a4103800586900a81c1e201c0040c0505241c840e0b40d205c601c240b0000034085a2945107005010845845d038150001300074580305500d41c4d81000c0d11003040000d0041024007000d254a082508407140541c020359032280002074948280000c5401c004e070440e000d0400e41e16540da07142103001103051200101c2c0c0e0000320440000781c41d5030703445100f958080d070b02400115929280101040c203080503074001d41c2c25402c0c04200b980155038100b2000c0d82031610541d0803c21541035440d6407509015100c1e0f0241000000030b001001c2104c5080005030421040803c42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 187010503 1250 187009253 187009321
    0x304060e070305030a11061902070c120c030303060801050f071407062f12060409020f180a0501060c020a05060f22090f09020f010806010905031f0b0102150c03 70
    0x180c480d4010320408000402d081b0385040b801e000861032501807081d15111001100740040064003940028000742e52028010000003225464003c2c14423900f403107080c000c407000b410342c6809000c030346280d0070202c07480c1e140808006845a89003031003a0084840c0c10042c1803c1d100e40401712580c841c080740100b420b420320358a211158846e038092131300c1b50000da80050390407a108410501034010b10b620441c821801d540411107500f466070010280e90b0024100182058113240881c16040c1002c00d84d00d944416401044880d01052180602401d07180c600100007505c142c0000388031140740e0240b5442a507002400c9032070851100110f8000c004011040009a00c204000001e000280c0c468001c245040c040a41d800c021a440341350519030f4010040300c41c0395040d5004440206004204c0d5040c03000115011a42c0c0e5804c00140c002402810700c011160b0091100700e100340d500b03101c00c0382c1c1558400c0c1900080400d43d001d59541c400c0c81c02c1b050907101e035290444a072118900201c101c041450f5000d0314 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 187011753 1250 187010503 187010513
    0xf0f0203060f01020a03050a1b06050f0601110601050102254b2108030907081b031f06090f02030105180411040207060212091507020109050c060304060e0703 69
    0x1452162100302c81c50b11241c42c0d0342c0016038030740241303940040005604218040d4514000c4201e164142d281070011035800e456640c0725800c90f40c060f203036108101000e408100b580d43e805485503c1c100c03600c4010b0149549040000307503850510b009001d40040604411744203500c1c040c040c0384014110580500e4010b0862a02010501c1d00320903c41021f814009100240e00d2ba51142c0a1401d45002580b8010b03500d001545481401b05034001882900b90035058404900700b0b0025501580b44600585040d510b890f07541da1070400b001803014296281c030202c41910340d602141d00320071041042102c1c1051039142003158020501604081d00d031034500b911046640f5903036800785040c3d9006449a2244a0921600210400b8100c8004150080d404072a01950821b17402500685118000c0075050215074800344859072340c220340080720743d4451081e203c41c401070001ca00c0e0300151680000c0042c40c1e4503440d150f449542400700540141c40020205040100f9a80002d6040020b0400c0e070340c50540307078681 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 187013003 1250 187011753 187011757
    0x8030103020901140a0603020c010e0a060b0a060305090a0b06012a1106072118030b0402090705070f020d030519020c01030c090806040204110906070303020403051501030f03120f0f02 80
    0xc2a030181240400204912032010143d842e056001004800b207149000d50490196215141e9040c41e03540312554505000400c200c00e4103c10301c11400030884415220500810701c0341a0701c51410036050005220481e1000303d00d849059400c05012501d6642d06401070f904074220416101c29500c01c03803046c0103502444800034101e10b04c156501245100705904004290003404400341290f8070100b4240c143d1140d030340151005240b103040c2071f5480c001d11082e80700c4640d415401a114900480c007007108502d0240741c00780c0c0c010114200503091494076100e00009a001e0b0340001d0081d03241002c1c046c20f160080c0d0a94656251030708044102840004000b51582200c171a030601007402e14018183c1940941d02c1340007555844802807145a0340d0742c00304005004070040100003220200504000e41d12140010701c6258081c0c7c0f400369489185141c1a80703040c0700c1090b15031040c51040c006100182c0340c08440c00c070b455010b01d0030341188681456000018913240215084035840c00040201100d81c0e900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 187014253 1250 187013003 187013009
    0x30303050603060114011b05120406020a02180f1609050907180e09031e040302060f0c0d0305040f111207080d08060303040f1e03120309110a0b03070c060f09080301 72
    0x1050f01c9841c0d9803000e6100790034400352801408200b2a500041ca011003080c0580315a9000f00102c2d041102d180d60390001c03960040e041b1100580014900d4815810600f001c80300700c5c0000c1c0310b001501c0c60070501e200005c030070181415164125407814000264810400c031001b4103802003102442e42459100607000380e070001042c512110220398001095100140880c2c41441020080c41c83c09a101c491003030603000e0503900040c1c0c14014080400580ca544002d00399289403034100950340c00400414514003405400320204050408041100265203105000612540002800060040200028000081c44240c14417510500314001024a070003d0302e5510301c0e105807501e8005403582018180c99105030b018404920118000800800d041d10036128624011001c144c40d4882e140e17580c60b00740408000c1d451000a0703e4021100520150011041120004880105c2200e00d040d0f009062070000810880c140050141e401c41441159001000b488600002c1000400d100d0b10b4560310300e4100380 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 187015503 1250 187014253 187014259
    0x2122a010b1e03070816030309080303090a0605060d0605041101030b0405060607030e1305070816180302150403051516020d0e060f0c1605030d050412020405100308040303030506 78
    0x1024400604418420110703040405406411a418540712081e4141c003822002905481403d400103401c01080c460510160810f040b55440d5070706d18103009240c005281c0258031160401c01c18000d200c10b0004803214440d81c4220042403d6440c80000b0342041c00407400502000e040504000810011070020b4180c49001d0b20100082c281240a1000703c0300c040703440c0b680003442000141d000c07a008804080c0184001040041448802d005030000d4800a41303a9401240f014428805c3c04050203044500104d140d10b0107800c0710901141d070300b00a81c2e441c800a07000c1c0458504c2d0084c105900e10845000d103410601302c43d00400d100100ca00c1e014411241101c103074229114103207045d48049000c24501409036284108191070310304000450b40240d010700c0a001d02040140c4207251300b03000200403450500c005401d11440c10301490b043c00018000441040010402400301030100d071a4072040c203405980024540d034a500e1840b80421845d00041c00307d2002103800010144c0c1a048588102404c4e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 187016753 1250 187015503 187015567
    0x10e0d030b0a05120309030307050106030215160b1f0303050c0105010501030501180509010b09070c0b1803161b03080301061701060f0521090a1709010e060a0212 71
    0x2420110121100d40e10016482155440b0401c2240303026021842c50a1040040e640b82c0a030b1000064916405040125520313512164204250714001520500d2b14250f5052280707010031041c4941b0504440400c01011641650041200d007040d06806088919141c04802080e41e203d007406002c64019050a20f901c0d07003004c0010901303511a010710b078100c032840c1c243c10010603640782604014160041a10490b9981e441c561103641d82c40411450081081d0380f0741c81648206414a48981c2030000e202c8038841c1b4070080001030301030b0000300303d94405145448281c240c1503c0d1504005c06406044900c030f407042c1e002008002d00c08100c005504941070740d15a603981008140c040c5172201c03001d2080f04042004042c400510364021802421140d4841c42c0c0350b60803c1002c2d01180d000310f426540d8000782e5220101e90001c00c00c24800c40c1c0e0f5130f0051010328a041c0745035113000030041c011004000f402040c01048011545000b0400301003051010b24503152900810040950304403501c2c20b00025105039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 187018003 1250 187016753 187016773
    0x909010204090516090b07060b04051e16050a1d1f0f0c0503030f0411041103090124050d0302100c02160905070e091005030304080604020907090602030d150512010e 72
    0x442c0503400294540f0392218103045d0716012401c9155007100c00103440c0103840707c518002554407841031a2140844541443e81c418110300e0744440103000500c4d00581c4000b2503030501030642c01509849800105281c0808000252000d0303880e01c20002e103815800003410050381c2c2244803034915003515020241e507220400c40c10400101c54000c4541000343c401d4004001044018144441c0310340d02500802403401030441c3c0b50081011201e0340b546403402400c0200030702c02e0094007030140b4801018416040043c1d038100d500201010b25403031081912658007a150701c000c040c000c0c400110100400c4400700310b41c10810130003070b413035070f0b603490075403030011050f603404a1051180d10402e40694255a0f5403114080a44140100c1c514040d00b0075940c1c0440daa00000d0740d9508000030006804000c003d0076850800d44144940700e04051720131824012642014003200d540002991406c0400d804003140d41e40c02281e2240c54617120382c01081c2c00404203080603c00701015088060201000400c5a03d0115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 187019253 1250 187018003 187018021
    0xa0c080d0f08040305090607050d0206010f0914010e13050a0605010503060a0c0e0f060c0109050a02040e01050c031329090f010b0a0512030f2205041e020a090509090102040905 77
    0x7400580c07000204410002040104e489000a000004030140c4107914001a82d22800c0c43c2020480c2c070240140d00c5400140000c092910003140100213980c028414040d0041d1031144202d41401681e41d111802000521201c80107040b00c2030094005003501d1140039136003030490142609014030b6020f4840c0c0c1002ca100c4101601c11202e1030b014a540d0801440949001c100c001ca01c0c4106403548003c0c10b02401c40f8050007849038440307032440b620050115100324818070040e5002e91001c031615034034050400c05883c0c000170032294480c040c01c03600d0748280418034002446006448021281c0451000c180340404004c00665008448540490f00009000b80003542a500500200e94029480510401990411550321160040d4010070349080c000031460381c0003241c10402204803c1070103a800c0d0080e000c04010038030041c0c401918180700345900040130190800c0284056122907030300084007a0184e03c100002c00140c40c0042650a0314100a02c0c03c5000c4d4001d03003d04c0080a01d00f01c0803e048103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 187020503 1250 187019253 187019267
    0x30b07020a080a180b040609090e07050a0302010f2d082a090103021209030915190809030903100515010309051e1903091401030504020109090c02010b030a0c080d 71
    0x1903000e02c44074079111090100300c0300701040403d281c0034101203002c041252015440500042d2a05655401960340750120b402c1c00d031000c048041620b90016001400103440e03441803002525020300300801d0008054004035910b8a138122031880c0039031030303283c0080c0040c803600232204005482da40e40511525640241c0040f4066510300d03400c042d00500300c01d0709080808000d03282078401410010b0806036070104105005100300c0380c0c803610f0b400004a600c19480e2a18920a8640402080340c0c1070017065050340c07a01480220411040c0000840040d04140e002c004560041c8400b60a5602800400300220040e0070160789840041c004d1a45203d01c035442031040150781c4da042001440d001204583c2d5094200600000549134040e55089004140798031007000801846943c4035074840b89890400c100c03c8680710714290400d1b0500081c000940e900802030340c1035503245980001c003040c03e0b0409900404601500c9605402003051a40034082e2090070740c4100c40782c060a464140e001c0400850fa01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 187021753 1250 187020503 187020523
    0x30306011d0904060f02070b09010501081203010e0a05061203070515090c0312070303090209010605091003141b13030308100f0b0d0203041b0b0d0e030a021b040f0504050304030b0702 80
    0x46815400180410513580068003c18114040146000d142d170302c0d034110010b0101d44044c000d0b91198010003900c28100481c0300900e6a2882d12425941040c25403640380d44041e1180e00e58981350008202c4d03940d540d000c8034181041c400e040301c5d590443e51415a48484143c00790000c809441000112012000303d80c82c40c00300d0001340a4851458020103024040e00540401e038201641c91090301c00503294601198007811300f41c1c50f102c2d221102441004405c1d000101c10000b0542410707002c10141c40a00f81c041d8000004034451034100c50f6244000c8460300031403035480030300034841e8400028942c00464050285003000300010902d5181c4040c0b50003028588940c400c80c0030104580c411400066029580151040b40756401003070740e800d4981409803a54210150203440051131500c0416984188150110060059030030291000f40194684900081261040640d5402e2106503a60f50780301e000d82e644041c2c003c0196040038100941d403500a4002241d1458201d00840e4030307a070000544200ca = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 187023003 1250 187021753 187021759
    0xb040c020705220608060709030b1f0e18030301060c060e01020f03010b1813050a05070f08070f110a06020c0613080423040e0c040b060c070303030b06040b0c030306011d 74
    0x1024100203c2054410001d554a000039640d010089000303941405910b0040e00259aa0050300e0706600707190540310805000340300d540b07007a000404180c12015040d0b204a030306601c94008987c0c1c5444400030070504000c040c89071070000000204030190840c205084890103210200188440341055600301d20910a1100c407802c410f00040015407101c600615048a100c02d44414514031000031034500010030400020007601d520030049030591a00c101980059140341485120202201c0501842030103000042009045025020030324050000e0010a0529030119000e44c55103082c104001c0d04a048095424040e041c0070803855440c200e81e10110b1a04555214905407a003078003045510322881c80301c5c844040c4040c0c2c0c3c0303070036640703c0c401c0000b0850b10700d000d050140408000c11007200c02803449a44503210a11140b07090600005000c0c05a079458240064035008080000e4036500950388801c449407400a0540d41050011010318040c160a8035100e8403007010500224010740c013000d029030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 187024253 1250 187023003 187023019
    0x180703050c060c07090204090b0108060f150906210901050705191206030b0f010509010501030603080f0315060427020405030a0611040b0c011d06101202030705130b040c020705 77
    0xd1149030010051030b034820f0480480701d125542e0060381c1e09030380080c0d000c00a01603071507020800c1e55802c00c80195103c0d5045611001082030308000074500b180b426074001c1c1807100030a8240040d00d039201203501c01407910034410301110b03d82c8450030580c0d0b03049400304540d508100204104500507029250001540d2905510881c0c04403c201c51013508400d070106c0c0243c41e040000040380c0303141502400b400c26981900142e60410f414480344001c184c2c001810185840800c1010400100940c0c006084e18030f9019542d40300c08400545041070300300d5013071b07000000040c0001c0c0c03000c0b406040c822240b12881e444030311420903030b4824100d01031886034940540210451100003806036000340405110314108134201507d0341d0452280da000b80c0040d20150b1b42d9164207500340c6a200808000000e1170000500351813030003c5110b502da8508d4403e00f500e1032070302100f0a08559083c04110040d00740070700014044102c150014015141d40003005010b0f600d4904071468281c070100300d05080d1180600056 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 187025503 1250 187024253 187024273
    0x15040e0309040e0c010c081303061d0c01020d12090c050a08061009050601080406090507080f150f010b07020904051504030c120207081c1e0801060f0512060d2918070305 74
    0x21f14503448000a528000541180400042e0706881198400c2c80f40c0120381c103d1010341c02c1c2d000c0c1b0740712036114101d05562007003800c558100c0e800720910f60300f00e04082d40461101c00c1c91910403107061054000350b50104440c4000b098041c00090010f01c6400c40d80c25120b9016500c0303c454040328820f4510b00c1c0003884200024001c0750f003640244820620410031221440c3c0c0e83c0f4905801c3c608650708244842e00821a050540f00c141d40d01141c00c5404010000c805515120101c030240c40f940301c000340240014070004007480424450b45040e080f05100c444034034940307864024201008220201c0c0d40340c424418600480d88000b400c82e059405102c01070204918103080c1c2003891880c800301504000445607020024250078a014111112588074205107505020002d016052112a800201b200a21078210b120000e28910f5802140a40f182284c5015030b00300590a04403105440704102101d41d0059030015200c2d40d80c40c45400d20302100c41201509401c40c0e519a0802c0c44050f01950002d8441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 187026753 1250 187025503 187025513
    0xb03070804020d0206160c080106080304180905100c090f08030a1202030a0b13060602071203090b090a050612040b09030a020a12020c0901080304060210091a15040e0309040e0c010c 79
    0x8809041c4c0020b040c941883c0210040745030080e40c05d50105e5103101d0400c410000741c3d0b0b00340544405001201d000d14102070601001d40d040407d040c40b4000004d89038514a810702000f0701c0104043c854041040c0404580d0840c0980318500900c5a6a208851844005220400030064480c002e00d82e0380c2d2800303044504c80c0c00e03202a4102074500b4180558840e41074504d03540d10748081070f086040c4a00456038614040e0082c1c10701c6030a0b03202c0d03146210704011000002c0d501900080590310440b81c400e8542c503101c404070b400001d0a070000f6030041c40024601007181c90407451075120b1441800c2d03070090340d61118042500d81c018a41910050390094030602c000500c0011424020010352044440e44a40741000a12001081c0d11516032904001014408250b061011200b0300740d00f01400e0190301c81755510140740380c1e004009411921494404070b0b0480804482c400c060040c01082400a501e000d01455265030081c01c030280320b1032400c06005400701d000b07e665a04070405865580e00b021203a107607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 187028003 1250 187026753 187026769
    0xa0518062404030b0405010c0f05070f1703010305031c0605060d0b0d0209070908060c030f070e011e090905180c010819090c0602151b0a03110705160b0307080402 71
    0x14400d00800382001c4400c0314445002030300c0218090451030400d8141810501e00319100c0c080d0075001c02c49800c0c09605800c0d004130440d981150702c13050031118401f560400c0d100c15100a042c040070040300100000034010b001000d4005d2060900c200080f80720300c18000c1d001ca070b15034480c1e5a004a414003540f059160948d00189078420f010f04003040e0002d01c0d43c00260000740071510302020802d410030500a64170204182c0da4058520840c80d0702d0360401552075840050010000c0c000c20480d00d5010406920410b9161039104a0012400c0c2628007010003402e45900d41c0504c052403854000021002403000720140e9500c100c600107041c40a0b9450011260340000500c1c03116a6201940e401c0700d85215485910140c0d400344a00041c1e40b030400c50001d003420130000003503800a622a050021890411455016114800410f00e50700e500700401500a01052141291803c00215181b0103008010510440400c2c0008005c1390940e01c0c1e0020090303902050300d0075000110705400180c01800d040c3c0c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 187029253 1250 187028003 187028029
    0x513020c0c0409030503160201060b0d0c0c0506010b0c0d0801120605040503040e0a06050406060e090601081e091c0c0c1503060302100201090501050903070f0f020613090203060a051806 81
    0x107075640301ca9041c01060603a0075414040300082c600100f040740c103d108a100340503200c40380c4000d07c00503250403a960a83d0150341c01400c0e581d661203100044603070103a40ca84145580c4103050301d04030340c0d4502a1214a0f00444039580da203014400500040324854800c103070699180080400b04580c46803507490003090018070450341d0703120030031000c20100c0b4551082441541204400300300c240c140b900348800c1d1a1580d0114040c08040c8810701807540e039071580140c0c0100203190141803551082640720340c084410341c96481d070b611400c052280b0b04074049454001484076401401105010005c04c58098544500140558400c04001c0c408490b80140e922606960f030325011030b0003a12900011247ca8000007494050303991901c0100c108a0280100b652000310000650704008440d100c900d01007c9101d00103013542c82d203003c50350442d650700b410380e4101c151300d000c540b0b440d503102e440d418000d600c1502c01c54820005040c001480b841c0000500100b109582002a019184d020920402c000448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 187030503 1250 187029253 187029277
    0x105090c012304231e090f090309040207060204080d02070f090c02161205060117070303050c0f03030106230304331107020405130b010509070203210103020102010c0306051302 77
    0x200080758403900703a002106462607940214405842000c2205d281e41c610681c0040b001051003011640d03880b48a2140c0c882e0710148010131a90b01c1e0b10b9010f00391f10a0340d055a1b0f1151000c90720005001e5658088c00541c0d084908441407941700c16800e80c0c0c0c84420f0301c0346103000b0902500504c0002801c4e004825104141c0c01107841c1601000c3c0040c07400c0c0c074207420000042d10900280d40a1203810480c450041864814035200c00340003d076165110b90050101609000e400541414940760400c080d41e80220051b040d00d03102d586910004040001c1e17002028080a110b1000506031000001140d010760340c070461681c3c0048102ca030410310040c0c03140400054010052149440003200c1c0213400c460b84084007280c6e80d80342684104000c0300c001406a102580c15014010700042c2483c0030319064682c05c40340c8500d681e40e041c1080f031440c890840240402509c1581401c07255055110142c181c904c01d800034801c0b010801d000705e00300c0e680751042690203028144200c0300b80740035600400f4100441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 187031753 1250 187030503 187030507
    0xe0705120a0807140a0f061a0a09110d050f010510020f0c01140d090c091107260c0706020706110d080411010c05010e07030210080405030304020f0402040909030e01020105090c0123 79
    0x1480201d401c00d0080302c03051b10b5000d8007140420420880348184528403d2030711124040c103240c48042400f20180e03020711244540c3d07403101800b031a42d03c4d00989003442c0540c101480319281c103085206ca1a0020f00c1004e0003920302000c42c440e0f075400895081585050701008000080c0c50400450342da901e03040844e41c00c00700c00c0281e0744904080f8050103950300d005125149445181040301c20440351012000c141500c2c2c20b100250000c0c1c0000840c20b10003000706104500c500c00c0d200150142c2c4142c0030310980500c80c0441c000350031600868800304440445c3c507440d440d071802007415038840c5000d400705400200c0c4038000500056142208450740b96043c9000380d010f0003140d59950840f180080050481e170302480d010411403810742d181c0c0c00310b24001d1600e4051410540d603880d95038000a00020b103e000100403210b03170798960341d0540d4020070a81c0c00500c01400b280c18050414490340300c03114019400c260010b480218006148003003038a040e900c807142c888031169036070f01a404d90165180c480d801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 187033003 1250 187031753 187031783
    0x80d0507080a21050402030d0f080103060203090106052101200318030d0f061701090503030a020a020a0f0f061d0703060f09050d0206100e0f070c061e0e0705120a0807 73
    0x21103e00484580902e410000d00742c1454010140b40c0b54041400404004414104003510380e400050b260469034410700250b240c1d1030f144a2503000d41b00c140c120680102280c05001e45102c607214882c40781e0850180200b1a10040104042081d0b111403440304981d5020004111000c0c1011600c542d5141100c040d04e0401c00c00e80101415642d600a0b184c1e50180c541e0001d0180c43e480c1d00d03a4201c1200e581c4020403a009869451684a003c0240700078105507020581c481c446000340802c90019030700c07200341000d100151804541c66044104140c8043c0c1c50140c8006000f80e05103811400485050010301d003541c503503a501805844e20440d007015050301e850f03004001981c01c010100319030031242c000d030000f031824125108040d82194003540c115188441440541c104920070503030840200d250a13245076469042c040080e145503100c14941c0504c12078021070444055002070194810301080d20001a600d104000700c07041c0040070806560007000010000070842c40c000c0020901c01c001c0c01c2c1c0d00c003003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 187034253 1250 187033003 187033037
    0x10e01080a0c170a1502070302120c0d1409030703031716120207020109050a030b0121120806180108010b0a081506120f01020c030d0f090c06110c12010b010801080d0507080a 76
    0x40c0185c64001c540c0d0081038500405405108010704000081d60350303401d1030240118036a5450140c000345c810311143d200501034214060040791b00104020341111403665691034002c1071903c2c808000c024084da03140c04140d0030214a02d0100039400c080d9500070400000414490096000c2c2c50201e06104075548001a42e8680d0342200707004600680f00c000302589425480100d8441d41888060581c524a9170700000402c010b003061280d810383e28103003145661b03901c0800d1420aa40e0901c6801032400700000441c0d880540080c9540d41081c1c1c1e42c0d0f02c900350b035198080e81d188110a50001490a0700f8000b590508010101c2034000a502c000c464042d120000640d003264012980514107400004403210000c045028031101c50380100c40400002d0705030b07102c0d01c084aa103402402d0402800780d01c101b03418031040241440c01940201a0360144400280b014020050641618082240100000742a100c0413494004080f102d840d000d15003070340c9a940343d4140c2c1c0308641c4002031000c40d19640040b05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 187035503 1250 187034253 187034273
    0x60a030f0f060506060f07080306010c02090901061a0c03090409210c0204060f0b090103050603011d0718020f0403110a0e18010b040b010e120a1a010e01080a0c170a 72
    0xa000341c9900d500444142000002d440e00104070f02d00481d002c02022000004d0034003100c640a8002444a0f120f07150480100c51000300440042e40c0044400180000600190304c081c04a42200a400f00e0640e803486114040303004035240d10740180c00c24810918281071681009038540d02c1a250400800401c0002a0340d40600c1c0f4188400100d12100980450030640f080401a1000f2075402c4825803400d2603100345440f50103040d0341011345410206210361806d400c808584441900b2090f912005030b0587d554500c00c91054100483e43c0403584107020005100b181c280c103030f9034800b55103407609545036884d8103510725a649400c242c80c201c0000c5e01f0b01d0002d4a060081f200c80312075007800140d21800c1800c1d0359000c0c1c0b41502c0789203403d1070381c01315a81000c0080d49440c419240004d00001c0c0c0c41c0c002341040c1d1948406400050040c2c0082c0780101e000880c0c505070b8103c0076004080e80d80311200c855840904d003000501c56180e960050000500035007040014240b21400c8445580b8155105c1100c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 187036753 1250 187035503 187035533
    0x110123070f150e0d020705030a11010f170c1c02031e040828020d030b03060a0f2007050f070b03370e010b0d0b13080412031707180e060a03 61
    0x2504854489050143e05200306c01c000c0c14100d005148107501500c0d445058090b100c4481c0c144000e40c05c00d99512405019000c110a00690208015103081c4218054a9000030004c0c400c104469044580300207691096a00550241388011207018031610b0720703c80c085010f082500e070701406000940320320501442c9140c0752030a035840f0040c1d40403010382c040d00d0300d12829603510506041c40c440c03124603240001c82c41d50021001d080840c8840520440e007005110000a4401d018543c00030448036015aa008206146c418800c0351015605003545540315002c5002e04441d44200308007040107924900305052031200070006005d645200d000048481811000a00e82f4040d00d4441d07002d4514402c0c81032a100280946180310241850380d01d030f072044440145000c0000141c101c5c44004d00c05200306403030180c101c04500401c04019400e0151480c030890940b444103104420000b0b110b1403240307494851a07c45810a0041c182c1801c000c0b0b0728003c00182225000345c5a10b1000000c101a01724583e00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 187038003 1250 187036753 187036781
    0x15050d0e0705010801080a120302090111120403171303030305070905030a0c060809030c030708070609051204140d1a07030b1314010602030403020109090c1b110123070f15 75
    0x2240b80391400150000c2d130141d20081d2070741c008501900204603100c8004240703600524005030f03503408400050350000e20402e52440284201720000d030072450302900400559009038507002c07011011049204442c03040760704021032303140c4007002000043c1c0030350051508070302681006080d0b207031680042841d140065074292680510700c1070400076507030011542c50f00041040301452414002252041d07403442000d00060080100044400a1240d0750340078002090380101510322050581a007a601c5030000d009450410101780c4c0403601c1031030580004da0110b5400440c2c04201c0420342d10241d200c0c84020503000901d030b01c5040d03803141d07580c0d1114020b0a415900c200003072210303400290f0f1288010140c110340c00f954020401840540c4e0090402811505d1001300440c0d20103081404640580544d000d40180c540b002080c04c0400010409050002d13000703a0b9090112820130303442184210380f0640782025010200720390400700b001501452000ca00490049001c5071504181c00c00b20742044900300d917 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 187039253 1250 187038003 187038013
    0x9040504080316081006080414030301181109010c060506040e0d050a0e10020c0d0602190c0203010f0501060806060c0f03070c260601090b01030f1d0c0a030c15050d0e 73
    0x1158043c0d980d8404018403180303070028003440c180480349000c15043c0500010b11000c000000c0c2004400c4c20008208201481600e40303d50f07440b400030f0640c5800b000401c00d00d505000e82c50456020320820340d82002c905a540b94825040d503202c2900402014014640060f00d80303001688402080240a645100ba0307074845036207090f800e01c0245449020f501c401d1061455000e140c072000e60025030000300030340c11203040c0000c400514191000340314291400c0300e41c0f0a8180084003007a08907003034407441130089c7c0003800f51951102c0c00f98201e501c01d00038140401c10040c0410182e003451409044101801d404555003010800c3c0410724540249004841c0b800d000c0c0340522603880c06160810f40044410500c102c1035880502598440005008049400b6583c00c00f003810b0b40e100707800002c8000740210741040038680f480114075000e20603003080341091281c81040c2c034280c00c1042c0754204484d00002d2845c4101d06000f200c2c8203404c0c024414904000b81882a40440841449050300561028009107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 187040503 1250 187039253 187039261
    0x20c18010f0812040b0c03070f03080709080102130b0a090e010f140a03080304150b060703080103050609070b0414041409010207110904020d0b060616140c0a18050c090405040803 78
    0x36010030741d41e810062040d042070070062000682601514195103d20301c010b512003929001481c51400ba01d06c019010303241501c8404103040e000303076240c0d0041002c1d90380c00122a44072810b007401d0384a201d002c407110200c440740400c19480301c03602401d0000c0302490000c3e0850769580c103203030132540d0070307000060310031003420f020070026500780c000060b03104043c0c0700c3c2582c05285482e9840c15000c000c00c0603003110f100e03011141043e2516031041006c09401801c0640311041401c0c024510030007400104c5461040e030004c1140130b0800203210080300d45680b051861b02d4100007170000c66000c4022415041611420841c0408c2e16084c840c0707108500c80000181c40d00c03000e0401d012145601c0c08803c0c0a0304400c014080540c0320162a030080c0c6410401080d40c58944070007082c0144141ca81e4003003070a0250303c2c14020400341a620601d038144020272540020301c0391003004030030380640c0b02d2403c002c003081c180d00c4158405900030f582d01c0041500e2441c241030204000c901900d004a41c11a40c100d8004104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 187041753 1250 187040503 187040519
    0x20d031e0917010b0108041511070602030601030501080705060d0f060e0c070302121c05061f0f09050f090718030206040e011805011a1b01060311010207170607080601020c1801 77
    0x2c0315000880100134404081641c0010700720242c05000500300c05404030040e0316510b0035800070303001d01e840c0c100d00980d25502d0707003000002504240c9500c3e00103421305000045c08100003691030140c1d40010030712490702d585110894004c100b5542442d1900d0780b14040000e81d04401c0c80784c60301c01d100c990000396452810340760003401c01c074050211854001d405c0c002052610868640c9008207105000000b03600d80b41d0000046c81c0f13101e50019842054980d42607a01c0c0241d1260f41c4800307410b0580c95030007006842d0020041003100c1c0b81c8085421035803010000e035030302d82304080450403e00d030540c00210640d103d4004c03c0b1035a005030800042c02c1c104d00010041c2c006000a019509404000c04100700c4d41850480704c0c5911290381209001c100100d000600c4410400d014410f02d40540000c000e025a82e1415a2800c4072142249016024400000035244445081c038121100c103a070203882c0039907644500b40c2d0002005490941107206400e40321450707484000c124007494601d000c103050198904281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 187043003 1250 187041753 187041779
    0xf010c06090632070503070509043309050103120e0d1202060f0105030f07030206030705160b060102070b0c0c0118030f0b1009060e0c030c0c060c04050f1c020d031e09 73
    0x20f540500324030501004501c0e944442500c1c0c00c2411844c0003030b603c4410300001000b5045640020040081e50f6056109003800c04800c0543d1451100d112408503035a4680c031b5040b210244005010b5020b030218185001e40300b0301581248203002420480c1c07101031070300d03200078040d100701c0f1810243c0c4c05003040c0240c451421a080340140b404400509098402031001030701c80700e003803000901403039020012a10700f5024006071000b0f41c000b0b9159008604041c180150006425035015000d8010010041480e100880485108601c80030080c038200d040a801140c0f00f040d408040a0350811040c1e012000421008094a043e07015190740e178564149440c03803a0040300b0035030004100c5841d000c0104003030900720544950101d030314103580d03441e03a40d444102c40e1644203103081510907000c6c2100b00704240602c03602400a42d00e0507102d40c0b0000c950315080c00781c084440000e0708100940c41030700d84014900140b0022146119260250042408070050034550440a0001010509121050081c503601081d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 187044253 1250 187043003 187043081
    0x2091f0902032215050c0d0e0304030209150607080702010507140c01031d07030b09071d01080d08150f04090c060c02240307120e070923060f010c060906 67
    0x403032801580c0c0342c1d4401051002c5466440c02c031a171500001801c011a040560f22691002e14091008503844010706459501900040b81f00301c1c1d8046c08500107003054007409100c91006402c4034900401038451004030340200740b0481c10848104064000100c03281442c400065900d4000e1900500040c00981641c03096014258000e980d00d07016421001c0000b4014102e940102110243c0c0e02c2d5400f49604044880e00040a0a00e0399582d0003640042a580b96040310f400b08192490391000e10402c0340c400405803202d00103941c803040c80d80d115103040303501d051400794010000941c51740c159071101d00410aa91206c00884c400d0b40080c029030800d2040d049070002048805200002071000c03440171400042c2581d41008071441407070007480065841050500083c4040f610012355a0608a0240c102000c00740f91781444003a04104240380b913120f250040705d0007041000d10203444070044800c10010700068070050780b160500c2d008542e02d4800e5509400f6915040310036292104601514082400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 187045503 1250 187044253 187044301
    0x60f03060513051e0115080708070b070312110715020a020d030b06120c0f0c03090f011b061104051f1e020a111210050a06060f02030702091f090203 65
    0x10b051600040c0003c160090710000c2044420400c86801564900600035421044000d0141481c04100f00000141100c00ca5a40742c080b590011f841e104441c0103801540e0000f400325071103150341e920200342900021801c0100460a40c200685030300d803001600004801e4542503070780004d101100690501c209140c1d814207090900400780c054000c10064070401d01001c1d040c0007490b001c214415614000c64101c00e0a00c0051a02c0719a0802c1064807540b02c00142c0c1d1040c0d1400100e9000c55004000013100c3c2c01d445641c016501c0090b0721290013034004600324035604142004003152a56418003681c809941005020000d480c0071100a851240d5100719903440c1888880c1c0045443d17400290308840c19800141c02c241a82c92030003141007000d001d1049200b03070040d41b811240720309299010b188141c200c007200740031641c0d481505451150f82080006e0050300704014160142c00c012401541005170644486c40244c0c0700041480d0070701003508028503040d000400d005208510340d603810f5040b1005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 187046753 1250 187045503 187045531
    0x6050f0a0612020309010603120825080a0b010306050604030506090d030204030b0106050d0b04230f0702250503030307021605040204060503012c010b04030c09050f07140c01060f030605 81
    0x214102400b400a602c07104403102e50008006010300b003080d000fa400542c2d012400140d606031090000e08140d00c01c83d50a4560085251007944910070158500c1144004e9200c01d542d9880309115000030304100928141810780320900050b0546400d001000214001c201825003030500442d10b60420903015040d008040c0140024008100e003901158112469420599030703d420060410000e0201c0740380b50342d4024940310b007071410780181c561211019401400d181c80545c0e9a81c0c80c151403880d0070360f01200103034001da034014402c0466056084d01410318081c0490003e80d07840003e41b4550046444400680100341e002c500c3c055044021000760100319030a40c00c1c103042440041c020b010521603c82112004c208907044a81007070b18103103207540660840d4040e0742e1075103d0884154040d1000301d9142ea1000c20014414019201d80360003000d03e1030303240c88a0f40705c0d40c000711a0076140c803d0a40c8902400c1180d0201e9103024440e89004182d410550090146141813840850390000e019010546c58 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 187048003 1250 187046753 187046759
    0x7170109111605070b030f1e090715050c03040303050408070801060b0910050c0d030b10020a05070b071b0e0103061d0a0b0901090816060606021b061e0a0306050f0a 72
    0x8100a4032040020300329244040310443c01c04070f1500905030300103203100e10000140442440020403043c81403100e02c034024880c10700b80d04244c01d1110204d861180d150000c00d400c0c002c80c1d605001602c400b10390f03440d0181c2072006e145252811540190306c101c000c01c100040411880f08240f2604001b03202ca0402000071514084a402c02c038132070586114800d1508001c030360402c60051040d68031008684003101e8502e80d000c1d030b0140c010000352402a2140c000c008844c81c0f0b003480000d01c000d032030768441c010b0003529161240c418041e8010b0b6034100d98000e4801040111241c1302d601c41e1008102620b001c404035451410301c0700c219200e400000d08240480d144c101042d00b000584840f1f5241e1241c807541040d134407810801d0041414040007041c0d5400003d188007200ca0507042c602101d80142000c1080aa4904043c0d9488160303402080858101e1001c4100d68980040a070059184205d8140d4808101c11483d10f00c81e4400c001c0390022950b948000e100030b083c41d0b0f80d94200031105458074a24141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 187049253 1250 187048003 187048031
    0xf0319090812030709080a2d0c03170705030307020106030308010b0f031f35010603050601030b0901090c1d0702030307020a2010120507260601090302030607170109 72
    0x512003040c840d4030700000861040792040c1d1000317006000c0441611080342d080d02d800d0a0203403500d00300300203022903010004200c6065039400c1c4e2595a001b400b41300b4561569403441441d010404000c84501814404003003c6031007030000307510030007480d80001401c80c11464003034101001078100c82e1080000380311314082e40da50302c012a03401c00341070341200c8100a440050103104c140c02d50452104528050303c98403031481d07c20180c421203a01c201034142c4417050390b12500d003200c40d00c0c8401b510981c011001000481d0503000707040e03040b00c1301d440042418002a182d03c440302820703600a0030b18542c030000c0320300803a0715241a250840c2c21031020354a18100601c00a654054a43d006007100d03000861a07800208692204200d0b0300014040c42103a2807001000307030034040700d00b03000c2c54032a0910340007801b2035119551300c000d207014000410217020441340c0e01c010101401040d0300c2c144005034801001581d8200700781d901c1a03090355a50b00c03040c070001c259a015007606a0141c00c4150400b80d250241c1c039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 187050359 1106 187049253 187049263
    0x801021803010c02120f0403020301140402100e032d01060602031c0603030f050702031603060507020114040b161202070809150a09150509030f03190908 67
    0xc0e400818103080c0e44051081e007005800c00403001d2400078101d000340031800c2d00882400c1c240354481d0302180c2103491110512420441400407c0114a480d000491403021149000c654500006e00400d95458107121151050074590229140b80e00340c0d4041c814102150400074014590740d01c90107503caa200851024404d0034080650b607020299001da1000c0320f0f41607407400342d001da104808440342d410040040380c0c5030183c514075804010f02d513440030010b0750040000240500f4400070203421550207001d0596a21103001c104004244808151588050440c10055141c1b4881f0ba040f902c0c02d07525014010244c1c804200b07a000c4c03090420140c0200712065940c00c00c00b1082e026503000318010003120000003429504184000f820205c404003640b03c45003461030811007060002400c0088030310124a203540003240e01e00420084111120311040c1a041602040b4140041e080e00c503 = true := by decide +kernel

theorem cover : BRFrame.Cov 186870503 187050359 := by
  have h0 := BRFrame.cov_init 186870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 186870503 ≤ n) (h2 : n < 187050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
