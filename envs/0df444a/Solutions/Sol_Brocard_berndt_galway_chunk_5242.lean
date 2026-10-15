-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5242
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:13:17.305215+00:00
-- url     : https://prove2.me/submissions/4f4bb27c-3915-4d63-9995-c3827c17002e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 942625899 ≤ n < 942805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 942627149 1250 942625899 942625913
    0x2003030609100e0403090611030a05040504180c080a0605160c1b17010b100318080304062d05010f050114030c120414060112030816030b06030c0702040e0a 68
    0xd0300c030328207a64140464880d0080da01c540c1d009070707020340c032142100c1040108041e4490540c008650058031020800b03401524282c0d01c0e07005802200c40050001d0000304994540f03500401203080c14a00c1056010040707484250308046190000c50540d40551850000c200880c414150b0003030003030f13000d500d001d000300030003c0c802e040c4c050024007000e2214504214003040002054024100c4e039100240c40010b044043c3c2c00380003406a01c85c4103425001c04003040134064080c1c03180b0159146400101c8504170b5480303c030b16800160081c3c1c2d03000e90360741c040c1c0d10070420790044000600c01c25807907031080402c0303580f050241d9405810058030064203031000c000c146d070001c0212a13003000d0b81d51019145d5a038043c0c8000c42c0c0c010342d034a01800e45001401d00041c02242c02c10000d1050b2030030140d5105030b88880c41e218a4010f151801800140308600045800240641c5040304820528010404520a500080d847c0d00203541015010340c00190600441c90b040c4107814007202c0e2040a03103000300550315211 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 942628399 1250 942627149 942627151
    0xa08010e16031a3141100302031e0303010b0c120301091a1503010504240e010305100c020a021e030601140f0a050f01032d05040b090a0c03060216081207200303 70
    0x284c1c080491044862991012411444101c050342c40c61305100e00d0b003001140003024087c401640280031700601c00d0350056045803410110001c800080d840c42c0d02e44207030101154425146011039000c1c0d031131400c01480800300154000d003c189404103500382d124494980740781c24400c42e5445031800d00e4100c000e585480051f40e046a400300e0b00001e4036503094403410640700c0400d0040c00d03980405d00011138600c0300c0320300350707070580c0d020390101e50040344440e003018111510b481e40314025070f00c91a07500b8010300d881034191002e80c480340c0b0001001c45030280480d00e44031082c0c001c03900200c086100c42a40d07041600011003040381c103d510106040c504804200743c10402800c190400d51100d0b1881a00401c202103011450302c603071003a03d9017114114055000b031a00360303000ca03003000c11030000c00da1489001840029080d00600410b41d91341c61035840c90020350003013803070608041d101080c40f030110f110b210181680780c800300c0c500c030b1003850854001841ca8244958000a0380c03d030600b10541420000162 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 942629649 1250 942628399 942628451
    0xc0901060f030b030303011502060f070804020f04060902120414010c0912061103071d0117130c0f0f0906050d0f0f0302030403080a02030a08010e16031a31 68
    0x304000c04807203181100507200d02e00702c1981501c000400008d07102c162401c01c400c0722806500f41c80d00c41c0c582005441c02d042c0e0a6940400180d9020b0208025140c0341c9818601024000d2000a8240e270b0f4480c04020b0b81c0040c000103241071495000c01c402c0c888072131104a41d00190100070803140a1401002d81040e40380d018901130580e100082e034080200950007046204203c902032500c0e854400c41c010720000b0f01020301103401801e001c4041070703540180f001001500008508200540c1c40a4060031401c0304140705a81d8104a00300000304810b0002c041c078003800060001d03a00f0141000000740607507000ea4001800791500c0c16602001c5002e61001c800d21070b40c000c0304110044030350700b8201e02e0360045070000b6140c04000a81807040c680c0000c004c2c82c080c40c00351600d010a0ba658041e1031000c04c011a81d004841121a800c04040d03407081d03001c41c4048000364200380340381428030041806480e0403036036245c0e581460691411042085800c100300c41c01d007500248082e00c0d0308200990140500012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 942630899 1250 942629649 942629657
    0x15011509180b03011803180b0901080405070f06120e0736020d0f0b010c03080c1e1b070e09031602030a0b0f010504060b03040c14010903140705120c090106 68
    0x520051041d40d504120309219004009001002010600000703401c1611030440100300c180d58000100307000c22401801703c90f2000109130400303524400550320b040300100215490300906901107850b13038801e00110041d10381680d40781181349a2040940c221154211190b450341d025600420115200c0352011000d204500e0b6921035000000c000100451152481c10300322500216148007078100c0d50b0b00442c0e40000c544414004141300d00010340e00c024a078038029001032420000607485904080080c420f82d50101546424610052031a0100307070000034614000140a92003040d51500420110703001d4203449010900900b03200060710f550303115454841c03d840c055030403d802907540910110a103540c004c1180e06131032130701401003840090240602d502c00c62070800003149808042c01a0b0744101c1c1e12a2009a605040110b404481d01000d501c0c0c0e810401c0a040c048001400c00e0591404445400c005000c00c03410941007107406481c40f94250341550011104d00c600d59180e41c0500c0c1120f0003420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 942632149 1250 942630899 942630929
    0xd0b010b04061206050d231b0a090b150315060721020f0a060903210e060106020a020a0e0402030123100b1c0b03010b03030a020c0307050919020c030d0c0215011509 72
    0xc1c00b4103518604064032207150081201074406e84010580210846c0000c49d21f840400ea11002c85504650040300c049030880003040b13140e031020610800440d0007a20081c3e00715a02c615a00000d203280e48440405c46250590220f0380360b51503400e100e0340141803640d001521f0b903c4000c107031441d9211001e95028042640344c0740b03001c003410300448006c2c00815064000ca8801c00720f402c0d01201502d01c80100820300d1154000014007548003044070070b8010350040204002c28a001031031078404001070000d84c3d15558445180001c001d80031212003d1b410740a05c07100f42403802103500c0302640016840080350765404c111002800d4805103c03048624410003000030401407002c0483d0051140d4076005070544400600e200e10950005054061510214111a030254a8609011680405035401108a4000b0710020342118058000c4c000c0d03244445c080340c1c11301d904520000155200f40003141c02682002c00440c0da840701c145410381c0900805a59103e07541214440142521241e204900e0080c42500e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 942633399 1250 942632149 942632183
    0x30615051c0206040509010303200c03071707090216050c0402041d040f05030c030d11070203030f0a05070602040e0f131515080a0809011d0a03060b0d0b010b04061206050d 75
    0x100c184e8000c0c1c480504060f106603140d260192500944055030000c6c40700000318400c039050001888420341901a014007000752400805804c4011400e01e002d240340034044003c150004188068503801003100080c034030007401c5007811410401480600c41c040d500401050203448a00341804650040005c05c084556545052007010781021460051860000041010139000c001025205840c18002c0403c492248c03d44490054811494020b40541061102030410300199002c3c0a100102c1d04085290030b40d6952600200c1e030103900b01d188081102c1c02400780c0a0403c050107603100c501c0c4114804c50381040d484020542d6944e4424005007034442c03940711024014401140000e04c0030b04202c03164110103203841c1102c3e400082000d800a141184c1240e244c815201501100d1803001d020708601c541140c0f034201c064495a22120340020f18030304090001404489018001c001300400940c039107050400051107134041d80c0403241c440e8285102400282d407810b104403c1c039a48490b000700114004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 942634649 1250 942633399 942633409
    0x41208070206060111010e2a040612020108040c08120a0801060f0c1e1a0108250308030c0715050906011703090405070215040623012706090e0304030615051c02 70
    0x703402c01081f140182444000000c4525103071480c0e000400c1203551070110400207100445003a88070b098820040b0006203005035000307601d00d9800c030b406000d0302c0da40340780c480c00740620b000e00286118403403040006e400c480741742c0c0c05000310780504068a802510320240020080100c1a81c510151054914581e4a41c41d0ba041c00f0070546640e5214004825010081403844102042440749151078090540d050202d110410080200c41d0b110b8404045280d04640f14106983c10040040701001d600300f10301000300b01000c18003030303c0e010786c2c940104141c94400c5a881c00c201041c0c1c0180ea4580061044500340503000c410790b40385001c00d0324001115500c9440807442c0c0030050a07058800d00c0d10005000074415550400d02d050094204048030482c1e5415410316045001d11406e400c10307010f800c0024040317683c0f580c0644482c40d07246002c615180c40d40c545400f1514200780c0c15804d640001001c00402110b070140465038000c0b84001e0381e5003450704010541c0765910604041d04502020684801c540e20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 942635899 1250 942634649 942634661
    0x210303110d140907080c030a03180e2422020f04050405040f05281b0f1409090f070e0a091b0302040e0615010f030e060c0304120807020606011101 64
    0x7004018024200d01c0402506222420344050803240135807400800ca0b048006040e9a003001e02500929405460703840403a4884040aa010717200011072100003070b81c46519032100d0148240b50362075010101d0442000d8a58082035282602440c904d041d528501051180400845503d24a0140c1c0d6208804c01e83e4031644181c0e041550f11914101c1444140f05c1c102c00d003031000c24425012100c032150144810180e91000c0c6c00c3c01d5101842c049a1200056900f04210904890841a40c885280c41c1c11015821801c00c0c0c000800160380e103400c2c1e40641c43e1440440341c219146501410116410761794040c1c40d40c06030b02461440c03648000201c3c0075050302d03074000000550000020602403446103109001c020b45803106902c83c6040841110324244041912350203080164160360300400d0500041d20401d40c0365403210309141d80d41c480303520100d2381407203407034812403144202540c9d0f0b1409241c64000c40d2580c03078034601000b40368010461543c0d00080c4894015400b42071100398103001030481030242c42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 942637149 1250 942635899 942635917
    0x7052d092407081201060e130903030e010c0203090301230c130f060216050603091507030e100603051203041707080919260a201e04050121030311 64
    0x40d000440e40240310a003005490130910301000039507282da9a00c0200e0784400c0d1f50925561090004988e80b90041c050b50119a0480c82400c1c007181d44032404000340c0c00c454600c010800581c20002c1e81003041e00c1d00388100d801450140200c4040808084100141020010218503603c1000500307110079072080c0c404800244181042483e4454031001c0013500c85c03003450003030500d65002d6071b40403403145041c00a4074401c0400300c0090003c1038004860113203a0703002409034014595503084122840348140506000d29441180c042201c1d49580b40561800ba83c401490400c01018814080010386201101040502211340b20782c90300c0450805049610400c00c0e2154070050109200c40582604c20181046030600c0400740f100703900c0f860700707120a07110070056028950000700354000050800c0680c0301f144a00c0c20750ba2000207400c00c003c5204035440c1803c1d0002844034a54190141c902802040c2c050514001d0340340e20000315801c40641000300900082c00c1c161129910a0745581c1c010076a40c070301c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 942638399 1250 942637149 942637219
    0x40231020714120703030507091523040e060a08120a080601090f03201c06150806070804110301230910360210080c0408010507052d09 59
    0x411902074440c00f42d4010b80044000c6810701002030640f901a90101007140c140f48080c0d03150380e005550445c9c001d105259100008100e40c0c07202c6082c2010480500080c101c41042513886060180402c010403000d030b4050700241e803013000380c80c84040011080e1490007200e41407030040e13625460016110002560800744d41e040c1400400030a1050844450641c004001c2d50004848103400030320501e400c0c055031080d01e080c0c070343d52a200010184d0b03115051992150403000001611844c0040c1011819130702c8000280c4080144002c0c4660141c3d801e1140034201d00070013404044c540d01b842818003585030341c080080850000790030414184050848030041c00010800422400e14098031103140007541c43c0000c500080e51882d2040e0341910102d030b47d400070090450048076030340071116010300416103c0102000c1c000003c940c0700901416004076107c1d12803580300c0b0503100d6a142d2a0300c0c14501d1407840c1e004064101002103584044400d60700c01a500001c02c1c81d01c44040100c070842e4008011040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 942639649 1250 942638399 942638413
    0x1a091009060b0f0d03021b01110f030a080106030204182c0106140105040b0405040509030408030703030207143702190501031d0705130605030d08040231020714 70
    0x31641c0b14503100300d82140c0640400c0c010009200d04548150001005079224056514191b00d03503684112501c0b40500d0f140c9820301814107001d0410b041711540c0021544041441402942c01c000303214003500f0107150031030a0500e806500c11150107a204001c00565440c0c12120b003820941c9918548101c104111101d203d6200800038003c010038805c501d1440c01c1000c20003550340c400c0c0200c0707040303d042c0443c03030b1b0901d8105020030005000144c04004039110810000800440900213010864020f460040e128001ca0400c10242c1180816103a00d50704494003007451602c103203c000c41080034008550790701c04004a801c9940c5442d09401a50201d074040340280c40d801041500015588280d030144040000740c0c240d00c82c900a00000019075800840003480309050807030b0008030344616040c02140065840d004a41486490312165000800c0c9104000660909407440f48440780702c0450911001d0500300421f18114801c1d8111515540008524092146c1e406a074082d2a10300025100c507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 942640899 1250 942639649 942639653
    0xd121412090609280b06030715050c010b0103020712030b0105090d060f110405400b031b010912140f2b080106180f080703030206090601031a091009 65
    0x348050450b007080e428854034012480e080a4109002045500044811805105640d800170070407001010780c0d4140c4120180001c408100303656941c0a4849911082d41c0c445030020b0840c203548503500800e0506004010020004100c802207030212221403a00154020001d40102d600d8170981c40503d0b448168100c00f031060048035409145581803aa100b0840401114140e10580c0201d20685500a4070785185002d03900c10304c001d2521070011108580b00711a003420000802990082031201a0741d81c071410100d16041c100b000002c01540c08507040055008000000c0c54a903a41c0500c0300305031b1014070420100150749502c43c2216040405558120003a699a640c2d1207903504009502e10340004291200c1ca0440d12402c556442640e407003001030781c2008020b5440884129031685c041c800c041e8006019001c01c0c40c1c07030000d0061580980710030351a505009241c404040c02888803504482c004000103070340100020f80300c2c0c002400081055459080003402c201c44225906102410220b140342 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 942642149 1250 942640899 942640903
    0x31603032307080c070f0b0d180f0222020301030c05030c1207061202090a03030305072303010509150d0c0602010e030309070302011413030320150c090d0f0602030108010b0d12141209 80
    0x101c0d03003071100c2081048642c20ba40c83c40e01280c0f05240a481740300e400240c074000d0b08018450410380cca441e080c41e4203518007041810101d900903030040d201c203444890203111034601806102d58000040381c0c8150b11040c000c0c070040d100c203200d20840d010301649035031104040750396405a5210b8500140200c4000c5c0d941e00f0301a028004c1281c0300b600007900000040c8e141c244164010b841e0707102c10000310782141c0c00e08040c443c046c00090220b101c080c4020303035400c60995808000790304462090007460311061600d4800307400e45201c03120040b4650001c0c03040207543c80000030403404a07a02460400c0c3c10680040110f041d03813280010500c3d40c07820701c0d4008414103030000222284440e098854020080307000407016194030840780d504070140744610218100c24131000c06008000c10081648000010540d10446800700300780040b1900b0350080010807c0030300c00c0c826119003410a540740b403002c0701c0325914028400100c040500600184078134024514a0903802d4407400c038130b040c03c2c41c1c94900b00481590703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 942643399 1250 942642149 942642157
    0x1c03150e0c09040e07030f08070f060207061b020309030604020f04111b1c0c0201080402043902011407030203090c27090c06042102031603032307080c070f0b 69
    0x203010f5410f0021001d0601c00c002a01021260003a040f1200e039051641c07604a90b601200f001c0e82c0c050720a0702d131800494920300c003c00b001d030f106080008001a1203402e00c89a00650300031402550001d103d04900740e2030205500c1d501c26412540846120115400140101944074984030221008511115140c000c4070304602c0500440c0c0446194451400c00151030f444076085140004420102801c015402510761980081c0700a01c0401e80100e802a100700e6000d9030307000d0225504050b44640b0220b9480c800c0a500c00805200070b2080ac0302000500746148005001481090340c000000303020b9940601101c00314890042c05044c00900c800c0c0400d9140e054040f03c3d90001200d0404160444030000705500640707006816981802d140120207150500300540001c40c05d8100301c02c17100140d4050002c200040c50340780d03650210f1425410014640c00e16102a011085280c21b1031542c420100d1080e02d1190782e110000950720204508030303a0070700c4156480000c0c00c8003054400300703042c802d0002030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 942644649 1250 942643399 942643417
    0xa0902160804061d0d1a060102150a022a0303010b031008060117060a0501060f0f020f0709020408100228031d01051e04020d08030c1c0912021c03150e0c 67
    0x103001441005401c0019a00c50000010f00311010141d92100309414203072071b103074020814010303111403004081203103c0c081da0486610880d11750018080c89856414007400791055007c1c4c00369840da46c4240303604c6649101c1801031603c00310340403000038181c0108241e088043d00414058031141d5a4655111044c6082640c0c1054203000f5103000451170344980c4140c50403108a0355803400860542c003826240c0c07903d480b0130b01d0114003802c50400c1c0304040402001008299902c8010fa5407403621a040d170402a600028891460040043e204440c1c0708214441006d540b03070340d0030701500d05d0b585825001030407007006d81400c000110340401c40d464010740c025845610000041490f00b40f0300c100659461504890003544184c0c000340340d002189010001e994403000c4004e02615003040090011414000c2c0c152141c0303015141c00d004410800c011000601e141300f603000811450700440301110885c0d07060f4031603004059a40500e05000b1480900410090100368018074650030b00c00e44d500e0460380040c511f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 942645899 1250 942644649 942644687
    0x50f07120e040b040e0a080c01020d0524030a050a0204050604021606090b060d0f06270f03030b0406051c05240103020f090c030c0901091a03040308150a090216080406 73
    0x20f00c4065040500a0126101c0b590001d82a00840d90741e451007203401415000140e503501f40300d140920b524501c10280a44810404014640300d5034690301007140720b00c480a402500244444030024100040c41410203904907008641961380e400410020b0041d0802294190102005d000900a90384d000c608a01d005041d56031540d47c0e0a400d016044200c2807008054102a943c99804a80c0e04c1d0f121b5541d40303400c036848075004e4030388481036440b440d032044003036441c0c0d00e8003a901030805805126487d0750f06c0040d1010b110192070a00041d0569282c2082002c043c0740502c104020442c0600181d0b281a10301055002070b44101c0380342096400090000b240510301c0c2044041c8646001d03400f40744102c070b01603009482c550700c0013400c01141d00401d0001d8140181441d010410395202191900e0f608440c021858891a00d8100100740480103040d2082210035803000c0c0c2c0e119144d000e00e600665200b0040540d4034202010712a101d02011030014122620200340429090390080342e0010f80107000345 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 942647149 1250 942645899 942645911
    0x120a09020114040f050402070f0b010f29090418020301050c090a141f020705060a08040b0609040206091005070b0a0507020717061302012f0f070e0106050f07120e04 72
    0x200380d0b10610550050340700340500b0800400c014a080c1d00103100491182c0b4800b40c01c10b0301c1c0ea41d45840c0301c000ba0007221002007851030038071a400d90003502c40e801646100120804001e003134040000c6210b003001c814010380d00d840e10150f0b4032804400002600398098000c12061500312804c4034180c0000580700d103c0e0310f00b0b07400011400c100c0c104001c00c11300001c01c1d000106e100700d401e805401000d40030400c15402141320018460b034800003e00001c500710381b01c00c0140d14080c9170070741c1507031002450188a80f580b5408d11015803140020341e500030400359807041617201d40300310503555401884401806445010100a042549038005074017803841074003110000303511007000c00d02c0885824401280b9600640001d602c5c1d00c2558002c500355401810402c648250242880b840c20915207624070042907840041688036074104160311035020100051b0001c1c0f4141321001300703200d0061003042d04101020945007004400d0800701d480055009589840c0c9080458024046982e4640704030710130745c5020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 942648399 1250 942647149 942647177
    0xd1b0f060318170304020a0f031209120b07051b06012c0403140306040603021018120203060c0d060b070605090d0e060306010f030b120a0506102108120a090201 70
    0x14551242980e000d580c010005000d0103070b1441e144c00c000d2050742d1190844400040000060101c40d000d940a21440c401441021002500c1c2c4800340c1d02074412200082d1707418021510340306600790040d0040c40c0544c1e0b100d010003085543c60f040c3e00c01045240c00f41c440005402001d4034800070500c04824040d03c0ca40030b664101414030401201c01030301150108400341d21a1810000441d40720200a10009000303440c0e8000c100c5a003000d500080116806032800088030b800e020080300100074200b500e19550480b80e01107078403924040c15044044001140d00340c0c840c00c441c0c01040152102e40b02c03140c0c64650038108000648070644000c2842d004800300e94036414400c00c070440c0e00c904041c01017840d5031203107001140c0f1040000902c1d010140d84140307801540d41c40540f07615030005e5410007451829890b060041c00c0003406400c0e0f107020702c06071408001d50345054030740c60350450580c80e1001d0b0106590801c02c00d24418101c2a9158492000401003001260f0f07000441103030007a601c0c00d210314606 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 942649649 1250 942648399 942648431
    0x129180a0519080114070903030c0201031b081005030606010c0609052103011802040605090907020c040213051c0c03020d050a0602030c0408012009041d030c0f0607020303150d1b0f0603 81
    0x41c2e400c0c20000b4103409081c23000c030780a2444207031030501c107150001d1201403142c1c40780040c605034400c40d00000c244809004c10359900540103405020100c0107000c040c103000700060302c0141d011070b00030045902d8407400403d00c4814001e03042c0d0618150f152040591202c081c2089c180d1090250403820031403507425001c2000d1900c240e03821b4034013580b2000d15045046080050b01c1c50001c0c203080c02c40c49046110320094840e4006401508652901d05849a042c070040183d051120b4288000841000c40e104d0041554000c08070101c0c1d030140c60000700d81035941031036070800800c0400948100d00002c01c2c0003621560200070400c43c0c081e40001c00c2075081806428042c2c60303240840c801c1c005810300c104640da2525134816090011504a5500c4044100d0300450031500b018904078519001580154400b8a003481060703440301040c0b01039855071a1010904806079030100c031281c000c040e0b40c0c6441041000402c0d003080246031218480c02116915003074124401424019140040d0807d04204008002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 942650899 1250 942649649 942649651
    0xf0201050702060f0c090406300221030403050f061803071208070905041407090509130602182e02010903091a1e030129180a0519080114 60
    0x255000c0c01440e110613611501d00d1078090000391021204100c48541641d480c0305103802440e00752050f108000e00c0f140480c0c0190a1246045d17141c1d05d91130080801a601c5c203500301201010010740c0c617540f00c080d0020b01c0c558015500018181c0c422070755415200400041c5c1ca6200e0900948611000500c0b961015244d0040d0a00144040c1a41d2464044103000c0d880c40c1d82d018a11b49096030b00c007513444002400392103108000441c175403100d00900283c140e0001d00003019080998000c01c05040c40c184200b2004615036019180703984c04a20005110440c403d0030410700001003440c1c0030008100310082d00b4038000c80b00f40c0c5441c281d00380301d1343e24140103000d1980940d801d0303215079039400d280580524048240406031200e0810400c0300c0c000844100c2c41150362801e660700303019100d41c1869000c0700c40743c1884181e031104460852a2500320a1210700b00c42030741e005804122100c20307048002c070b1520329240c0c010380e41c481094012600742e0f4806494400484001c01700038041d07520602004103400700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 942652149 1250 942650899 942650911
    0x291326100c1b030309060e030c100504020f0405010801020307080711300f25081812010f0207060b063c0d1b30060504090807030f020105 60
    0x3222000d0821039003903120400700320380c504090040700300e4094075510720000e09400728007107036840c0811814000e191140c000c5007210309005516015848a100c0d556251001d0184c1c2c140b82c4500c0041e04549910780250781c801c41c044c0c030501c00742d40c48014141c043e410440f0840000740b01480081c07001c3c0e200b40084460441102c0c00b07040c075220301c0500c07518201c2000d114812006a800341135402000c0300401010303070380b9912510a8a07243c2c641520070070074203203a106507002103044126801040c0c11804444290326600740805031721035103001180c07a81c2e0058984104c294600f1041002c090140d40060000c544910000c10001d43d80c241004840e0140d0720072140341440300d0040c150b006407000f1603180074140709060301c00b0140307030324860000761745c0201940d20322503484103c00496501031010114280040c1e00b010f5410404000410f4640300c880c00317031405295041740880a80720000c0d4404005048050002d004d449540d090000c0c50341c0c40704030118006100341a501030528418400d160040e5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 942653399 1250 942652149 942652153
    0x4020901150504030f0524061f1b030f0905090f0f0601050d0525111203150a030602030f06030303090c060307110105150406091104291326 61
    0x80d0801c416052070385009481e1505019041002002103a0100315650845100e840100760300c06036400f00038404080d54480400240d42181440095a80c00c00300740031194025050014481c031a0800301d81c500c0b00c80341190b442e04415110306040c10f0340607200382c142c6021034650100b800d07030301c000340000c070f0b28110745c000300c000d80720000f24100201107081d07150480c0c0d0514209040503444400e4000301d44050320200610540c1d18414082c409810502c080b1080140c1401001c842051a9154503140301011210142100000040c900c1410301000c06a486015040801041e00e03403a150001794000d0fa141c0c501c40008000141d00391400004803441003009001402c0c8038400c140900035a900060680d4080c0107003000004680c000c240b0901d807003801e007000200e10902c19142844119101900828101070501108411902c0d004044500b280d043c41c01820b110b400070310301e024803940d203a08200d0354103c0004003050500300c500b41c04001d480120260104840d00410084851a00d00021034695 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 942654649 1250 942653399 942653401
    0x60f060207050a0b0a14180301050106030207050318011e0e030f0109150504030507062906042706030503220e01150e12030309100e0109082b02161109040209 69
    0x1c1c1c00c1e40005c0e244c000c0c0c103410401c860000b12000c0c4040c0d5004406010035080baa440d00c0e03065490700340507690042029003011860001a915001e45074410300c40e548041c0452a00c4408190b40f0429130b00f00d940e204080e00541e082e070001802800340c20f4040b01203100c3d1060480d1843e1110040c4243c00506910080010035024020b03011070192034000c00a40c10302c50180704110201d04203001d0303108400c5410040141901000740442c40015410300b42030b0045c40244402c0c0200703d04411300081d890100c403401c0c0e135198102c0c0300801c00b6044982004003280004100c10002400d030110154a000005120052036a1038000f92605082e00344281d410708010f0882000e6142c0c0100300c0c2824800b000350503102e4145058081624503031081c5c0d2010141e40c000030307901c0381d00421445035040d40d12a901c000d104050b0780d070f10340564078004c16980100c044104407000440d01d14401040c0340041d21150255191000248010a500e5550a00b40d55000e039100c02d41d000c610b400d201140c45558020890891 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 942655899 1250 942654649 942654659
    0x703021e01170705162103050103080f25060504030210020a02030a0c060227010e030c09040308061f050406082a0c0a050709090c050d082713060f060207050a 69
    0x800b0030182410701885000c0008549040301d20b03043c4038805000b0000026010302c0500d00075007440000c400d1404142c900001800052000c01c21580c00c040c0032690607480b940e0b05001c0104030001441c00c9800b15003d60802800c1120740d42266224501070780a643c10080403080d41c44c01da100b40b8585070016003027003100702c140d2801612841d423024040c2c0c80050801c00f1024455076020201d01c850b01d01042565000180707580d1010040c1444038041e005003140700708100c08513902c0440584020140501d08001590707584500780d2090343c0c4214011907107040030901402400d01d9105008000001e4070000000c4e4921000829155803000c1c103203a03422100e200000010072681021006800d1400b03040c0c000000720320100081e1004c3c126a40f8006014641c0307151030301e4407145560201e8004c0b0048800c104c04111020251248403e014001440c10001c098140100f05c010742c210561000511245010380d1314154447c0d030a07500d4090741d18503169100e02003644d986072117128403503011501d040306000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 942657149 1250 942655899 942655937
    0x160e0403022a04091112010506090604140408030421090602060c03130f02030f0d030617011509020c0c0d03030b1003050c2703011806060b0a0c140c120703021e01 71
    0x701c0c4c90082003800742d0032040c1000110790ba0103408011482d603440b58240006440c1100d00c554000004840403c5113040c004000c0c3e02c1d43d580204086c05d8000003000060520011b081000030901078000d0300d583e0206d22000181c05140b5a0095030011301c103120000c2c0c0500d5024044038080d000022030700010301d48981c0e5501c88040c01d00b03422600740c0101c104004105c01c0030001c20540b40790544001c034005080110300020740b9100c03a02c802440e81000c24443c141041c0808103800e07100621000f683d02c0e0110300c1d9661a01e002d18460036002500d6498442c241750713040c0c1c0103442c0c10108941c0c80e8123221107544114196030b01650000e041c5030003000740403003407405a41900c4040c9584000c4007190110900001d003160311101e080d50071f85050490440c104981c901c1814060300000303a4080c140504c002d802400d41c01d46600003020260091190003400104100400456000402808400d0b140080b06601e8074842d2104034051802d00001020301d5540401d0b0320300051041c1c0d949074050716000c282c81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 942658399 1250 942657149 942657161
    0x20d0b040f0c0914100b030c0a140d0207150903020c1903050a2a081c0c05060709090c050316050306190f0f05010e0f01050c160e0403022a04 62
    0x120200c0107030000344001410000e400000b8a6050070010740c1c241d07140d8070301e450010010304071640c002d42040c060200300c8240099a030000d425100711915201c405006aa001541000407820900e0200729102800169001080751611841411822542601691b41035408455009001d60407025400c202c074144840d400ca080110036021000c0300d40c2c2d81d100c00f801c0030031070f900507944540f003d4600020001400d442860682d000c460301c80c90f252804c800603458503028501181c42105180049810600c2210810342c540d030041c080d1134240c10316640280840d513480c070910081c24109188401281e0040094038840d0b00c0d5521a0104800c440e001201c266100610a40c2d100e206008210b0399270410850240141c0078071708003102c132a420f0003901c030092000c0b5400303d13041000c130542000c01d0740c6940421010a0400382440c50300c52044081c0141000d03152800400201c0ca8410300003646000300c0140380c0102c0c081d0b002e0f02c51400303001201e6101d000c2c5c001d80c42481550300030f850f00e1041c20241c2c004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 942659649 1250 942658399 942658403
    0x306061302070f0f02091303080105010c06021b0f01060902040f0302121e0a05060a09050a0215040504090303150501020d05120a02160b04020f010e010f080903041d041e020d0b04 78
    0x1454140580c0e59000780c0022810300f44c1e44420346081c05011410495503030303904191b0310f4520301d42d154410754006002c0f02050044d0b60401121286030340420540da01070b11100b61507041641d01e8031310250b24259440240c9800131200e98202807000400524920854013500c1075080c0c88581c403802c5800740019035011440429062082c815000f445500c01140004e9070510003000c0c0000c0b0341c25080c80c61030040b0240202817010f280800e440001240040e000440c9941920881c0034050300c00c030b400040f40216030044d6042400e107880304c41010f905030700c244040c3e44024540340d07040380c076440120ba0f1810030900b06001300c2c10410101d07104218101e02c02d580301059000151600e4850f0540354000c40e0050421182000030000740301c00c51501c0e461810441d0b0082c07178070400001c00d09000070310b2220811100000d0081101c00302e848040c090003143d001d48594000710706090b03204540d5001c603080441d01960754012049510800c6a080704141ca9207035001010b81200400f651142281c4480162003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 942660899 1250 942659649 942659651
    0xd11030c07081e070e1302042d05010806060d1707050d0519020c010219020a0806130512090a09020904140c040f080606030d03050c04080102030408040f080c03060613 73
    0x14145a01004000c40700103005040003a00c0301d030410301c0e05200120a00d21803c101c50300000014420014110f20090b0b0002d10302c0c2c018140090749001040060007050b403841f103595000e510070201c0c240042000411281190400c000ca0ba99030403600d07444040c1910110f0b0302c11f000c0c1025002003100030a2054440d03281c189418608981940ea49140041b44045031000c51004580510740c8c4039607007220032800640d40041c008003101240000e4659544c0071644400c03581c0108001d0035519540c2d070b0304d07001e01480e408503011401e001c54644034061001104480a108409048080716007107015106080700141640744080d0800c21906c002c1c0d001407403410740040d83d5251200520402013819400740c0c0046440d5942c485c10b090b036042d4820b1700c0e500101e5481c2e00c45814000c685c1c8000900d410300c40038600c0c000071a03446603048203e142c072030b5500003c480d40c0003000b44001d01c003007c2c0052044480700b40700d40c5c41407544c0c3d0800c1a01c5da0000a0419415084100010498100700f101d8150210803044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 942662149 1250 942660899 942660907
    0x14010206010503151b0a020703150212010612020d0e03090a080703080405061803030a2111120402060405031c020c090115120f06030b1e0c0a03020715090f020f09090d1103 75
    0x85c1c01030042e0007035941e150059112010400c1031019506201c049007241007000d6240c555444900c0300c820506211f03a808101c1500320401851686034141c1d005505166800e0156150724405c40399682c2280c0201e03842044031540005204200041420403280c0c03110b19035060030310300410400785da0040820004d406981d0b41c01840a994103200501d0f41c000d0390307104d00b01946141103956450800d4904005a8245003011281c0f01c2030014040d0703000d072144241c42d02980d564910202d000c03402950f10164040c400e4a0503110cc00450f10300100b0800459800c8415000c003000401541c4002841251540d0340d01c90001030700350780300b07094001840f800f51078080ba8400c210380116003126055072040d41d5202501042c0084003d10a49002c14541d1051100f03000341410300c42107a09100e40d0004100341680040c2c94420440e01095260380c0300c440359810041c04415080000f4410704120040348548000420703141d5610341280d07101d020701840001418a0309064006854094000400c000e8603c0140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 942663399 1250 942662149 942662191
    0x6080309031e15090f0114130f02030a06020403030c151a0f030a05030a050d06120515070c0b04150b09070f1b08040303210e0a121e03061401020601050315 68
    0x7102e160b0182c0701e0304d0002c103280d03840c2e00a81c0742141c4110400d500034a22007800d010f10042d044074509100383d0441c010f00400e035017601c0000e20b8841d08000c020000c90001c10000305041e0400032001c6c0260050145070490011802460100c450b0030403245c00b02c4040421894190a110760104a0a480903049940e00300094503a54555001840e0100006100081540703001546004039402080020000244814103564075622004c005090007050f400a0b0002a00d091046002800d85d6807c032050b07600c1418507040980e0400600c141c1c01584034185590200b150421010240c400c08080c0d84070703410040034030f8080f00c01c807192445080c5550901070030580410701e0600108019403007501c8100b5503c4108200d40c5214581200c450032051500e0907d080116010400c45007142d40b01035864243d00c90340a080e5032120050800e012015000d4441112058140e40403c0c1940c5610503030700408001c14004a17520202401159055000f8244203070441d8841c50109400c0009221b070210462248 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 942664649 1250 942663399 942663433
    0x2030c03070902090a12170a090e01150305010b03130615030203010f06080f06091f020c010e0c03071e12020f10020109030f08040b18010f060b04030606080309031e 72
    0xc0d400950007030b0f50004101400f460200c1c0c0c0d04000341141d1525802001c580d4a55420400c141090034421000010f40720700e003148500c021802806043e04000c10030b507182e202e0304010640030307110007005c40d14080001c02d01e525400e05aa1145281046544440c0c246541d0300d0b02824120351180e94442c001c000110050340e082c010003250090700c8400040309407400c5020751401d600d0781c00785402604250b00b404046c0201003007124207001c180d484100411b0590ba4410001d2050403600071040d440d00c00340b140440300102b4002c940034000c9007141e207807548035007401d05c42c0e0401e1042100c8074059020100b01d070130030100c4048a4640014803441034920440040340580e070840e0341c00c00041c1d54070180b600801d42c025400e0b81091946203008000751400380e558420441000d0328159010101d80d01080e0840400d400200362091110000c0c00216550400030b1955006400200c6256061410214941c903000060701c0c1e688100a000340030a6181a040903100e04000c3e40d8507015015246480d452a140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 942665899 1250 942664649 942664663
    0x2010e03070b16020a0905010602100209010e1804050c041803080a02120c0c01230f100b0f0903010f0209011b06092f0409022b0b01060806100203042102030c03 70
    0x20b40b00002400f40300c3d20400000424542010085900c5c00006000b0b1950001d10354075181a003074001030755825040d005884048a03888070903405100741e80380301c4007401c220141c103003d0781c8984100da144000410820041e2034600c1061441c071042d10342c909010a00c1456440e0304051700e410010b1412100a04007211040c00700c0d486400f507100020a01e01d003c409208401e01040c501c054480a4400d16041041c042c001030050460b0ba40c070900842d61080042044500514415034010b136103003100102c0c0350040d004010024469460020314007001007090086400580c0160b5951240c59181c552450700340900840a071407082d600e510850024108002a500b00c1084407800039182d46c4450114080001e00b104190185050680d040700507208d83c1e209084007501f03000202640385294294075103810035403001a2450002000001b22113422070651801074405580840100315410001e036a40e120300e01c900703040b1a80380407440c58160b01c2c00307003102403c904c02019550a2004100024075002d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 942667149 1250 942665899 942665917
    0x50a11060711120301060c11210c01030b01090302030601030b1902040b04030209010918150b0a09060f1e2c09010605090a0e03070b090a02090403021507050408030702010e03070b 78
    0xc140944409440003c020030102452030403c02860b640c140302c00103122906c140c6004143c1c80305204e65130b00395903900383d41070300603c0c3c0d200c010090b40f8402d00c0e076255141c141c10215400300340382040e0071316203512a44050050700d40240041444c0c4e403959039014080d200080c01c041c0250007807080505840000e000501c01007841e1a00103271204c0c2540100f0074100c206a01c202000c0345082070070301120148400c00248260410720b139810300500406014017078610b2040c0780307170f015a03104404600d60406038446019690805101c0d81c1c00c80c1c840e00d0350202c8400d901001d2119198001c806c00000389030b40c424241a2140307010840345414650310009000506942a44441e515801d0a01550510080e55544004410410701403400790190041d00d074030920030702420040391000001d050b0340003003004500d0310340c1c0030304140c00a11382810000d403603204014441440e5100da5003c500c07424825001e8030141c450303181c09940386c11203642c0159411103000d0100c5415003c0c0d04c2001507042c04040c003400c4200d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 942668399 1250 942667149 942667157
    0x27050705060310080d0507033609050f010911041e0e0a0e0111090a033c0303050c031b03070212040b0901030608030c06270a061b0804030f050a110607 66
    0x15040500843c01c01d41c080f041c0d9400c22009208160200703500400401f108043c10a805040720490109c40e019400c503c2c8540c040314521150004008031194491032150300e10359a2810341e80d89030040704050752a43d05444245920601c07081c4107070144c1c1e0245852014030000c0c0d90a08664450480004200480d0b076100c905582d80b180703c00e100b10a0140e0541c1c20708c895007692800080e00002461a03816001c017400e074046a02201c005d03203100c50340200d0012514074403502880d08403941400e25841c46141100000c1c2018081102101c2c54010344e801400c0c0c4010400c0311814085e004407090300001c01d010218803650410110110201006102500191810a5454046030300240543d490742c0d1291740b0710f034002c00412540c0c00011030003980054814100b90320341c003d2841e270320502d481002032030100c0e03000c0c40080004100d119446800c4e00c000d51180d000e10f1f000006003d841e241d02c03c460203000301d14060030080302c080c440c03001401e203c0c1c00c0d07040919420101241c000d14100c03044031000301003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 942669649 1250 942668399 942668431
    0x32010051509100315110f04150207140d06020708210603070b030f0a020309120a081012020d0308060103060317030f09030c0304033810050103270507050603 69
    0x6007800d41e41030783e1108821003070000c041d1441c2d560306600140391201c0800b03690f4030040360b4400341e080d404880450024100582e141c50322540a4611200c0381c3d41c0480162042c0d0740005440c0c1001c00d01e203494114010904001d010458403000040c1d480154203d480324070030031101100c032004511042420400c045803203980d280400605242c0301440e005a80390241c28020444018800010f8a600c40085680941ca03520303030000036460006242101e42e441c103404540800c038a42c4c402960f0b44280405501e0541c40c1e07a80c0d41c0164445503680a01135080300d084441200802d025141168002406141c001041585d0b0340f00c20707000f0202d60140341ca0040c000801d10000d00440700c40e0941020091014500e8808000d01180c1e4030300c10780c48000c0022860f500690350100c200a40c000d4001c45049000d112880d02051b441d011143c02c4410b5150b04c01102c8000c40d00d54403a00c2031f511021381c2400c8c0c000340290465503920314058a44001c940c58410014081141d481d00c034040d500847c6c0c80c24646c504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 942670899 1250 942669649 942669691
    0x5030a1d070f09090206033103050a0306050a03050316080c0d020304051504210807060c0302031905010518100302151308060c04120516080304031502040303201005 72
    0x84810b4a6001c2410b1504040d0800050f1703544c1b000b12504038400c61032041401c1075180c00b0607a061004007500d20080d095090020074182c0090040c001c180d040c0d503007000340f1a1901c0c01c03c2a104814000a000342d401488500304240c1a1004608401d01a040d91403d041c1c000b4005883e011600361014012b030800700d020045414400111105440121001400c1c103040103010101401c68410003482c1c0c04a0074400010301c20b44400b2240b0440e0000c0c0107000c1400d4250026020394005d5071030014005900110307107901c105c940b00d658147c40c1c004000c40300d016030314a4180c912040180071403a20068010000005030740c1c40300d101c4060441c44201715128407299000c2c0304a09129441203041c0c0e0018000c03c010f0380c40d403408560980740d940700046254031150a10034607241c3d40d03800402641c0a402408601001c000000c4c104507441140404810380300d0758442002d90150784402000b09a070000c2610310004080c5228500c105d010702103503584040c0c460300710f0a07034805440030f20a6002415035040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 942672149 1250 942670899 942670919
    0x60a090515030103021026070807020d02060f0a0f020d09060506090c0711010f0215011e06030b100c0f05100504020a0b16060e2d0706021c05030a1d07 66
    0x8014040041c6031030440d03146401048091000d021003104110300754212050717401003901d040c400340c0c408840481c0240b03800a0040d000581c191052805803003180185117050780f0001d03284c1d120b80d0810200c0c1c191a201c4012103005001340b18806600f05030248000002044184500f000060040310085200d00345070040c452002000b0f458204c0c1924100041004111072500d6000615400e00e06003c0700341100c0d00c200c0c18800d1951044442080507800001c11042c0c030b10f400039040088000c0e40b420f031940c6100aa048400981d111500f1081740c86910200901854018600301d00520743c208c6503402c0380d81d031142480300c1400e030381403040d645006100550070280b2001018088580302c1e6840d00c100403488200514614400815090302c801081c0c1d5000000c0c00840184031120303000154541800140003401038454a902c1c1c8603104145c40052103070310000d1603c0e2084610018030f051812100c0301202d4943c0010101c1d404651540f001c0e044a0502c05c20306280301060704040c0c0380e0103080c030b84454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 942673399 1250 942672149 942672169
    0xf0f03060f180312010315022104350d09080f0c0c0103090201080f090f011109100c0213091b2403060501141e0703120509060c0304061a060a0905 64
    0xb04141c0d02c1401840d103028a0450710a0540350083c3c4c010528410019981000e0301c5190701da0400340390080052034007035000c0c000f080c0c0114407410f030380900c003050350103064420350020b01040c04001a03c0504a49805071900400310003243e40e80104003514561034660483c0d12101e0b079091b05c918000351500184a0a108521500000f403034188010a5990002824803034050304510001100401041c07001e44100090310a542c0c07004000d10540c503001d01401400c0e003100c41005d016503c02c252405205104004050b40f156009210100000c0564181d41c000c000e40b1908a420260445442071070860714948540101041c1d240340c45d00142c003103280620540501c4600b001d00d410024188180d80e0011100380c0c02c40030f500c1c0c44640f1416045181c80501f0032210b84000020030020f50030081c0366114080d102940c00c1c031301c030512640e2240d0388030b070780d844200703c81d940220b0509202140c002606900710201c00c205001e1480c60b10740c00361001a40a5000a00010100d0402c001c10032440c00c01e10309039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 942674649 1250 942673399 942673441
    0xc030806030706121503020a23090907030b07230415020601060e01050d060504060f1d0f0402010c031106010f18050c09010f020712050109170a0903020f0f03060f 71
    0x9001d003946001800f07014050660407500b00161202000c1001071a01712076440159001880908882c0c0c0c0c9440a10100e070304080c40960610014500d25054140020b4490003910084028004107196403076280d42c0520285c88130341084880e1501c900402000018180c51030240305440d87c0d0b507442d001c140c2100c491222899030075908004010420703542c0100c4840c0d00a003080c02d00da50b990750402c1402000f0001600040d603c03518004020608412201c1c00d03a064800c00106440103100c10f1810302d4003101e0403074800418400650004005500c500c183d80b910a00c00c0c10a4080402a003954600b000c074260014050103000c95810000042c99100e2800311540c81c00d41081030b4103280c843d15549214003c0c0d010b051000c6100e406c0050741c070801c00000101422001c0e20208065494414003805011100f40e401e02c000e90108640e50b680e8404030f8121058580710700d0346691559082c03107000c00568407415403100e902c00b02c01a4a031818040b00d403090b00b50880814003464901c54a4201d143d0b80034607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 942675899 1250 942674649 942674653
    0x7150c03090806040b07030e061506090607051b152b06050301360510022b090308060f090a090204060504110c1c0f0e061b0f0106050105460c03080603 66
    0xa000c4ac0e0803a401100302c101c5029906136989040d078402140240c85040b2004140b0b100e003400300100300410796403021040780110f07aa0040181c954003e00021f0080307459580c0c0004c82d09420340c4600c170800f41c4000080b0f12646000c6009961000080d00b10398601c203480420450041c1461240d408000402c207623880b010003800a100130f10b40316195a8480401d9001e2a154005500780068503c0019102d2101400c14043d8000e03100018400c040c003609607040b40030900e13080108401c5d1400640860a6002c0a0a0000355a036100c14000c06083c000c202a60816566000811291581c2c051544a0304400551384d1f0f4840070a00f440780f401c0b48800c02d40c040c00c8116104195660380c49018040000c4031860143c0c8815007a500183c018401c002c0140400c820b00030030b01001c40c0010854051414070b0b40003c101d2696140d005448034410300085440010006c080c01441d190002807513000c840c80b01e00408415181d40c2e1300445240640a00100415000308005081550000303101d9030010050b40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 942677149 1250 942675899 942675901
    0x103180b1f06020a02010c151d0d08131e06020a0e03072309100b040e1602300904060f030b0c0f0409050403051c0c020f07150c03090806040b07030e06 66
    0x400039101c0a03000d04c024100000545035406000081009880e0030b10081006c000410104101c1c000b010480740c2902c3d02805818000355045006400c83c41c8a64162030711000d0019072035981024806115110450814240d140c81c40454201d2000e40301c0829242c0361010309044100c2094600042ca42c0b0411401207030b0241c036109920100c09003950140b050726661601d40321001c42000c1d000980d0844400000e0208001030b524130b503300403a00039075122181290810400d142241ca8101c0365080c02a140c404001581404010240e115840440d0040450a08118900140943c0c20580c001c2014201d403003400d0003030104121202d50020a40c1045601e0a400b05d03c50f0f44080c040d61107000c03460760f641c0000600f80344c015001c8803c29201c000485180c108000402d000030140c4260500c014407980d091212895000607241c0d052b610011800c20540c9684d0740e0494040b420358004400308411a440064886e9003000b03540d0007180b203103d080d05185002e000c020304940d140300864040d40c0c0701c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 942678399 1250 942677149 942677159
    0x813140c030c09131403040b0d0b040b18161709010603020301061e03021003110a08040605010501050c1f150603050108060609040b0a0507050903030c160b0403170304020103180b1f 79
    0x60a110301540658040341050841170f046045001c0c0e5403240700c01e03d00010303d070910079105501c2101a510219003c0100051813018000c2d21140c80805010000c02040800c07100f00030b10345a610300420314506200752048144448240701c60968511035641e460b001c003402145401c1c000c540140c01500030160300302207080b07598480c1c0d007803e11001e405902d0810144803414440c2d0000c5035544003c820702652007941410051451004860548103180780000104032588107008540868005000800101400740e90060400c054100750388403950381c803018201c0448502107910024000c1e520b00281e15807400031054109038005065500c206001d80c10000013940b11554980c20820b02d8500042d5959540e0301615a482070803041603061002245410f811400010030101080c0c1ca101c6d03081e14130f5036444c40b41034035005a01005240e031902210303400402144030091a40a801494045030101c1a505c0d41411007510702d00646030f1041220030060945c00070001e0b9000385051400401c0424030705 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 942679649 1250 942678399 942678421
    0x80705091b0708091c0b06040506030c1e040912021c141b0106050a121104050402031e10021801110f032704060e2e060813140c030c09 59
    0x110200508030f8402081c034440303685a0192400385029819400d01c1000b40c0341c1000d44084a04580c542e11541c01c0a00103030a5003404a49036043c0340002d81440c0c200707580445c11842c22817003004403642240e52160f01070f0205441e8485440080c0e1541c02401c92880407020300804036070308c0b40c408010301c00a03510750201d088041003181c240d00b0308076a04506800314551081d0141000d1307400f1aa000b06840800303c2c0328614a4580400540300e8075400300d00304000000c0c4003d13204129000380d4180c0005400301800e4015949298201c800071050761641040300c40300d6012608071308507041d05028204d5080e50296040751002000144100c02032609644c180c00b200da0368419160000e03104500d60040000290900c11301940c0c1c03003801070003403205a8a84200b1040c01d402250301b038008202d10f01000c2d50f0400e07400c1b040c072080e415a461011869042c94419101100080c000942d0040342010040100d44800c140e0700780c244a03a005032030b8104100e0704040c40c000301641c01501c02d800b40420704c001c1c0c40007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 942680899 1250 942679649 942679657
    0x30d0905190b31080405100801180e07080a20010512010303031104230306130f06050c0705010212180d020c190e19050c0f0313020415080705091b 64
    0x107620030720f0010748800803a0408044000a000c000101c068920800700700b2114054010b4030f10a54110544800ca04402c0b0f9840744280300d14440361000c003000744404006604010103c00501084928842d50340e0805860921858000d5482180c01e1208100c0c0318114115106502000d29086041840005281e95800018400103050550b200d0490010396030041c1030701c005201c1d05041e502e038240d01c00c091480080360034019501c82e02440d00064049440b80f241100c916070030500e034200304885076503490002d04004e000c01c2d403005401e000400c0005e0090004043e44545481c50382420f08160954a44c011143c074103a85480d0001071855100b281d00050901c40443c04aa0605207482160050408615150844e8415800290801410900f06458101d0440c5000e03010171480c1d072030700c02e140007038000d00c079a010301c603a01040070030a06505c540090a01500042c0009148080040140800c4186034003440b15074200701410080c2d40303007002200c2e6000998150401203820400203c41003403003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 942682149 1250 942680899 942680911
    0xb10050712081504050a0b0d050601030b0a15060503060307051e09010b0918060a1e08190209040221010518060f0402030712060e1f2a0c0f05030d0905190b 68
    0x16a0324005880d841c00e0343c0100880e47c4001d0100b894200c103604119894150034001916001503650104581041500c0354081c016020b500840249043c464112142c1c4d10241180da07052080840200342c0c0e070f03030b152981a009031700d50b0343e1802c0040c005018440b40950503406412000d80a204180168030344ca010249040c881d02481c170360594424002902091040c4c00c03900340401c107410a10036804181300c10405980394541141c0c05082c0c2d0401c0d80c20345841d89900250030440420104005042140d03a6402d00c54210141c007040320503003551036003140c404a8901c40c0c0780113441e00c0786080d00803c0c012142c0001d51001780c04a00e26041c1c01090743d925940c814041c2510901c8111400c2c85210f90190519500400a503990b11001c01d2002c8417520030b00405c01e2041d40f6050110040c1c40301103e41811300110250000c481100828060b180180c0100d003d541604120540e080065000e0008021080c04014002208442410000d107404d602801041010701c220041801180403c08040e521003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 942683399 1250 942682149 942682151
    0x90e060402090a030b0a052202060403150e0114070e0a030c142e0906031a21010509101b02030702060304030c0b10031205091c05010b10050712081504 66
    0x4100c41c021552102c03c1e944040c00b00c406101c02e000080c845600101d010368001441c24900700b51a8080c8010480340003002913001d1400c000800006800b81450300048944410000d4100035503060035003503036040040030504034044410002c840e50802d001c4142010b00b501c01c007103140e0a60780c2e0302150400368010884541c812004185041c0c0d9144045024043c00701d5901261200d43c3c000b140403042c00f003180c4804912641c5020840ca80700b4400d140e4050106c09080100807818010320011281e150b600142c1031000c0384ca01181080d0034018036000f50300000050440b4000c05002c107007290711075460b25041403136106500324880e038000181c490300f60b0100c9020341d89407107500c1d0a95902246000091046248404200c0004000c441c550202c07400741407408034240404c041110503116215a06a0214529480209071503804200786106440b403c0000344030101c0ba000255850005c0c80d101c0700261001030201c0c1004035031480584405014184054203042100078110000440300e100c0b4000c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 942684649 1250 942683399 942683407
    0xd02070f051c0807080f0433080414030a0810050a0605030109021305090f090f070503212104140a080913150b07020306010e060603040308070306091812090e060402 72
    0xf01c0070610480c2c500c90f620460886d90340e00d1510758601c1e0390700f09100d091118800c4d2010404404082c07002e00300741c560003000041618036009805e49003400d01030800e0b10340460071150180315510030802800150380980307800c00c2c2ca252645406200c0c140700c0c0c002c4d900900700100108030080c1c000d801d40741900c0b00c5010142c2c44410041c4000c18103c9581e215962040020007480302c240300e6810340300d0068a1071400e0b41c0c0d03a041540d00e8130380c0d104800d20896825070700ca07501c0700d00e2050b18980260282500c030407000b80340401404c0b00010307a0b102c10300c1000c0b06100f00428041048407014003807a20fa00301d0405066002c035541c55501480c020b2a034010700540d10a01e124690008503842145003031100403c20800c80d0b1280d07440d80554208140880c020300c0359a001040c14100c0400c030612402c0b009046a1075907440703940480360703520050009410306840d0744010400e0030903800b038851046110a0b0314046c40b411401d200c1d208045041214090125647c0b0910000e01c24000096004906480250b5a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 942685899 1250 942684649 942684653
    0x1a0303130b16020406090e10050402031b032b1b0503120a09060e160803040b160206130e0403120b0d110d20150307020d03091a04050d02070f051c 64
    0x102110903400940c418a450400b24080305698030514007d0542001ca924210b5503024080c1140d205903806907256201d621414201c00004030151140c0901a0076070720210b0080f01481c04082c40092020491240150f10322010b43d0700090500648155147c4141d960051340c49580d22032003140261103940c19444001000040950000b6500c01e074444070420050fa14500c600c0d440c1c43c010803100c0f1038200703060f50014402c1740c0042075030103030b5003404403051505481e000300c0c0c00881c0788210100d030001c00501480b5001c041904c03521005240725000301c516860980380c010103081c6040c0c94290001d144c1003a041d84d6441e6441c05041c2194004c442e00e8031138400d5000102d00c0c040709940141302c1c42c0039030101d402c6030740e01d120a0040300000b900c241210450101c078547c1035020890320400164011105264468032940003202e81900800154035200301c02c2d2100d030100b840450f02034a1a601454003911116030402030740c3d00800c0d508291000b511700300301c000b074815035051403021420f05401c181101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 942687149 1250 942685899 942685927
    0x80a0c0206090603041a130b060402090d0f03091d041a0402030f010c0c020a0909050303190b100f0e0901050a051e03030c0a06050112080d0e0c040f1a0303130b 70
    0x180b41c0c024100d988a140528004048804061202c0300c0c1c100340c0800f00315410415058070204a84c000c4400149540300c03401e01000750003a4242c40c1e0300c1640c0746011004108030b94401003050703000b540c0391492103040440e10030101080200c940d401028810412011615250440110281040520245484a0000925101c8007007822200c3e9440c0821030034856420041c0c068400d8420346410400542d500c3c1010200c404240d0040c0164100300005800c00c411841864404103803000000f541c41d0003c008034a640120b055840003140b0f1200e0304002c0942c12048052596800b12007070f135040d6040c00082641d03445d152040b18094800c45101c00100b071004400ca845030314003d02225280c0c6100d0180d06c0c0d0b02d402c3c94900341d42c0c0d0f40c9007500200d84008aa9905413406800c000c03094a0715282c03202c0240144440c0d050400140100340f108800d540e03990180c1c451041c03007804017055101013003001c080c241e1101c02c020f03407181c1c2c000c1204500c000224a04542195080240d41c1d44030458818a91 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 942688399 1250 942687149 942687157
    0xc020102010f05011d090726190b0103060f09020a0506090619080118020307050910120c0503061201091104020702030a0f12030c0f1d0d210219080a0c0206 68
    0xba90040c00e01c0004143e90940402c1d03122100f04400c900c60040d200c030f200d1580c0300d040c907004a220070540039004c0c00c4c80f80d24507405410000d4000c000c0f526510980d030f0710002c5069281a080702c40824070b000400520a040c09031a00382c04542001700a14101a4002100510340d44640d070700505020805140e070f5900e990036684000d04110f4895204503802600600460090185003818044208038241441c3c40b4801d8070320030202074851f41e00e0940c3c2c407000c0180503001007004400708656680107440c00030b050b0103520880321494450544a080c503c1c1040800005c1120108540e0714206150300442d50b40c030600460002c0580703005a552700d5038004281010143c0c2809403548034030b0076406080080a20349184070794070b07654040010304a80d42045440c400000c549000280c1d0030b240c100d00440044d401c1c0180f4100080403203800c04c20a40e80c1c01003407403429202c00c40d20020700900c004290740521232224a01480ca00b60400303018142c0d2a01e4690007541c02800410801801b03078030454503140115 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 942689649 1250 942688399 942688421
    0x31c110115030201030c0203270409080d1b2a1110020f011a03251802070c0b0301060c080a051b06040302070b0a09170115290412030c02010201 63
    0xd20242a81991101c880c0d450351200300c0c006440c00a000409510101c1501c0e280d100e140c5000512408145200400220104803030f50311554500c5400f00154000005000280a141021641071088802c01c1da100400c000c80d4014015a101c5200f8a40c06900880d0382103504500c0b01c800d000030700e0801c104081c0d1032210040d0072100c1090500c128940000f000410041c134407009001c040140100e107826000c0851080c2e80561001da014500710b2050100882d260004940182c0350580d900840101a640c14180012156000540d0300602c05000044005803160002d118a5540361640080c59105041c2015044240100c2ca4491151044d021114120200e0715650050300d00200b1032500c860301a20300f10b016201d45e0200140b20b0b05400140ca040e03541d26154024000c4c60300c60405045500100b041c8019540c841c40a0200f418041c10840035100c1845490011603d20041c0c001f00307424601010340c8600180130400c403032609490039451255141c07411500440013440103034003515400000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 942690899 1250 942689649 942689651
    0x80127050a1803170108150604240f0906090204050603010b0f0403020603070302191d010509041b0f110c0d080d1401180f02030c041502100c080a1109031c1101 70
    0x140802c3c1903110b030070700b102c03820380015060440c0d1741c40b4045943c0e0861800c0c0a40b10034110030000300b1902d481c2d840400204410030200805100d0a89540144101a009140e000c08103042c14001d41d10240308240140c052a10114640350524000412501051050300e00400b40085c05600032003640c0d0a0701c0003103901400c80c07074607824006030140207900158001855010803446401400f84580032a66855202d803005100034001c01c001103880b43d000ba41c40540158884960416800b606e6042071300b200d90582e12015030f003030500002002c40b480a0341004080e4440762080146949407840b1220407680018155900c1d201254001c3c0035100c0424518050143c4800000340072100c0d051401000e00c100c1c0e000c1085e140090310b140300301c0c013007500c0c420710b0b0b90018041408610fa40480c0700b0100d03c0c5600481d039103502070707040a03000d6400b0f10b0742d0000000c0498051000705407150207410000c59148030020308145545010a9465040180b900c1d40d018006050141c814010428192500c0b00400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 942692149 1250 942690899 942690941
    0x6060c06010f0303030b101202130f140907020607090e0a0f0c0f27050405040501021614070506070317100801181106070206030c0921010c080127050a 66
    0x502d00d00c2508051205030042400e10803030b907485181213034284850402540711425480c0c2803a40503c02034000030300080501c0f0031200301044804503080070500030041401d000a182040c1014400c03030483c0600301c141554400414040d03407541049920302071b41d00362007103440283c0e60384031050043d02660043d208171616101e080c00400380c2c4002240d4004e0820344819000359a8007041d034000e98050440405008206a03081c0071605c0d0540240d074005015200250400c0c080c030f0261140d004a080080b202040c40d50006100d0050a00c0b80a000700000c0380e001c2d040c440c450301d004d8004401050016103401a440c0091100d03000c841d40e4002405052000308a013500d51422654081c2850006581d44034070351101d0075842c94460210364034154050103503070541c0c443d400c0c00240d54008400c01c5a1010340e40806812015010040208001b04e090001c26141703c68000a0004841a04007101c1600c4071384c50301031000700c0ea104030108010384d1000014550348120b244001040d1802144c1c488080f400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 942693399 1250 942692149 942692159
    0xc05150702060702070b030705070305070812101a04060c03031d0d0207081005071b060f02070b01052d100e12010213210605070309020901090e010c08040c0e06060c0601 74
    0x40c0d0702d03119883d00c2e0201c41d01d41d6226010b500705400200c51311400a181001540b0001c0d1040002d408180c1c0f203a0132450901681002007c4068822914452480704004080100941d04401c41d442c850320700005616190510800410804282c0070240505490300c1c0651048034000800064025000e41610140141d0810081d11404140700c0d502c070520585140d14240b141070700c43c15000343d000c1e440c0c072103072402082c1d1a01c854003100e59040d20103903612071081c1040d10040c001464043e11412058000b0340c140420018200c4088007050301b1200340d03004904101100c3c3e0030320700c01007800320b80210980703c0507031084030400b50046260380c01402d1441c0300407141070150041e1500804490402c03013071b5903d61300c1300000d81e000a0f50015424420349190000b0441c554445a0083c00c1c40c9004100045a0740109040420030b03400555603942c1c90b5a040b440708428424942c0400f03052074651064281a11500e4100d03040d0300562481d2200e10010030081d40d1020b044802d80300d48403080e00d400d50303550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 942694649 1250 942693399 942693403
    0x1b0c0a06020d0f020c280810150e0417030603030f0d020306040506151210050d050c13020c03030c0901020a0b040302160504020f19030213082107020109060c05150702 73
    0x4280402c2c0031407194400b44040c14004602c40d40102e82c09000307842124100000c1000d03109620a80521141c0b52540c00720314850140580300d20b80d0000c0c0f201041020005060714141e070080d501c008a1200c41c141408001000610241d03030182040c10001c0c0c4984509000071306600c21560000d0001c240021415403440c00c0b9005944100403c480800c8140c0e01c0074207001180c440100400e07540201040236650703078900461a280c10540088043c1c690f079440d1004610004094681921a60301103003010b902c070300d8008840c10b07008004c02815802c0c811307240070003a601c3c040a480e0107585200441c0740c0040364420040418625007214041d840c070300b040e05000c0d4942024005010205180c00800310b402c0c24203008840702d403080f041840740b81c030021601d682c010420404c0384904040d0200030000c00111441111001b50446030040c00e61082314682c40210341200002d101d02a080034020301c0050703030300210b40b80c3c11100c00b410120f080018920f0824201904608603000d801541d10520201da540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 942695899 1250 942694649 942694663
    0x9060a0801080f060c0d0504030905060706090605010f06090614090409230a02180421030c0801081212130203030f0406020c0405010e0c0702060d0e0309011e051b0c0a0602 75
    0x819401e80790f8014441c80550b490b20000c80e001e840a40003048512003074122607115a61043c020705d03001c1c2e6000e850710002041e0380d00502d01990300e191a81443c00c10b0081f03500c40c49005052081c0500b00740d500d40400900100e4641c0b041805000c0064084510007015a0407194882c20041082110010345e00d8001049980910991007100540000303e411340c07c0007820b28451a0024003442070001840f01003050101c008000f1035090358505014101e02101103500050010962808030300d4400020004041c080c050380a20740c940d000b00141c4940711040700c2280c594200c2d03240b1910150360307411125201071010304002074062100240701000412000050f00940700958250341980c45501d04120036110280603210901802038085005440c210005100c240c0c4060406400c0c1444103900ca41200e07a2410041d00a0f000024500b0417582e010066584214043ca03420510541d07464000703202d80115070141c140180c040d07525196a060400c041d1200400051400c580340b500ca070402511410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 942697149 1250 942695899 942695909
    0x50a03020f0705060910030e060403020715090302090a020a0c050a110913020306160c0c0f0f060807080109051902031f050301140f15030d0c050615061e09060a0801 72
    0x24851030030380307103500440c0c2003007155001840c0030b00b029000f00410040c00e0b9984403003400d2550ba101c590844440a000e48d038030990007a00079012161806010451140d120000c4008210254400b800140e490201182c1c11800100c801a1203004500e41924003040300302018010b031040910303140030856038100030407088905441001d400d460b02000221020700b0008001d40c59040003002560003100c06140d40e510804510309003441412607248c5c2101d00c01c040d0000d58808401404c28048410f0001801000700014500300e00d4502d4a010001d1148806000d252242e5440b8004030b00444080c1c45c00e0901c1e100c2c8100115500e081c50034825401901c10101e40f81c0810041c80002040e00d030610514802025006542500340d54444400d01e070058014800b480f010862034203d004c03070b10200110b40c15140661902e52840c1300b01e0901d41d1a00b00700500f030b09820065441c892072180c60b80d00960b0480c540c866200d400e140b500070f05103412401034000c0d45401c00e9000c109140b4407540103820604803070b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 942698399 1250 942697149 942697153
    0xd180510051b04081e030906041205010518060406050c04030606140f01030c171e04050604053d0e030a230c0a240204060f02010e0c01090504020a140403050a0302 71
    0x15454000c0c502c0030307010300d100351800343e0810b48403500c1821004118040c40d1004000344ca01c1c0195070800642540c101d80c1107140344501c00d14000c01040303003d100e183d030018000400e4080d03151110303902e0350f92103200500040c11180c41d10046524212402c003a1000b45501110601c021383d150b5040c007956034055001e4a200344a17841c1000b0b160b500a00c101d0714200c1c00303951062122007049000d4243c2440107080e4442500c540d040307140c1b011444201150189200b0340c082e021a0902e828000d00c1c004c48800e10010540c01180c15682c1c10203018662000d40d10b801c2c2e030030340010020340e440d20014100c2030190405c03030000041c90340000f03602141d000702c00002d1104145800b1004c2201d51624024140d00d11513551013941a0b1003c258809807298403100400070141c0c1401651450350140d03040355000e0000325243c1ea80c039a45160f02800303110800c400c1c0030000d002d907421607070000700000040c0c41010b000740c2d800503008500c107219281c911000380030444882e83c1d55035280744c103580d5500c01e14010b40040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 942699649 1250 942698399 942698431
    0xd031b11040c0906020706050a050c0a120f050c030a030902040f0609150b0711120f030403060c1409030d1b0204180501050903040f05150c1501030b070903080d18051005 74
    0x807500445583e415684268001d1102d142000c40039101d0390300001018092020034402d034103c60310108103401e00c9900c200d8454504403501c2a025000a143c80c1c900350500205000129040d00f00000361105c188aa26020840c44814008200201117942c43c150429091407008600c0e60350034ac00c4401380138100a040803c0c1a42c400001103640586400108408254030301c2c0085e503e030280780385105038110300c1035600010690811614680c06544200d0b00d180d22a000781541540008a01c00e0f400400003406140406010000340c58200504150013880306620f200f03040b95402c0d090040c0300d658042c008001d0541e00c08103e18406981c40400c8410f9820500021075640300801130740c045401c1c60b04289045414241005840050b800403459840c40500030300145040400081c03d1412000306402c01e55410360900144445008084200b4044404820800541c100007121003001a211000808400d2000086017030700503800301410f14400d2007440d022419040d07024a020745c071503580400e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 942700899 1250 942699649 942699671
    0x1809010e0d0302120103020f011107082508030d15090e100b010c0f0b0406090c180b120304060509030a0503031e0a090b01090c030608010509010c02100203060f0d031b1104 75
    0x83c1e22402c15a02c8100b40782c40010001410600c0042c261020141061040380e13840944a0340b82007a40d43c00b00846601c105180070842200529101d9000e0b81141c4080f81302e801c0403146507a070311400d440e9408041d036070816480034495011a60003c4c1047d41028403a0071000d000b0107a803449600c6840481c00e150032801c401e50b6024107a481c071034075442108200743c21919216955440c40041007603804944845ca4840000c1c00200300501030f118403800101503401c844a082c0489004080741402142100d410000d01c2c0d0f40002510122110b41c94810340d0ba14002010070b0030140c086000400301d00c408000d03c50100e001e800481003e8002004056140e41c07840608025149019400740940b0b11701c42c010b1011030495004415008891f00b030100f03035540d50701171032401c48104a91410f0b440c0d40d110f00350f07080d40c0d5041c801c0a5070364203062001c0d4254109680000c0040c03802c5a19540f1482180c004801054003d10050000e120325200b003508031201818086110030051080906c90b925150610407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 942702149 1250 942700899 942700901
    0xc03010c03151d060925080117070b03060613050d08070b0a2f13062c060412020126160c0f020913050604080a0f020304060c111809010e0d03 62
    0x140749803025079160001400000c4102038240e64000d15186d02d0700781404034941c000c40c1030064980d903070401c40d890a608248590480400c003240c42c0c1003450704121302c858000640382c026604850050f40c95048240355600350742160701c0300c0d42000030044200140840b000151444e180a40700044050795600400fa04440c890003403241c1064051950480b00e8001000c03801041420040242c40c220801c1c100a1041815a1180300001c02846110075020000000900780d111480c90f48600c9496a000060b002e0085024100358034480400d0038003507a104d07201c0e2100a42c0c80d07030015000861401656202c084040b11142104480344a0482d4528441d0f5681c1044a4001650030701c542095801c004081d1809400c1c50700006450b528a0003090080c002c0764052440f60b1410b965030000b01001400c540340140c081400e64006220401c2000d40051117068446e51000c3c150800900c228001502c80c8484982844420540c10030402c3c0004150320103030700c10b40c1090880741e00082c4414220 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 942703399 1250 942702149 942702179
    0x10c05151b070816030e03101d0d3c110c102102040b0406030f1406031e01110c0c1e01120509010902060f0a1d210c03010c0315 56
    0xf44401400c000f15501101003400110000c1e1007480c21034000c440301c200103845c00340d109480c1000c09503034030b1042030108413080141c404883c5240140a00c450200c0d0060881e03c3c4a15080b60a12002011650f81d00b281454080002c103020084100c400410b1030b00030020b107032580c0c6084861182001034805407800c007400c4000000140e0315000d28000914046070000a401680d010323150b001c0c4400b00d045204800a88040c1006a82c0050980348064160b02681d215a4010000e00010030a1249684000c070b0100149040c540224500101c11100c1174010041400500800710700819035007035480c4c020401c1801503408442424018203460112591500036200c8640070070104224020106a141c00dd95071001020000040d031031816000f09010f60b1003420400114107001a1084540d9002410b2402944c1d80401200000652402084c01c03c554410a5440040c0b8842d400f050280200490b540444015001380054452014090040c1081c841c035410060300c0c180c408202d14032103407462 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 942704649 1250 942703399 942703403
    0x23300f011401090302030304180609090c030b1f0e090f070b0a0f0c02330304122015101406041202060f1204060c03020a0e0f010c05151b07 61
    0x2500603900c0c041c10804000c007070021031410300c80e4590002002d81c2d014000f5100820700d0380500c20081c0801c3c148c010880315030303170480c8118901d84000500851110a0303288140d981c4250144601d40300c0c000c09100164030340900003034014208901180d8800c40040d5540182090000c0b07603001c0c0d580071001ca40b243d03640e0042c81720a400c14000040007610400700024800e8543c00d10341518841a00443c04c0c2c00100c00c540e201c00c0400420f50500c8805034611041f00704c00750900d080c214105551502c01e0300c2c641c1e061000401c03d00303c0200b48407075901e11000c14901402c5003220300840141041d4101810b04840104080251146c00034000d54441c040001d90340c0020455441c1c0390420a40311143e0f0052a81a600325405114042446140700020321000d2180e8000000d5881c29103005000c0d43c000200450405005010080540d174100c010410306a40c2200d5810391204200e004072031139580e51901a000b03104003414040a44050a0384901640c81c01c10341c00501d000301040710f078040c4901080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 942705899 1250 942704649 942704671
    0x612050c0a27030510020c1c0c03051b0a0308061908030f130b0d1b0509010e09190207230c0105070803060d2901050f03030a2330 57
    0x140b480700c14041c000c40e00340600c1c0401d0000140c503616914a04005000b07100390003540080c03d0303014075100300107890700d4410303014442c2d1815514400080c204007000c880101401030124950782540041e0303411020390031000e002c5501c3c01c407031400d0003485004281c642d20302039601d010109031440e07031000c3c00c98103542e0500001c40c50079403c0e04284080b9030003400e240360001c28280b008640ca03100c60009051303804034680c001c00c403425007142195480340114030300d8003440010000c201550340c01000c8d440107030000301c0e44004241c0c0c5860b407a200c82c0340c640c40d003014030902c0058000308002d151a101c44a1061684809038440400303011166143c08101c10b07540414401d000e4100094200c800a40e40715101402862415013656140c58140040c40130304403c400d04000c014100c007480049050040204a4060b00c44486980100e6264032444000b501008507006800240c90f11074a200d0030000c0042c11038551703820340341021030055841031500c0d80003206159071a20228104407903280c090070364404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 942707149 1250 942705899 942705917
    0x2709020303122712180a030501050f01060207090203060d020d1419060e010e031c0e0a03030614041506030207080909130b01090b030337030204091d150c130612050c0a 73
    0x245c0b1207210005414170b5071100d8642008000284203004007405144402c0315010030317505010700a806c147c2c2581010000c648103204001c400c0c0d0f5481c0410310520f806459a48040c409410310030a4040b512184140501c1b5a90825034215a080f03244400103028142c10046001e49180644c03d841d122091101c0756807003805075018011003591310b2000c00e03a4524002a0700c070b421040b524104030002000380d012a8dd00c100070024400b00302c5403000342c03441c2103e00b00000310034449441c917098400d0284008056010032020200600c084c00c031200d0000041c4192090f1400400c142d2003401f0401c41140c441040d10f000190308003050281250604000b001366003040144d024051441c0705e05509040b0407195030800050040000b030030f0301c1010180b5a405070340c441c103143c004819504502014125001c000130002c0a04002140e80c5031005101c0c002e04e5604d8550343d0701d200c82400b070f40040600f0703034903d078500062251700403000040e1030105c154140240d580b08944010036000c2c6011810200c2c07041a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 942708399 1250 942707149 942707167
    0x1c05040b0a180b01031a01060806100f0e0406080132061504050d03091401050a05120a1b051207110309040b040f091b2709020303122712 60
    0x18004200d91545040d0342c14550006459801c0700c45004c0c1e106417103054900400000345100609218050069820100071034104500850603241c19200c40c402040251410f080c14079101d403001400d1060002e00034810a61a200c80c64001c0030304039503c0320848c1070640780c074a60780390f03038140641114400d8201031615940c0c107046c44402150800038581c40c180c01c00c004959580ca481c0800142406607591000113814001da0300000607201c2015814000e00748242d5803070680c0001103c1101c21a0321904885d901c480301c1060180101c100355094404110304109481540a4041c0464828180c8080b2140c1c0300e00d103059a42c100280340500c10380d001080308510794201504145c12019001d000028695204206c84084070600310044494050712400c100003041921a66009000145c141da5804003060283c00b0310608101a00c201160704c030000e4409540d000d0050350000390101c1e000042900d00f0b09c2c40311a0050010340710541030503d00c0d04207454100c000501d5450580f040201c540341040c21 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 942709649 1250 942708399 942708401
    0x206190809010c08240d02090a1d060c0f09030a02220501060c030e010c03212016030c0f0819081605181504030503040513091e02010210111c05040b0a 66
    0x1c00c5a2904401b10360340b202c005850340c0d80340d24410740c000c7c8400200703500034840028561180c08801031480e031000c4180f15000d86103904903006144041062955004010086424143d403290f002e54032590741da44030402041e0b040054000005030007810050350780c80745070540c2c811001d8a03000d00010801400c07420154001e0114402c410b00034107107e44400d2045405011806a45d45150241921040d08203452144880007000103201700e11500d04140e01d54809030206043da42000d010040741b01d1909082c044543c004504164100707281c203595100c46c44040d0b06120318900c0c00320000d8161030005503203006186080c0c1d424642c036030b511890700e00f031560f034481190880082e040d801103002c4011050b1001140081000318441c5015540b22485d00040250512105280400c0395042c0b030920701c005600300c6030021a5180380380c1495441e22840c00100d240c041c00700e003908202441c1c44d144003800d04204024240b810b480c00100c40f4045600310000c030903200c05903001009640701102044c0341180c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 942710899 1250 942709649 942709711
    0xc0f020a0b0a0f0f05091b18041205220f0e100603020c0115080106062319031d1e121801030b0d0305040603061a0a0c0206190809010c08 60
    0x80c0060200f516010001d0b0241190b4080e1001412503001c034031001300c6119447c4200d5503484003220a02004004a014007941c000001c0c4010888904025a80b51050003042501c90070b4600b0000e0703040c0420300e03c001c000c410546004048100c221040c00098440b0030b0282544500e80c0f030980080c0706413401e54164080e4000170840c44040d521b41c0105c1500c04051500350006212400002c1140c40c9000000342c204030305403aa00344002c0d4980e004002c84a907a9040390070924241c48646480d01310100100c004080008000c0c0d02070700d411480c4a40004000751401581101c58079090103040d04542f031940e26005404119404030b010b10480610144c0b070b211440c0880700604000c100060100300080055100720b03002c90110f60082000e10070070342d061040c00081e0a51488010307011101c1204407416004d083c2e203403010089102d0101c021916045d098070302c59070310303400310340c40d50701120002030840e1fa002c84a800980d840c207500c5000552059031a68050715035000060500d0f802c5424241ca1261 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 942712149 1250 942710899 942710921
    0x5040504120305071e0504030606140334080c120d020712140102030408120a060b04050f0a0b0309070603111e0c1c2601060f0c0c0b030a0c0f020a0b0a 66
    0x21880f44c901d86028030b02c005c0d825201c000355280c0760340e0390a6203000c0c2e04688035504044603200301c000100b28130361400030395034805940715142c2c47c40099910403e0440140d548100c02413a0751391480014915070001141c50003d44201c03610035041507501c0807156500083d41c200001a4400340740ac011400d82c04490110044c0242400d01c220310390609051f00703992080d6001c0fa0303900300c00206510410010f1004541140108100744503807403802c0490605800385004480c401c0c0c510300f6401c45540e440c5c040440040c840c00c0c03805038503440c080600f1511400207102c0c80e804241010104100005040215028001104a84000d422107400c040c1025040120f2900d0648992004060700030320720041c400084a155a84540038040081000000244000c81c0c0b86c105000c3c40044c010150021030800114000e8908035900d028a07080044c50852581e00020f0f01c40703000028044c031240c090708401d01c000d20645409402403108402240c0c0e8580c030103c080c0902d40d81d040451158202da402044903030ba = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 942713399 1250 942712149 942712157
    0x409030e1e1c03020d02061b0a02030d0c0906030f0203060a12030219050a11040516080718080a140601062717060615040e18250503070504050412030507 67
    0x721103080400d22482100c504600c5400c90a407200040560402800c07400c404035101900c02418940d280c100444440e80410101c03110100320b120400c1e108005503800c5c841e0001052000079003111003d01903007240c3c002ca00000f0705280102c01031400c64000c0324011540903007646502c9103440742404040c40000c008030114011a800c0f11b40704410141525090b60065000c1c020f07082d2249002c064540c05800d00c64012824202003250034240342d104c01c00b40400c90b04104d440350340c03150412240a43d500c0d540e2540040c9801c000309448500140f04c40a0603c03a650f04405070500ca481c2690704c110901c0390303000241500e0280442640c1080c581c0101418403202c03408443d868910062a1514070415a90240e0098040013154130b44038a0600115161040305850b10782005010625400e009002c0c06849100a541e0030100108100701500b00e1404100700c86105c45a00894070b1031031540c403445203c1d2181003070115051500e4070403103026a9118241001c1c00c0140c00c0294003615000701014284 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 942714649 1250 942713399 942713449
    0x70e0607051b1c0303090503220f0b04030b16030f021204020102010507093006150303030b0a0b18030715020c091f180f06060e0f0409030e 61
    0x1a16400060306a0324400c0000c1c0c10585a003288801c1c100e00d882500300d10405440858201c900c0182e07041e120140c2e09840d0204100206007081880d40c4035600c201542905000500342d491200403512109542a8061000f042d81e5602c044200700d0043e400007410310074840010400000c0d525011f002e003042c090030042806200c1002c0401241c0180c140c020000f03030607504000444d03a0a204e1990300800e2401c000003042c1c20048212040b440c04040c400510007040303500b12140341d40364151010750350300c82c6060144416072a03000320110401d1000720b0209040080007e010f1400c038104d141505d28400280d401c20352021b00d926000031200304243c2e094000c503400850121403d10141a0a9005800401114070070780140030b030a10001340226030242201e85c05a011038030151649040301c0c0107080840c20301c449140988000e000c0041c000382c205180000008ad11381d0030881101303644100310354180302a081c2e10f0a0100361000810f004000a24800c01410f0038030702000e20144510210484840d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 942715899 1250 942714649 942714677
    0x1302062b020406051206041a042018030709050f0a021b01050a0605151e0703021903020606090108010b0a05061c02160c120503161a1603061401051207 66
    0x803a445038021400061002034140a05549100c280d1b41241059504202000c00d01d2040d50b0540f0340f025409104e10748410010480c80d0303010118405150004043e640d40b042109000340c665454088414000c4c0621500013803010b4640c468035114031075000c40c2c0ca03180d540c1c6280440007540400c000d0340344210000b01d010b4000509100705e603c1140a10380004010b4200b0b010001c1d4a10521452070f21007104000c0e80d524500d42d50030101081140c280e6071519003405180a905100420707540705003408981194105040d0300080c4240074000c151143c00d400d90300c50380300034203a5420b40b403010707044580300e8420492820084014062000460707004000c4c005940301c1c400c2640e010030100840d04442c0c90704c00d8140030010420034010f140c009034140c2c0c800c281d0b9807407a03280c1c02440c201d403102d034003200702803014040080b1035142c604035004c2059030700f40b03449000340804070011280180020f1030242c02294080d9819040c00c220001616018201181c480002084800086c80c1e0340810000e0458688 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 942717149 1250 942715899 942715901
    0x10c0c0e072016150e030a050102180a1d1b180a0801060608011a16030815030106120f0c1a070302011113030b04111e0301051302062b 59
    0x10240d041560b030b1181c0c1c40b02c00440808400c2c11003401540941018281003000b0a24803514402c44900b214000c008219041007079516019442805c0d03094010346404100300001035000f44010601c4501c200c41d02c500400900604c0340c014026030402c48160f200790900543d14407003196201c1d070302c241c0e1204040219412990349401c10168516001060300404076580760800c2000301810721300d4003c000442c0341c41c8009045003410310680c40341e0310110611607076005409080707814075030b1344c0400c02c84800024a0020601402100d82c1c054201c8041d0300c2c04124501030142004540030f4085008038246651035418244030b001c1411034448a03040d0000601418190140c502400205481a10750713039035050190943d00c1c0c002c1c4043d03107010b04121803404046101100130907a9085104020b2a907914540114141d02d0044002d40c803000b4580070100c0344c1080c46403401e0b1408194000e2045440f8000f441a20009080000b503020700b05000c0e00c0200d5465040400400c01003050100a03581c1040200d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 942718399 1250 942717149 942717151
    0x50628020708060a05090613050a06050c070209060d030e0f01020102121303201f09050111030115080c190c14150610090308031003080301080105011a031302010c0c0e 73
    0x20140e00226020050030b48140710003070f805040300009201c50b02c0c000403101e4640c80010103034200d8032502e0b422501444010083d07140d0040e800601002542000c41582513207801c0080200d01c14844200008c005003411142d00082070740c184c42d82900c003c0e40300200705803202e41d050514115942030007030315805003107582d40d24014a403008040482c1078090030010300210140341c07030090000400c1c890302440000000d10b0243c4a071641c08100c22500744600ca20050700d881d060180c015800c016421889082c4400258100c0e80004010744031a0044081503e00101c101c40101801506101c00034110710302061078000d492561400b42c240c034040d0b54036080e9001712041c90385169072146a07000f440748202c0100d1900b201085030b00c00103030744081c00020708003d510b00008040e8800071010035a180300038070300c00018540c000485921303580c585403a240282000d108080c5103d07080700400103541c040204481c0039210bc500e03d0900407010340c00641e461140f6080c00c842e0403144460002c2c074988400045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 942719649 1250 942718399 942718477
    0x207121b0804091d030a09031205040305060a15050102010e070e041b06050304050c010305010e07180b0c0f060c070206180d02090403030207020a0e010f090506060702030d020d090b130506 82
    0x81c130160a46108030302c14942c8020764505500401c1080d07512908844010201c960001c6840489440920200e4242c0241d500c01001e51280d0401d1007003829241e0850052071202c0f40038801e03815a240012403d0369541c503c0d88909070800d1400b030141c1200c0000f201c1e8480d014100304080d05d208012a01141801c5074802d8001a5001c010312040103401d109505201101340703801c0c8020b505001402c014648007800220910000e000c0e0460303040c4201c044500148040541c140d141e080584402d501c2d0080b09445814901a450004148144280c01c0d03076050387c0c01416160400b00002c00b042440d89542001d40d901c40401c079540401690f42e0100c061080d0301c80c1d5005a00c91130244148030184400303402c0010031465190042c0202001d8400003030448a0200e00400c090b1101c001040b220b02c54058003940601541c02440308090300003640001040803607031180c15259941030340010724020050203800c80b2007441c42c100181c0ca0500090060b95030b0610b422281c4411170001c51085032280042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 942720899 1250 942719649 942719651
    0x2090a0b0a0914040212180f0118050f03130513020408031314120d050d140f0103050f010504170c031c0b030c060c0c0d15050a1407030207121b080409 66
    0x1040c08036a4464107103ca400300140e03015400c00740c4c1d250036002c8101c00200002000c1441d0340315013500304400c0086c031074181c0080e4000c02c07265010400c14001c1c2001a10180c60902c60303a200d101c0078072400001c441c89200c4c00c0354a11419814a010032a43d0800f224a010780300d502404045107218051008081100203038541d44041c1d403502e45680101c8a10700c0ca1988602454400d101284c1c501013440c541e03035400c500e0626920810380b51342c000108030410b10352a9401d01e12040141844104e12010b06aa00a0301140d1001d0490781040f426208100da0003012140803484507159013a01c01d01901c12541c1510070f5900f0302d0050321000300c608520302170010040b500c3d035800e4215030a06100000240906454032031520301491707022580d80380342400f054041d000e40c61010080c8401c88442e400361030b02074041448207003446003244d03002d4000aa21040400d01c3ca00100f500d940c00307442260b000c15408410011071001140c0c0a9807020007a085428104140000401c001001a801440a8422410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 942722149 1250 942720899 942720917
    0x30108060a0c022e020f07050c0a0e15190503030c070905010f032001020a211b0210320706051e040b1306021b0c040606050a0302090a0b0a 61
    0x4081064502e50b4203154195084288140800388420b0403411008060f032080000032005803103568001d00c62814a1108000d02107030010400030301140041514a080312042c0c01c0d16110704088501c1001903c819407003145100c045015801c1c1141e42c440b60700b0b40714441d9900540d5402c0840e0840e130181c62510a0340d040f20f8000e20100e840303841481e014011a11607039411504540e90450580008503c0d905010b403900050030240e0b1080000c3e0000c2030303000c1805014044210940901c1d94812614070011a2050004a9442094211200c0c21b590001c140d600d5200d100201640e040d05082a003402d8058800b4020374903941a1012140c108a5050030b269a0216810500308130f07840541010440403c405060901202942401e500300e80c03c80301c4040c19072540c1407ea100070240c02d0004010b5800495103c66100c6118100440f40140760182c1b154281c90404210444840f80500c001050060140c981418460303800b9250010b800380c1800d8045480304c0080d1350a400c03e000d0000020300d840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 942723399 1250 942722149 942722161
    0xb03060310020a020c0f0a030c0e1b1206040b030106080d090f0509010b040b0c010b04050a09020301180803150621071b03020705060307030b3a02030a0b13060203010806 74
    0x140750080900741021400c204001c01c0003034403000d004082c680b25000c4440c030b002e01d50740c41142c51402158019801c0c0d03c0d02d640c400c1e41d1914000111480c1d0881803002c090740081600040440700c0c00b2520401d914160340d101e808200040c45d103200c849070559a03800000c198031b0810400c072000a41c560b1148241c8600d0041c00d0a0641c1c2c050f0485409070300017000411821685a064a082d10382d81e0f0a0f850b221080250b41c2030041c0b406480d0f13a0b91290501f030900406074125808210342e51b000f50000c2c00464440c3c02d10b000d02c010008801441c0321410800141702100c0318860300340d011030050042d071910044505d0340c0d64056407001220001d002e441c090141190300840c50324201c403022040340181d4091610083e490340e109109aa00900f000000624098030a034402c400c0c034400140b100b0804034948000c40c00300c9031908900c0f0007400345002444040345d034000020308423541c010024107065500f9910002100d50250175408040144400007001600c2c0340055800f07010207000402444ca000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 942724649 1250 942723399 942723403
    0xc16080d06080106050d060207140307060c1b0209011502010204120c240903060b0f060d050105030106270c02011d060405060f0705030604052503020d0f0615030b060d060b030603 78
    0x359202c2c0c1c0d2980e240c40301c00c110705e488400700002003541068005803111b0142c02e14201c40403103128043c13214000010315004002d40d035882482c000e056a42d82d040c41541c0c40b40d04070703240d00031180c021703500c0680e42c401001404880d03680100000194400581002da480f414081000d4002908a032040041c1400380300c2c11804822540c0b640d41a03820383d540d900c050800244c0103940c240000b4040303030f845510640e0b07261140d02000180c848090203141c0d44008003160040207200030301035a84070f075003846000500004c9010181d0341c41340068179040c1c0f0111001707090f20000d08004940310705554071951200f5440b4030400c41054024400b80103030045240c9071402d20304141c4000c01c803044103c0c2c800305001e0b4581d8080c0547c0e6120009850001c0d4645070b114040b80181640c0d00a4440b8004507034020192652640140c4220304c51448280880c0211505640651392280545600208081c0d40c1e1820745120760807050b0120000740c82d4a190130061015901540c2c00d5030840d4151101c000140701d620304007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 942725899 1250 942724649 942724661
    0x90c1d130908090f01050403080708030403090f170d0f120510050402070c17030f0d090c08120a0e1e06161203061401030b011e2a0201090e0103080d050c16080d 70
    0xd00c2d00c246010708540c5d27901e20764004d22101800c0610301000281c10036008481e000082d001d4211180c01e030b150b8480084003060801440501b043c080c4d036003010f901901410869210459030345625560801032400d000040030300030700440380c042c05503000143c0390700e035440282039460140030301e01946414040e08988652000520704441d510404c00151110380c43d01c1030320542c410001001c280c60005c1e040642030500c0c0e541145055000d0a000359458440701002007190700c425447d4602000c0002040040102103002c43c2e4111b001c05040e03043d03da01e49034005284100d884a114401c1340c14985507004c0003c010341402e4040f0781d561006120000c5140c80115445174246024421400d0150000b04180307450044860301c0301403000c2c5a44043d007e0f110820b0702031461100c014030030120028504030501d4103201680400d40c000703000b05000e101074100c1416690442d07001e81c07500d05466094001008002c1420301414414060380f298a0b207491000200c03240264512900c540c81c2107820022151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 942727149 1250 942725899 942725929
    0x40605060d15090f150f03080403110607021008010501020f030301030b0c03190f0c09051c150905060a0b100801060f050307090b0a0c0605060a0806160306030212030a0207090c1d13090809 82
    0x911b240d0f0801c0002c0ca81ea089a00b503d0b07101c01401c003011225000b042050165840c025840000c0c101c155203030580c8144164100c803c00d908a4500511210610707859100178080940b0080e864000262070b0005417000f0754200f001746115090011184a10600b152261000c211486441c0c05da43d01c0c115601801100241008680c01121480403094190362408021401490310700c0c01207440c80321801da640b103942ca0b1a00441034881030714100c07807d14014089851200e10a2a0743c0620103012032081b86418103961450312001c0040341100c90582d00390300014020002c00a02500104848226201420042c08191150303d5030034050b01d00582035840013422280220540e003820072005400094568001e16051904848070040e450704601601c0e0582010b900640480c0403681880400401440c2e02c544603803d540410741c50b03100b50410348007061441c400140b40710110b0102035000103040ca01c0c0000c0100400650071521403103000382c8801c0304064842c003a000c145d003046400e001110407001c0d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 942728399 1250 942727149 942727169
    0x507021c090f0501050301230a0b04091b0f050a031119021f020a020309040b0f06161101032d0e10020d0e03040e040b0406090b0420040605060d15090f15 67
    0xd0f04003401190407100441e036540c04c84100323107200840da13111021580b003e0000e41940c259a02c7d25190180c02408050300380c2c0800014070600e0310502442151681080c800c2c40e0744d0795141585c48401103000d0304c040759105503480d50801c41040c80820900c1104804203a0350050a00610035080c10107103c00043d03e4402d1186c0100940d0607903590100866201c1c0f203045074001440c2d080c0700040b9001d03440740c0c50290307000000003403101ea0980b4104a41da540603c240c908480001d4168011000d445650000f40054815030300c2100e1000d00418441e08034026100d40014000544c80a8515081c0040b0780355074080d90000f0703980c0c1e12300418054070b0100418000258541807070241d07542c00050005101419210801c070101e810003100d60809441c1d0b641144000c0001c0c28241000018642d4032007074400c1894043c002448181405e000304021074100038040ba05044036865100c0c00703020380e4050504e2500c032090020411440394403455581c3d10029000090134810f0072140640c2d0b40f51038125031024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 942729649 1250 942728399 942728401
    0x1060e1914010303050a050c0c06120f0703090503030c09040209040f06080c010503010807151205070e01110c0d0b10030f05032a0307030c0206040e070824010c060507021c090f05010503 81
    0x130a4000b412a004994a8035005580b0110340740300904201c0d1074048950700440005480c4180c2e03103032007017182c0074183c0180319014907102c10000382c003221008400240681c00500c0080d00a502030000780601c20005400940317441c2064000900722038002c014443d085660301800d0141070030411210b2060242800e04621750f50405550310b503680e801d403040e0300104a10b144503c00c114410f070b140859503e04000240058103107150080c0100521400c8140000c6a080e0140c0480c00002108031082101030b103900003001075a20341d03000c441001000c1d9a0580810007000001800107803051020901400155403104c180800300c0c03416800000c40a030116a096040001040000c01201c031015414288040d20200601c0070411034080e5510005075692500701f004070042d0801d60862017611088104002071001c1d820018034002030490050000303401c410b04100146150380110f0b0824050300454214504084607a40041c0c4100c43c42c1001a08482c000c0010680003d015030260209082250071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 942730899 1250 942729649 942729653
    0x90501090b010801090b0a0e0307020d0303020d1b1b021c0305031503061b03280b0102010e1c18030c06020f150103020f0d170c030c10060b040b070501060e19140103 72
    0x10301d03070026020b458030719030701c000500d40b00d030302007048070703400c1e03030b000d33107241c44180031414041c0003034110300c04d43c0c1645410084010400250010b03041c6040185480300c40400c0d040b01006a074540386521b040360010200c03841a2000e40c3c50074246441140710f596155541c0c85d10078050058000c481038014003ea00810500a00b103404d00072200004911412042d101d035180c0c0031100385008a03020100d0074001d06948070032081681d40194612940a80003403182908114545030780306071104a5a1040e101306022560f61485140f480e100c032034804080d6182240c82e6210342c0080a0f103640301d0030240c0d001d10300e051401d5000384141844042c19445520a541c075607004640218211100c0f0740c4074030080d81006042140d43e515101d9000c002480c4075480c3c504030030015550340d004d08001001d51040502078503001603240155002c0d2070000c01d40d9410140780c441448805d400001080302d0f103540360383c0c000c07482500f000429842100c61016000054003505e2a04048074030310440308241c61041401800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 942732149 1250 942730899 942730913
    0x21006300203061308070b1501020c0d0803010611010b090c130801050603070608040f120f030f021314011b0b060907022e060f0b1902070f1401050d090501090b01080109 74
    0x984050f0800e103002e90700e204c034a4200028810880000c050150900074400c65070881500c500e80c51000381c007215800e1910b01c0c10130500f808030103002402c940e0100014803600c1e101e442042c4034000301e0400840c66040c101e0000740400340c11600d0080d440d201044040c1c01c0003911100744010280704008010505000020035110314142c0901c10501c0a078401007020800b50390482c4500c19045039403001d000f814220000d15072400c80752014002810142c12154140082c070841d1100b0010030750100030706240a40580c0e8881103094414144800b0802200d01c1903290048000400c6c4140e03107070a1549000c104000c0c042d80040d11030402c42d1b10000788101c7d030500140c00d6801c41c44200d2194032594406c0e0880303501526450300000c0004108010004402d0602406003520300030300301701c4001c420340410089a443d04240314500e03a02e0940141000b00c4816070180c40e02800042c50101e14248980071204151004010122a02d030b544810510a1003001c440e12409060101e00034040c036080d980b9100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 942733399 1250 942732149 942732151
    0x50604150f0536071e08010e1308030c090301380f03010207050f0106051203120702031201080c010306060f050720151201050102030702130c02100630020306 69
    0xa0041ca18030708809801c0201d920000f03450001103a9195103910402c081d62025001540d00310042044d1400c00201950048856041041070380d440081aa10b021011407051001030300d0b502000e80d508154a020611020041d4030440c0150f0030700395102c6101052608407200700c00688000340c01da20440885440c2e444d0f10b400d01e1900d00c0d21210040790018000360328680410304481e4035610009440c0100800130400542c0080e40200801015983d00d0600107802c1c3c0307251081030035800402000c0068258044015001070080c41102e05002000001181015080c0c212687d00d5001a51001d215a03040c000c0314041c164501c0c00e03c407240452440908a8082d544c0f00800e0022031000c0600b501d18031440321281c0500050454210420030014074010380d2140c03070228125028000003280d036500000c22120269805402426012114a04180149a031f03100c41d8086000302901c01d03001100902406020b4540f50380b03000f51076050005002c2300c2047d036590309840c140c02254100d001d660003113107007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 942734649 1250 942733399 942733409
    0x206040c050d060b03031309060806070c08070f1703040506070216090c0c020a0f03021809031206030a02150a0908190323030103080403140c0f040c0c020310050604150f 74
    0x868582d04071450310802030700400d104150503200c04945004402c0520150030115408000e08100541e210087c2d81d8680f0b80c00c648910114114041000010b0000030003001268040c501e00103080101c1d981d0f03d00400c0717482e07a100c40300960120501050000510241d5040b4085000401108951584014a4001e28400c1c40d01f139a07900c0a03910500350080381403a00240e0300031300d860031460725203840100386505800240d005070007415078030034450030b2410324601800c4c410000b1410429142d03000b0a2a500c0101225054054072800e40700580322140e122071010081d00310a034952600307910060130a1250360000081c3e178018007201d42082211080340c001170b501458507841c181504503c5000f21700c0c0070902e40481c030b80004000030078414000090720a4a108410740d9440c07200000b2a913988816040ca81c0d1760004039101004468a0700c0d500c402040300c1a82401c1007010542d0300040d0a103045500c51f0294240c40300c0c20080725207094815116403581000c13220b4100341c10010652903c1d0454011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 942735899 1250 942734649 942734659
    0xf0f011401090e0f0a0e030a0504050f04020c0105040b060418020904060203070203120a1a01090b1207020c1e0901080d0c12030908160218060f01051c0e1b010206040c05 74
    0x502441e446200d44002078910032400300714074201030800b12500340b0b085500d405407916040c2c00518180b0040102e03403e010055680780c0c2858100003c0060414210215a501503403c000104400c0760070300540f031040c1d00500d15040186001030912082e03a0500ba40080490044000000140d84003400140c0003030f0401e400580381d98403110140c0c0385119060b40591500456000c00c005d903151a0419100c1c0b590942c5010304210b109001550134104601440d02500000d20411814803450b81e002c1d41e11100e6481112102c140e2440825165054041c0640090b00d01090740109030810101040c018800301d40140b0000b0158080100031240041c401000b40c2d019481003900c00340700e500300c506000d8000b1051f0303540e1002c0c4810402862034110041340600b07804032100307040e451400d100c584911400303000b41116000b071500440e01980400703040014882021001d243c0c0320f00510030208555900700c001d1180c1e602840820610240780c030503842c11948240100070004205a44810444400340d034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 942737149 1250 942735899 942735929
    0x6040b071121011506080612070e3405030708040501090b0106120c020d020c0f04150f06021e101e090b0612030c060c0f040305030f070b0f0f01 63
    0x6403074480d0007240c5990302d03801a5a160b4402402d02d0248081c071040e50050000c2114003145548081c403407003148902004110300c4d1000a0311810400132401200b40410180d420140e10b80c10303101840c00e02680c06803402241c0043e1000401c0c544d00141c810446441c4200805010010008200c1d200080c6100100f00460010904120094004400f0250b0110200d034203507848001c020418001c0c0b11000010905002107040f40c0c2c2c0c004103a801610030668050906842101c050200d0182d200400e5900580d842d4094141c2c0350743c0340f807120b01910700100d181c81003a00d4417000034581807a02401c080c0003850102040d190300320020f06043d00d030060120203d00e415181f1807480c4140c0340100003010325410144000704200030709034802d1145e0011285400c05000148151f55240100101490160f0201d40030400112000000d048900458941149419100d5894600310703007007034003420208075000c02c002007080482543c4543c040c04d41c42040c1024900b00c1880d000c5210103208184002c101a5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 942738399 1250 942737149 942737153
    0x7060908040b040b0304060506010c0203071511060a02070c081b09150409030201060302090c070503040e10030c090204090522110616031d0301020c060a0b01030f0f05042006040b07 79
    0x1c1d28001c045800d189500c1c0e96035507085082c141d204440896200b85080d0010b007066025801c01042c10340c024005040c01414008007c200c00742c614010700030701841c0824050348032400c0002c0b61050560f51405a203c4803075140480c1e21030f800e41c00480341500a0885101005000070421550000490380039126440c3e8230520f150a0f9210803585421604162900007415015000034003144d100f5541c84046030750b0501014903900031014010902e030410070040001f80204001729801800c550301c50001a9500ea84502c40005590b10080f4000c4e00481c0404c03020a0900c1203a030f10139240c1c21040406030f031350300c442075070742144030320081549280a28003100c41c1c50310419078241c106030840d1410060741e5030401901c0d50502c0b40100c20300c115041401c00d030720300301030090b14000f00341c42e40203006031340b1820300c1000600000d8010904041e0b50f80b5030321140969a0140d000c050320f0341d0100050a04150500c44060380c4085000301410710403014802c03064943c1030440c1c0c111080c070303c220743d02e8112078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 942739649 1250 942738399 942738413
    0x903031f090624050a0516020f0616060b0a0f0905041115090906030a0b07080903070605101401020c0312070611040611190302060114010c12080105010e090408070609 73
    0x181d0000440070307151038000304030891003a1100000c02560004a01c601503034a900b225030780701e81d42901c00005c2013800500c1301011201c2c110000303244004c01100d2030148900100c0c20b00d41124051780402c070150201001802214032400c030740c807401600c00407080c0b800c10b80082d85000b95403180103901903076440050140f140c004900880322200800031008402c1c40aa100c2c0070750450050306104415140c00724496103000120302043e0f640c0510214100d40e03ca07001503e6004000b002608503000030020b40c2c3c009a40c0340700d603511540300c585180440074140b0311403c1540307110300c03281c0d415035100d01c0e030015455800091890000c07000000e803d0b03070340350185044005400d40c1011032100c0540483c0200e111500aa030380701028031a0300407130b8820b207044600762074280103010340a805600444010310486c13884020505841106062002c1c9903040c99a610641d0f00c0306400345000168810010310541d81d01c408140070a42d030460360004541130507140d4400c613109064004005680c0d80002c2c0b01003002c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 942740899 1250 942739649 942739711
    0x60d0504320c061b102412120207030501020a0810120309170c12010e0607090e01120314030a050f06040204030816031e020102030105190b1902030904090f02130203090303 75
    0x44c001d6504034a0010f6950014000d1142211841da0740e5658050105031208080d0080712100c01a2000c1e046c01a140d04181d036078415901011406040c0c4d020000c22024002080d01c18110ba4611043d403910310310699082409420401d1040001c41840c408640d009030b0000607143c4500d041000e07488a07250007480c100d11840902d41000459105500c3d81c1019072001a5484110b0192a41c1e40da0f032050441ea810114000e0916190300440140001c2c1741c450418400c00d4424248148010144800650103410440d043e00803592140300300300d00642010305240c0c00a80c251000c1d8203240c01d5645010315401904600410400350031050002e140c0700720f290f110000c9900c1d148417045200050001c0c040c1d8401d0280c82d020740b265000503d501d0f10b26200c80400c640f01c0d1084a82000e40c50001e08050788031040b1110118030081c03020381702c0d0350303128843c01d00894411645848020024414400f0707240c0c4c941e4000300014414000c00011500100449511500b560540844140401506050313240707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 942742149 1250 942740899 942740947
    0x30604200316030501060e04050a0b04110405090f0c09100e0c070b09030301090b0a05060a0e0415080c01120c0e010f020a05060109020c160f1202060d0504320c06 71
    0x40751404038622920030004602c01d4a00400091062580315001e2000d004001e89000317220303502058901001c5401041e01c2c03a0810b20420354000e0079100300740064161181030380d0580d204c0d004180030b00d41e150820800501e540f035069945180a1402c3c0b20b00050742d4086104481c0316820340c40004585501d60350881f24040d0b444503d0b60041c3c00c196140035a250004d006283c0080e181094400c060b18001d001c0004940300100310a00d4400c0700202100c1614111860a402503203a1882465840e0b0707031001c00c0050101000203124060601d4001082031084800040d000ca2801d9a2413005a034070982c0350301c0e00042030070030001c0a4000c2c9012403414103003042c0544940903400c00801c25407441d070000c0104542c407004840714501c406600f0400b0072135503c05c01c202c071259060100301e1443d0403203070481210b00080420b410604401100000c1d00c2d0200c40807544411480401c10314a41c140c0c144c980c5040a00e0b681d0320240c50300601e5241c1c1e1344a406c0041c0e1084a0100d55000103166240003c12405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 942743399 1250 942742149 942742153
    0xc1c06030602030c040303020d02030f0a0f03090218060a050d02100c03020a05030408070e071806081503030309012003040c14040207120c030f020111030a2a090e010b0304020306042003 81
    0x841c0001c0fa1181e90f401500041f0018051070030032120312407000050320f40c07440003000034500d02801028186c40c04000b0840003000e00d51608014000741e034425442c15000b0412040c010f50b9407500008201d04424140c000c207100c2c1210501240c090707106c10034000c00c0d900007403c1281390415a800d083c1e190060507031000704144000580401c8103000410074400300c41d4504001501c9454910043d210580354821710b0300414604042000a9486074001c10f4106108416424501d202040130a041d076101300c4900046a4603820840100d900302c42c0002c0c20030040c00384003070550074683e135110b0070383c2d50511036040c490103185000e040903074403a0b04550b4410350044203549070b4800440c000d000400d8040044d00807481c00c003404409180180103c0c46055220311106186d131351081c040364024220310701003100d4a0310070b1461781f9503d0940b91101003100d00907280d8805840ca8941c00c400344800581004004600600c107000040e14001503154000d903100300001d0b42c1d0700414448403d19044411074617414 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 942744649 1250 942743399 942743401
    0x190204020f070c03261210080d02010b13090b04150605060a080f10050d300216080a03050403020f0f1e010305090127061b110d080c1c0603060203 64
    0x80c07680c1c1204100d81c03240507140c030456414a102401c040b108a000308131001d00b0805200c00c1c00c1e006403020340c001e005034001d1247caa154840e8500d04558801e402c000360703548400c0581303940340150166132410b40100d014031603c000342c2e40740781d00100041c0c4000c2c8103000c10304000c1c0840c44a9000140509005040c1589039103c444008001807000e0f00c207041409503440115030340341e41c0d0135407400035910090400000410baa9a8840860610400e04907091101008511040300111881030001d0442d03401020b0b1504030248200d5074101c940c1c0059056401240038a000075001000e86040702d404994010144081a0100d220404050700b02a842200d02c500502c441940d0880718005079000e036003c01c81640c8412007a400c940c50750380d24001c102092141c407400404072940810180d48900c3c0b01144203c0c4148081b2110540d0440210108011400e0600c52500c00c00503607000c520a81b4000e1201e0420180e1400588954203040c120020140e1680c0410341c03ca400450046038082421940e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 942745899 1250 942744649 942744653
    0x1020d2712054f170a02030615030f03070507090209010302090904060515060c070e06120a0c17160504020a09080a0b040c0e0c03060118080a0c26190204020f07 70
    0x24044082d81c20900104400040d040c946a603a0981507500f942c3c441030750120b40c20441c0740c416551342184d801000d41310310010107006803000d00c40e1030701a00d440c201c01a4400300d6807041504113408518020701640c0700b400301c940400c0300011000c003101c1348000c0041e503841104c00120042c0c4202c42e2110b8211034040244000c01c91203920a0744281210080e0102406d1880100039140c81040120b8606a10448050041002180003c1e420080c001c05e000c2c11081d141d0951414810340d140300b0365501d90404004c00c2100040c09460400c100b11801500036404400b80403603c1480600415018035400b00d4001e14003406425118050041b850450f0140d00c0f09141170b620404007218112102c0040c2200000c400700d028100900070140d400d110b0741150380e40b500442e0b0801c40304442e640c684c40c12071000142c040e014024141000c0c000c01240c2c0c5000d0902c81000d0451540803c008210300c12021008414040800c810680d0b10b40c0d141904408096800014080e0050b1404816035a4000501e042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 942747149 1250 942745899 942745957
    0xf04050f1305161206030c0504020d06150e011805010c140f031303060609020a08072105090d0f0906050d110405100203130501090320040908030901020d271205 70
    0x1e580ca035070303901e40d5150803404d108419204a44001411052002c40900c02481e264001d040400c02e94140041c1503a56018901801d41c1d082e002130011541907414010704d968000762002c6542d69200343d90100303d1900d00001c05425408030080e0800180540380120301d18203001109840402404490301c540482141c0c400741c0e0312900c400c485552802000040c0e00d40d960094458a100685900203190b0b070b4414260350303605487c0880301142d90b010030f01143c10100c0b44603541c0100d0040c0014025010b85047c007070440120a503508060114403813003000141d500c202229407000d0107038004070340d40c41d018400c001140116040168010180304148450650000241c09800720000c100703899203981d000151000222800040d00142c54002c01700107118004202400303218019200003048942a102c03542180c1054400e441c10381d40000300003031180401e00501d000c150407800801010010000181c070000396055000301082406601090103078018016684010094051642e102c4c004c1c91880d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 942748399 1250 942747149 942747181
    0x120c010806040903082a12010513110307030b01110601121a01060509060c03090d0804140f0d1b080601030501020a030f1a09191a030c03030f04050f1305 67
    0x24002192200000d450349020700074205601d415841e2000307151540281e00d69040032400408480c03031038030a1145041401e0030010b04044030083c9604101d5410482041001c00704503c50f07032110790030821500c03442400041204c0d081805418002a410414001a52856030240d4a0034450240e5400010414071290440604522031000ca84004550b880c002440380820f001c5e40c00001d000b0f100d840c0c070302c3c24020024207100700e189085901f45552800090020240c80904550200c4080b804000450615010030f01c0c0c484200c0d481540404c034100030880710303904000003405c030041c403180da100c05c00d00d0480084040c0c07500605403001507850342407890203540411842c1f000030b0300e030000300940a903d900c602c2c04092500e21a507029054210100203504601801804000c50203500401e983ca081e0f2040c0206150711401401952000104060034012446c01d80d034042e400c100700c081c0c203008100341141c041d2a0111800d066001c03200011070020080380c54214059447c0c241401b40c1400504416 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 942749649 1250 942748399 942748423
    0x603070309231e070e0c04031407080c01051c0510050904080a0f0f023d0911010221070f020402120a1b051803010e0109030504030b1e060f010e12 64
    0x4844074071441000800c07000c00c801403003e464101c40d0040c0412441e00c1442a040325240c500036003055146e03141d000203103800e203540c00407a0788401c1e4100320383c00081c001080c081909090032800c110146035000c402c1000c10000701c9900d550380c000200c003502d50710234070005400041e0442d446072802e89440701507135012803140d8000c00d0588407401180e51103805807034600965540648282d2486044a50344204540825400c0440750444219040c00c6000d841c0903c030b00208020030100c80b103041000100000740e0482d4119000507041e03882440710300f070702c51003140c1c1f813460340c1c03580d60829040004030304801e410b00a40c800d00008503424030b003011841c0140614105401000f00c200010406907081d0708840060012a0040c810784140c22043c000d503412410300a4000f144610800121500b144c0e0000c004402007080814140700348124510a10360180ea40110b07403910010640071400d038117030001c2140e4441d005582e1005816403242c03d1500d0600806850070058543e80c1c1019a00c603044a11340d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 942750899 1250 942749649 942749653
    0x4050d1101060b04050f1f0203041703090916020f0d0e0910140d030207030c26030f0412020f041104181b03051b0d05070f051206060307030923 63
    0x80c0d103600c100602c141d80071075000312440c601e040d03d041c09100151003280c0324154010400400020060b103104132085004007658040c5640e541404101000030340c01503009802980203104402a030380380d5160103600305111001d1601104004131080340381003c0c0d24007086141c0030703c0c0100399141d078000c0b4040a1402c03080359000020343d140341071082c03254207901c076450b075219a1090703440181c1024058040b0701c1e4000d106a84607103480f51500d03c8400c206500c4415404e6000780c40024404810000d030004040e039a0195162400a840c12955401103009202505044c12502c004550303031010400c810344005070061001c030f000c50a1515098100388100c034011081c0309158081091180314840406120150101204202410403802040014209810320020700f0344000794110300400f90000c4503540301c02044504c0e21010042c50100b200c03202c86c0512400340316154003260742c1905250300550540d28070341c80c0d6481c03580c00c4004d0001c2d40c5000c0d00c0c00007680c50b6456600654482c4000e21501c29003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 942752149 1250 942750899 942750917
    0x2d0903060c02010207030804080c0f1f0b1e0613180605040f021201090b010516080a0219030206040605091207050304090b0604030c060c060902130e1006060509090a09060504050d 78
    0x18040e400c4c0c1c0700f0010003c0c001120800041c000410050140c074401b5040c4049501d102c8510307210b030b0f282813901011410380d000780300041002c006041c010401c90580940b0f004d8412000c40f2503841c4d5800031030008910585000c201000c81c0c003944c10001c001044441d9540e03002c021a6076080f8010031841c01021f005500f01002c4c1d80c480c18080c000c40c0ca501e5507841560700580e10701a00341d0000c25500d2074142c1049002c0046e030390a0a0001021280c450042d140705907114098034001e0f1500002c2c100b064850a03440c03070321002290f00894031039445900040080340c203981701180c4901b40070101300e44042c5a40045906014440004094000d03242c01050030441944c1c02e00400c015400703940300c018100c009c90780003441440c1c450070441c0c44540c4689000300d629a081d90000c0e0780d13045281d40005030035590303802d000c0c40342d00100309821041440e800200850340c00e29000400b240301d8198014040c03001900455240c24003035020715101a004541040141028505243c544464980130400145d20b00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 942753399 1250 942752149 942752171
    0x1020f061902070203010b040204170f1504150b03100c0e03063304020d050403030c0f270e0c0405030615010804120c0f030302090328032d090306 64
    0x8846018038000201d41c0d8201c440540500d0180d0b124a0301241c1654036a0f900740b2141d182d80c0064000b400302055000b4034800740c02d110350310b000022042e21490f039110018640c091100031240c03540198100c2c1c0c050f06020225004c030400342030811200340d0107206160700325008010307591121800b902c0c2070752440e42c181500f80416940d000141d54003242c40002d48003100c6000c180da146080d040c0e0488d080025048407050006003280c1200c403004c620a40c4413003c201c2011740c035101c1c41148079030604003c07c44222042d0018001d450b0380b452501604030701842080614941c1c01e441000380610214000303c0e10344490032880c190420710400c1d0007407058002103175004081c11006000300906a54000613a9190b4851b4844070309800c0c520018804242110707000f054441001c958a00d000743c8016941c1c9058900781403a240415000030048040e50a1040b64250403051003031b2001e4141c6090620884072201d100c9100b40040141144958a0210303d004560071080c80801c9900649080021400352 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 942754649 1250 942753399 942753403
    0x10e0106120209070c17070f06050603030a08060418140a02010216030b0a02030a27050c01090503120f090a080a03090e070509100509100305011701021303030f05091e01020f 76
    0xc0300a41c0840d101c1c000681c418070820509a440d1b00504401414140c40c0c0400d12166100740c106440445030740360391109210260103000d82000c0180e00a40c42c1c4186884000d00507a4084e0815110703545842c0389000300c0c1828400d5481640e00302c0b001c400c6d4202101c2d00c1c1542c0e1400154100c1c094000d100e00c00381100320003481c8504894021071042d000c0e5850260030b4000b0742c8020102e800ca41e82c3e50f0240b0f8911001059000030b80c020014008241a06904103246002244001e03103040041e4210305000d680c03408990000402c5028820355140c52207103c21018a005424000750010607140001030b00d900006071410505000761204003101e9101c007051b0160080032641100817600c10001030109040c10181c2170351071041413504a0a2400e504001081a002c4080c41c074000390b1944014001d11480b4100040000486802180b41255401c088080c9031000c0c44050140300c10380d104a290107014104a8058810090054000c51500043d20110015030704107140140300780044294811382c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 942755899 1250 942754649 942754679
    0x61003030804141f0504030305060301050903090d022407061404020d0b061815040612030e132a0813020f0d080417030c10091a0423010e0106 62
    0x2669816100d642c603515001291a01e111140c103142c4070b84020344c00369618030350001000101c01c0c0b00c04507207810036060040035520040d1065210ba450442485240b080001c03c4600c011019101075038180c04500000d44001100001c540740c0b149050a00703444580c00380c00814040d8480c000c1080440041c0d003145076010400c950080d00056980d4505010905004510398480c60050909141141c0c00c0c0c003070002d021040d680003400000d440c1c0011041e2926024140180820356030b0004c0030039407900d0007419000d0440f801405140720f581075110004860f0031407810903900c0506c01003401c5030480b140d134005035005107001c002000a0045024000360b01400200305400074000072189441d03100f00302106040e40000c4aa00004100019102030780072214143c8030b4050019544034204001d81501301f00d15580710340c142c00e24100c8a880007510310140c05814400752564002d859403549000344000c810990911908401e40c405041d50312015009403025101680007405410754a5030300d9218003030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 942757149 1250 942755899 942755903
    0x30f090506070b04080c0f0106050f0114030c09032107060c030203090a1e1b1a031b07060902041a04060f06271d0702070608130609020f060a03060503061003 69
    0x70301000711101190320811030030b8220707000d1501c0c0752400489041032441c0c03543c40441d81c22643d440d080c00300a41e10f09603071b000794a002c5c00e080c621400700b1030348030aa80c03a101c01440b00105060110f010007a94804210094010a00842540d050b00031043c50148607000160111030302ca0900d24115045c911900a8a0240c0c0140d001040c1c1a5055a9075507260076020218903080c0d411070f141c42022603030b0000009501003450310900010b0f401c0c40d803c2d034042c1ca02412120102c0b0000c0003070000e1041d0085482c0e4100c00c2180b140340d11030a4500d000c8014128003140a036200d401c081c407044850440d030030000800501264204035080d554001001540100e125031000305d0500307800505e80303448070300c010307140c048604140d40300b080d0301c1d15500700f50310403c5d0764010b004080b82e0080040c01601000091701920309130030445000c0c60502009083d8141810b8010040c0c0d45800c0110708545a454100c0c015000040005071a1800c1d40b00003401481c042c80b0340b503c2882100302050700e1200c00274000040d20713 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 942758399 1250 942757149 942757159
    0xa1e030c0e12032a0613050304060806010e0a08030a0e10020c0d080d060324150506070627150c230c06041104050a0b01020c130605030607050403030f0905 68
    0x700c010010005100d404200d1192203000410030010403c400000d01c14a0384504600740b00448070b121400f0b0310b0480300070620000607201c155540049000042038404031500d525110714941e84032001210014201c404003030308201b050701e000c6080d081c04400b8040d02509940c0b070f0040d00a0090400c10f001d150080a403002d0f030001586a0f11504000c0c0801e203110f401111130514106c03488601000b03c071004c2e84140d400490780d01e1403902c292a52641d26040441614040c0a0f448600d01d0340034003c5c245100713040c4501800920780c41003081c00d4000102240c1800704c0d40e070040100c98881824100d0b0300400707c2e000608607055002403d16441074030050400350b551644400000882ca880038042d801c40c140800c0b405000c5885882d00401034070b0b214034400c040b00c2451541c0d40d001d12040e25005412800707107500b01440b050240e640083c07481d01e07000044a8800200c10301052480090a09800c0241c01d40501403c1041c00e50300135005004880c420380e18861800e524410403220b00b1040e00540b5406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 942759649 1250 942758399 942758417
    0x50a0314040b07030b060c0d05040527180c03070324110d020f04080a03170c090f0105090a03021e030607020304060503010303210c03091101110a1202120a1e030c 71
    0x1c2c030b101740d100750710b440806050145400860705106282c0145010200000785000405115030308060400c0708a05843c9546440d0454800c03100e41413024000f0052006914010780406004c0810008421030074030180503034a03110345030f080c143d80410005001101c0041c507030b02000c54548262140d604a01e40c1c10710020b0809400b13640e160f019512500e084400c4001c1070002003958074050020092041c42612403080e800445401100c90791801401c005080354188076001140d11580c0c20039102d1802480c02d82d40e541c0c4040c0018a400b090b580001c0e4200c407606078602c030710035004540d000001108500300c1c0c101c2d946613141280d0740d10a50040070006601070004100090081c800b4a030898010702c0c6441c1140501680792049074a500341c4500003a0304d07541c0d0340051001c42c0d00c00300c0000c0c400386008602108403840e0240d031030344800030017006c0d4080901281002c03032080c040500400c034107603030b820b58811488030010a414506a0021800744808040c1c5069030700920402c40c0c0142647c40e02040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 942760899 1250 942759649 942759661
    0x10606030b10270b0a03020d05160e101209080c15090a0807020d171e0301081b042304060509010902010c06150e07051c050c161110050a0314040b 64
    0x401d00a85181803600d100382e503030104481300302d40003415a9003850354006803994400e4095106646c000382011207080d400310700018401da8400d55000504d202542d0001e444c0e0300c0e103041118004030240010901503e441e0b014010410050f0044c1a80003041080300c9001412021682c00610103440d003110a0b484400c040300041d0000003c1e010085c002070141c8928204c2c0d4031403009580b50035003903030f100410001da82b40499482e6000c1010685a41e03400504640c10310320740343e07616610554560303e409103840d84440300d80d80e15004041e212202d404100500d100782404080ca8403010b440845410b401c4c8000036010709030510038001d000750143e49160071050681c0f2950003c2048542100308030782211070108040d64420a03c5004100b9070381d0711683d400c0780050301c3c0841c05040712031142c2c480c10031043c44901d046040660340f020400d0311500000e031210385042c84846003507031182508071001411800509030800c000d00018a80c60f14140b02d80c80302e04e000c51a92610444005181d401440c0c08501c0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 942762149 1250 942760899 942760937
    0x20639010633110a0605131505010320030319050a110312040803040318060210110c030405210706030911040e0d080a06050a0807140307030f24020c010606030b10 71
    0x100700c0709081644c4c04545291111425541c040b909441c0c007040140d0003004010001503174200c0c1d00fa542c9410043c650540d0b48842030440803064942c00075204020480c0590f40c140100c54a10303545081402040080e20000f030865044600c042011902d00005500e0780b90021080382c0501520304a80e05403999595220861078001030300503402c00810786140080b14030043d2105015140a40041a1040e1502c0b441001d0f01c4d802524810b0300c00c400d000b5005038510010568040d80c01c1110b40340510030740c5580c40103101d60003408007842441031040004400b501079114103171550050034455140b0380c0c900203010503544080d0600489500c0181e881016911402c6c0d06604030f403921401140741c40e80c0e200080c1c0c0034003480c2c105006581080c1020881da034042e0000103032a00e0150302820304107245848003400101c03404000342903031030741690300b0b84800d581d40f03d00032100440c044110341b551010b0781d23450b000307180324040d0001003890704015010a1034400f1841d121801c1a075951002150800c82c004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 942763399 1250 942762149 942762167
    0x50c0c0706031a1c17072d0515090111040e0612010605180603061b040306022203050c1810120602121e13020639010633 53
    0x2105491540700030f80b0650382c80039003560300002140013440c00d100075400c0034a8141d240d25480403041d0010445000042d40c1d81004003180d401e480e09001110001920351440094a95070040803400382c81181c1401c03060110030380d80160108002004581c403460010003483c401ca0140600515052001034a07031310b08100601035058580f000411001e9460001c0361750030074070b01490714a0701006004c00c840c1e81010000954080c40409508201044103003000625111303602014040b40d4002482d0180f40c26100480541950095908046141e690800c203480345500046544603030140036004d05002500900c40d40144542030318900344c9442c1045100301022004012940a50203122204e04000d141021170700c101c0850310300310346202d02d503402401c03011401485d841c2560201e40b00080580c4520041c1c4200206819502e010360b10f4041586501c1c00440322030410120f06020803a800d00030640006080fa1072040c51115401e02d00844201c4031410104421103103002c000c81074881503ca90108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 942764649 1250 942763399 942763421
    0x1e0c0e0c041a0d0f020c210f03011701063302010605010e0f120d050c07091103040605060d0c1e0f050303191704050c01270e06010e0a0905010801050c0c070603 70
    0x6075640340c040031381080e1303040884010700c00d4000c1201c035005807041a00031008158000c0c14035280444613078400200b40810301601d10b00301542c5100702d200d101c0c00d52001c00582a171b2103903050300f940c0007490010245100d82004148031605004112142e005000300c81c20b94105840d0f4009404c011002c0c003414504034442107078440098007103646420700a00c52000d80808558030241d8803425009114540210395000c50710240c500f5034405401c00c0c0c4031044d42d4000354080d0300071540b6202d9000141c00000100f03405881c0303040d1000c001031080d020303441201340b031080d1056580d91955180c007645980c1a603482541e070190000c0014014480178244002040111410501039042500841080c100c0c011101120198060064141c040d80c0100c20b1048031281c940400d410391086034110401951940f01e20300c0ad404680c0080b440c1613004bc2d002019001c0c002d4502e001d041c0c0d079902083c0251000b0702c2450410f502c0e10780030038070420305001203a03076030300135a4001c01c074051403c0c00072401843ca000d25 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 942765899 1250 942764649 942764651
    0x70b090a300f02030d05010b0403031b110d0f02132405280806042f010e0d14030a1d060909011e0b0a02061501090503100203041e0c0e0c041a0d 63
    0x7080c0303135200a61003011f028142c105420750b10b45041d4500a082204007001800c01484079119240000741d810031140381c04242035608510221240c60b03ca49842c4100320025440036400380310104040c0c2c0c95102d20224001e0031152030134a400e80309207503001c2149001d11a00f00d00880c110510004405203003005c94500078100120b11a990004c2c5030801806440480d8030303040ea150b9a000c611007441c1902191100c036901044d5100c0880000703480c0c5c1c034450fa80b03540140000c46000050148803a0120031405d040800e50717035900e0000b20300401010071201e0420004c10201021401420404155690390902404004403a42003440f100940c034041241d42107003822206020500984c0b000240031001010f800901d09410712241c1200030f41c49a581890400a040e0400c11191340d000602612100489030016035a0326241405600003500e400d00140c0e4440201c45a820803440c0594141202d01324001e070a929150a50211102c0c82140b0031824041e00164025405240074802008002e80c0d03004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 942767149 1250 942765899 942765907
    0x503040c05280803091c03090503030a03060302090c030601020c121204090e1b0a0522060803130e040507060815030a030f02011518020906070b090a300f0203 69
    0xc001280342c1180c0b4141102084450030740107071460b2500b280c601401105001d1414010820301080c10300c3d040303009074121080141410740c1030501030480b440140c20040e05480d6198402d45c0060060111072104a0041c14200006480020024150390007410143c4c007911504031100200014150b02d0003a07074030385e400b400054003010207452000b000144462000441d040144d0403030241001079064076043c0c00610208881c246643c0e031000d001c1607450031161420100140b1020380240036800c07541c05034191404401203040c1c100000a054452851515841c240f6101c15007000e40b0b440c155402069a4014035081c007140d4090070549501401100e648545c0706d8140700003915054001c1d800f40e0105082c030148205042d421f01644400202504088050307501c0c10310400e10349c110194500300070a81c086510075081d0b0300d8008440c1042e400c41490300e40b07404c0c400708403603d84950240484543e8a50400307050126519884580c0700d0b60611008000d0704000d42090320140c0c0346581030310450101b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 942768399 1250 942767149 942767159
    0x609090c0409021210140f09090313030609110a0f030f02060f0d050f09150423030a09150c1a06060f0705010b1306150c111f031b0509010503040c 64
    0x440a05982c50000444c40481d0801d03958030070a50f415600035080c401545010300106864074820391343d0408007900c100345a40c0e20305040343c0c02d5001d45640014210441d1b80c000003404555001260b1050240c415143c04000c48400c200c45d070720151059400c00344103944200007140900c000ca80f40607001070081454000041d0869056901050340d8138880c9540f1000e1041940e48079440e5580030481f0401030001b941c0313403000340007400801030004200c18400c3c42000107440d0182620036107042c01d40308a940303400591902500403d81c6000d4004400b8940020b80e10007031190304800081364000d4031500510784030004910544100910700394210800b004007030b80003820381004119081c051303000012040060b00400402141403004101003509110050001e41140040e8a0540741d00d03041c40c410048c1c05151100400800040700ba80c4203200c10f030048503500400c20000c104004a54040218030b01c00d60b000d40120325034601300390001e0005c3c08541b4065002e20010354101e03000d2508056465036030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 942769649 1250 942768399 942768401
    0x25140d050109020c1204050f040203090a080310140a0b0702040c0306030c180506060c060f190c090501020d140a2a060225170304060e0717070f03020609090c0409 71
    0x1e030b2084500c82d600150003a6036000600900600f100c400700043d280a00e0280000c40c0b0300501c42500c1e03c200e07030000104018460800207042c0a9911850031901c0b483c0c91510211007190921908030303903115078282c0c0046454640d03c01001d40d1400001035041100c00c3d0207006c010107191141c20245a5240d80c0440440c142c812803030010400300000c501d107880c800d00c00b0000d4890151000380101001e00c40b1520365440403c100703920110313600412351517075194001e841000140c42240c1c06103610300f080701400e0a910030b070b904003074620a03000c90b03086c0c2d03c00d8401100c2066010803420312000e4203100f0301520602c01d122242c540440d40c0603c0d0803c0c07080007401c1040d2070002900320784060307001074403000580404924120000b031809001d010388090747c55014181210301ca000225980020000b0100105540900800c03004103049075107103034458040030140090007010300428452f4103c0000d4894040510106503640900a2070500d4400d0050284100f805800110012400d0201088640c42c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 942770899 1250 942769649 942769651
    0x607030c0302250f0b0f180607082106031617100218150705060109020a050f030412082a09040621020a0905010b0313031b050304090525140d05 63
    0x42580a07111920700030004d40c12001c0c0c2c1d8400c1c520781505100000f5080541d0060303a141d07440010341108042414000180a4810003e0040103200b000c510b4881c1c00c0483e0205140aa004c00001462034070f642081640e90860b001000701c41010b40b0328144074101e114144080c16090460440d0043e41410b407055040e60020711700d82410340404090300c2c0c4c040c078100c960104d60401e40c22415190000607107030303240c490b581402001032054000581d02c030042d20840445107554031465190b600c03424146010303000b180e070b14106480001c01000c042039040044101d0b041d21480342c51a0200340310341d80c0004071119000b0850b0654020355a503030001da80308090901603c10302207614070201d00141c42c4100100c14515403c211451441d01c40140510085003088030b070800981105451030035400e10b01226450094a00c03592031801c000003070300c00c01c040007000e0410380b00680010f01c00340d59100c003010140c01503a0b004c1d502114102e441c032010140030303069101ea142481e401c131b103140c49694080b05042ea88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 942772149 1250 942770899 942770953
    0xa0b01110c040b0415170115080d0f0c0c0305030c010522060e0312090304151e0c151b02101b1101200705190c06030b040902030d0c0309140607030c0302 67
    0x707110429103886c081c440c02c07901026410707140d01c40608061440d90348070720056007601404000390740311800314015289051960362001d07082c105a0303204d252203501c0342c01249131104030350f00342004161800021070403045c5502508031005410503107a02c40c80042c0084040c62a1213010801c5180003401c40407080b00c0c4141103240041d0384c1c403880c04c1d545070405c10700e03404003000b0000010351091498140c40480880448240351211222050b410b103442c0c20300304840a800b02a252208042202c010070410341c165882a4095840c07400c0301c1d040720f4041e9101981d140303440c80041c80e81c1590040c001e89064601070564400000c1e50f442d0070141c4200c00004080c3d6a00748000030078010100141000110a840c0d01e100c0c0b85868940d280e5503034840c00390326000e56401d0648070503850301c1944480e8029244550010115413a60104042c081c0c008561001e003500020340e131040115164201c0c403085503c3c68406051540b504d4040c2d1401c0304d0316044803000f1011405050840c0703000c0074a18128000c015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 942773399 1250 942772149 942772169
    0x305180d150606140a20030d0e0106090605060c0c040e0a0602030f061f080705090301090b0a1a060a02070603020a0302120f010e1522150306050a0b01110c040b0415 72
    0x80c18540c000e03107034a03c0c0040404c07520100308620800181e024025010002c08904528008804400c503c0d00354003c42048001441c6440d0a014440d501500004110b079141c1404120a6849205108051191000090342030b40400c0b1000503501302540300b140c250351035505440f52122655510b0003a648141c1d00d42114107200c40507c00d452a24102022a244052a2901d050003000401414410b001000030040c0240800e08c0300c981e440a40040c0300b142e5201c801c041440c681900e00340d00422080250040382c40c40348001122a0070500e003104d00b66100d580042101a250032002ca02a50004424a0400d9000c0c029502d400c188002d100e030040c0d9040d25000201c0d814104040f01070480140803c104a035802a02869911000f07c0340e1000d41c01503500d4400101812841d5002c2d1003148031180c003203400c4c90000014006242e03c4540600c00d148030500018039103000440300d44492000205482d0050b0241c802c091074507a112100c1c1880141002c500c01200007081300d0800a9548a0150340c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 942774649 1250 942773399 942773411
    0xd060f050a0c08070c080c0726010908032202060307030f14011208070c0b22050307063e1b03190201080a112704090305180d15 56
    0x9424020a64040d81c1400e04000822495100500341007025140d201804201070710481400070300812204805a0007040355215699641c13480010301003c0544800e03e0014960715101c1034040c05902001d582108441c0d08640300c04d000980c0d00e80144611060060421022a0050f11844046d51040d5101e460005440c0c040c42805016200400526580c0c0304000c0014424481c500d2103011500d038011080c41d03100d094621f48010754110a400608410b803012807924002011030580500c00742802c200c084260355203030701340750f59190715000780004035803138600c0001d00e000d810711512a840031071007906003100745850340c081c1c00c090451031050f0250021141b1040720810b500520000e400190000c00b105003c880c601c0801c0c07260760000030f04102c86100440d030192942e03048034202d084c3c01c5140503926124520041810640702c4010450580300c40100039051601c0d105800035690140c0b01c0600e0000380d2024000224101c030071072540444100040e1002c2001400b8460515614100000d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 942775899 1250 942774649 942774671
    0x27090903031401180207170403060b0127180b0d0804090608070e0f04020604080619050a2d02040e0f09010b060711090a0612031706010504030f080c03090d06 69
    0x103a07001a03400464055441e00108811400d13450321001112485000584a500c540b500c010b40c03041a05010601c6200402c020042c0304a42d80030280519003600d1300d0340740c5108401c4440b00c501812040a8180c5030701103003040030071019030b98000003a045040c00103c00c80404001009603215000954020b030b0045014490208644a400041c101c202c0c02040c4141c6024010095601d0003825076190941d000f0204003113480d0f804c1030340c0151030460181c03445464079048608405082040020f0f00300d08100104800300714038401c408086070413040b43c484032800e071044041c6c41d005081c10708825a0b82084002a21040b400019019003002c203841e42030b604148506030709440d9510002c500c99841000514001088010b6645070000309480070b00310750303884904400c01080c260b401040e55908414081c0c04241c1d1000961400034034211450090340c45a90046446005a00005200309034941c2d20b8404140700901504410340b100c0d0440b4600003085000ca0315642603a1412280c0c16180d90704410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 942777149 1250 942775899 942775901
    0x50a050106020f101802030709020702031212040f021311180a1206050a060e0708041506050a05060c0f010c1e050a09120f061a0306090d0503072709090303 68
    0x40140082c0c4000d022038011840803a480d805000704581c40503079915071598000c000c1d203101e844000d400900b81c5011136a103802e2800031798000c0908034401d010307403006280540d4a10043c0c40c0b0200880e00c1c04e5440d81d6850307a42444c10809100306076408030b001c14001030320400a0194500d120404084251555a024124002010410000d510a031281e581c10320540e0395015903c031107160009c40c003007215201c445090004040c19000040c1c030304103020402c004190070201c03a60040b031160040d0348010101070450000c8401074042c00340d2140c00840f080002c0c2c40c1600c05440c400c4456030039200d44070001122107085410f0004002d002c01d10114600d41269904200c4e0355521030780781080c52800607401002040d43c6001d000d50400340b280c1071810005d00555408000250740e10001c200180702ca411564640c036421101403601c00e20803c400604082c102040510703c0011740e40f2a903045440f0080251040901c007500a90503084080780c021240204042c030380010800510000740b0f252150030010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 942778399 1250 942777149 942777151
    0x250227010e0c0f0d0204150e130524040b120c0117060603070309081314030d05192312011d1501030b0102030d090506060306061e090601110a06050a05 66
    0x104041e8140010840e10b0050202201c1c0307542ca102a41a40d9024100101002801640c120b1200c0c200c070b5a05003c00079401007410b00d900340f81190000d00510080c1e040070207603001102c6c10740359201d40d000303100003480303040355490038203040180003045101d200703000315070b031140c40c10803400d0f00d2b0384401c1d02602c465822560b0145440c0c001010010b0f20300d006004107c0f01e00c809060402055a0340c840c00052160304015215403100d02450080382c140d0b030303e40f40214140c10301100b600c41e004004080310400d019404590b410341f02038002d06403800010720309079095502c2c80f2800c041a106040c002c4c00300000700380105210881c2c00c141c007d0b41d5050000504409600e0240310a91101138428890901002c40007586002003d1a001c10402c42c4540100d0541c02142481c41d00c05040030218002c0020209480c0c2c400c5800740d080361400da031080e08112541c102c1e10074410308190344002c544002d08001c001030b94003130b01c1814440c02c0300a40c8800c2901e411030222007507411950305c0301402143e0300540919 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 942779649 1250 942778399 942778409
    0x21524060a050f0711041415191d0402150a090b03041e08030403031b0e0d05030d0c050c0d0309170a0512040605040b010b0309070915080f1f050c25022701 68
    0x2e00c09240508d5109204214111400d1046104400e00d000d92000c00e441e64002d004441040d64a6541000c030b101130400c000e5074100c1c482d503c42051100319803010010b540d5242d400d5610340c183c00c2d00d40341d20342c251584040e00544801d03d503070581d200342c440700940c2c06920902c104250f50382c07803400d03040c02811501d00c00e4005907621407105041e4080c0c2c0d40603054000c81a41180d0041ca540d080d894880d00d184110400d007000c05003003280501035242c2000190060008031401d0703401560441d902181221403586c40204075034040b00e0f020213035246103000381400001c1030410030b10b400d1202142d0040480229021108540c8401c204010000004500c5005009040f03000d8214245002d0b0180c40300b8060040e4000301741d582d40a240c0350404207401500912029058500019910303400c0c03511419144050000e00d03c1030760002040d08aa481124071507421420028104101140d41c0c207440e449005072900341d049040e59403805a51008440f210070b142c0720b82040501420300260303c581d01070580c84 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 942780899 1250 942779649 942779681
    0xa121b050901090b040e0d0c03081b040b070f061d010b04050106120b0a0b0d050f0106391a010510020c06070b0c04090507021524060a050f071104 64
    0x30025916048940d41c1580c0700070f40081160980310700418010040300031000031900c5a51042040c10303400103100c0e0315042c025682c2035419620741d180c500d0602600c050812502104010420180711840050900d681c490451601ca10825464010545180c10340800d00c045662094412154003403040e03c11461040d10144019858000c010300694003a1020100e4071b92212894001503842031001005081c40015a9459020b900b100c000204000c803440614180e0b03220010500030700415505c510074440a090040000318803004540740e5112081498410104e158041d0000c1c0d14203031180c125604c0c042050b1030940c584420005178110032075440096410101c14014252038580c00c441070182c21a44005a40d00c880007400c0892145e036100c000342c14508824000c26039408030700402e030580440181001e0f5202c80b420810356150b1880d444044660082d1034409a050140140c1400541da0030040e06003d0b10080c3d4002c0340d400190110b481200380c058480c03c134902032061441c18440d00070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 942782149 1250 942780899 942780953
    0x112b11060f1f050402030a0b120a121d041e05100e0c0307021e0a050d0503190509030f04092f07030c02040b04060e15061c05040602090a12 61
    0xc4014020000d41856002d01c450358200603900c5000d01c030035004110140045540746400b880503c000d20031003061912484007886c040001d00340c005005822260089812085946481c00070340314641e4503140003882c041d141c071000549954603c03501252404450030490710110b22842081110742c02000061113001c60381c0e040c8070700e20394801ea856000c09100344155494642ca0b01c1a1310b4140e00c594601000d9410b04030744280c811010a241c0002c1e0b10070340072120080a0800d054503d4001117642d980390303900d40b40d100c1143c0c85041d0070041d0026640c10540e40b42440d0005c000001d82d0064014400c420f407919408080808680180c0d42e002d011601c5040140c0c1402031440e10a01c505071000d02080b030341002d014107540c1c581c0d00c0005d0403840200100060740d50380040c028449011a0609140135a4480c4c0b005241840c0c402ca030581d000c003d0b246c00381002c103009154010540604181c071042da080c03049024646a03004100b025000781403508280e00e03500d2401240200b079a5805030a5181902 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 942783399 1250 942782149 942782161
    0xc13020c100905030f130e0a060e0c07030c021c0c05030c15070c0906030b060321041208040302100509030706020c0907030c110a060222030f0201112b1106 68
    0x1203407195581e1501e41010030600d400c2c0c24064a1401182c9405011a0002130119010300c10000b039601102c0042034003181642d078520310707d01221224854440c4412076140041c4014464130000d0492911a06207241c1101540d008a03441009000240c1030f50102c52158005100c81182100010f04007100100000c060801c0414001400d07030345040100340000c41c048041181040d0100003505004030108019944c0303081c40c0d411504150b039854001d0007110126000c200e52030150075410340d011004a4a81860202203c10407003100c2c0b01590610130030711000c00180d8030703c200c091108072503030380707050312814010700309800c1210f540d0000f800d652102c0300f14040b030307160000c0890340329410303050000b24024801d40c151504030740725100c03440502030281c40c9003c0002a502a0480d00024104d0004c0c203283e0b4130301110107074801d010103840c80e04409500001580b03d007010381003011035102501e0303039894290040110060280e146520303d8460f16000351045074080030518880914500030010b60400da = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 942784649 1250 942783399 942783403
    0x30b09130b09101817031017010609020c1c0f0210020f0d0c0801080d0302072006071e051006061e03021605010506090a0e060a05060f0a03050c13020c 66
    0x100008040110190000e100c00e641440002e036881c00034481030118130100348010445080c0303510102e80310040350304e00720750068058055030b2046020351000f41c01242080c1c10240c0d9002e080280316950742d00d554020070b10070f40f50b0000d0411802d442c070040c0304080380c601c4138000300e4503582410001c00142841c4015002e0b800079a00c1180001d4030001a51361440800110b150300c9440702248100741009840b40c42c591b4000456070480d415034090b901c440c0c802d07040450503489000c0000d031241800c46441400c8020700d04450b43c82c6c10005000c1880d1500958031068440000182042e03002d42c1080d4101c2407080a01c07001276a503100c2d0408100c402d0400c007010b05101081c0c4064105c3c8807083e28814049400380e8101c409003440b464600810000300d00d403d6018007411a090360042d00488041004000c50b400b4150038000050081c3c00c0c40d43d246076800380248002044583c0c06400074180e401309850b00c0e400c810186009030090b2800c803002c8014058041c100c00100852640304002c112f04803030340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 942785899 1250 942784649 942784681
    0x10609021326100906060f0e0a1b0905301b01020102030402060a23040906180608070b0708040510030509190201020607050702031606090614040f0909050f01050412030b09 75
    0xf001c000207120080750510302c3c01000b168012011284911002090a28280c08207500c0384800703501c144118000000c2d002403216411940a02042c80342c94244417528180b03440079091000c0802074040607441d805003864500402100480c580c1220042c40225401c054022a88840030f0000b5032550a003907011808a03c40d040000c01044a032810030031702401d9080561803d0000420119140c94171110307076074018101031281c1d5200001000c0c101c84003480c54055201106c4400c0c0c040e00c8140d02d051034040b00d03981300c82400c8503100c0c020400414295070f11030b407118455100f554001814540a41c05500d01001d965146600040d5088540c1c0103131380c00169503512031580d00d40aa1205000d1000c01d151186a003003015a8807003004010801716032102c003941c2220720954a00c1e410051040c210305081c401d901410000d419080814800c0c8006e40d04410783e140e10400c21140d0f102224808a17084a1040e80c084400524200d80c9001a60b81030046108a202c00c484607200c500303003c8140154044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 942787149 1250 942785899 942785923
    0x10908030a05190e0c033307050706090317180a1e05060a1a090f0a09020105120f060f030d0203031603090b01060806011d09060d05010609021326 64
    0x10302c8800207803a4100000e8414016000f41d40c1c02d0004114400c80d090f21105220314040c0070b0300c07642c006805110b000122190240071495061107618003c0225840c04040042a039000e02104000380e0300000e00c07a02c5000c08950184d56400c60b0410b54100c0c00001200107802c0c0c0c02c07000c0380b100e03030401ca44d18082a44601d480d03205190a008001c0100e05903814104048043d104d4020201000140301c0160860f11244083d2880458508001001c002c0102c0342900c41041403e01000000c40700d03907441d404144200e0050500c141030031034000303036440040000c4403101c001001c01401d20006090200d8101c020b100100c0c00341100741200000295203020040401d03030090034041c1e00108040c040d84c011191207402c0103180c0003540c1c41d2034000d000580b0680d00c10b80026001040c041d00c0581501d02c20041283c002d050503426101c070410000c00062101c010f41e9695a5160300040760000c7e407008203564034410600105003407821044021034600388003903c0600c0200b50319015828000b01c0d1800100c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 942788399 1250 942787149 942787151
    0x12060b01111b13090501152421050703021308030f0a050304020f04020f031f0f05060702130c02070305210a050d020d140906130206091003020f1602090108010908030a 73
    0xd0000c4002100d020f0b04a40741640355181111003020b0000642201c40342c2c1c15020301c180000355440708089080120a03080d00c80401c5c403805568260351081882d030900400d22452800c4550482c035129080324800e49089000c41e6000440340d09403894004044020600b00000d5801d04940d0072640d0000c0c45684250010088004002170031992031040c22000c1c0c000c080c10464480049075440b040642c0241e82983c400a0050344818003202d44090340402d0707510204800c0750329403915050040f280c00880040b030b4090451501031010009078810f0b0520903240c0d90084c44100d146042541c188442a041d5109003d0729405100300600d200080b5044040c480ca405c5075161004210384000b40103044943c1d00040c1031030452036500103540855806068600d041d034440d0784075200d102450b400c00140c001c1d004078051260945c1032401030607d8640b00414100076150840c9048081f1181e480020402c031070542643c0c0280560800070207490241002030001c0041100f151100c42e2240401001c141c003103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 942789649 1250 942788399 942788443
    0x1103070f11120c01240f0905100303050c0319210207050c1c0f0501020301090b0d021003020a0e0a08250f09020a032315041a1003140112060b0111 64
    0x5101c3c2507018501c000c0000ca000d0100d26280021903511181a100d41528421403090108003910342e889107a008100110310744070749600e1640c0a03180da410880460909010600044000850510b1004128401a92003400291101140c4d11420032080c4c1c0d1908100d20500103400010000142e0b850011011036071403011a0003042c0d900c40c004806880244a034010f4000c607820420150081d42c143c07090b03140284100590802804007400c4004800f0f07510689500741001c2c09802613006003408003c92500404c0d201046020851244a5078059201075010204000c1c0c0f0271301002c0c0d06507a58801207078004120346801a000c004c41c186006407425998001840300c2801d0082d805400079500a100f040e0446074030350108038042104442100900a0740c034445542440c0622402c0c2031048142404004103c48406020202c1e01e00c40c4510b0074180d484a44088084260b16124000e00080c3e07c50503200c01541740a60544440300c19041c140700208407100f040e02d001182e010f00e0810200015200c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 942790899 1250 942789649 942789667
    0xb06060c0d05030f0105010e01080a050a1b0224100e06031c052a0d110f0312040551150a2310050702041103070f1112 52
    0x26100d4400403980901c1200070980c4003a801502540c420040b5104107007441e0380e034030700541703203101036407202d500140055000640c8081680c0c00f00f40c12034140c08001401c10b010508460762a010b00441c400507a10402d98817610136030340401c0305208c0d8010703580510b050a0001c5415000350540c02006503688014000402e180c8081100800e054110480031741030701070344880138005600c0280d1038503441c8410600c01203200c1494001c1940d54190340c0037040110301014080302c040c9407400390030246000d203a412456a16007000604101c4a074901c41c1d4545080c00e2400c0c1d132801d002100f070001f00e1004032148694000d48850205088145440404034807080c2100405800c06090040d58101080300180030420500f070340c00c002c2441083d07802c1550340f502c443c100c05c440c6d04220011066110552507501d82030505440b5228600151700b4010b007800401d0340043e0a45803aa110030000f000c000c003c10021a62056480d034101c036035418801494a510a24182c5034004100700c000c00d040c0000700c1e210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 942792149 1250 942790899 942790909
    0xe2802060a0e03101a030a0302070902090609030105010e06011107080c010e064b0304080f1603080402041b1e2003070b091c12061d161701030b06 64
    0x11070b94014103071140703100f000f00b0440c010140801401402401e4141d44810750800051206040c0d0b09500184245460203203404007950091400329000f65017840f0700c540ca601c0034041c5074083e295400c5000524600b83c4001801400b00032040c86543d440031000304110400071a541c3d0720404280303010300c040c04001d40414070520507401c20044040b601c2300114154543c40300b103c1d210000400400061000d203807041e01c1140c3d400400c03810030395020008100000c848030300802d04161200076460500d05a68000c03445129007000581c0450400300c1080214a01481541440c20b143d05552440303003190140240391030443c070b40c0d000318500b00e6194210b2441c0500046005031a56084203920b40c100201100d07229000307020304035691050f00000c00c07050a0046400c00e4100884400507090385d0b010401150050860100b0f510300b5543e400340401c910705042182c0341411a401000700c0d090400101c1d03203043d4a000d94102040081d400d1000312880590321140e411070703030800240601500c1d4440007071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 942793399 1250 942792149 942792167
    0x609060f09030f030905040c0306031e030c0c090903140a08062107120c050a0506070f030e15070302060f060a030609150513050d080705071b0305030d0e2802060a 71
    0x2e41000141c0a43c0820107900000f00f00070f4036403c3c0e6080c03007850380800055094403500d01004282c11450051564500c03400c0b481c08482038000d140c4810320030000e481e5028000c015804c007803a6240c4420a420034503410907018290040c1c02c5240a2410126140050543e60054519446043c0c20292020426510350b1040b00e00c0076880e007503034002c0d55548096000540b69503800c5a040e2884003000560b4606007110300112032018140914088441d034a02a84844030b4904800340444500210119103c1106184d50000e1442c0c1840e95980c541c00d020b07281020007840110302d440e0003410000d4540b00c3c1c4007010100c07603001030301158000daa450505010217102c80c81029a034500350410100482c1307059002f49040c002c4e415200c25048980c82180d9000c1e0440d040808600200403510001c3c030786112280f0f04520310455420718544a0b82c8850840d881560010040760311001d1100c80c08009011b5110708524101c01040b2030340b0080905c201049075500082e1040c0c40c0482c221200034080c651003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 942794649 1250 942793399 942793403
    0x1c08060d261305041802130e0d08060127120f120c1a090a1e050d021c02010501050312030714030c0a200a11010e03010509010506040e070609060f0903 66
    0x140c0c451252040141d20250402004401030764000c510000e514200313449030741c500c860202e000d00c400442d5a020700c02060002034210900ca6540d45c000e0310800c1043c0010030105a0b40c0ea2000c03810706102000600240c40768180540817044031001900300d641040d40d480440d500005806c2585ea00e50410044210b01c0c035a01800d2040a817124840d82c03640214945880c0f0b00c83d100320886441c0ca0240c0044003c000c1f1079107405d6600c12410b10340401d90200b040762034000c605100e9910400e2550320326050207505607c070000b5900101150110302030102801070003a800e03100030025985800000380e9aa2500720801014030000030101c0c0300c032449901c0026100e01754211040c1c0e6405c0c6442030041c2c66208480d51030000c0c500030070030310020301205881d0443c00c004600510f00c10b00300341c0301c1181e0f00440c40016810b000e500d62103e82d13240c07020300036a8840c020800c0002154a01740b0706000945403002584031113504021024000142c004900c0c1c8140c1d4194a07115003010342d000d1095417203803656000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 942795899 1250 942794649 942794693
    0x9020f0108390c0a140d08070c02040605031b0f030f120a031d0304060305160e0909190c030b011e0e07030f11090a060302210903070c06111c08060d 65
    0x480c0003d00000542006051300c60741808010303030920b8402d207844130349200303c20000490500101d030b9424841c00004a041d80002c000117040c81e43c400029250840d102002000030000310305254051030300b4810040030001c1503000c0c2559444202c103c945411390126024281200454101c40c014400e600c0115104e508100c0d4800219800c44210381e40e801910a00000a0820002442000511548038003082c2551240e69016003a00204505400300a1000805100e0720811500030700791100f40748403a5018080301240c407411410030f4010340c01c058014011500000645120190031081c00d201100d099210201550311400400c90141000000d8058154207004c0418000c1e000c12000f090b0780f0300211411001d06958400035003c0c2d010748580c04044d40d004181b8400035144030034145610400020540f890114250383d000801806c0390010b40000d1900c00034100b8404040140d1440d41041c500301c1603058002c03c9009080440c001d146a000300440721007403040022610b20f01c02c2c80019409 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 942797149 1250 942795899 942795907
    0x2150d060e0108070b040e071d0a1404110309030a0f030e0a0c061d010e011103042409090e0c041d011a0f0f0904060c17010909020f010839 61
    0x4440c1c1d1004020700520580b4000e03400c0024105003c1e508032011202e03031807500c950903560850180c8903984002207401940b44203542d1510f0035584c55407000050b00e0034080075402401110184000ca8007400c0d00441000000c02c2405001c800c00020f0b07600b09100e9160141c03e00129a0f011800343c001c5132a048014403400d00c41d0020017882c00c2e4070509507100c55a40e807200c0001d4401d4100c1c4401d5100e0b4081c081081c040394455654400d0011000303031012801101c1c540f550781c40d20020403a054400f040300301000406051038031644603c80c0c400074034503000d01b0b20000c04442a0b19480354001c1c4200d41c4507039a204600340f1054401d540b00852040a02e0080100360040b1802203511510800311718800c24100c0d81c2402140340c86401d01a014202825a480a65440d82c4100c0285461030100f024083c0707050b5010940b01c2e081da0174602900c2411400304031135045206001140348150040360600c5608802c10001d0303201ea0300b214055a5049500070321403280c60300607669003004010b410000700c00002d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 942798399 1250 942797149 942797159
    0xf21111603210507080117160b0901350709080d0c1e03080a020a05041a1305060c0d12020910020c0a121211070e041104050c09060702150d06 62
    0x14405100c00120300b5101e40c2d150103202030040898004848401c0495501c1c0014030141145114030f20844142504485c00107089500c20300900400358810301d442c100000c2d800b07441e5684400c08949410300007140303945070302c80650784200080410340b141141c9010714000950592040d400c50005003035200a5a450300314445000b820200060829a010546544400404011261a00d04268144c3d5401c182e40d112120004042d42c40340d404c0008100050202007205002081c02064004200c0420340d81e5001b80c4800340c000c101294820341c4075001c14020401290400b10301020809894505415250761003012600280a44608240c02c400d00c40c5003103890703130b400180e80306070704400316024035003140d036201370007011182648001c0c01c1030b0724001c10190307040c0208811805450540c0c10f489085413224860340b400c5104035401e866880300301d00d1491803400c00744a895000307203200b4680c514010150000c512a445401d1000b40210711510181d00d14aa0400c00d80d10a03a480c1c10003801020340d10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 942799649 1250 942798399 942798407
    0x20301020d1e060803091503151906030f230a14010f050906040b010e011d0d2f09220507060503060108090102041203201006060f21111603 61
    0x1441c1241c0c10b460400d02003580e144c000107444031880c000742404200d035006e001d0f880072030700054203140f0044e1100303001ca000342c1c1c1c1c0c41c40c201c01030000c9005200340c4203240c44c1008040e92441020f41301c1b820700c0d0465000b9021400c003055510b10100c0b07140003101e0b40325000c0d02401020400d40e00c8400040e00e900100750090501c18500c04ca41c4100c07000f030580c2e100d03441088100c494216100d030114052513085183c0754045e070f0505071140010980c0c084400300c504040b405614280c2021a01d0f0742e820902140060311041180a58551344030003d450348808101044115201500210400070601240c440310304000c0140740e41607900038242c80040e6a9000041c00c1c40e0019950b090100380c2c1da138001085010148255400c5569040e45400d0454440c1c0341982c0600e1001003034541145910806c1010f1041042841e960b00f808007030000b5514030344800240044081d90074541040300780036101c5429200002c500b0400441e40e03e002a10844c01002454907205000b00d55141244081c1002d0916402c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 942800899 1250 942799649 942799691
    0x120615020d1701030b0415090302010c0f1809020c1908090117040f02041107060212010e0901020c12090105122a03011d07050405030a0f05070e010b030c07020301020d 73
    0x81034085030307210350322050150740d408441561001ca45601200400114010001040c3c05c1405401c8034008154800c0302d65080e00c40100c01500582c1d11140340d90712241e840703200000201d00710300c0c00120b032509412162002c801c00b881000000c503008505150030032010303c2981c81150151084504030501460600b682da0045003c0d0340c04034040741415900c0025044103d807080340e100202d481c415485908120041400c004040308011040c4140d44c006041c0b0300c01000114a0b442200005600d000039401c285400142041c855900600002c02029400501e4074440702000e40050303120030b101130040301c60340906034056030850810710521a10030285808070400300014543c0b91040c00010800c800036100a06c209403611402000b0744540b2045108a0345e0091254503046203800c5e81c540c00649040c41c1400160381000f100708164003046001c000400003407c00e0081c180381c070b41c54403403114207600008240079480348000800804640c0c007941102d0002c080580100420700c4210010360600d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 942802149 1250 942800899 942800939
    0x21204030c0e10031203090507030b190c020c030a0215130605030115030c08010506090a0314031b070501090302060d0e01050f091905070b07050f01050f220b010e071206 74
    0x80800030400000004400303501303417904580042c05082c85103200f1802003400e000c040c4c0d003502079000040b00042d0362444481c060b41c05140f10060b009451945a002ca0741d962000d03c05562050890080780d44001ca02000300c0d6404444d58155003072031940c0341d2070a01c242592600c0402c0b480f880418019084030185051720455450441c1c1140b54002c281d04603105005c62074003248008004004a243c10001000d841c00060002000740765655100000600000185000f030340000c00d20510107050740c01f840c610b0300040d1004010b96450000003800354010781c0000390180400240d1850198480d41055032000443c00c0208954a003010070352415044c1076403002840c2c040c200c11481104031911503180019007000c0600a02403605000c0c0980750b014802c1115035010350810940c900c1e01c28401c0c144a040c10469074090b620740b240000c00b001c11042158540910740520250104001c4518541562007001d00a07082d61036403a810380d0070001c1c5420303000c0e54030f08281d0301050f070004104020340e51003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 942803399 1250 942802149 942802169
    0x32313030c0605040602130b030415020d0b13020a1d130506010215070c021003051e0604060308040b0723030f210403021c090623090315010e1302010c03030903021204030c 75
    0x1a483d88c884e100300d072206031005003151076110481c001c030802e02c0d402010090040c003000900c4211080109400421190b60b02c50601e40c081080c4040640101c1019513090421240820004c910f13000180038442c02e50b0300c005256901e10004809900820020b81500c0f841c01444695251990b0000c15440350a46d00b01e00808240c0d900001080c0240106c40c004c1d46500303900c2c034600b00941c10310704403600b004109a030302a80b91030000011628160040c8094030404007226600c4006080a402003503003403002c4015840080800e8501c2c980201c1507400c24405141d8056490307034405030401e4a080c0d141800a09c044583c4c00303100030035400184a004d00789546003074200e403d00003282508c50103030511400022801640f140b4225007800c8000b59108119480b41138241441c050100c0c0c03918003a030b038110310b80c41c1a8400502c0101102480903600ca0300340300912080d4403007640000c019503d00c4800801741612350f03864000301802806442c0003042c44801c045d880e142d49081100980075184280304070f607 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 942804649 1250 942803399 942803437
    0x60d080310060f0c3f1709030405030a060207030e0a150e0306100b0c030c070f090b09190b03120315090a0c08010501050d140c040303032313030c0605040602 69
    0x3a00400b004039445800080d01040c100803606000c00a1204142c00c20300381d0410703806517140c3c52070300102102402d8a543c5840500d1098040e922450a01500c41d090030343c03081c0300800c050340e40040e414110690000b0056140e014528082e40c000781c0c0c90302d03c5507218441c42000304080f882030107051101d0400356946100c1813084000e042c0c684005071144148400c20300030510051030030100034a6086220300880c0c1c50400810000da0400265410502500c145840708000f8030310940a95800c18408503a00550380c02c00c21802d41d0001c001c0140034042c42e4540b840e00b61969814464071021060903800680d403031501000f03a82c00c60f0285005103215400441c04280985000e10070074200740d05945030b07810583d00b801d0055070250440b0580080302c54484103200864950b00b500113006001c403400b0035440d60b007549805020758545003805400d02c10380c134804e44408001c0070012504541070318840603910155040c1107405500080c40600702d1402e001c24842000b0695000348603d100d400703218905 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 942805755 1106 942804649 942804677
    0x405060f060f07080723070b041505070b0405011d010612022209030804120e090a020913091b0501020d080606090f0d0308100504060602030f03060d08031006 69
    0x2450401b04055000c083c00e840f0005040144000a0891282000c8100115004a2180d01480c003006800740c0c1403075000c1d1044552981d00308264040510f481c0c240140a001d180b1000c0700e42c44030b41201507910110620441d000e68582d15440108121b26400b00041c0030401442405225002c148074405008244540c0d14400e100e6103c003641c3e46058100841c4030a045101c2d501031191030301211141d41d5440d60300070307803010301120016120298030700820605d01e2482c947d20403051800410600b0300061a240c07074949108401c0d0071000316103a0004a844418014554004c03920b04000300d0700c00e160100c0542031410000d0881207030001081c000901d000c20109007074002c40c4085080c40300300345c8150851806000240d80c18060b41d442e09100039134038400e6405180c040d00000c004100e00c0d541700400c00f1101c0c0e4201c00c0032500c90170284d403c42c40210f0148600e1780494180255019 = true := by decide +kernel

theorem cover : BRFrame.Cov 942625899 942805755 := by
  have h0 := BRFrame.cov_init 942625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 942625899 ≤ n) (h2 : n < 942805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
