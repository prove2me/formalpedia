-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5550
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:14:14.992983+00:00
-- url     : https://prove2.me/submissions/4a4fe23d-cc47-49d9-9b64-3b320fd633ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 998021582 ≤ n < 998201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 998022832 1250 998021582 998021593
    0x2a090903031b2a061b03151302030108010b0a050a0602120903070305060702060405060a060f050f03281a0603060f09011812031d1e100612120e0102 65
    0x10441d4020303581e01e0b0705070601d051400308050b1212503524020482e4100b40505001e200c000125002c41c28800040c100e024510540f40500d0b208108041c21a90400120101c00002202c1d60000c56851011803101d8a110b51000c800000d1004064102c00031240b01112040c4100d0b03100c5080001a1000c0d00640c00140d0129161101c00680c003001031040c50b8004040b81c00e181c2e629030390320703203443d004441031001a0014030900082000422646400c07880d0780c5070900019080c001d41510421007803013818400c0c480e500380c604954a043c08084603d8803240c0080e1110490f84011400f059200d060490700c800c041074004828003100c06a85005100050152100f52682c0c8400054158040c0108140707560364501c103002c408100307920706403103482000c80d200404103501c00941207540c80700181c3e0308041c00c9200b005030070720040342c800040c2c1d01043c0e1600301010811402d500d0034064054080002e49040c0001c42c400340c18000e0f10b0385a43c850450b4615200110b1001c60304008140041d07030241c1c1c440c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 998024082 1250 998022832 998022841
    0x1090305030315010e040903020c01110105060d0b0406090b100f0608160c0203030d0204180b030a171804050a1d0703240f020a11010501080c01120c02030c2a09090303 73
    0x1607100700c40354000705240401e0085c00341c0b030000e412541654000c40140c3e0190560245558000d80070009680c0000001c00a0b0302e060000705170381d01c8402e01d00070403001c900d500280802c001580007038240c07a00012589106c4c60854a142c20026540c064445203000f8541d0020f2038611808203d403003050400c0ca5044031a0a59000b51386800401d00100d9040c04148440e07004c10403144042c20013401c40c651110301151180c8001c1040700e10001c070040c0607070049100d40002c10004070b441008000740d440044c1d620040e81415060074048101215402030030302061081d81c83c45600701080904003140c030b40842141c204400ba41e10700003484000d1000c01d08007c0316560740c4400d032484007602c40b1508041550700000c00503c040340e01680c031071004180c1180c001c20880c102485000d0140c000c02d401800e01280600020f4003012020003001c1156331034011010382c43d0301c00e00c255200034400c00c044400c1105100340c0f04d42980e8151020b59401001410403440d85d141804469009522103400340d480d5031207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 998025332 1250 998024082 998024101
    0xd032a020607390614070509090c07031d0a0503011505120105060310020a050f040b13050406051e0a05090f0708070504030c060c022215051525020910090b010903050303 74
    0x25440740c00da130100d58441c0c0501509444264891003140295542c0707544401d1001000b003184000342808440307490511074600001d4000c01d1030755030540080c5480000024060024404900720f0b005180c05509150784286c40d030068121100036118200d6005008003e044041800c0b1903048680d142d0580c402e128120000030258001c3c001d00c600c0e468035903c0d08072521081c100f554001c0d840347d001248001090701c1800e02007409400544030860742840780d540f03070400003074907002240711401c3c1d041807440556050b642c800c03079624001d0101a04601d624500314880500d4800111660780100d0b144100050905118408460035640e1100200200783c3c20100110b403100d0009000300d82040e6800050109c920191186606401c00e00002003883c01948440710a4036200b580194040c8114a24901401403480300381c079110482e45590a000304000481c00700c00c0740c10201c01941100041d400e1140700c6541702c4d4810251080c188040c081a00d0480045031034407024880a081b641061012684101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 998026582 1250 998025332 998025437
    0x50c090f0607151b110d0509120f0604050d02061e0703230114040e01021819091a0913020d03050313020a0f080105180d032a020607 58
    0x28010600301070610350f91148402200c88618800004441104a24002c3c0744d1200c5a0f181002484010b030409540c43c05024001d0301912111600c40c1d40c003036480001100c0100460710509000c607049440718100b505001d601c1d800c0c04000b010060092030005100300700c15000e103240e40c4040324000c40c060303611040110000d00001810030340c1074104c11407440307001d10321240c45806000d038040000150481441084100c9118506035150340e4014000c02070302248a00340c01e1050034043d00c08108000c007500251034031705400d030400b1080d1840e1900550001d5032210100104074030603150001c1c00d84900d503a02c980340f961100002d621440c66040000000d12800c00b65420840e07801445040d0800da42c0001e641ca0f05d00d0b0010036004110719810000c2510901481d5084506044514801c2240102241c0c980404076250024191601d002006c0b504c850400604105090088180d040740c202d64001c0d00c0d644142ca402c0000780c5030001000b484c04c86555500003101c140308201e4980030702240345003001c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 998027832 1250 998026582 998026597
    0x170409051f050d08040509041b0618090f0b03121c4a010e1e070b1606021204151a040e07080f060f150f0603130204020c01090501050c090f06 62
    0x1944e09220026107034072400c002e01e008038490b20348107880c4107411a40341044041c2d684002d04010380303100b08680c0c40a40039214000d454000c4804244900006050b50107000e1460010790103110b825180c000c0851190041d1034000240d1011a4003501001414000e840c00303a000d0101001e4002c2d005c1580301024504c0c0b8030805115007074084654180b0007103e0382d4940d003103c00b0903240d45910314404642c1d000e000c0d0041c020720311100300032207800c00c1c480c0b80d0b521360031b07030181036406640052042910203910802d8407550368040e0041d9034075a44510b40b00703150708003950300300c800c01207108a20760194045c0c09007144080d00c3c0074021a4031201035040202034101c600502900c0d01504078080345500e800c1c02072807400c4409400800150038035091038161600020306045100e1001000408140c3e1000ca101c2542c6400300c9246450b900c413040810324030103481c2e200075071280c40080e40303220209040d00043d01c0d8501880c0200324565507840401250700c02d4080c03003075101140019403541c0340380050140206 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 998029082 1250 998027832 998027843
    0x1050304061103010b0c2404020d140a060209040c020c0108060f0d12050a091e061101020904060608150a12081e04080703110d150b0607170409051f050d 67
    0x7582c042210314800355000307812030b0b0343d40c220010b9200380b2250100030160001d900c1480c120003800c400842d10425650140000b0320403d030300b018803414070403400c0f5001c0b07282c4603207000d4424400e09440c00400a42c042494140650b05013a0580d482500116007d030b90054180c40d40700c070366514003041060003e504141c40d603100740c41040806c007103441c1070200d8455041c0d544416035944030b401009000f802d59a4045107011410141d1002d519030140e4100003142c070b56040011140c40010400380c06070003425600380d0403500c2e002c00096202d510a0f5641c3c000c0c4424403201e070040e904141400b00010307450060030944802840d107400001d8141c1c0040281d00d0f07622103507101e114901507500c0d40941c000d6000251540c0902010b100380000481111a04141103401210399020350392403144000303005002160b081d039108000c41c000e40f945c01c2140c6102d507015040260b81c051200851107075406c03c0c011001c40d2460038002403201c000d46404034003144100f90108000c6c81c640010421050002e85003140c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 998030332 1250 998029082 998029091
    0xf061227110321040914010b0702010507020409050a03021f0c09030b04031b110102120a08040b040213060f15050c1015090218120105060d03110102040f06050c0c0118050105030406 79
    0x14504511043d81c0d41d00f9000b800525a55480c0900100030b07141e0402c142c9010420b0f2800403c13011b1411002c64141a50a007030250700c0f407240c3d00000700200b041d000c02800718068503850f8020194042660010310951201c001d5107100842d55a90880c5e08807400480841c0c0172030310900c0401e100c682e0040e0711034428a4036a00d1040c110313200540c5085107050440d080009040c00b43c0c829070f0184007000a00d54541e0519003008904000100445030151001c0c0c613007001480401c056459551054440340148035040c0319455a4458a2180744501e2013174900c4911528200884c1c00c3c4500e0441d001c41582c1c0c4002d001d0089002c00090042c2001a04462110144540040c00044a00141107020024000305640d80c1d00c6006004914070764024100701a4500004c01c640c540d10741421100c007070340500d450400c90480c0c101540c02031003079411211107030740b5580002400650040050626146250070380300e00c2c406000054650081c01038110f04110314052080c0000d5124601555000d4081c010108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 998031582 1250 998030332 998030353
    0xe0c0d0f0525030501180807020d050a0b09150603060f0c0c070f0f0801051b0a0f020313090e0d1805010c050a020a060f1710060c08040f0612271103 65
    0x2c4180c1e00d414580d05054482550400500c4800c0c802c04881000c40c807040d1456540326a02d2615a108402000340b00f0711304000c203e0207005040100d0740003180d0043c2090f0b1a410700e030b00025034038880c2c184c10050260b080c00015629041c0440d2140c0941080c2859081a49642c40e0070704c00d540104a0b900303c0e41c4a622400548443d2110f01c550050680b504002509410f021900d800e440d401400e440d400c801100c0010010030814085403c020380c0d61400003441c07020150304a042d4459417107004c40710002040e0204004905901510700c030300e5280e08581e40104003042c1034a07041d42c99501c0c9000c11120032010091540200025411148205c0640c2c4104510b980000c0420409410a81c0040c5c030510240402903040308041d00c9400c0c84c0c440412652820001000113074240780038945c10404202880e03020001020b050f43c01610b05403000410700b45d22000e000b01100030404d41d10242c41c0c20040c5020f000c4403498000c220004d5400c4003c41038400c60f07182c2e5810a05100e040680502ca40b09011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 998032832 1250 998031582 998031613
    0x70f080a02010503130b04061a01030c14030a02071505090d02060f060904140a0605070f030b1507020a17010e1c080609090f15040c2408040c0f03060504060e0c0d0f05 73
    0x80c7d1007548540000115118040c80c158020003219120700e0505181c040d032904844d41051640000f4045821300c00c2d40c80d80ca580c01341e80030340181c040040902c1043c2a843d4100e4002e03800152081000004443c00650b112401700e035138450549001080c45042c10116480d414002c103da94041e0003420282d0402c09000b0ba121325100f10200190382180d0783d10140480c6a0740514955200b0101d8035003440700010380e100040c0c0c680241d50981c07002c142e001480204544030b690b200402040364012001921000741030080c0a8001c6101009150180800404440d0b202910b1140040580d80d140d64071691094188800108043c01841e4079110340460035105400410048010000b40c1d9455551800c013458280300007030035030b0440804400c168981c0d0903440c0d15a11212540750143c9000503050312542040743c1031141c036402161008002d404007200380a03064100c180200c0c420501000061070350500603480c0c90a44102590091240035481c001c0f03400601c1d100c40c102d0044066411104100c01803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 998034082 1250 998032832 998032853
    0x20a031a0d0812091921231c0c020d081f14040b062208210a1b03080103111912021c0302071a1204080a2609070f080a0201050313 57
    0x8580500d81d401c030841700c011030340302c0b90b14203000c0380d0404800881d0700c3d247c0d800c01003000403843d5404900100d200401c2c0700c80d09012408e1040e084008106004607048003d4a40010b10002000304216a020440100342c04080ca030603d10403075611030015013450100c01465125004d02d40d40991103021005050f5240401011100c40107444e12032952110540c100041c0700c503501400c1d07039030881d0500c1e92490450300c082e400700b841038901c641e07540c0520030b0007540c0c103402d007110007076411059075550402c05401c1035116041e01e0003030702e41004040419041240d00f4417039001c1c3d0102403d2914080103c0859244d034100c02c0c51009012201002142103600c41c13014030008158016408001e04000d05249030110aa4580c18001d0f06032504291000c00b0380c2c0c10201401c024040080001d8203400e82d4130480814003018528884517119410600d0400030b0890b056030000c01502a02000007075150541c001c400c1121040310140c8080341c5550015229070300020f003102c6400003103200180004111410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 998035332 1250 998034082 998034133
    0x1030b0a0e0a0b1e010e030f0601091a04020702030a03080601090902031312090e04081c05090f0721060908070203030301171b01121d01020a031a0d081209 68
    0x49410782440c0c000b40490a0f50718100031240140f60300040d03200c45800003c96411803840a0800400510320800030070302d8208035510f01d4119000350303000030440b84220340060110b0308508003603c40700010b80040004074412200b0007981075000101c13050000e805140f03001e074031410506000101650310007035041030341d00886403060b6148100c0040380410121035608800d0303040c1e600d4520600d0f41840045c108030306010744040d03c070f4507011600b040d03407902d00c801c03842da480900003052200d03003032000e4065962014481e0701e6243d0b0003640ea002c0b0b89107980b100b020741d407441c41e66105560718503540c45610050401003425545143d0401010000d0384040000798000d0110b500c071003508040e400c11440c02c00702036a48d54550038a1070301c01250280e9101240080ba00d10380c072400522403112007176007100c008009034068282d5001156681d070729505903103c140e400319011340f15441e803040c40d001c0100070701094400800055090140a480f40c20301c00119500580c01000c5030100c00c0e410303040c0b4043c05038001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 998036582 1250 998035332 998035349
    0x504170610090618050c070f0302011407050f0a0c0c031202030d06090203040c051329040609020c1f1e020714070b090103020c01061707060912050a1101030b0a 70
    0x505120141c9219044080186000b40c42000160300703045000c512200109601a0034a403200d0104140c0e407100b81c111740310150701c4030120764015041e15019000e03144a00700500c18000f5800041c03403540c040e03000c4800008a18002c2444d101c40300c3c0040c0c544c10504001a9262000d0003408800200d0078983c4404401060f0011612041c0660000c01503803200d4002081c0c0a005106010002e0030181c0328900b40d4070100e0300820006581c1c1c401d880244585001c0c4e0281c0000075900f4420b400a501c0440c0d5001002d03036091042d607031503002a10a91040038121003440d0721020b1089001080007050181e04d0f1003d0401280c022503d24200001c0650080c4a000751540010f0b007200f00100050342803203c0c50843d000c1d01c00a49031140e45086409481100b80c140b44e00001e020012030000e40c000743c007a01c1191082464262450800e80e51021f46014100101700c5511020680d0041c9e8441880400d0380305008014403002a5901c50301c1c40d5400e5621418140c54280c52621039403400c2c1081d01811200c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 998037832 1250 998036582 998036593
    0x12a020f0d1707020102130b090420030105010e010804051c0c1a10081504080903030405130902030d020f0705010c1a0403111911060c0c12030c0c01090b0316050417 72
    0x30001c982c08203400b418810031343e07104000f40d400120036030401008681081e445a5190b141d80800700d005008140f40760303c6004102d09003040d99000401c051030694100380e940001c00300c42103006440325002982c01401e594001484013105003c01c5404116603d09403070702030f45034940d076070390045004010307160714280d00e003040c007000a102200c1c41c080e0001c0007168014981032035001036004516002070304c00f9119141c00152100030b0b0701c003003080710001c03d0040c00d6501c08114038444038000702032a0104920901806600959140c800901158088480009486000e20344401541c2d010503480040baa40c081c0c8001285840a0300c2500300d00c100d0013034507025003c0c000f030515030303017402c0c8048403201040b5a00404030380491800409a02180340c1500c0e15980e983e88518143e2030200315030140c0f03611443c6094100051000480034110000052003214004921140103503001003941c018610128000c0c0001030140d0380064400072a00b0503800c200d03103051784545056864000c003a521041c82c0d40318 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 998039082 1250 998037832 998037857
    0x30703050a1505011d0a06120c0905060a0302090a09030c06061212050301060504090b030c04050c07050705040209060307030203040204110316170105100534050609012a020f0d 77
    0x6801c1a103214800b50b6500b08001d6043c1030407098002255000490100c030302100042e0424561742c041800b030070201000c02c0781100240340c50a031060481c010b00380840d04080100301582045620801540c3e80240303654801d40e994030010006014404040c0c08005180f0348410106266128100c041e004007034082080d0040c42c1012640c4c101d0200d117040800a04000410080380e0280527078080d543d1102d800302d0b00c8204480080d00d000f2a511140368450318003030901800c0d40d84a001031121b03074490425110b119075070b8020402203001e103d801d1900b01100b000000e5150b4807d6000310f5015100400004180503007264003941c503001250014110a80e90000c800050f03000030580400480c0d0f40044400c0e076042c50081118400b405c0000424068007003071124034a01002419481070b8001d850380440400701c0401610a8034004406403503038000c000100d184500103008403054038502081c89064404000040302a20b084203164100b1401010004003c4078824414148010090f94039440207004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 998040332 1250 998039082 998039093
    0x201050f160b04080714072304020c07090605180c0306090a02070f0302100614060f0a050c0f0d110a020a150212030c030609100623160c06030c052a010b030703050a 72
    0x801c4610000e40c0041c7e020440c041d08000060715075840032004800d035105680215010340181c40d1660242d003d82900840c15010300d5000d6000c4600c12500d0024141d42d0315500c40750144180d80c4507079800d404100082e0b031420203007286500b001c0100401860006035468900d00d07007020040490040c4c01070030440c04145094006c0310b02914515500142c0d50285600152007440340340280d5030141400702d0020f000e54000e000340c820125080d81914003c44901d43c4281e11030040e21020000b192134000c21a0500b240020402e4010307502500b03880206043c0784011344500e0301020802c046106040700940360035030140265001d1f0452940e096100d0404608111282600410211101010f08000c000c0594800380b03900180110381a940082c0007000108041485240d00109407561000c000c1e40821540758883c1088404640c4d0800c4203c99902e412070341c8c3d105586503e2540001c2e42540d01004081e40581200b2003440c600002c0e100c0343c0040401e040910f40d900a0351940c2005910405001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 998041582 1250 998040332 998040353
    0x4030507080706090b0a0c0813050c100e011206081b1f0e10020c100305041b150809031c151d07021015090c12051501030b0303070201050f160b040807 66
    0x118a00410300500021000040608c40020a483ca80c0c005900d201c0091000900000c40c03000c00117000441d14107080100075140f0707040141440c1c00113807003100e540c541c2c5541c4d00c00c00c0166003545014082d0012200c8a40080c4104490166840a500d40000c1d0036410140840400d03070000741c542401c06807c4008005066040450030800d6421081a800b070039507440419424803c2182400a02a11281010301e04030300400391081e001c041a2074080f13088111400506c055080c6c658441100d9a19034005a849000e00c03002880c02c01910442c116a041031030b007000c0c120703040c1c504645484540c4e4007104030a10001441c01603090b2043e0f428021010360500080c4031500b03110900f44100c2c00002c03250485003841c5d1203940a01c0b6510120b6482092007a040302e62501c2c0020024072080c24288405050030070103a000301e001c01d00d40160303400c590a020090340e01c0141c05131100742c01c0c0702d416241341a440d441888600d180b1508800c0d0b050000301505020750103540512412610b41c0308a2400c4141c55 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 998042832 1250 998041582 998041591
    0x20c03030403020a0b0d14191b12090303140c0a09081b060711040e030a1818380a050909060c0906092d010503160804030507080706090b 60
    0xd4108000c14405621a104854211016180318565034000d0000b414024095107500c810001600030a006a003400036225100045031298200400186000c00266030a45000300e280030030b1400c00601c00009407640011040ba006e400c01103510508100b4030203010000711421100341174040b4119001c1d1742d0100a00c00070b85228001400c601074410b031030440c02ea504030340e407506c030b540005401d0302000410b8884580d8000082e0050011051b084261910383c1c001130b0307140001400b82c00c50301c205610384800440444100c1c3e40201c0310070368010040380181041d0944820448904c0926174004c8426916420b00d0000b85041800003c2840302001501e070170036800780d4803c00c141000c0c04121100801c400ba00000035841c00ca0703031a82c04c4004078415000c0d4a0740607500c48100c1400900740d0301c0c080c1e22941d040c15080c0b40c4586010300100151910701003603d481d61007010b8152400c1101d070003903180e99081402400c10741e04041c40790f5070b81d5a1543c09000211003441e140c000d00d0041042200340d17503401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 998044082 1250 998042832 998042839
    0x6090708120c0a1e020402132c0a0c14040303020304061b0203100b0f040204080a020a17190f0c24030c020c0f040e03030103081c05100e060109150c03020c 68
    0x5040ba03080d2540d40d502c040d09409000308101c1c1d600540e10b4501c07098041d444503805070040d911480c1c8404801d041e8141e80c45a5584080c1030400c219039403010201c2c4c002c0d40030310404404c1054072620003440041c04500e01d10001d208592085034405541e101c00340000318403aa0096036600c1c01e002d0000d00d0170002001040f0881056440440142e50108804c1c4080d03081240011301c0c1c2e41d501000608013141c0c90040c5030000c1c80040c000c81e9840001c1110502c5500035035540080c2c2c0d9441414000b440080b00c1c0c04440c54000c1040031081d002420000781e880780c01080242e40003025a182e802e0000420b03449140c40840c0c2545001003906100da4400000b45507042c10002d2042c004c1d8040d4a450581d103500e0301c1010794610204d007541e1280c0c01098800e14a00480e5201e603107900c0c011881d64400d821041c0b80d0040e5074201c0c080001140141131280015255110300a482e140c1246200c800262925046c030200c0c0c4008a181801e49000e021421101e50703c1002c0c0c09900d003006802d044201508900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 998045332 1250 998044082 998044087
    0x70b072105041e0f120b1608010506030709080d03020406020d11030a201006060206011202130b1309061a04020f090906030a06020f03061f141b0609070812 68
    0x1940c202050b074048803101c0c1071408040d16034212492007070b00340e9046010020f0740e521000c110404c0c181c40c50720545100b034030000640c0d00c94030410880480c0840720b0400050110006008500300040a940c0003441d0b03040c104072182e200c11042c0c1c102123148281c6400241e0100301000502c0c3e04004c81c0320103445d1402e28281d102042c01210b500c82c880e1070000001c1c030501c2803182e41c1003140c0d84502849503401a0a581a40283c078000001a010340c0c032803440184940780000c10f010038085076444800303034001c1110794000340b1007144002505a910396240c1c08408000402c41c1a0001c1c001e6000c09481400c0c0003504c1826488c403603820180e0003903a0b90140d031050002140040c0414200c03a209842103940c0b00c1c456944400191400b251074200402060020400704aa800101c020714011f0f00e08a441005101c54180960300504011014400003803071000c03810810115840148420f48000c0c10701c3d4040c0302c00000740c51522100b5584140c081c0c4c001c54081107004400d0201000740c401a000751403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 998046582 1250 998045332 998045393
    0x621050f01111213020d110a05030601080105090c030708030d09030c08190f0f050d0504020d0c08031c0207320f07090b030a02030d0f0903120302090406050a18021308070b07 76
    0x4280b8080210014034002103c9550182a41d8008d00e15000745001400c40c3c90359a12400301c04c0c0038080940c2c4207031a9120744110200c1c40c0c0307004103d8600740d038a0100154140030411910101800700e14009030180442c01840da40426039200040c0403400b05c5014102900d044804001c1105c04405c40e55410003494004802c0035079070040c01c44074624000d60f80428282c95500001d103c4a0000c540180740c0300c0726045c00102e00d05c1c08000ba00090401d060040c2d05624410b541901768452840000d0210013440c0030100580216030b1f090304441840c2e00e105100d480d002103000e2070f010305002d40d0040c9600c03040341000500440c0c011058080001c0c1c014103021000c503408682d90303460355000403040c021100302082202d441034034a18000d40d0483c0310440c1c1410100320250081d030246001c47e004608003100800c450420525a500b00e9200b4000b03a91070712504008000203404c0240c142c440101c809100085030201041054003511494103002d584807158542900c000800310b5000200407020305110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 998047832 1250 998046582 998046589
    0x190c21151d0a1a1506030408120708161403010306020319020a0c230604122a020f0406031e1a010308090a0f0b0d0c050d0e0d020f010621050f0111121302 67
    0x1e04d4004c8060301c1058607502c562411f036165001e02000d00301500c900e00200100da941c800c000c1d50082c94110950540f240c00b81707000b200c203030300c403c140f080000204000400000f10036900a6500480f00c00d5813100729410303080420166070201e0b4032440003603940e030b48000510030654902c1c0507904803c004502c418901c03807509a01c94100620290460b401655414801030081c90b09100e00c6c0b00d035001c403401407480010600c46002c1c8dd0402680601400558091107003464491801903030742080000106204000303403402c010629805c200c03040140800081c40c00000a101280a5441002c0c25a1078111100900c05c03843c40340d510040290454407020020146614102e4045e880b803210007083c41d401000d010344a80c840d40900e0124185004003011016601140f0310744003e80a500f03640344644070074502c0d4241d650b030780208000c50f0010000c180200300d031600c0b6071605502c50015240c500e154130a0740d500311001d40c034641420b180c0001d0040b03000010b0f201c4243c0e01ca68020f8441c0412092500070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 998049082 1250 998047832 998047861
    0xf0912120c150504061d0f0604061a0a0e0f280b04090f0b160903031e02010608060a0207031b05101d190c21151d0a1a 52
    0x110018002121030300014041d81482c41e10b8502d1a04400380098100b901c0c080e40244203030b4858aa480481241c020444040403e011030082c0044e002030000b03844503140c82d80102440480c800441814403030145c00c58031800c030304200800082e00441528940345003005c580100003010440c41e0500d08003050b40d480b001055918401001c01c000080850324000841d0017005d4505000d840c201950070780508200d18007400030300c62440d03518881402c20300c0340000d680c0142d2500000b004101c00741c4014154400d041c20701004203000c0c1c8000702c0c0140c3d4035500a418408165900d565040d00000c1078001d15400c00c0d400030a00841004400244241e921401e440c1c10844100003482a169940d4000b0644800a00b60740c4a03914401d40390740c0051042044500d4a001034222540d1100c0000002c45900140624800d421001030b840032030302141d6920f0303641245086040600342e6072411a649802110b02c94820050045801402212a10b08010301c030114907a00050000d00600d04200e160009001c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 998050332 1250 998049082 998049113
    0x6060206060618030705120102030406060501030b06040b03221b1208190e060f220806070503090304081506130509100c020a120801030b0f160f110d0f0912 68
    0x41c0008043c0071072000a0500c202c0d640b00984c0101d19001e1060f0521065004502941c81400c0c204076141e0344074015410f603070320031007a141d000c00700f4081007100b81c200c3c0e001140d100d41c600d84442e20079058040d101540d46040030b02a50320109450f40390b600c445101484402070400000c1c41100d110a566406010748a58143d01c100f00030501c01c0d070309420380110012462414000c0c01c6079103031803044001800702d801c50408951a04140034889441c0c40300981c01005461700315001d02640d6403080001c2d00c2d03541c0050240c10040c40204000182440d042c00220b408100c510750240107424030100b0046011032894424040900d054240024001e00168134401440d9048000c1200e041404081c1d040540d01400501001102020726100c141e0000d01c00d41a02e02c610045d1b1240c3c0c0b501d8102d40c4561104035412a4040c0e40c000604000c18094449003035044403074074210031121714410040c0e040c624101101e40218030880d03001c40380ca5402c00c003a14054002c1d1f661a44083e606522030107000716a101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 998051582 1250 998050332 998050357
    0x203070f0b0105152727270c060f040f090204031118070e06040314010f060b1608090a090f0b090603010b0603060d110a1205070e0408030f060609031f060602060606 72
    0xc118082c82c0c458180384a80c407041c6e202c0002c03a0041960140c4003056084071070031800010341e11071181c00d400304100c4e0743c100d03401107004140c0200c141080c02003076440f425860603813840510000450402045821000d002c1c514005a211032031403821141c00c55016001d41c2c416000c50381440c05030040080c4a0398807035a00d18016515035050004a080c6104d90342024010421a4000c00491481500404080c0402e04000c12440d03989020142c1c80340258403030b548401c510a41a20080f8156202030000c4020050001e43d4565842d04488121568031084034800d9403105420b245600d0013080c80d5500c450250004e00c0040d100c8000600d4038030004222521940c10a4121024010b1400c4a441e402c1c201912500312a5103070070b603074008500200804c40391885500404203400603400b29041c007541d8000c101c03030700b03644500344100031840004200c181c0050041c0213800703035503904108144030410440c030b10704210036483d0f0080042d62920f80281c001d5501c402c092055a88030b9030102d503d003c0094 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 998052832 1250 998051582 998051647
    0x70509100f11031810030915020306010504050904060b041410091d191412030105010309021f05040905010e1513110304060218012d0203070f0b010515 66
    0x1d4030a03141c1c41009106400c003803101240c1ca0300b07504241481c441d19200200c402412504c81000c04070151010920014155a2a030401c07000d00045a0095034004c001414000c0c00c0907141c0c0c0200d642c80340215010351b503075915255010030b00c7c180303841011180380304203192542e1451f00060941c85040c6512510718126620a5010100d0342c40b800b024004801c0310081d80e400c15481041ea02d0808500c0e9410340d500703410a1410310031441700003260486060080701860441e807030b050041d03009000780c0c00203076000f222101c090005a0007060380120446d4494542035210750402c0d22090440b00e0503041000c080b24203106200d00560042d03020400341e582120745142d849542038450014008009e00303440c00c64404020b010030044150060a441c2280100b41a040520070b401103840c2a04070301101d1441e000c0317844044041c41d030700701d80b00001445801160328000310b075651295203428000081c1d0303030052010014002440c08030500344070b2083d20392190f41068040414a0702c42070fa00c00c10040100c001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 998054082 1250 998052832 998052857
    0x5010e1303081303091203090806070201090c0312230307141309051b0304110f0f010f03020c0f060114030111073c0c06090b0a052a0304060207030b07050910 69
    0xb40b07040e080584813146c80c1804480312890b029019403580c1c001d11025008100c000380f100b510510598003c260418200c900003851a1181e646118510700c01004000c074105500300c117210000741d02140000a01c0d401e5036a440c1c141401881c90701465040d2089541c20801c00024000d6808110191a5017200c001041c2d00d8103909104a40c40000d103d021a000c04010071050040710160008484c5060311181000c11545042140c0c64900703208041c0070034a00c5083e81030381c42c40313a40a4000d00c03e00c682100d401603101d01c10340b0714104003607100040c03514400801102505003030041b0091403401500c40f5041c07550700daa500660010302e03c801000c8124400082c40180142c0c3c042200c10095944501e680800300c0c140490701140340c1c028100450100c4d0310000c2c2c146480000c698100c496950749c0f13820824041a0b001d0b42c43e03400c4905440001e010400d03401c0055003400103000901c10ba40080c0b02c65450b52900450140004103464140842407050940b651507415241c441c074601880e000b001e5011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 998055332 1250 998054082 998054087
    0x280e12060a05274602130612051213150e040903031d0616030203060a030b070f03060b07030903030e01020a060f0603020315070504061808060a05010e1303081303 71
    0x7402d03490007449160b140d18044984801050107051078080b100404c5a82501c43e91031a012214902c030368052001c41e2070795807880034044092600245c402001c0c45442441c1e0190081035030115009444004a540074103401c20408012140d540b81d41e04800a081024441e54100701c070b05136200325020703e202c41e00300f04040d41c450480414000002007040020b4402c80c24001d00806428401c46821028444061841c100000c3c20710722803075000f00c110040c2404010220302a40000c0e040702d410404e4040b01000081a0f9001244500050356071090600403a580080944080354483c50000c1c0b4200401004664010101c40070750307400d810702c40c040f040d884004030f2030048490350241c0307414a0701c0c2070340d100c17200c4580050342224000c4003101d2500e010883d07010140c510646031200414010001004054069047c002c0300391441815a1210b0360340e00141c1e400c1803801c6500c0c0301c07040c0d40e030401401195000c0700b40d1342c2c0285a41030301070042080d59030094a14540030348000c101d140b01c0e0b20311004261 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 998056582 1250 998055332 998055361
    0x307051009050f07270b030303040f021809030301030f080d111b0105010e040f051203070c031407020d151808090315100308070602280e12060a05 64
    0x1640001110034005036010003800518155004940700c0c01501c1e900031583d080043c8000644088031100001810f40a05510010840b00c040ba100d2949904070304005035000e2010314440e43c010440c48080c0940ca204214407410f0b6080c0105a0403060001e0201a0030300100303981c15240d20140d07143c0c07480c02c2410824150300070310030004615410000ca240071f030204c62015146004104507000e0380b10f62150510780c00d88009005180c0141013290025010410105e8807000c51802a01598410f0001180c03d00896104990704400b15881016000030168010b9004510601701c080701414154a580002c11603941c0e4080a04034000f009090940300e206640103001c040e0f4002c0c180110400c461801152580080034040c1c0300c1e024600070024030990b40040a0b10034682d0020300c02580781107544bc95955003051209440c1c2540c240210108001406d02d45080080c200b032042c0600d48031040300500120f03c601140d40201402003045058050005480c0c0d080100d051010600350340d8481150b902c1e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 998057832 1250 998056582 998056597
    0x1107050a0311010501150c0807031814090a050402090f0411061b070e0622020904020d0506030c060a1b0f0c0e070311090d0b061203030901060e060f09070c030203 71
    0x5015851480c0304064000701204010041c0d10000c0c08035030380e95148242d00342081500c50001c280c0e034806c2c1c50005114039004103649442410074414121060714805440485330f08200308004030410001c2d1640b6250341c01940c07102d2858070500c00b501e0940e02094070381e003000d810b5219051244001c1010400311960903019881c01412081c0c90791a840000c94040c4d1030700210304e803a070184200c08500f5142e03024000c0c0c4504000740107002c1d044c90181c00c825a401c80100314520aa5090000034070325035880c002894901002e410210790b908202c3d08060800250100481c4169400c02042c4080c94100d103550741004400d510a0b0303001c044c1410000140410300000401c150030302b0300041101d00780913014a01a00ba1542c5c101300000c520031808040744500303d44540d0010520302034800103442035540590040010b01a88013044030303100a50300e190410741b03410603181d45441003440a10144000140c1c0524111510349440145d5000301d1907203030b409800c82c2d00b00484180701344103040c001c10464080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 998059082 1250 998057832 998057843
    0x60c1506030c14031e16050915010807030b0303041701380a050d06051e09060c0a050702151921090515040309050906040207030905060d11030108030307091e091107 72
    0xb8006000b0700caa40340c6d4280b4000000200e91990301050740e05004440341e1244c25980f20500e0609941740054032200d40041040b010151140d810074415142230015000030003580c070f0101260340342d6a4030542035904200f02c01401c034030364140e40d940c07030b054020600511098039910740c120703000c0c55000b0a600c0342042e00480e410142d58448001000070503803095100706445c401b80c50340f000502c040c507210110241c2d01c1c20031035401403001c07071100400800140002c0180342000b81c5000316039400f00c1c406d000d001d240c0310309990012034175003c60070a500c05400100f08516151040c1601401e806e00c603800c1a40c4401215aa1882d04004010041010464602e60490308114030320f000c1c0340040c207104003800303034074042c080560100d6070070304060090303d441e290305840b5450b90604080612420f0f4218031041d205045c0c41d511901001c0005000a6002c1d04400001e10f40c1c07481c15a0300a014030700c00d58003034514200c410004000c03071944003d01ba02690511a008a020280d00e8a000c8507801100006001c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 998060332 1250 998059082 998059123
    0x61b121e02071a0108070b270907031a03030f07060507020a0f05030406090621050c0412060209040605030705030616090e01060c03030c0305090d05070219060c1506030c1403 76
    0x9101c0c1400444064003c105020011070384c8640342c0c01d413100824481c607540b0100c180800c60018018030100041c095003503860300c1b09005000c000503042d407416200c1d500880c0c2d07070b08901907495415102a0508003c158000e514004040502042e1446060070140200b580c43c804940164828400d01300455041194042c0c411401e04190381c99512a2080c0c10102e09441030002e0002e000b20040d03e13811480810303c440c0ea43d10700030a20094100282491401c0e9000c00c4007007009041d0307008424540740240e10041c2c468418a0600040b0f030883d8201c00e20a0b8041c1004000e03d81d0300280845d405504980c21401560340d10106a40c0b081e841e070024142080d1810010401607403107000e07501081d01a40d8107010f812141c1e503041c0c0c00c075002500d0742030140c8c11101d0042c20950044006181c0b45101034194902400300e002c0210681499403c510005030903007010300b052100e0008040750210a0842c10800e080c9140d40c1c070120701c98144110040c0f4085200c0c8032203240c1c1c1c10b1111003035910003071146a0b0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 998061582 1250 998060332 998060347
    0x1b010204150f030b06030408181203092b082503030c020d0e09061c020d0501051e011d13050604060501052409040914120304061b121e02 60
    0xc0780c0c1c8021250005100e041d45a0718a0b101340162010058060241850b40c0c64035112003180d680708444400340c42042a000e1001174076110840040003071082c4c0915141c2d000d203010007843c48031f1040110020741078a40803000341840c03180a20305142d4030407003180e960700508442600304102480e209150002140030f000c203141d010f8100c1030340712120303a09440101d05a00000d440444074811840d4002c0141c3c800540d01d800c00800f9035066006003400408d06071040e43c0010034610328a0000c0351aa51294240301810000001c2d06940c0204464022034a41c1800e030400b490f1881094419406014000850069181030014040858000042d10000e01d400c2c14410060403080c4110740c00f480c0303040c1d1054407141c48914401c03401c1c0000c0303111900e414004810480602940a070607601801080f00007002c1020812100c400510034101b42d540303274a4542420400ca0b42d8400020706017681800103003942d00c0d03100c01c40e9130380c020f000c4400140e0010740800740c2e015103401300940c1c6103032440000e00d0f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 998062832 1250 998061582 998061599
    0x9070b03010f0303080a0c0c02220612050f0607020d08041a0907060e030c0a03110103111204020f04050708060d0c1a09100203040303090e090c060a050c01050901060602070501051b010204 82
    0xc0b020b4900076180c080d49030321130808140c11589030315104000140440201c80040c50f00c682c0f44600c002c1410b0042014a4807020441c00311a100d81c04000380300140440b000c20488240700b02c1c01200c81c041302902c1a4985400069103031030140082400b000149000201004288195002070821100d0315081600e07000c18541d41d52800d80c010440800c4058a10b58801d00d0006942c0b162000701802e00301c20f062442d9074980c80900c4406503541850740750000080d0040c8444050503400050004400c02c50600307005001901c3d800b484143e000c0d900780310400031103603003200c881038001d0010307140c440d17466000d414103404085c3c1c140c2011012200c9004401c101d400101d02800702064200c804c40e01c40036a446050703a407031080c1c0c44018042001906c040244000a41042e075100542c0350031f86405103404000900181c1c40800d0400c00318a0114840b0303100034003446203d52107480316008103c0c0a06103480a50303500d9242c4101c134100000001c801c01421151720034403624008010007551030f1900c0340b122 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 998064082 1250 998062832 998062859
    0x1422090507030f110102010b060a120e010207140a0c090501050d080c0f07060f021005040515130204150915360608071d280902032e022109070b0301 65
    0x9545c0150300b004040582d5142100484040b0080354036122401e0b50620b2200025141480e40341055550a10030300300400c032004048501341b580100509103e081d1803412300021725090300540f501510704001400305885ea80c080254041e00040d155031511000c040407481c017101c186d81a10b040c001c0c840f00141190b08445c05c140e0510140d000d5a00c200200f4403031504490040314080c1c19030b80484100c41c807510307200f2003107908600c0002a5541c03010f943d4001c1342c240c541d51284100c000750010020420307503a07184a031065643c4107000ca14860b40c649035101404141d10388802d008240d4000c4414501103040c0380481c1d20610510b4180403181d5149082c54403a0f5151040300d8038240d80103403911811901c21400ca00c035082814010b000090425890f01c40c1886014046035410b40c1c4840c51005650204aa04e0300f400220100b051044040882003685246050380c0851440c014042508404c0003410200e09a0499408005840c0c3e1071402c0989480d0b5181d200329201d2600100126584100064 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 998065332 1250 998064082 998064113
    0x3030a0302160c0902041a0c07053c120d0905011b060e03070209101a070f080c2d1207061d010f05010e0c03042a0f1422090507030f 58
    0x1c080c0c0c0b020180010170747d402c0c400d980007184503030080c01d41403017a071500c01c000451800300c40152003100002000c2c0e100300b502e480d45000c10130381075500c888205440e0440032904104030020141c0041480040e02803c4400c00d4041c2d1030500c0150150b2000d040f82c00e1401c0180d0782d070400010300c6074a8144040640f0b80e4003011059008142c000e0028914030b1050384030f503040b5a000145944030000c0c9a10924030703500b000504503200c0300120680400324616402811082010b807010744100703a0f040d5503108007002105810201d0a00650318004007540104004d0009403034080581c0d0344017074900c0c0044c0140704401002c510015003030100e0210310b80c1507200d0f0b003901c80071043c00c1200346d80320f80051000110840c0e003121280401c000103400035940101e2a04200c03514402c60644161510514030040181c0c0c002054140700c4220402c104503031100844044003058540c5005014034186181010220105090b41d26482d200f4a00070400e0400071100259003002208907038849034a000d4101400151 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 998066582 1250 998065332 998065349
    0x170f07150b120a150212010905070f03150e040611030f150604030b040f06421406070807061a03010509011b0f0905100906110c03030a0302160c090204 66
    0x2050110a0400c040902c801040d560300600340c4503032650724080140701d249210841c581d0240664840101d511007010b01906007080007095030b00e0059801058640001d04074010181005115100c552602143c0015a859000d00d650295124101140944404862503048107400001c11044c0c591504000d03006580c601400c0c0c0b100102c076420000107010700d00010b48101c00740004a0005905040444c0da000e100b42c1d0041240c0c02c882007a1102205002c6920b450b0030000402d41d2942d20200c1c91500f80030030485004840745041c106035802403981c40341682d0186c00006903074020b10081c4070540344c201d0b6010506105035500c980c6540c05121810201500945c00c100c0801d9a0b1001030003941c1085100c407001903400800d485044406401c114903400601944c440b000c00d26448005501c1d0705071015803200c0002c145440c000414101d02503074902015040051005c85998011048580540c46490301580341c400b441500b480f01c4000c48001412292040c90024891003141c016000301c07401d11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 998067832 1250 998066582 998066591
    0x6040303062610181709030c011106180f01020f09010e0301050f0402060d020717070b0f010602071a0c01020319320a02040302031006090b1c170f0715 66
    0x4101d8070501e078074110082c05030002d84461869800c1079000d043c3d1078500100c0440014026150945c44268448840120000015034082141020800311005a4080c03a14085002c0460191515a0340284c00c401d0302000c00a07120b80c5100c0e040104554881c101c6008541c0c400a000440105a0000b802c081c0400d0000d04098020304e41131040c148542d004602105507982c0e950b0810000e90305c48510512195424001200480c1004021101c90b42442c0710043d0381c0d000d2410900005107000b482c40e10302c5502d00c40180312150340404d80324200e61801c5501284d045003405c40b0702d880c0c01090100403196201000300405824506c107032640c4010b40d04001c01070005980c3ca45040c2100492020041d44240034040215084500400c8d90014201e80014201741d207a0340000e04103410182c6002e5010344400e007d0084d2291131003100b0b2040001c403051000c04130300c6100c50800029000700030b010080c0c03480000c65401030103421185805c00380d9000302d41d00c0c1158a0403a5201420b030600602d4039251 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 998069082 1250 998067832 998067869
    0x909070c021c0b06130609090804050901090605011e230307080106020f030a0e03071226040e0406200a050c060a020703020c130603020d15050717011a09030604030306 73
    0x156060b0764181500002000c10698951041c01160344503540380506550340d8030000103e0109520828020318070a03103403195918501010000b9018040c1c00ca8180e50b0b28204082010f6238100c00c1d541030300801162003c0985410300c00590f0a0741800c441c00029031181706030070483c0c015580081d44603200a4450b44401d9813145c800303e9681c0080e60b40905103510800c0f181003030701e019001c8140701d101d0083c00c40344082d4a50b14502100c00d5000c000f190012548002d800c1c0c4555011109044d070f03040c007204a81048e140200881801101420142501d90b4408114242c0141c4a07404d20444850601c2e4030317603584141c00010120b070701c4191010b009005820118a0640040c02121a50783e0542d000b05410003483c0704120808a40d804902840c940c2d6071000001600c555030308481d214010300444c1c2081303203c40488d01c103954005051030108480c0b11617510902c206045601d0554204030420107171040204403000caa0310a454000340c0c0740c444c400030401090b501da0041815500342c041c50790080000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 998070332 1250 998069082 998069119
    0x50d051902060702120702031c02010522020616210e040f18120203041703091c0f0b18120403061b050d0c0912050a0201020723040209060909070c02 65
    0xc162100f400680015490b6401100d83c0c1c8050304075580024203554a04460010640012540c0010700015035142c00421205d0196034181800c0507801c56415405410b4035800501f5500ca02c000c1440700f03980002004c0144141c2c051b03034410364090f00c0c0c0706e0002040e9010003e0300003000c0c0c002c120701c00d60030075800e19070b00340460103100300c40381160018110049441da640307641c4e060700031012030861000703000009011142c6240c80c0000c60160028555817040e4805002c01c0e6402c81c03208400103040c0e50000030018105001c502e03d8a90009080d0100e600d80110450b60910a244803d803248a40070390710030720345d803440d005004076881810108101e0520000701403d040081c1000008140300f404440f940710000d40041400102500d440d4101075120243e81c001e0403120344083d902070740648075420440d40c0401109002d454181c0950303050b4145003400d10488000e01001c00d004030740121f145145915044140d5089110050100c003c0b4a130464004003000071001e0306a100310409400450f1404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 998071582 1250 998070332 998070343
    0x1509130c05180f071e090305010c090509130503040f0e0105090a0e250e2815050613030602120717070c291e06060f160609050d051902 59
    0x300e5002d4200d550395502c07080c00715107420007000e00c024000c0210350358003814281c2da1880702c0c2c0b008a480e8007201500310f081041c21250310310b40034001d000840d103051241d07950b51085182d00c00c40d08400401041c0c510b00c0c040741903004690240c01240c4c0700040200345101e2504105050f1703201694620a140c2d1030030007140903038160340000740d519001554030003c007050340700c0040c0d40c1024624201e0341c1c0a9441d03103049440342c0211001416106c4014282004030007599510200b40d1070100280030a6661010842040b00e1a1060501c04c5200040464045024222990055030403d00454131075520154220014000700e686500048a48408440100c244907210b03000f00082c1c3d4480b03031890040d0303032a20140c0400405411550b0440910307080080410b0302203a2085200108030381c802c890f1030034101203080f0040e0a40348202c1003808201c0c804143c0030700761990711005413551505c409113800d18800810010314090150f001d9001d104980740c0c2c0050003081c01c01003404030052460b02c601c5040b42c848 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 998072832 1250 998071582 998071609
    0x10605130213030f0f02090a05041511040506071104090f05060c0406050f03190c0329060f0f0715060509011d070f170108010506090c07050606091509130c05 69
    0x29251190103101180c1c1d00703081c0f501180d104000000340c1d0500c54000610441f021039880e00c003039494908020810043e840d0054032100711701400c0c820703903e2a0070080504d00079406402d0203206c0114540083c806603103001d082c0c4c0d80c00507004020030007150500400040351000300361050b00c600004a000a0f000394202c80c1261590380e5064100340c0c40740c03448001039101034170400843c81e1041940f5a800d0b407900c1208412483d5860004104200031682c401c1c0c5140308020140e61048100c0130885521143d04440083d15044480c556446c85001550b4281c01104006442006a001d07501c071030011692060042d544100c03600032883c1c0e80c6101618080009182d400f2605070a040072514050159140800c0826641400100048094005500c0a0003680107050582d143c90a0100078141810b14075000740038080400c0c581522a02d842c1c1c2d0f50000500801d000d40d064074002a44100000c1004880b420300901c40101e0b810000326810329041c45400544010103081350004141c500711030041c00c031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 998074082 1250 998072832 998072857
    0x3011415041112061903050d09050906011103070803131401050907050616060f1127010203030606120405030415080603010b0a12020d060e16060201110717030a1d0106051302 76
    0x55030b9513414083e0902d221444800b440d0983c02010000030002d00c8041c81460041e0340d48035105182404002c0c10190103400d0321b05200015422192094021044484540e04421403980d079031208007041e002c0d1011800040c00c115141d180c00d04015106420607402102060700f02c07181281c990080081d644564100701d10300c0520b210900000a589401141c0c107086605000120909104400c9280c0d034413001614071407001c4527000111601211501000c0d440007031006600358900302d000710307000c0c0c070902d50031000300b4400100240810008108031405812104140400800c0481c0080c021003400da419a12039420222140c4550030400782c000119030710107518003900e021580038000c0b40134403010241d54154455601ca0b00200302001040d4518036101001c800b070f64030b8210002e085480c5129001d8007030a0070000400441c2c2c0003408441c0320000003442c20b54036118400903074001e20300c0f202d00b001000d035640d6000301d5038403040d0b1100040380e01c180e85501c41c0ba40030404880c101d100e8132409080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 998075332 1250 998074082 998074117
    0x501060f080702100507050a140f03011a0d0c0504080c0907120c090b120601020d0c0803060f130f1a01140313080f040e0703110a020703060506030114150411 69
    0xd80324820503000b0782014441c01581c03503901400060700165101211040d02050300010403403191940f001b40d01241c5c4008012480c1030030101017003100644010700c40c0d500e00ba54a43c1211078507070322850444100540034401001240901d102c0a445500548900c4906000e0000248003c2c01c248007681d101e65180e80d00c041e005486c27801070f00d0062901007802400c003c032002020516000e07401c020880440303485088126072820304e00091a14100e8070840741085242040c22002800180c156070300000110b03407401642540030081280704c000c000404140d68140803002a001c1070580c001c1107005c0c03480300806621385480c001901d0700c03d43c1750380c0c0035002c040400002d00c5610803424840072803441009054a0001001080c01d80c54102c0c1d00301c84022120030703003407240301501440342d441c4c80f459940e8028106450f942c0c0280d201c40842c071000d40b0b115150000076400e50303401c0d03000c508085440c0c1460300580c2814100200746a803681710460041c0d1a10300c0122800c03440c841541d008800c80784000c0c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 998076582 1250 998075332 998075357
    0x90605150907031505030a08030412051306032d0b030f1216240608072301120216030203070b1008120f07080309060a06051c0b060f120d08010603050106 67
    0x10b0082c01c55562000040007120404500da507070500100301f03a5400303078401e503459081c107081c090f0811040300c1c40030050083c1000100321051810140e141110141d08000a60b002400c080f03001400502001050900094881c0b200d040c44641c4142c400c01c005400300d96a04d036160a203152b07150064040203903c100148100d12040c080700c1401c9003482d204660700004440c5007032801c60108421000d11200c2501c50030144070f200c01c1085080c0081004021a11702c0d814001d04012511515414482c100301c1c2c07103c807401000c4201e0b0110b03090307107010b280c501d5040151824000e40701c1c1c0200310f0444560390050b01040c802e8074404040c900395580200a0300794100784090b241202d902c02c2c0c41e90b5800072014013480d030100c0c078076001079481451584007410306c601d4624801002c03103021f900201d10070585c811454003425141003424a100798440c00e0803d20307480b1480000c0020740c14074444c540c002d11048032140880401b04189100da0340b0b68840e15031903604d41d8025010388009008980004052030b5020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 998077832 1250 998076582 998076587
    0xa0906020705011b1707050d020606010903150c18090c02060109050f010e041b0f1403060c0405060901120c2a020d020f010e0a1e08150115020f030d090605150907 71
    0xe48280b00c3c1d005e1504000e802607203003001d900400f0003552590043c40100034034903014450103501001c00d18000140c581965a501100808404001282640d0701c082586150281d01c2c022144d640210750503100c03641d1070103c04007034200700c421400140030719000001e0402050141c1e60261031000b1041d03946a0820401c9010040f000b00700341c07800d00602040314112085580c0b1003000c0e20364804040101400d10711507034208542c9502c058000d40c401d0b0200442454aa4103880989004841301940c5920000048642510b064000e0344414501020042c0490b00200b0481400d44284913104035543c41c4c81c0026410310112501075004041f800f20000149800303600c504408005040078000101e41e80c02046003c402a00024400310000d04450b005000720212032004181e11001442c01c4121081c00b141441010300c41e82c1d050400d0044524081c034020301148460a0f124001c42e0b0b1a82848120036001e00401101691403034901808075042100e060501c009818003d01682c0007a00c8080c1d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 998079082 1250 998077832 998077877
    0x30a141b0a02070f080606090c3c120a1b080a0c11030331020f190b0c03030411041413050c060f091903030903031809050106050a090602070501 63
    0x218043c40b50040b0303510240f09a0354015019100040c2918904907062211800c0c0c0580034030504601403000c1d9180390021607100c0e90a4007a605420b078a40002d49040561034600f40290300710020118003500c5203c0314131281e62041c00b00341c40501c01c0e10300e459886800c0681c04000302d0002403000c00003035440740b041e400116079105549000c0703246404e051455404d54100b0794840540e8070601c003c4500fa6407903002460001c520041124a00002a6000402544201100c18003980d42142600c9960843c0c1003000020052030407010303521700404070340c66200d0388100c4044501907050802100d0b10300f05403050100361500c1c450714103000e0310f40403140d0b9030140c1140d004490900c15645042c4060b1100e8024000d000e42030310b45140c4402e591020080c0c4069041d5000042d690a0902000401e901180110440703800d41041c1d4015804006440d401040c40c0e001000c00f2401c0000003d45230703501c60014440010159180105030b612910120386481880c07107000d002501742d050240c041840c4205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 998080332 1250 998079082 998079097
    0x307020a063305060405040f020d0c180b070804051c060e070e0604020a021e0102090a03150c020c06030601030f021312150e0a080d14010902030a141b 66
    0x450356510829550102603416080120142c91800400c03142030320003203a0540c00310b5182c40e9045010b181400080340301400b440c4151841142c03a0070780c0710603c250542c11a000b08545c0d8006001c01b01e4012005420303a4010031060800e0800c41100040001d12002900c103480d901602940c039003494001000f1030107034a00303041c150b84099140f4840c0090381c58403501c15045126400381401c03510300340d00704400c00704c0188405c4c000d9004002c640306450f0b020a8100f18014140d00c2c2d10707400d603c090b01c058024003c03100e8039500001046404418080082e880c1c02c0714520400d01408020258001261038080c5507038410303002a01071020400e0713503000745c00c1101d05040100005081a0000801c400c110701c25500131915842d20429031010311020000003024000110014040d00c0d680c009a240d8a85c05140064240c1c200420160313003444081d04018115000c80000c5041c40d6101c29001c0000e500c107032504400c0300c0c40c00c4002600c81c0c0d43c0d00c40c0300d0b108149004010082c000c020181103840d038000c12 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 998081582 1250 998080332 998080337
    0x90b0108070e120114070207050a0302090a2d020d0f0213171006120309061412040f0203060a05090d0f02150a06080a0606182a030f1d011b0903080307 66
    0x1035292800c0c40c8244a185864801c244854170113040001c80641089191740120b03009010000301031026031141036403550030512600001950f224030005481310b005000030b0003203041c5042c3c03c04a40d044419009000007801e1503108000440003148880308900c0b4042650300c07039004510b002c005040851f801158000d03200302c1a1428001c005c4c0e04e44003100d000b50403c849a402854540c02031682c4200c615001c4c0c1b0050800000c100a603030418042e038020200741c02c0341c0c15030b80740001d002c1203406001c04e40c05580c00703000c852150401c3c820640c00740c141103803a4a6a80302d55080030040c0c0d403080705a9060341825030050803a0302048000c1e5100320500038000b010700c42d1218000a803e11040002c44802401031400040d800c1c2414550301400419012000d002806c00050000c3c6110115044104000c507400c500031481c1208400e40c050124012000e100925082201400404800401001030240402041307a00c0c9858038000062243c1d0340107200081c0b603010240001303039401c401140c0040d21070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 998082832 1250 998081582 998081599
    0x13020f1203040608010e0a0e060c07020a0504020a051b030a0509060c191412130b07030c0204050c0d060b0a0f080403140403080a020d030b03030904180c030615090b0108070e 76
    0x49000391865005500ca400003070b039904010400c42d69803a8480750020841c0e2420b0104801c100c0f5180c0d55510302074561400300305c0004403101150317600742201c001030001074400e54903035034140380183ca190441d01d28a40403c4000e512440e02c0c81001c012038491005517220706040c411940b044c000d490b0040403042606111b203000007402c0c081ca082c50314a01c20301c1580303001000d01c0031701440c509007240200700c0c02031841e06102c0e1741d2040c526001c0c040180c0307440780c0c9003586070800c904080322071450300d40b006034010307180c1003d128181800c18000c101c011003105050040d40e6480707850810a104400016000440820156240a00c074040041e0014041c0c40c000a4613110580741a94580c4158030499500e0000200c205011f90180042c042c0506c03d8101044600964030107c0d489218450440348600d0351001c8030151080a0417182d001140c0107403142c0c007400e4030303860100e005102c48004080007200002000030800e20900800ea030041041c0e594200544171000150b0f44184425281940003048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 998084082 1250 998082832 998082859
    0x1d030304080d14040f050919050a0c0e030a08070f2d03030507021b060f0c10020d050f070509040b0409081602010f0c05120d090f0605160813020f 64
    0x400140c4007034090240a46800700c005a0050400c007034401c506207904606004c1013220201404286003144d00541d02c00c05540d031a000581645c009020100181901e0301c0144051084980d0004043c02202e4840c1a80c02c2a85010182d6031485a00010000c19081080c0400288500f4001c032005100780c140080c440340d201e072007106890300c0c050305a07050825052400141a890f003e69600300310107002800191841808501001341400200f9004140010311042001058421214041d10120035100c000c1900030f10b110207507104264000003a401e082c04188030034800c2c501940100a40e89842d85005648400d100240041284442c0d1081d0b0366801100807070201d20080c00c551041c09030120b030488852001500202d02e00010604222110464600140002400452501c0d0703041c9100e8580070490001e0000d000440c00042c01d400d25030305203004105180c2c000c103010b04113818005106901c1424112400003085400020305d4a4034000701c0c02509107040300d9000c01d58051b2040019000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 998085332 1250 998084082 998084089
    0xe13081b060403030b0406060c030c030203090a06020f0607050309031c0225120203040b09130b2d06130b090a031e0303050c0f04210605040c0510020106080d1d 70
    0x204504000c4880c0c11240400c410540d05200f81c65001100310b400300b042038140361004101d80d05104005040c031038180804001e06000f0419107161002c01000760821544030b00c8029200e503903c100c101c482d1f00c80d80020070f2822b40140241c0e03204040301c3d0300842c1480b121407071031101e45031a440c1c504981c031ba00304040f5051801440c400da0318280c20b1441001c581a0500d03103680384045141090045420a00061207400a030354111070502404907000080c45410141d030500614107080114ce001004c10324149408169010030403500e18442c0141c11140400c45c14440980b003000307941151840080d82c14003000c65200007500390303243e004e04001aaa6185c1ea9040d40f1240e94244441a1060f03000d01e103c20150301d07001c1c01d03600c20814040e0728148545104000300c0350107980200c914240300003104041080d280c05035580c0d0395070000c4013885542070905000081c41614010140107400e1615103008044c014055141140e92460041006814140341194030751030380f0032041010481d6520b000708568 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 998086582 1250 998085332 998085367
    0x61c06020a050c250603151706091606120504051c030209100314041211150a050112050703060203130f080d0c09180230040201080a060e1308 62
    0x44250b11260b03a14649024194540f4191025074809408120422103940503515105070480e881c42c1030200300d081150701c18101c00b002d981c0003c0320f000d4411182406040002a0081c0240461810340b0390681d110049080194128014440420080ca8880350340010a50040c1da04c9402401a9546480c803030803001410603800b0300820009801091074141481c0004095101124a05003000110100e211500a04000a201070b02800791032803022041400342d03080702240000b41c0143e890901c424a198146420142e400c0e0243d0740c504030011030340707150304c803040c040d01038205d001030441c20b2956a40d4406544010481e020301c0200f43c61020016122148218040303205801140d140e0450340108400c440311614020b003006017030b400420071260200b40c1103c2c1c14071413620250390b581c0c0303401e5420010801d8400e890501078420807800345030360b1030300940c5000c6d030700c00d80e5603000380e8486840d0300041d03540c1030281d06180c000301404108401030a0110000c01840780700f24a0a10100224850884 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 998087832 1250 998086582 998086597
    0x21c050a02010e0f03010921020d210e0a060e06010f0e0621031c0f0c1d0d0206040803120f0c12192c01020715051009020a090801050a14061c0602 64
    0x19002380c00c882030145c0d400c25000500003030501c002c00107c81041001012015aa0b68032602581890003e15900d0b800790043d8000948980c01c8500010f950700c0e24074014140c00d41d0007601806100008900d140e050802c3c1c004440000d1801c080907140c03071080042d41c0d0148140100c0300718508800c42c804060a10180606040c070a07140f01219000c42905002c2c1c64803040114022450011002e040b10f80011450070301007010000c12004201400c081200c0200703003940690300c42000328001034004000402030001200c0c144100f406501c2e44141150701d0031043c2c61411000005010748010f00510f40c41546e80042d045080c06022405070750380c0004c5072200d1003600303034031094840c400c01c941014040185590030180c1c000c51030030445444030300c1544105a5480d03907007510b0f140443c0b1400d074021468070180a40400c115941e86c3c00c0040900000030521504519500344170000d0b040002031f11907411319090301401c1c04800d076600320400c0303a01440d101018003080d14480245011520f240301601d100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 998089082 1250 998087832 998087843
    0xd021b010e16080604030503041502040503030d0b100305071b150e0618120d0f3806070b0a0b010c08130302090f07211d0703021c050a02010e0f030109 66
    0x3203407010b001500040c080e002a031455000760213101c002541b0104503544240c0100e80340010703070341c1e85980c40064440c9078070040e818400800c40c40e110900c0343d4400c00409078101d5110340c2c652954281070702960742c00c03100b40c000314a451000395007a83c002054121000e20130080400d02082c51450300c000c0300c8500c09078a03580d5018a0810404000710890010025612002000118940c25403071030248a08120250f0075034503521004443c1a02e0b8000b000c422400d101d0a4034501c5e4040750050f0003203403c50341007050300c40d9158181014103000040f03412079030304904200a40e41e10000f18401030402450903604000e803940607100441c40c1207000d05400543e052a06101c81e00d1401000304d42c4c500602040740c904154001d200313003640c01100c60f4480e2868281407070303d8049075252100041a4071954480d0000300802c103500f4400000c2a11000d59200322074004c140f0165864095202c0c007002d400405903032200c002e010256024420002e9000d4004200f00e0416041d9000b082c292044480111795 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 998090332 1250 998089082 998089093
    0x6260106140403020901090f11120a020904180308100906030c140613030b09070e0f060d0c0518011503060608010308070c0b0a031a0405070c111201020a0c050c0405010501050d021b010e 81
    0x194548c1c4c5015610031880c1e10906503081080504441c21004009840031344156030014102c1d980d619140c004d01c6810f4035081d81c24856007040c1c140500348d0300040781d0b01110564080804102c16903103100f440103407900314440c241000c0c2894650a6010340c440100350b804081070010b90080704424140001462103184035010b1828078100381032800c071068001c884601400c000304103101c0b0800d00c0d102e5000c4030884650304500c03031360b0803c442061810340000340c000d00030080d03900071002e01d05101c50407a28045c10105c0c84440c0715000301c08640480c040c2030f00181c040001000410300d98405061114014610404010303078070b500c0c000c40340d886061100007084c3c540710714403c9050002c1901d0748200c029a001e00c054070780010000c080c0000b80b14020307d00980003a41a0b2030b0303110040d04100e444803542c002c40d50f51443c0c040c0604408403510701112544035a03888960b4a0a140c0100c0b0304a40068403020700b8622103a0488000e50480100340403580014185451020002d000c1c10100c8600d80c1c2c003070704 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 998091582 1250 998090332 998090351
    0xc14030c071d010501021902091509130c080f0d2a0308011e29160318080d0e01030c05091305060414012105070905040c0626010614040302090109 64
    0xb5025041640840e065400c520540f00400d90f040302440c4100354112a540c415a8580c3c150824010035101040d41090f9690b0400180b45520748400c0089400351416642c40ca07909c40016a582203e80004c285035005100d00d00d013042d02840046104404035194494407084058440c490010504070940004042c2801080100114000500500365500c2000860b03030800c4070810440751507489107200e00100803c1109540342d07450541e030140600c20300410b00d280b06824000c21407600e81d1006000c10700054000a100f4034005100e04200c1a161900410420004019030040c006682000c0510004100c1eaa00c161b03950555400f030410f40800018081c1480f00501084070200400e60380d4041210005010b201c041c0840340c1c0344208a10001d40340c8102da032602d1402c0000320b60020711070908090500041055074260201560625503481c4105444501d03400440381c4018085022583e000d07005001c071038483c025030300c264014410950702e0300760f41c0d50101d10b000000344d100028042d074a44014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 998092832 1250 998091582 998091629
    0x6052d01031505070e0112021605030c0f031c05060a030b0a0f1118060f0403050708061b030112030c050f0d11010b1504060c05010f11071407060c14030c07 68
    0x1d440c5074031042c008218900c2c0c8000b002d00384002059a13581403003079070030545801a0b12074049035480440c010404540c1c0b021807030199aa41c02c03c98410780740e802420304c010481200002541c4840212900704a80b071841c1842140051502502c030700d4110001e1f60001c4082207603402c2041c00390100d12000103003a4222a51301701186e082191410b5a82010081061000c0d03007018039400c00402141c01c96903e40051130008054402c661000303119009001c0c00050181010407030600c0380f042900005480b04400d01000302c00d1009001d603503010b20b00c4400c1180404c0c031600040030110f00c0b81d400c03112030400b50840c080c0b42a1200c51030b240043d01502541284910038001c070500381c074054038044058603014528590500a50044004110010362103c0502c002500100c21050700a1400c1094581e03011103006140d119182c241c586411410003d540b00d00001003c1d0202c48481d6580f0340c50a0b4240d59804a00b41200071403401740c4424041604171b03050522004004100e082080038050308401c610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 998094082 1250 998092832 998092853
    0x40e0607030c05031e130c081005070905130b190f050a0e15090a11070f1e031e0215010e09060a020901051812070b03060411070f06052d0103 62
    0x2c040010074024011113000040c001c400401c9030240c0381445907600d007103564003420a1b07400507100c60080702c4001100362000c50242e80300d400144041c40f40d40d641180c15181c1421901c507141d04514049001020904036520202243e0300040c904c00708507500d101c0c60480c0075100c1e0000c544441111004108900c2c145504000810810404400600d0310518608090042d0b03400b5601911030800051050b80340e591080310710300c4070402100e4907400325080840841d96922401c0b100820117140f60440c01c1d000c12407a18805030f169840e0f0081c80c4d4512241e01c10450300600c158107520848400c0030001c1528000680a8207a0142e4031626203424803509207040350281c03100b01042d1041105000c0d99910804484041e90255525100f00454030042000b0f0310f816a00b0019a0054603004500484114000d5004240c1140d003030003019008060809144280c2100908200825250b100010340a41105078801c00a0b0010300321b50051440402581e02040b4414035460f00c40c400520030024150103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 998095332 1250 998094082 998094101
    0x1080c01030e0f030a08040201140705060a05090f06010302060f040e010914060603041734050d05040819140303070305041a040201080406200a0201062c0c18040e060703 74
    0x4000d0202110b222503113038411004118108150b440000d0250390284901c204200018100c9a079100302504005842d444107898040c80681400d000ca403070008005151035a550340c400180210344d1841e800c1060036401013a00d2810740340300340b10004079210502c07491b900074114828003141e410005110041c0a401c002c0c00b1320311455042c000e0001244000d00101800d005d520305c0c4541d0380d4003104035051204180303070a00c403455281420f07002d4480c0386030305074842c04c920880c1240c107a41400070050701c0d240a18026120325501034040c1e00030324000d43c0303045014240100040c0940d02201000343c0d04692045400f000842c0d210018802082452084000608402a10174201e4101a0300007041381001600207003095403a02070310f40c801c80c200704441c0c200139034050742c0e00d40d41c640944020b80a4000c5200b50007500e5030400d0702d91040c46503643c3d000d00c40c1030040304c1c01c5803954600f8600800c40d0455401c90a2127182c2411095880e22648515402c83d040140100450301c0d21850003400c2d82e040d6070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 998096582 1250 998095332 998095361
    0x90905011d070909060b090106030c020c03030a050a120605040c05030709052215090e0d1211091203130e0f091513050a0503070602190203030105101d0901080c0103 72
    0x1c000e140801e2010892030150f603400f110204101e4180d007004009001e003000c50a0344801f5130000004c10750b426a11207881414503800303483e48e05060004260b01c9002e44440b04002c40c8040000004061040c01e0030528100300007800030301070b030b2507002040c00c071500c8000807804900000280034001c0c0e00a502e90f0b006081c02c513003c00c00c070301d061480341c5000d403020440f0140d42512030310510024040b1010f00c10103070054013810418850801051651200c211070280085211400100c03907550950207010840074441c09901c2c9880c10384000e22022811600d11103040d03010a0000c19802e21840f0200d03001040415801501030400e440e500030140c00103040100f03a41c0c80003a0201c0004556000e850340302806541c03c1818125a041290410080e403100410701c0c08000b44076030802055034050812104900e859079000c1401282c281d035240b0081c05001d51040c040d160001280d403050041d41a42411781c15100c10400040b030200d01200000c1e001404950090301c0140c80ca56032504c5400a40000c06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 998097832 1250 998096582 998096621
    0x1d032109030c030d09031b050705040b0109051e060409020307030b04060506090109031e0c030515090f070b070809090403361428050301050c0c061807090609090501 72
    0x3060f9520b119140c549030903261107900880c285801200801134008080c080000340031000e143c03958440390706000c1d0510581c41c044241845521038050903094030030103405003901c000385031007000d840c00d00420010b078000d02c00c11000c201c805090000c0c60040000303480200d6a11980000c04c010b0700d0103a08410b0040d18240b040500580c0d01203489811170381c00c14481c4103020704580d1a0112240220009420402050340010801400247c4151003031480d15046140ba25014040354039050740c02c29030420b9500640301403100221a000604000e886840c05c14586046140031a42006080743d0907400300d12850002001040502203200d080c904541e10008201001200900684440d00403050790b107500d881840070648640c010006441d07014000f02480d1504845d20350300d22041c1c0d0081d0b5000b9403c060120307211f000d8000507555120100b0025000c0c1e5545c41c3c64015031100c0c8586c41d41c0803403003522400108007116118520103060440c20103e0040d5450034080c0c203507841c005c401010603128 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 998099082 1250 998097832 998097847
    0x70c150311180310090302070906080f07030818120616050a0207120c030204090c03050d050f09090615310f0608040302010b060f030105240901031d03210903 69
    0xa1011984481001000b030765a080c03490000c20b01c2c1114820050400928240f01d02c4240b54000811000b2620920003d122940d1100401600c030001c007602c01c120b41d480044103000084803075018004106d040d01c0410482802240051100200002c0740d9259070007180c2400b9107040b034840070300d441801c1c0d400d009140440c00003009540700401e01c90400a01a000b5102041100b01b41140700195001001800070920504240030801000e10007122148502c9004001c0c55010354252a200700d40108002d0038903105100b80702180708000c004035885141d817091145a61443c02c054030003840f40e415481881c00b0b404105600342c1c0104440004038102c138100030002042604003210944103189000a03d40c3c46601d4181c1c05002101101c50b400b0f40082101780721000c0c80c4000d5412108121a01c1c124562003140c500c61550100c0aa6440d40c0000c02800c0403550103a002102c2d0200c00c0c404102040b101c0c2003204d403d54000e1340034a05680e44600c140000d420348062625003001030030300510724003881c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 998100332 1250 998099082 998099111
    0x80a0c09050a0b0c0f0111090310090305040e0a0f050c1306091410120606020c2d0402032a04050a1d0a0c05040b1603021011090409060908070c1503 65
    0xb420300c02c200070460700152843c03408a0502a09100d036107140000e1088240f601e8103940e4607080030300121300070b10403910b480f00d100c5564010035548580548a8070301e41070030885a050b84140060045c006180c9401d82480c0c03400461141520542c0d5800754142ca03002031080c05880f40b055030340031404201c3e841c6070900011100005000c075403102240c00700c01c086201e610955400f0a079a010b008000c2c94208005030194000c40c01519081d011034221504800148403128522440c003083c03444414000690032103820154002d5421500081814000c1c000c0c1c80b10b411590400030b01c02e0001d50101240402c50342c1000c80d4800003400c1e4140c01c812206254031a9003414040045c001c82001e912503081051890007036040320098480441c4aa50ba03640040b0034084070104d0020490044c4264040d22044140354841d0300b400a205c0464180b600441c5000c11024059455040d1451139550751294009000d550041410034400e1040015071481e0841403d10200201c1a01c014182045202b410549 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 998101582 1250 998100332 998100349
    0xa0605090a02070201022508210706091e080d0506030601030206180f27011e03020f04060e0f01061205070512090708030c1b151615050106080a0c0905 66
    0x2840070005072503000500040b440c1800084180d02c00742c1341e014049014611044281040c3d4010804580060840354140e5220000106411070680e07000d01c818000228180c01625506002c0e0f0508401c8028540c2011200c03e0042c07000c841c129400600410321035000d0291544c80030040700501442c0d80f454012440c148968892203010f807603141c0d80e81c0080c3e590998500241c41004e03105002070545440c0c4002182c0b0520038601c00141c6400001989403000301c9008290210507a204110701d00d95400d2086a50186805c40d51198448802240d0b01c3c0c2d40490b018891055200c0078005940350002c0540703403010050007001c2e50303130406041114050700082100d00f07841c5a144c40c40e149903075140100b414200c440d000180140400a0035100b01c43d00002e50b801289442104c15800100c0302c020011480d141107041d0055110611140c1c170701c1403606000404480c05086259040078203440f081007104c109800450109051000740051190300e03104000200c895802c0c4000303030310b04280000e0070b201d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 998102832 1250 998101582 998101591
    0x402031003021c06020313020913021c060612060c0f050a05030c0705031b011506022a0d0807080d0c030e0a170f03040b01060e010503070914010c14010605090a060509 73
    0xc03003582c0022003503c0c004250411200750041400c648900f4030003200c050604030740400364402d40c24000481d1008038002801c14606038001c00aa141c1803000e040400010125803050307908070303030724080090032914001c0300c000403510510000030340b40800301001d0042c1148180980030028107002c40d00d0380391b8000044a400c1043c4000d0b19845a40078035240b07141d40f10f03202d0415101518a0218401ea510542023a02c141c05610056040c8644a41e022aa9010044852901039000c181c0b400b80303120a05042424082c0e01030491882074a098444e00307a158070181088800d030320001950302250480d403050440020032441c007401048451581640d84508404020b8100803803901c00e8101000e05000300d4414545043c101500e91500f0309050703080090920405002c1510403111085541c4990210b0f0b1007240070340c4884605608080d46070120101e03102d80710307051081d010030010126458030701d183d0700050ba0300004075203242040f0500c50504030181c02029071074101801403010303945d10804a0340c071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 998104082 1250 998102832 998102839
    0xe1510050a2a021306080d0201090b060d020d30050906120a0204050d0b0a0f050f0f09030f0319060512030d1a040e07150504060c0305130906180605040203100302 71
    0x80c0400c035030b41080b4a0502840c02548035800b01241d42d5420101d0b0000021540e9440640d860301c40c65001c1682a545c01280081491800d0300010310745113070009014403c1c50010745500e401c00300c0c0340e031000c0c450303128204007039803200c40c40c0d11020074000c001e6400d000301ca80038900241801c0880740030800c00c1c001d144600140d000e040300051403c402c2903041e1001400700401d500f107560810304048402c40350070b80d51114041d0038400d000880d40780d98010140140100c0380c11aa06640303004a040364014041d0403011503020400442c11b1b03525901c030140d405201d6000d8217405180c007002d018000c844407580494000c00030290319608000f0040156044108a00ba011645d44400010107003144001004958400c0ca04602c00ba591f103800a0010309850821500d2095030b15140da040c1d0b102c0c0540d10030500054150790842c00000d200d0406072105080c2d55000c0f0350700d10f03154044501911055007107a1000380c0c11f1205030300d00f422240a054000c2000366030447c0b9604124104103411034041c00080d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 998105332 1250 998104082 998104127
    0x90907051b0d081305161d0108060c1c0b060a0807030e1c0f110a0303090201020d09050604060309111809120c060705030709030b09063111010201060e1510050a 70
    0x505c80180011203210002c0390340740b00d0107a20f619141110903c440b480c00c64a000140001ca0240e60004049000d0031030f0b465400e0808a812510880080064140840654444115818940f580c0c009042ca0782d64a4840e00007610788204000c0c1150402e55201d1450b50001011665180c8120140f0106035458503000300000502c0000782c440682112003c00c5607c101c0700440245a41a030240c00c0c0b00303100346c0c213031075441c0d0b2441d0003142c42031414040d20794440402c00c01004518029408481050b02c150907008800340c0020000d03611404101000241d40410700400c40e80d8141804a00002540f8020940c03c02d0305540321a65140130080c8228144000080406c0e4018040c41e901002150b2000d081d80d05403a0280b203c0d0703102c10080e501b84120700d54014403e24000882d580c490010320804603031076003002c1203443d5404607000c1c1c2000301e030555582d024040b40083c08850799600c40c4030700360405004d160b50a024000d9a400740b080c40002c004050080c03580c0650b010241001d000c01882c441035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 998106582 1250 998105332 998105371
    0x90b07050a120c1110060f080615040c0c0b090609010b040221070915050408010c0e06070b07180806041401181410020a0e01030b03031815090907051b0d08 68
    0x4803c1c0084e00100c6a5a1040340ca101003051400c0d0041700596079070070b480c01d10b0180d07100740c1c45a43d090140d46030a0040c0484100700345509241d40681c1013038180e0b242801c00700c00140c0362814001d01c180d50301240e03500b00342c08204a4074424003507400d0340c0754203882c214501101100710608480040001e90040d12800b004510340b60300c90f01421016100c0301c5080b89040d6007880c80030740380c0d60084c419900154240300290b00144c0c002d440b802078090001d8020340c50b0080b5a42c61410010f401401c96091002140d150307440d54008240032805072000c00000d0100e4182424540e01c445446c05008049a040c105030340c0d0907104500158120341c0c0c1c8081d140c11003801100c400da09142054010081c0c8500c041650071005512010140c2c803070310f00f82c801700302c400120b40034141c40f4890200000000d00000c0840c04d02401e02c182041c282c10785484030282411140000110380c04c5081d644540081c00101c3e1503041980d40285243c460720101d801030980349600306000d171802100900046c0300456025902 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 998107832 1250 998106582 998106587
    0x9120801051e040f150e0c030705040314011b02010b0112020705121b030d0b010e1005031506040e100f0905040309061115010f1502030306210a15090b07050a120c 71
    0x12514800013440030b2100303c00840d0706280d84850741c401c0c5c2003506c1802001c100706101c0c030307412070f80654501c0c2c1d00c0c1442d01e400c58460f0000d201c0c52a401030401d42d41d800c030f98900c166181005c0c4501c001113034004500800c528000508001245100380d402c0c80c81000040c00086d00042c081003a000c160801d6a21205a1003511001900340030140901d800700040e60420500300354842100310304240c80d003142d190781c00000d02c040e800a242d590004147c040001c1851110408400540c40c40e006003c280740c1912100b08024541c000e64141465455004007406182c142010140240681000400c83c80c0780030b0303c004080821512601c402c0c400e0f004801e5503002c0c01030040c00418400c440d189100c55035103113440559081e1a104956444048001c1540b42c2407010089900680c402080c0010304000015501802126a02007600604c41c2418010000b504441c1e00c5060204980001640d03180508140611010082c6000c04010042050b003040c1600400d91950600b000c5800140440030344006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 998109082 1250 998107832 998107841
    0xf060e060418050a05131208061c080c01051f061404030203011401030201021c02061602070f1205011b0807120b060408010e1b090109150e040609120801051e04 70
    0xd80e00300d000b1078690004220386800035400384403c0d1208002d0390f680d00410940c04410201c0041407004280300b80066240310321282d235003111004040e041205254206490140c0d02c01c00c08807080031021400321140242031186982c020030b202000c1485031160320a10a950b06a4000c404c1401110300034044105400c60942d80a03681c003030020483c643e00784d070441103548824401240188100d40d00c0178000344001040e180ca012058004111036190079005064810070003950381c0c214441e02d070002402420b0440e00c7c3c4020030f0150000e41e084001c0f070920a096610415081007082000d901c881d207074907405a00503600210514101082d14079100080c0040d0546510199003c0030200c0c022990000661002c02c2c04402c81007141d40714803698000c641c03500100820300f94408908001001101200d800011929000d640340c07408894844000d8900a44141c405649943c1c0d2044000c003088540c00c4280c2e0019114186601d0303562401d000901d42000e001c0700070100d000c85000d0820039417110b400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 998110332 1250 998109082 998109089
    0x210a2c0a0801020d060b0f04090207020d0503130806010906030c050f040603120905090f011406031801060f09050f1611030702030d18141302030601170c0c0106050603010f060e0604 79
    0x1031500301596a0550501070f40024064103503c52a0200000307a000f0100101c50141c691005100d081502d01050ba81c000d4101c06800e0340c000c2d90070068030b00090010320007840c202e000019078501e02d0b400c220000e841c4c40390582103414054508030381131001c50038820b860021204200c80e074440b02840d1f00040f5024200c140c1c802004046074428480d59550413494104c1540c0c2e0959052105a03a55450307581d01c00c0d02031150401c1c080021080b19680d04191000316070204c6d48420180c4090400d0004600310750b01a0f11450050410203014440490107024440d0091080841c10740030b410a50701d00301c0d000c2940f44000040c4861080d02501c03025040c0180c1c4e1541c5c0e0014190f8641e000c45990207040940c0501c49030b6030a0302c6036100414481c030640c404134016140500412140050240321100a5001400d000c4c10310994481803e03003a0000740c100c034840c02d02c1c4007800b034a481c4072044207420b44003543c002c1d61240b002840140710075004039016804403500c62501014105086011403054482d40c3c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 998111582 1250 998110332 998110339
    0x3190203130312021902090105042004081518060f0702160806060411070c05010c0606090207050a02031b0609190b04081b0108071e03020c010c02210a2c 67
    0x3000040c00744440c1e043c0c403806425000da07491014810044031400c18803180c02544201044014401e90800f036004002c1c4244021f8816030070781c000d040700316298005500411080d40040301c41003050b0341c665401038120445e100301e00340480c8190000c649030103004015600c860b03040d8002401140c8200440701406040a241c10251030312904080e8852108445160180307082c481d240f5000c1411008031504550424010b21134582404011507070380b01320680541d000d03901c803900460603a400340300504c481c43c81080104130a034450b10606003006401030408130301070f0042c00d007100d150712510101c401c0307084211500304400c6c0301c28a035032160680d580c206400584002c100440c1e8034200250226402515901001c503056008004403040c030301c116034490026082c03e050a800c0900c103180c407400d20340c0c542000f60404c4080c000c282d00b1155010034070030040e80600c540344101c1441c08015100240d10b4601245046000c0c1400751690046400c140704580e61001c2d8000301d40041c0c01d96140e81030005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 998112832 1250 998111582 998111617
    0xc0c1208041712040c0e0709090c03020d1803032414030115080a1505060a05060c0c27090f0a080c0f0d0302040e070e011d0f0a0e010303110c010203190203 68
    0xe000f04956200d045400301c91600c03030918040b408000c904c04452060366142d036080207a90130107081d0000380c1010001c08090540034002028466158000d0705100c2900c0140c0310040c0d451424000d0030748000c103010b1801c202042d441d94082113401000c0c0d6081c0c600d600a101051806440828010704184192114441c241ca002040301c4201040401e2014010890418445002c803000c03022201d007514220740c8400c052400700324038180440602003520318001a180107826290124900501c552030203420140000ba0481e500900d12460705d4101e004400280010faa02e60200c80c2e0303840e42d040014000410118260001e00c000300041c04003000d500081e51280040400701901035009801440d10114503900060321007485070b6000c50f02d100341651204007051650f403001c032501e02840c1105030030503400d010a4a458640c0304103400101140a21030000b58514240103158541d02c00d408005d907005030f502c00c0b1040c0c0e0f0000a4030b108585801c40c0071118044203405034507502c81d2750381e60b6124030000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 998114082 1250 998112832 998112847
    0x50717030f01080d0e030c100201141029030109021b01020f030f060f181008011805010b0114220e0a09060b060c0a110f19090c0c12080417 61
    0x30601d114100c9000d102160084111107005580c1c0408180c0c1c001c2c2c2590044c402c2c3c1819182c848005601c1048a0000056448062681c5491840102c504184d41c071030109040040c40580c0c0c031240c40300d0a502ca65809603404154215a05110611403511b000e6000716040c40441c18010740f101030740c2c0c80302000315038940b08907010f0202c0d03400807104041d00000071400540d9a080c1100d03980c00c00c00005001d183d0312044c403000c2c1c220102e00640b0f84c011501d03d40c14080361020003441040e003216400c0c00c944a5060051600368203445001400d01e0401120958145280b00404191006401426512032900c00314201e4504050303800d42c01100c03020010402d000016515510049000707004110912050010400b070244500c160041e11001e43c0c89560014003060100602503820140100150b4405c01d085001030090441000c2c012220310148201f042a80c2c0b2501c00d5001184a6091504d0868a20703121181c0300040c1409500512100200207420840c003404803003072810880c0244d42d01e9418 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 998115332 1250 998114082 998114101
    0x5030c0d17092d0a12050604030f031b08091c050a0e0418030c0203010c05180922050f060f012102010c060e011409030c06012106020f0d2a05071703 65
    0x9075055042d014844e050400314002280c5811030000c0d0707810400504c01629030750b90488640b6003082410040582e41e0f160390049100c0005150320b08682c607a10301c103032410300e0410365040012406519002c0060454540c5a26401c0070030384403d1303040e0342800100c1c1740300d03800490050408245444044068103800108145e04003008007901c1e40240c1c0200200625000c0a450512800002e54118001013060040314642015096403050080f42c0c06064240281001e0107040004a01150640c02000e606002c4031020407203298004210702d00368400794900900004500b08524020501000d01401802964006c605260036154851002c0000410020405d8001c1044c2507a0702d040100240100b0200c25001041d10642d502e0345d406409903903c0c056148868078186204510100041c0c04080d0115107148040d004407013041841c660784903000310b8154120b03030200803075890741d00e888441c090309807409048803446407a02c5d040c2a9510728440c14881d0b40140c040c0540484201c002040114201 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 998116582 1250 998115332 998115409
    0x16140c10050114010c0804050d0204020d05010608160f0906080405030c0d090f0623031810021b0d0f120e121206120d0f050c0a06050105030c0d1709 65
    0x142c20f481d14050541c2500d004551140c0303040c101600050081c0018071441c6000c010300d42d5518030007480145080c003614147e400380c0f80241c0c400c1011524107010815200e90102081d08032031018641b0403002d04502d40082c0c03d1481c02d019083c20400480000741c10003004204840919080d001101da040c0302c010b000030107202d85d50003600c45900c0c0e0040c1c001080e5004520002900d060a1400c070207200c0d10b540300301c7e42031300010310090300a14100102c1c0414041031080c00903e0700710360310142e42d4407030201040955140366444003070103a0000c0c046458050344130035600ca03002190700d4088405507080700e00c01d010740181282100c290248000006407401d404e40200a0030060107501d203000d03071307801c020008070000c0f18500303052540081320a03864132485440310b42500c40503414a44c2c1895252101546002c01089040385c81e1039a65005120915040100045682c0221107245405500b55216400341101c0350340c0c00c8030020301050680490742c07410503d800c2122662107815400c10011800007000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 998117832 1250 998116582 998116589
    0xb0a0906090f150b0603060d1e0b151c3503010e07030c0f0e061b0604030201050603010b3012040906050102010917030703090212150f16140c100501 65
    0x2180b11900340c0f81c0348021402100802da82c020160f81c19540c0b014240024408400c40c2203d0441c00b2414809400b04640030b5050603c0c010401805070703107492400c020166041281c1c180c4224030f22181001040719801d2030515065200040c441e03c030698010310304002c00404070480700819003000c0342060441c20000396041742c0001601c118640c40c2e107041642100c81040046001880c10b40a20481a00410350071401401c05002585840d4030240c11782c2d10041d02c840d00a4082d0481018031040c550309004158000a040b4003c0044a17000700002d092101c122524200b4030400404c2c00c0f01e5001c0654100034400c0501040d40c0048403440341040c2190f0082c040e100069280480201d1340d548140704184c80d299000340301c15003425484000c40056000106824205030310f6004103001600c40c0c54560780010790041c0100042540880b1444c1c26610040400c0c80740e261117810030208401c5098013010690440c2441d40603200c903404041e0381c0d032180c5c2c0c00c0001d0600c84c1489000c10320020f0f40c0224100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 998119082 1250 998117832 998117843
    0x300304300f111c0b0a090b010e09070906060c1115091003020c060901091211070603051906030b010f060804050703020405061c23030307080c0306030c0d0f0201090f0e040b0a0906090f 80
    0x30365070310303c45d041202e90035003000d4881085c44005000d103040c9400b44a40011511041360020343c0d859401700c041d1a40f40d044100010742000aa80402800a04c98090304d0b100722103c07125520803408105460160300b00c110b207d24100310423500403034041d5044468a17565902941e449203030000025003c1d0001c084120b41801c1010501045580304170b100c0b0642141c190054082c82c0d24014045011740800707451010040400703c0b5105900c2054410709008621400c0088115850082210000c5020b0fa0201081c001d0700d100b040005000410100142c1c1e0f4101c900203895110302d00440c20101017158940c5901c18030481020501090901c08150341042c11010600c0c4032101401035101c0c00113598210100303070404d01280c151006070014661040d000340450342d071100c8030000108951051803040c0e03800302e00300070142e095503441105000640002e14840c113441d880c01e5890401c0b40d80c0104082d00910500010800c000b4851b0041c5810980103141405400194180001e21900c00300f03003141c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 998120332 1250 998119082 998119103
    0xf060912190c0b030f072a0c060206130f0f05150a090b07030b0d021e15041403210a1803030f0e0406050a05300304300f111c 55
    0x14032000c00e00c1201e1181d51000c9072000a525002d80c1620b40b4a0005400136014011000b1900c129044605c815540c7c2e0040500c200c3d090314164000e4180300004d4188880340218100741c00100c0c60404038110007951104c40c00300c004841e400c0c40c0341003200400c00704020200850500c61420317010b8101880042c0a004140d03121b441d440001e90454103100905500810b031110028013615041400c0c4410850241c58040d0600000b00011000550041c5440c2e50303801c0410b0a20042000d041a001d016405074000c040360b03070703194800c0d80e0111006584404915030002d00c2e01c0000d031040d0f541c450340700014000c40c081907490345806000a1001c00d1401c1c0000c60090762410b181c900741c01070400300c1d103018003114502c500303290074045d4414a030301c5045404a44500c543c20a27070100d6030722101000c6480040d545460420403041d010312030100b000412070728450100104030070f9058900583d0340e2b100b41003c8c5000180e2424508031824501c24a5110411291040131800303c511142401e0703102d00760003103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 998121582 1250 998120332 998120339
    0x319030204050d060b180c0408011b17090c03030703080702060a0908090f0328020112201c05010906210506150109120503090909010b0f060912190c 65
    0x281203005901c12542c0c001280106040400c03401d40c002030b100030002e000301c0c103003221070046200b0318003040d10090400440002c04000d000c2c401c0c4240300b00701da103182c202501c024200300011300620124201ca9176a812103c045011141d04101e00c144e500d402a080e25118500390030090800c2404492190150082c03070005064009284254034001e9403006003181424440c50501109a45007241c1d1a0580f040f2200541110403080451484026810703c051001071544001003201e0120314102071040d0402d60800c0d00550800d5494107800402011940c648840c40b00b13a40400020b50034880c00e83d4030b27113800403034032010a80282042d900d400b55400a060714486030800c4c00c0b00303c18001760054100380080703203840104c640d0380c4943c904140740104850b0b44801050003c0c0c3d021400132a12a0302c005412070250908240e03555000c09080c0082240e48003120106241d511002c44562241d440000e40f480030b90f8070b0102d60402c0400001c202c2d158040404001c3c180465076020030359240e06d1190000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 998122832 1250 998121582 998121587
    0x34050c2514010206091b0a03021c060b060c0a11060702100f260109051305120a2006180106090c0801090b0a03080d05040c12051e01050601090b1308030403050319 71
    0x42c0181c000c800285900d15030381b007071035480c00d400603030740c50340203080c81c1000003d07a0700c2c0b070000590187c01c65040c189030b0300c3c40e1a100f806c581902800d82d0181206001c12402d4980200c0c40308103a682201241c0040e81c0c80310001400c070f00c9000c60080d8004c0c50b01c00c07804800380c0c0c8002c1e40400300003181c844990100c1a0101601a4100b80b903170f0a400c200c07d6801400390315042d8100a40140d80c0383d680c41c80c980d081355111030034a1402d40c00c00e00202d00100307904002a40c000c20440740c1d102d44903002c20300c1002c02c680710b03515508000d00503580d66950140400310840f00354000c00040021702003c200c02c0c224284014050b02c0203105200c2000d0600c203002d44a40352413142c110440e036000001c00e280c14040880080903100040040d102841546000601450040070102c101d91140003d84482200c0760082e402d4449a10b4164081d68507020400110b640c0012050094031380400006468903680c0c00000b0310803030550071440150001040000411000101900c40040224929030361051803e508 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 998124082 1250 998122832 998122843
    0x30c11031e25081e0f010608030c0106050a0e04030305070e030601290a0e010c0812040602071b0b0d0e01060f080312011d0a021c06030b34050c25140102 67
    0x1010100d400000040a0b0307501d50540135542e08041e0016070b2007180c0795104c110b00711070711030b481142190000121210540000c0c8118005882c089030128203150902c00001440c2100a1000301030658403004038840364050700030161000401000c0310600e41e114164a025800341043d030700c0e0717091640019802c888508070140d50030f00b811503a072544007910b401c004581034080c02c00240e034410400c000a07c0c1c9990054540c9104600407440544d45420380d141c81c00802d0b4860074042c0307034040c100a083c40609020000c07114407131320f400b40c04914585460741c15070051449a2052144001c0c0700744c00078186001201a1200802142c14440b50780c3c0d8071203c4104814000b09a0811717280241e000403a04241c45c0c1c0039050760101c8001d200e80380c4000700310741c80440d45903030015140c05e406038003040070300c80007003075180441034115846894408c0d0012214a14001201000003400404203c0b410911802c002c2c4a112701078280414041c0c40e504c1d43c40301035030034081c0502441c240c0421810030017540001403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 998125332 1250 998124082 998124089
    0x170a0c32181312020c12010905060a2301030606060219031b03030e1504120e130b040e03160c0f0806180f101d0604030c11031e25 57
    0x280000e001c104601428900802000e8210150100342400c0c08907500300d9030903070340c4030340341c0c0042c0504d18542003080012082065000720982c1018440700018501003080d64204190388800b281c0b0307110100142c0b100002e06550302014000b42c2c0000828000c1c0c58100300e003242e116809603041c2480c20041d41001648401028020030558142a11040c4661030301400b054060300d4000390400410141508018502d00f400d10070b014520103010510407142003101c1c2030300e541d00304010114040004a141481060404e540c1c0594400b8030384895203c43d00550041d081c520252a500d1a803250800e000c840b2034001030741c50154424000c102402d807500d94130140d0f00051700410240e03444d214051520300f007002c1030103998011815a1100817108001c4603030380220b0701401007500000d49910140c0d2155040d503910150380400305206c04039030032074442d040c1d0741e412080440d000e250120210785441448028101c10421404400a10100100d0310b48000414209030114200c551404844c90300c50707a00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 998126582 1250 998125332 998125339
    0x51b061608090d08070302011a030714040b06070f0305040303030e0d080a180b0c07021306050f0111030c15180a1106070309030f030809060a05010807170a0c32 70
    0xc0680c00300c1c00440c040d140d02500202211081035080e5640040343c5c01241040380981e44a080803040d10200600e910f44513901580102000d03464629100706506409004501440c0d40e1342d0309800307684840c0c0c200c50060f070f0800c4540c001000d191a0081c0240c4c081e10096001034a07110f420103800001082100e444e24481e91141001d807a05400b4000821054030710200101d034034511140001e5521680718864004036500e281c41d540e0034010310042205203c42c5001892400000340805e60307800340481903140c002e01c0e103201416290400c0529520070002c04500301c0c4100803c00310180d071040d04142c4504226403198040340b101c0f40206a80300c0301c03100010043c841c90f040c102c1d07840c100764015000e2140285070a110f0310b9540d445081c400c0c50882000d5000400f240f040121342c403401c02110f600801d5500d07042002d5850607044684880e50703409074503041d1021701c801c110805010030907041007540011402142e07a90b55481c900d08840403a001c2c0052201801c55070f030161145204000142d030014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 998127832 1250 998126582 998126617
    0x1203042309070f0c060c02010f0b0901050306010608101e1404020309060408090a170a050705030a1e080910031b050f04050d1e030806031e100b040b0d051b06 69
    0x2070540b03c41c0d0b84203466400304001079180e100498220301070f4004074803661b00002511029881220166698101e545004031503100041103251000907c0341d046908525007034140303032280b0307c200c8a04039490b8000c001045902c1c0c1c0001c07409040c401d00c1d41c01c454010020043c01c0540c0001c3c0000d034042101c108400390881d40000c1d0210b2500c4008003400e0200824142a403a2518000c0070080128006400a540508203400c1001420049a009085c08500800d030403c800e40e11403e0101d0704035034102ca5190b80c20001004c0218641c140c0c0c0081d9002001204001c0b20310750014000c200b403180744e800340c40c00020041c003140d0044040300e2113803a040f40d410b4039141c02d0000707001e1800d591b80c034115020718039610100891107800010415461080e520b101c1542030204c1014a0444551441c02c085800502c400f4170240000800604500c4001004200c17507600c40001002866043da4550704012a00d003c101000004503000f102c00d000c1818400b03400041c072041c01000d00460700f00d1000d00300705 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 998129082 1250 998127832 998127841
    0x3080601030e071701023001150c2301050c03012d090204180f14060108180f0d0810030807020d06060914010510020111090409020f1203042309 63
    0x94200c0300c0340344451412201400d0341d03000b880352885076210042e00e03580d46c04902900d080403d60310841c4904134403c03140401804912485038148010f100c0d12401c0307400d0120b00c08074940a42503138188545c114904035020403582c982000c24841c0c0c2501701c46a54a003c0008042d1501ca9080e603043e520059000001644070104540942500403094007030300c0381404c00006e01601381c1c00144003a00900c04400940c440052003c4207641400c00e0380350740c0c0707820104528503e90520156540c0441c00740303080c103070b1078582c204490074031001a6141c4001c1d000b00c52110b1070404000074491800c601c1a655044942d80d00e055500003400c890000511845003080034001619010310300400300d5004d02000034809580e40d4094084550820000b0805068080100411710f040c0c4429404000303180000d124584401c10030f52450300c42d01100602c196a100c450000f59210608003042c0000040c12200c0d5081c580e4141d81c5e5250014480d11035100220400c0080c0940c50201166518101070003040c40c9441703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 998130332 1250 998129082 998129087
    0xa050f070905131103070e03150f06210d0305150406120605091501080c010e060a08180c15190219150216030306082e050402030a1407050306011203080601 68
    0x42c90301c0c2002c0c1d26444d00e850020301c404480c0154000c20301516135841c2109002c0a16017002c011441519041c480a0704100d1201e0240010540c8903500300c4241800d00030725259503441c01c0c851303800721a0f00c0c4920031000800c5909a480103019003100d020b04c00c019070000c07040009135001401455599640300c2e60b07002c0024038507005990003400c1082610700e4200400004040548242d02490035680003003852125560040b0b45150003001c10f039181403400e80d000d4005090807401070001d0880050319203041c0004601440703000060301c0000d04142c400300c0c000c841a2425000007003400190600010044002400003c120361190300501030703460101c006031140c101c89404039104560f0660200714900d250b41d40c41c0a1043e20b284a0b0301c0000e4581e081c20f41061070448420030501040596403045c088800351550320350010012814003041558642c40401d05044812200078590a62207509a400a101183d61001e640082c1c040341e415a076500c0716005003a81003407000c2c02081240700400c50951 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 998131582 1250 998130332 998130349
    0x1b151305071a070b0702030310090614120f0d03020403060c030605090a020a020a120c05070501051e070203010612050a05060f060a0905090a0503180312090f0603100e0f0a050f070905 80
    0x1820402c071681801069140c0c4449882c049580500581000080140c0e050b09100c10b8400f815159a081043d1030801b020b0b100081104280c0903c2401c1c5040d0314000c035881084203020f60100541030310045820000081c01942143c0411690942040d04250240b44a403080108880d00104000c42070307162900076600962001c904842107000c1c042c85600410400c4403a04030240e116950018034550703908101c1e0822505402c05810800f0402c050000507034001c050b01c10101c4407114042e03803060381d0710029006282551103080440d494580d100700344240414003888490003601078868136070711a00072113401d2900300c410b940d120483c3c03041403000311000c0d0710907607110441d40102d0391103984c0c1f0f03240e9a11b1070300000c3c03100e9401051518000800e003028048000000b821114480c20300c4403003800103204441003030074580200c80120002d50001c0f10451704070010411040c006c5028200003d901503404411a0b4000d011f40c00d000c0440c20100b03054907011310405183c0d9445543e40e05000420817441d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 998132832 1250 998131582 998131619
    0x1a13051002060723210a0c0f030c050d051612060302011b1e08130b0f030f060d060903020307020f090f0601080a1508070e0f011401141b15130507 64
    0xf0130040c049109408420014104040c0c08540b41111341c5401c18030a1048000600081c441030410440c4102107800c1882e0100b030030218100442e0f00e001d0210100c0c0c40380160178007203022a050005108082400c440d01c4000103d25685044d0422410501c00040e11040d10000f40010916640e144a0181e0305204210252054090703600362514a131640c00404640101a5111701d40081c1050210030900049070080400049003030402141c18050240c9010080496035a2900440028015501d1041010000743e116004100100c181c1c20000c2d0fa0703402c4031104900581449a83c4545460030701180f92041340300f00785a002e80d03504d9200444064401034440341510781c480c410380c11804210704050003e894114003c041d00b03031619030444d803032600c003400503c000d10840006001d40278142450420714082820704081c01901000c1d04d060030300c03603c0c0322524090440040116801000310325014244400f42d440913640d10350100c9010782e040c00e914002d0099000303176010000b10a0f00002406070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 998134082 1250 998132832 998132867
    0x302010f0e040906060f0510021e010905120418060b07110a090e101b0207090911090103140d030c0c03140405060301080a1b051005131a130510020607 66
    0x1545241e0116058820000c0121103068845000740059050203011340c0007440c00f140d110f4540100c2100103502d40280310b111001d0403200d03007030300301d064442500640d24180e4044203c80301c0c4004181402800d8029000300c034140200b02280d000120f45a0041c4800d0710000302c00c00345000180c0d69031100005440c0011904524950000600c2071001d21441900c40030500186c402010a10002d00442c0c00d08491660800152000034014503800101d01341580c000074030000703a0045c80e0074006540c181035500e09500c0309032a40040200b2003c0403480080c06407040071143d03005c000a4040c2c00b5110031009200004104400300d1000c87e200709c4103a409425400c481a15190312580421102c0d81b098001c04801d9000b4050041001403100d007454080d2041007518800c50b0400d03000840b6000002e1400080200100380005440001c0c14040003c16020603d004d41d9415107034a034400e500140040341d400c04605c030001406007840e00089440c02c0d55580a4481640c03030130829142d44120150100b20b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 998135332 1250 998134082 998134097
    0x10b031203060d0c05060c071e0608040f05120a0507050c0904082d160b10030c0605030601050c1618050903030a0e0a050303012603090f0103020a0e191a0c03040302010f 74
    0x10503841e008000c07c2810b4030103001e0480d050a00e220103800310105010422088080c000070081d00e6402801c690f00554000f403011003480160628034500507a8021049101000180e02850540c0210040840078415019590304804c610104a40390404440c040c05001e400c0041001a03071005121100182c00002580c0000c00c2002c02c200c0e00d5006180f107011044003100c1103c0604c0004080554400000202c10880034111307030351182003103294820042808008804152268011410340d10101c20304421a03d41440403001c140381004540b1a1040e00c00c44c055202c241c0c44240c1c0a1544a80100d40c0254610b84880b51b202000306420301e0481d0140c0a44846c540001e4003d05c0110f000f042c01441a851010110301e07100c02c01525000d02d030062b60b0080004109640f2405c140f4000302d8000d080040e201c5201e144151183d03010544515400007402e0f29600c1049005a90702d000c0e036448041e07420680c1c0c40c00340040b00e203126685c003140407a802032008000640c810300200c80c003565a4a803105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 998136582 1250 998135332 998135339
    0x1406060901020f03040f0303110f1209010302120f0a0605010302071a0403050c07061e090e06011805030d031a011b1e0c0b09190b0405010810050904050f010b031203060d0c 75
    0x1420b64200d40c02c2602001003d100070420316901140c042c0c1c0071203900d00a00041382b441c0034503595584e408d0080c0101100b01040c942290ba000f64141c605a10380500d9210a0707140031482c6090060040b13038416512840c00034003013042c0d4400c0c030070341e20415842a400b103120700e03949107450300c0d101004004804219040186202e1034005000c0c150003070003e52940c40031400ca038035070303001d1211171040240100a0b03603c2c001c03c90030311140b981e00d070810000c0c02d041d0501544813180802c00c054036007251b501441102c02d4521a1039042d480082003108070101c9036241241c0d0001100c40d07140340c0c400440c50120528500b00809c1c0540044400034000143c1c0a046080603a10a100c11205a001c003601c1000420700121604040110a0340d407800c00309903c4101d8285450300d140d42c0520300500c0d04010112000522030310440c2084800740c003004058070550b01d00340c6080e0b595503d102102c1101c55081c0402e140c2d4a050000b61030125442e801901403c50307481758240014848130b00d1040c0ea11800c10103000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 998137832 1250 998136582 998136613
    0x702040228080115050d0b0a05060408150c04030b06090c07061a03160b0412080705030732071517090f0d020c1c17040e061003140606090102 62
    0x11801214141480c0409041c5290080c05010b01640150104c03140e40c0441c000041d4005c0440e04003440e00940010310f0082c0901003080e0350202d41005400c00400503000c01c4203100000d6041001c3d1401044c68000e40e43c90002040c0c0d80102e10000700340c0c4200d4404100303180b41020051340e2058070282200e0400e20b040d100c0106803000e00f0001615008552121501c41c1000e003d589682050b103038480c0c2c119860003498841030300c00c80c41076600119552001004100d101000c0303c500507001030449032100c1c901e0501500d100641e0a0b816075400048400d050b0a0898010b410143c0726035501a080151810383c01c020706076802c82c503d00c20440000b881e2048480c00f64285400751508100502d82d40c0c000c0c00b4a1460140481080c10a41d40302c106140c030207a03280001d0520f03070402014084c2c6810001e10301007122808092040003403103004180825030741c0403001641e100702c40c00ca03803051460062410681c115503d84511101d602d406e000040c4003410124000d0402d200c041c81121a070b0640400316 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 998139082 1250 998137832 998137867
    0x60924070804090c051204030f020a08030a14011203050f0a0504080d020d020105060613140102031c0509160302133b100b010203030103030807090b031306050c090d02040207020402 79
    0x11100070201240500c1441020310507501c04035040d040040c81c08510291070b40c61030000800003804c0114804540d001944240401d00c41168003800c0e543c0c49042000c07040000c1c000d40c0c050b030780400100500018010741c901d43e80c2d4006e0350f0140c581c0c1346171094031101e202003580940060814480b08100004820f0420050b00704038070700ca41c0c0681001c03800701ca402401d49002811403803180000b440680d80c0c011070385120b642110003004031700c1420a81400103070700310b02401d020401e40245418100300c2d00c410580143d849000c00100382c400b5404145c8641d110280c203070201039000b01d487c6500e43c00312065035100d0072610a0b00000c151180c00d04031084041c5605045100d401a441c020301d2400c00b60080243c004070540d680c5061009030040c40000b0342e40e000512028040085640100d41500d0082c0f2500020f04540c0303011b0740c0c0d00e1800891500c806240054126001c40c0b078000014140842e00098420201d001403804000914540030000a90800343e800c2c3d80c4503038200a2031411800d510b01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 998140332 1250 998139082 998139097
    0xa0e03012703090b0405130b040e030a09080c19060309060b0a061206090203010b0313060e1c320c0c090f0405070801062103180603020c07080c060924 66
    0x407000481030030700d4014442c1a0070790042a28090522050006030360f180404c05000240720340020700b80c080ca0300090003800282c0c00e00d4007503020018120329895403140c28882521480022100c03c5000501401101108405000d11039400b90400b84020fa210340c02040d01030b4018a00411540e90040002d031800a8550049003c01d000c03850900074110789000e04401081c108400f141035614000040b01580b00044c06d20441110f0398688500300b0802c3c3c1d00c40c00f4071114450484001580c00e5032042e0f5103081507044d030004181458207030403c000701d1031426048882d000c107540c034001c80d58440d400302640040000a005004100c141c491030b0300c0d21540284a04250154082c0c1800d15081c494202a02500600e40ca641440001d1140c1007807446561390f8030b515140c000b580c28125082c11121010840818020405884800200d0b075505401034030b4201d861809580300196a4071030a0755031000128002e4004030248101e050504e8901d0088210154200f00d0300c091036410403038052558040704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 998141582 1250 998140332 998140391
    0x13060c020321010906050d110603040c0b040b03041103010b010c0b090708100203040c080307050c0f121506040509151b25050601120b2413061a09060a0e0301 69
    0x104914444c80c00b51500419059030b180c200001d00c2d884804c010060412128000c0000001203410001c081201100901c200445036803115220048400941d00946003034462900082c03040f661894184120b90401805031181c0e00007100da9950342034000740043c8290107a01030000000b03040b40c4240000f064040c5480d100507070300e00e0700346480d0902000503002400d4640c02030015000062002551440501d0704903000031030150b8020000e00ba0b00d0758000a50fa89004450440030040c04101949000e08400c81d01030096981d00401503546828411040550a2243c000b0950f007081d907409070903003045820031585c94030010b0716103400c250a4403046400c02013081c04010051080c10f011803405002c03408200b29490106440782d81103113401414401c1d840503422131556040c0341d0141c0b40c401c91280038100705c0c403c005000000c0c0040c922840b841d5003001400451103c2c0713a00e10b4049401c1b5071001414542091070345003040f0780640484c1c2d03019400d90f588801da003103515000413608106262a8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 998142832 1250 998141582 998141647
    0x906060d06141c0507091e0204120605090609030703050f090a0b0318031606020a030b0405013209040b15030a0b04110108100603020c030f040b04030c0e13060c0203 72
    0xa81408048104821240d019000c00000c0c3c0000403400b2503a8000c8031010480403400d8132481c0c00144100310042c0e1081180380c0700080c0014000d03051142010035034000c41d8100501c1d5101c1d40301545806048400c51700c2c540042100000090107030b4040e04450720f200144a05002c00f550108500203160f40100587e094003101308130006140d00c1040001d0400c01c009541043d035812500800c031201107500401e071540200b24801124420341c040b030b2410318018004c0c052541d40319050b0074295880301101a1100138521620621160601d08851082001d050314101c2d0350b441d10780c1941c00c50301924542d0a44000044a07030036907010040a4500d5014001c0f1035000d041c6440c182d081c20082401850600107482c04100414400666900890361281405a603602030401107500b148501d4019580d035810100f00801c0003a034100103041541d2003081d00f03a0071140c840401d1040d00c2e200319464140400704000c0d403000204140c000c041100e10b280100c0e41007500c01c2500c01840c20240441c000c461a85 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 998144082 1250 998142832 998142869
    0x91a010f031b0303090b0313150e0f0f06060f0d080c0606011e0c081305091306050615041203030207051e0105070e092a041403010506010912020906060d06 68
    0x6074034090190340b120030484142d42d19581e001381c04032500b4032131362130b61460200001c0c4607283c1c43c00ca0340111580c040d40701d4401c0f80301c4180c00c40060500806000241c4291038032642c1100c00091910130f82c0040900504d81561020200080d031410030003442d070083c225088c04030016400700b015080f00d80301c0001030b0525241060004000707503d01100c03100840b180c4d0302c2540020350005582c103407581d00b010495945010b030603402c144040d1154080c0345c0050034502040f18102c418590003100610990341071000341c440c0e20801400c640319000c0b010b040e2200f0081000350401316402480024401c3c280541049410703214030303052030079000d001020300c0c0b9407400303140c0340c80400c0c07003031651142c05802d1003c0c4c1003502102042200305e0040542810200043c500320f401c200d600d00c145400300701411401e540701e40f10a461803040d99243c5c1428065824803001c40c2d0150702807404981980d482c2c11151f0454882c070f03006c10010003000781c001da821070010400c540810405004085c0500007080981003123855 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 998145332 1250 998144082 998144093
    0xf0a0309150b2419090f0b1201060c020406090507030b150a05070201050306040e0f03040f0b04050114031504050a090302071505040e07051306122a03091a010f03 71
    0x24611070032002e00d02003000040d40ea4000180d05070000392901124845984401042244500a01c12564452403e62000c107150302013155030a44120300003071780c02a03039508080b28290141d504141448810700c8018092248142031840c0601d00003031000c2841c07641c0c0d45084d01210003c4c1c43c90340000307031140000c0c00c0504000100308103209002e402203240078880031700100180036400000f81000800004544559943d0708240c0c03121080400f603a04407401100c0b840ea60b0b0b40144510700d1500703049600055800c8102083d20211801038680c2460240410f00445141d480180b40400960842c171400300e00f501c1c1d901c6210b01c9031882040000e03030715400c0c2c1000307880d2041c968400c400c2034000b402a0700740d140d4080d040d00d045480003100c058044d151402c0903a500d010f0b0804d403420100c01d00320001030b6990711604a078002d680c1c40c402004028655590f40354010b040d4130034500f00309511010300b240240302c1d51200c1e41050003a5205204841041d10003500420b00f07921203012076500c504144203010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 998146582 1250 998145332 998145353
    0x1003111818010303020309040b1206270f070e040816031d06041a09010c05011121040201080106050901020f010e1b120604021003110c010c0f03151205030f0a0309 71
    0x21000c481c1801985150b8000390340f03216151400380150b8641c1c004503200d0320f4410001c1d2410b1074540540320a8a4110850384801c2078809155030703203107241a1400481c02010880e15480860070015026079809c100d842031100382c000d001110701c208100003c081c1d400001a40625042c803030b5984103c0d001d40700072140c143c28500480c0a100d0101040208072400c07004d104051034510000c056901c800070800141c8094055820290255003860b60303602202071400c0003032040d01d8421840d800300c69900384100c0c004040440b40240407410840040c050240144003074414084144100d4100240103074501d42500c10301207102d0404e500242045040340c1401c0540c207a9a5425554981c8210b42500640da494001400190040348075244a1a55078401c2d0070944607503c071001256a00c2020300101402402c50205242c0045c24508034000f04a100e40a4410498004915260f106041401c42c00c01c01c80d0400e01110240301c10803058003282d0403030028107170300e0305207440025444019040200d00c61 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 998147832 1250 998146582 998146609
    0x1050a0b04140d061a041b021e0c0306040b011d01031505042909071a0d0f0906051302011112071b0e0906090606010504030c0612060305010501290901020c10031118 72
    0x19032036482d04520440d400907282d0781c80d041c0c6c4600b0449550340ca400c08ad003006c1c034180320541c041c02070f0010003050150b440358540c1210104040c2c6009014800d880100c40e12080c00000d040c0d20fa0030703e54400f4850b80d174100b90b81150203902e814074001d001034a88801550300c6001120341c00c0b540390410000082c1880310000411208500480000355507002450921814503118215981c8400c1086c0b8060b16034480000380d07034413840070800307400c00e00110294141c60010483c0000d910a044844140c008a41481c0401d41d140c0d00905119442c3c0e9001d0703001c45070803c126141e00740c00100003104210103810b24011400400500384501341030a9113400c18900800803410700400304000c01c00107907200780c1c000440c0c0301442d081d03059910b008446006023401c1d90001d4265800d010022510b1008075018640721821594407805404141000a1550045401c1507015802840c880351543c18a20b9041480300041c0c41d002030350030380401120a40d9046600d00a20b400c154503945240c0d410100d03a0100c16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 998149082 1250 998147832 998147861
    0x271a09070f0e0913141002040b0d0c0e060409090303270302070e31050703080a0e040603050309041e0e0d080c13060f0c0609060506010801050a0b04140d061a04 70
    0x10fa00c0c2107408682c807007000590051126100d12142081030340140480ca5040511200a41d540d542e900f080e403001e41c0118000d0f807001c4d443c1211580c2842c1c050201035010141c00703485d1a0805140c0a1402d00920320600280d0034103803a1603440149021039010003500d282c8a8180c0030600d0420f0400134079210050300080e1200c1201424840c0d10191380242000c4400080100320014001c140800c0400340660300c020900e01c5590404010014404050014444942e5030550744c401c131402004180c03201844042d00d250400c015450441c106a00010400203114604401b0039050300540303030440d0419145501143c1180b500c40f401d9683c0a410140c000e11404030381810111641020711403007600d8858a010f00408880070030000340600001d041d400e030050001c100080060a090001c0c04045400c1800a441e000022401e40352800051003034038401c00c4c5040c20541480180c041a2001d81c003404e9102c0801c28098001804600566203010100040c914852040c1c03404d100a031121040403500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 998150332 1250 998149082 998149099
    0x1512020d02031b18060a031d010e010e0d050706020304030c080c0d020d030b09070f11032b020c0a0b13020a14010e120d1202130f0609271a09070f0e 65
    0x419015013000600c11040443d41d10360344520491003a002030081d0748540d48040700030f01400407000410340c00809604c400a0003400740c00900726146440300c00b4441030344d022135800d02c05000415500d6000d143e100d84241003103035001c1003d07241d158040e080000d86901c1c0c5da01628104014681c188800000c00705541818090300d500d010006000d0540200241c04210314400406c06483c403d00701d0900b880308070000d41e5a5405810848090744034051035125041c184002c000e03071800460320031100c841030746001400ea0244e05a40392400c0744006048540e841c10b2007115000035a0b9a401c41c01d00403d10b03184c2000f0411881c80000d4681c002c042202072154000400c544118600031070042120720040ca00300006260443d220b05c02801004c0120101d268030074008034a03020a41601c01c1a00c2e141d85685054aa668000da0800010340d41d4840406002074a0030b803800d601a0858090800e100c4078641d0b00c2c40c402000b25504201c115500300000324031512541085801c0211020507003001d0300d6801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 998151582 1250 998150332 998150347
    0x307030308010e100510050c07080604080a050f0c010609020702040506090105030c011407060e150109060f0522090b1906150e0a0905040f0b070e0a1512020d02031b 72
    0x7040120144207020076410508002441c441d203010003880034200041084d00700054034000102280c20080f0182a04d224080e004510850000742c400e00c1660300001035840e03c0322261040300c80d0f81180c400704425490130300540312605000e01482010708210440103898030541d004020603100013804160061524034010b000302c3d1000700f00b2841070704d420300341036965160740544c01010780316041010b80158500b01441a002c03002190320b0544502080380c885850f625032078040e0071120700344101c1c2082031041100300881e091182740f031890b18030903c4201c00100d042c2016003060303031414801150a2031000c1d080008034210500d003141681c940d00c0003041002c4c1001e00880a60000304018002e000501010b0b1040f903551200300c4018140b080010f00440c20146040111324100c400300b1100014440c00007103c0070310030040c040707004d90000c1095508a103850031200c2c58420350900380c000c100d02d01481020402090000f0041c085200303400607506d00c2c015507104a401400c5550f6002628204102c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 998152832 1250 998151582 998151587
    0x3070803030c030a1b1d13020f0705060f090a03180305010e010609110c0303010b0f160f0b0f1e060a0f0b090310020a0f030b03031204030e0a0509060a030609080f160c0503070303 78
    0x40001803607690254819441610001e10000c0b00c0303130747e540241070000484d0404a0352810142010b20700c80c20440707106440320218019842d07401c44a008030703035100e1040e00010174400c10621020038100b66842022580302d13200c46e400c0d51041420042c05a44403007080080b82c19a12071544901083c60040d410701d0111004151603200c1807080d040d48400c0850140d844402d03d03000c07a0841c04149002d030510000c9442d05801000b50b10b50103485851108000911034520352a4051017440603101600c004074484a030300c40c000e4030251101c0d0b00f2144248001c02d6a05401c2610006001c0f0b8a2449480304036000406181488011820403c1801440f0f402c1c11540c11420b00000b5034544c5c01c0129014090340042407840c0140102117080f41000e105100600d604014656258801035440b8540b0381c1d15101404083d010a440039034000d80700090030000700d180d6a01000107188180f40d0b0610f49081c2c000450345035002200c9208000e05025801001c00520a201d50000c00b026006808103901e546c401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 998154082 1250 998152832 998152847
    0x611071205090d030e031e06090d08010e0126061317070b16030b04021911010b090703020d09060606081611060a020703050c12090f15031503070803030c030a1b 70
    0x800317100c40c85001d2460342c6c1e000c0c0030420380809039401c1049018840f071022903851b48241c80e0503049001d4844000c01c801c0c860325480b07059071481880d1140e03507460b0032492003154428140344d0310b1564048043c0f404d60601809620b001d403580c0320f4840c0ca0203801d420924040300802d10040c101c600d040124400141c00182c1082d48228103502d80444207040380b005801904003080c07035550061000582071014174071516403141444079507075100700420071072176070302d080701d416110141d442000c540c00030301894486d400402140001c2c038030110f05000c0a650346400d460003900300001090104040154414403243d4005440006240c014040c07814010705e25141c0c5806048150803980014818042c103005404444002c2d04100884c1c807061955500754000350050343e442441801401c0741c61741d02e854400600341c0426266903003145503444012100c501c0741308120341c0700c0e054040e01200141075442400074500c20b103241c1d0041540c03854480f9070a801c41e1910456205041001d00c0e441044603032041c80c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 998155332 1250 998154082 998154109
    0x9100e0901090905031c02132313090f0506090d08010e04030509011e020f010c091a18060a03270f03080c0c121209191b03061107120509 60
    0x4002503005220b051050440c4a000c410110104000c0c44482e1b4040709a030081c080e00d0309290480c0c9107251144000300101d0303034940c0c4080d803014041030308010f0351801d40d007902400410b039a0002640702d42c69072540a0003403ea041921150404070401403011810302c441001c0011600d0004015030400001c0049018080c001030204400071810180036405103404803003c408919811128810009009585014038182031a00b54241592100c2c0c0d24001ca40f403905440c2c007030010780c103c00740310800c100c01c60f04030b5850a11000d5201645215540314400245801c03101c6a50110342002d00000d880e003c0c186d024002c0b841c2850088200c0b0128500f06901c0284651500c1c0101c521348421000c4607079800f52480800e054010100752184281c020360081203a03601100c1c002c00309580d004a082c5e2102c0c0d07a8000c4001d94104036031a0742c0042e00414a01107141240c52041c03000544039110300c0111001041d8551810000250030f005100038242d500320a40c000e89451807400408002054140e685444d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 998156582 1250 998155332 998155349
    0xa050703021e0d1d010c12060b1e070f03021b0f1003020a090807060c05100c0818010e060112020f0904020105180d020907050307081305031e090a0b09100e0901 70
    0x3c001661038a03580040210f68100d51307807000400b40151482d0f009050b000040000305005800640c00803205016010840356110300c8c040c10315036035047c030845010400c0001141c0300700800c0600009aa00f40c07103181054003d40c028040e200c070031500c1c00892641352043c00d1069002c07803080001955110000313030424085107005610f0390400b15080c0c0e5541c0c02600300500710700901c4004241c0d20342c04401e5010b060300410803240307400301034400d1800310381c81d030b01c0b0100000703415100040c1180c40c007030b50b0090760358203001c0001074186040302d4140c04d01400f03802991008003140c10b86400d601e030a01c00480882c03001c540a0155041581c000b800e140306652441c2034610003a1310110b0140d50380714250300c10340e0700604212340c0c40c40e1008000b0410b500480c1c2c500b0200d903086020a20455031000000c01c4030340e0010082d45802210b40b141ca100010040c0c84030070b8400104815080da031a8514400c00034402d10f602c1c541c031000305101b0070640e6039000b0f03048030401000304c402d0201540d030741402e079045a50740b5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 998157832 1250 998156582 998156587
    0xb03030703200706111b031c0203040b0c060106091403150a0902040203040b0601080f011a340312020a05030a110c0f031e030402060d0c1b0b0a050703021e 68
    0x204046400208994000d058043e03d200020b03d1038004118000300c1800d18181e5030700d00150203c0d0850b8007880070341130390190b00c49081340358512a40c080c19100c110080c01100d041c0b603543d811040c181d40c001c03100100240c112030010081c594100752682e001c1c4c140d4100030640d04407281c0120341d45100d0a8130004a01c0c0320340010540304106e42d880b108805401030015503891a0130700b40f05103024006d07140c950001e10944009030080710105070f024140c5e10440c030b1012041038480351400c110707000b030000c411820446200c54103603499030f0000e4040e01050446e140c05a10040c0c02d010b0300d200c2903001c050a1050040088440c4150f0080031640d01080e402e40024602d910b8081c041110b01a01c0200140d034451140c3e6006640ea002010744810040030070560050101c007040705400340002d5400030340040050000f2601e8108a400c5500101d01e140380c040d4111f020000000003031511000182c0b24541c2100522400b0b03110343c007402e58410705c2c41c1419458600060322034030304604032941000010001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 998159082 1250 998157832 998157857
    0x20d0c0201050d0f1a0a030309150e1c05060114062205041401140a030803270706230903070e0a0b06040b0a110f0606040b0d0f0602030106120b03030703 67
    0x2e40c007502d28402148104001c07158080c505540103150303030104042001402d10358494945404055001640ea142e65400301c110b150100d41014110000c4010051080d26442c0d030807607840707003140c01c401900741c1052140d060721181441400d092041c1c12800300108503103095172241c0c071240e00f01c45503007005401890100711003010550074504c2c1501720b55400750510240400b80d00540d001d80d4141ca0710511044000084081000020a0700c1e10009118010600000d1009180c0c0c0030001000300d00f84500102e4102c4a4a20350b0414410340c001102190091001565034040703004e084180d90385a4140350301d004409000255204500d20a00401c2d500c0640050800403141d040940c0c0e020019108030b4403251215076441164004292420001d0000601c4180440d00021240c1401c1c60010240c01140c45503420301c030140440c1000d8603003003501038038044005580d40c030030125407502800e001070300c0c0d50404800030158400c0707200214402d4144007000030217a401000300c80200d0f0345814540e629415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 998160332 1250 998159082 998159087
    0x702013905010f06140109080109020d2004050a02251a22030c030f020a0f060c032004050909070e07082203020c0a21020d0203250f060c03020d0c0201 66
    0x1803038210700140c13410a2400116001c00d031013062041c04c400d0703e50b442c0c12038455031034600700c0e140350802940c01310200b582c00010a5407450a85100c074450b041c1e80c58980460b00102d01910b00a0301c0e0042025800180f000402c01f9500c0f540b02c098030034280d504115040b40c0c8070500001c00d100701d0010081803280c08107041d80300340c2c00f0710b05407213000864603681c3c4032907800c0151010b40440403d8001c5251040c800304120300c013140b00201507512100548400c4080d0300c1c0d40740100003000c08031060513034501035490404000340c01c020003524000e045660321803d00b014001c8010001e07110190990200c2c805102800c10448015032001151034040e006541c0d021100000e004003664020145d9960f0842c4001c5c55400300b404204242d040c2d507298131840c1d6a10b600f10140b0304042d1074098101107444580c0c018030f0b00d002c0c10368449000500310f51440450a00900c2100c1124002c1c010850448004000101001c1d018130024101414810710015075600d01945407030a0700b00c80c0c1c5c10010482c2038801103a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 998161582 1250 998160332 998160341
    0xa0b03060a2301120c0f030b03070521010f051306020309120301030b100e0709171203010b0c07120308060f19090e07090b181305060c070201390501 65
    0x41d0203000c01d0000c1c840d00600c0801c20000e410b05034002064480742a203600413901a44240c030b8255a201d040d03480b55050200c009281ea80c60b005d07414015503600148540c0c4000c18081310040340c4801842c80e841601d811800c4490141d1840782c1c0a003000200031442828490100180343c01c8900581d49039a0010a6800c280ad681304600140e44044004014090084003040c4110b09000402c5290368039110000700013001120b21100241200c402446007601c2c1f0b24800d21071018a204542c2e00502111240c903082e0403d0300013450f503400124404110441c10014403000b0b1105110480841c0b5150b200101040c4004141c3c0380650700d1414548032503107400402e4541d440200ba16248266240e10f554009031540040c015594030441c00e001c11807421030711540c000e511000708034100c0c0300a2001034524080005000a82ca025a040880007081c810b00c0614031920241c181d241c0c0c0c034501c505c00174001a101100b10002108107603403404600c0341c00102040c190b80ca01d84142c00b40c16103454481e0140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 998162832 1250 998161582 998161589
    0x90703020918060601091a0a0908072405090f06030c070222110f0406080c0705010615030606081303030509190f02010807051e09040615090e13020a0b03060a 69
    0x80324a801c0100640300501204110300c800000e81d003e58552034011181a0804d00458995114452800800c0c002800003400500a14100680b55a90710414241000025403204c0c518012000c148101602c1041c00c1e1403a43d149402c00794105580d180101355415034103260180502c00020200f98048064000d9440241d401408090701020014130311031210798500c0360700044e9007044e503101404605e55040d100c4020800100c1c500300340c07500608544183c006001200190420407180020407800c0c0201c00c041d1100c8a405d459681444c0c100504640940d4043c00c108060b400034000c2403540324905801c090740514021a803602d400750a24201041c0207504002c2d070608000000422441603103070444c181c000d072100503040e9903041e4103540600c02c0c24a0002c02108446400481084030000381103030070805000040c919480740c0e911013400c000302101c9808501141805c000c2d540380301c400c5075072040701d00300c1d0710f050010240d0104030b02c07008600a0548070071010000640d25240e241c4010001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 998164082 1250 998162832 998162839
    0x90c0e091528090c091e08120a080a1a0603010914070311071202031c060914090a330e0d02010b060423060f34030c0c230102010f140103080309070302 66
    0x6240c07201c18906c6030300f0014802c8039100d0080e0a98a20b8084a68080d200c4195294490001a82c0c40880c150010410741c0c042d00c0007031210140c03140d00341e11280c0241d4042c0220110018406442c428060448503005015604050920404841c0c2058507030641c1e0509078401d18080c161190840706a0031401845110b0042c03401d0002400a808410380080c8100d8007284420403041e1100322248910140844a0802592000d03501400040b80e8000c2809003027079481145140360008880504090198008107141e2511400c80c020303110024805440403d9407070000b0080502c12102044060080348a0110154900c40c1e036501003001914141403000e80c0101001d54070200c01c0703134290042c4c100e8a200070b0044880044030304500406180d1000b1400070b440651048601d41d90100c801c000c4016007240c4202e4009400900707003000662542c0403d045400b4542d80c0036a0b100020308458041d0304840100d820100200310035100b1503d220f044d40d800102c4a0380d02c3d51484a454a0954968002500b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 998165332 1250 998164082 998164109
    0x17100504021303020f150f0a12020a2604030f0509060c0a2402030606180d02090405070612050c03010e040f140105040c120c090c0e091528090c09 64
    0x26030020726280c06066030300c02c545c810101000e401c00d10003c0c507001803044031407020401c41c0f441c040309907802030300c01095a03162805040341c054581e101640c200e09040c0c40860340d150300b01140040c00400341d131484c8102490340c0d0841c4c9019140204040d4008446500b400b4001030302c418152501c0086503007411113402102d0f01c95025180c5902c00c0090400d007100035403036001101840c0c00c0f2074002c07207000c5c02000f44403a082003140c0e000c04140c000180307421b40d0700c000315400510060b00c0d14850075119900a6018082262910002420801c802a102c0460701d25120400c0010f10306d0b802602d054030840c4910081980c0e0354a012480c0104079400905125545a0b5404c9070790340540200d841644901902c0c1c4c81c4644c3d40744000c40c2240c1d0aa0004c005400c640c01c2402520115030145c80d0000551410346101d602c50008950500350681d401000200303032030319228060401c081120325500c448109043c103101d40301035220880c45070340a00c400d450307282c08045043c9841100741704060060f0040c1d441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 998166582 1250 998165332 998165347
    0x250c02090f09060601140a120603151a01020a030903060e0c1801060f050c0d0804021302070c1d0103030c0b091606111006080a141006030b070206090c011710050402 72
    0x141c00d40c01211951818880d080020308503512660015200f66060041141000d80d0b910058a6031000c6200c01c5d988690340e0800000400d03906816448080f81c58500000c035440d041c009022000382c0c1c0780d20b281c155070202558500003503000c840c140403290010000155001403600d59070520880328909030340700401c0340c0030151422685490504840c280e48401ba12007039401c4040e61280100e10810084d900200c2c9040c45c0c41d4000c0301f209502030304c028911110000e00401210890b00004004d4840903698030051085000c0302d402ca0080907440406488990b1442d54010807164020700000c1c031075503214001c1050200e0821123181c181b1425a842ca5119480344401030980300f02800e4801240b04000200c9010481445200c0a8404c100041c0801286c00e444050a10f503c41214501520424480c00c070b02c07080301d116070009148121103090b11400c225038000c0c900040500107000c030360082c40c0010200e030381000c004501c1a00e1344036806290390700c031008000102c42640c0050341017400000c402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 998167832 1250 998166582 998166601
    0x41806150807051801090e0120070c1211150903030301030b04021c05060c0a0507020613032603070e0d0215040603060609080a110a0f090f060e250c0209 67
    0x40d059030003a034102c4864030783e41c42c1000301001005804000b4002e600005110f43c10303194001c40500c0c0d09050011605803c20b040414142c5030070740c28103801220200d0358104005210122034001e1000150902003030b60280c980c084030440c83c900891144010b24003ca8040c540f401c20342c0d01100008042c0c82e101d42e9241440606240111000c83c4502007021010702d038900c0d0180030340c81980d0004010150ba43c2c1c1c010040c81f40b07900010209043c02414810200103a03030ba8001440c590710040905031141d4178616110f404181040707030304070040d241340700001054208003040d0382d44841c0501d09140c07004075500c0410041450f2810203504481e4481000c0142c24912004100700d0b41a69020086155a44411610725400b400b07403102d560005407180000c500004882240c1d400c00400041001da903030090601c055415900803085551902090a11540c00b0700c43c01c8000c0940c80a0001e207890122140d5021a8500300340700364500d03a0108202800344a90b01604800c0d0b40600380901e10304180050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 998169082 1250 998167832 998167871
    0x130c03050705090c07050618150c040906050102030f0f0d02040e330315070311031003170a02030a08040602040504140a0501060c0206030705250813150509041806 71
    0x8550142e0400c0f0042120100c0a03800c4031030568009018007000d0712a45a500410b26044148811510480010b0314441c0e454601c9180103124040741c10360364924048020068611941c81039040d90018803560222a04a0702140e81c02000c036009250b40e1910f60014100070700840e00004000c000c0700c0200481d03500c450f0800303001d000b01c82c4201d150a0407409951501e803051174421580682003c00c19a007401d94495109401c900a03080100f5507003040c084804107030300100e4500010846002c810814010314000000c1c80c1c940c02240799250280d00d81c4041e41da442000003020070020503030f0000d03082c440d541d81620701400b40204140400f078103040300c240b10100240d4410003030506d408000202c45005410881c45240c0c00391405045545a01054443d90400c1400b03007110951600b81d1500d10040302c1000140c14428044140c4645814200800c0800c580d0800c018596400545018550300013041c4c41890200319804203070760b03494002000c40400060f400030b00c41410f007000200c922a44642 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 998170332 1250 998169082 998169089
    0x6040503070b4b1603050a020c0a030206160201200d060b0d06180902031f020d050103081909141c2012150a0506010e0a0e0703062c130c030507 63
    0x1034414060003e905090f00e900401d403030742e002c1c5003802c10080035151302a400030755005200120050608031460b11302402c0110058048005802060820034440070b1200d240030425511310080060b40d00c584462010309043e40390440414002165901c04540385401030700140035004105916116416211009802c550080103a4005802c07048500c0000c00c3c49040c2000d17030000e0042084040c102c03215aa220082546150300710740803c02400b82d1402070142070f00035445619440e5030751100701e0100d03070b9144404002400f0490345c00720400480c4110408411070310401c40354081e0000101c0c1111000c1903403200c00400641d606280501ca1040e244090b2008107070594103420709044881c4915243c50fa00020801201c07072510100c4c0b4141c507560b000315031001042c117110441a03120740014400035129403002c44400102000c215400f079140c01a1002401ca85110304a4601c407120204000c03901c2000f901100360000380085c20901d008090307008030703907003140340e0998960312410083e486000902 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 998171582 1250 998170332 998170441
    0x2030708010f0b03210f0c0a03050910020102070c0501050f0d060807090e06010b1e0d090501090303060807062001140712051311090c2205040e06040503070b 69
    0x280e0b001d481c02d0214202c00f80c5d80030b5104840f031088504248402e6500486082c1d170165038240444041440c0400c0241601c41c007a4030b446850302407000802c40c2c1c911601d01d0345401c41e40140811300011b81c000c2046c1094600909010307443d804880f5042c01d8501a1800c0c2180c4542402d00004000c0360100d059016070f00c0c020014040250110881540c640082c0700c3d00b540c0610030010079485448071091404401c0c610344030145040c12035601a002c2c0d4448020584942c0d540b48606020190148075100040900502810601c0d203883c601801540c180301e40b4400d1005600000c0640c15002c0d44494201c010221400c201c504064500034243d44008640c045041d01c0d00340422040002c1792044080c495201804d501200140c400380300f614180680030181ea80002d1090031449070005804c2c50414110b040103406861504003040203031060780d440309000d90409002d010100314040f003240c480c2c9030041f683e0704454455400804103c00c510803c1030104905045030203081140758210080c15501c1c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 998172832 1250 998171582 998171591
    0xb041401031412032206090501020904200d050604020409050f01060207091418010e011d100506010806010f1e110d0f1d0f0a0815070c0f020d02030a02030708010f 71
    0xb64200b9951510900400c4807858203200240000000d940070300c0c000b0b040035090000b1a1007568910080d03800c45101120140d40104099001e030a2034480d001d05044403441c1807101c3d20b00800d80e800648034a0104200f100c0d140c9000800340d40315034040760300900c200340c410011850160718a0100030303c00e000c0e00b0014090080c0c00a103464690044030550a01c1e01c001a1094849142c0230550f5032546820400a54a80605901c07400742132040a848054609800c00b0349055001000c0c02c00002d08942c01590340380100f0b02406903401611144d00c071100382804800d50325424810303030b0031414800103003010641120340e0301c603080c1c1d001c01c040400300112000c54201c40001801540c541d1041c16500780005c4403a04804d0300c6103007081c00b841003e980030b80000001d01c010008100b480e007080d0490b040b69485524641c0940c0b4080340300c1c2d64400030501d45107100c080c1030b85c0c58450242c410071010388540550500b407010765500b8031040c00d0340c0c0e9004080320740b4596681e141501800404011a1405240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 998174082 1250 998172832 998172863
    0x110c010209130219050903100c1805041e0504050a20180723091509031203071b031106040f06110a021513020a06020f060a11071101030b04140103 64
    0x49000b560307807141040b864650700700c0005600f03c030070380c00074a48030340e1610900000303a4001c4814410034800c0884c41e40c6000255048901d0082b040019601070390140c2d19040c1050b090003d800c66040c000c903038400300403d403078580b400c01d24500052032001900500c035054106017000d11014540c065400284c600301500b403010301e40ca8501000444640020906800c0c00c4040d0020101c9100d40094804005a0401c4c8202020501c403483e0007512200040002070000c545290402c42d00b041d08007051402d511f1450300c00001072005900c1002d08541041840071881050f00a04803560700a0308c981c2110a145410301780003000310820035003910400d19201240341881c045400300d80f0403032003035001480b1688040111048102000780100301568000a550006a4580d0916002014030b81c1c0142403049803450151308004000d003a2460007850302c070208243d42d03a05002c1c1c3d140644c00c0804101c0003c2c550713006802800c209400340d0740c80ba142641460b01c0ca8000d1268074142c9004204141d210360701d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 998175332 1250 998174082 998174119
    0x8030408010f3902011b0c06050906060303071709090403030f060614090603090a140604050606030705130c020109350310120309080d0809061303080a0c03110c010209 73
    0x2a07a20b120407824008140750f20710909205445607074086034070001500c03aa0913060340300c500b040c0710800d00001c0c10308403d82042c040c6901801c0d402c10b8041020301040c0c113095002a54074410f88400610b00d0700491030580d00000035030207484001d0005015078085250503d4010003c01d2401c211168041c83d0a00c0410b0a03440360f00c7c000003c07240881d01c2c9180042c03c01c204125a00700030604500c0d88190800100068848001075040c0d507418001044241454641182084e1005144a019a00c409801c00ca9039542004041042144550016030510454004c0307014108a03580500790000c411028150103564a00e402d00001c2801805a080d8004442d921601d12060304c0080301109031403000c0c00760210030890782410f14440d003080e101080e038640c1c081e4100302c01010790001107494a0304100d005901030100c01d92081540340c501a100b041a5009003080001a03d5100c01036903c11b11917083d41d029601c00260301c80b5021007541c40d0040c4200084c00703580422542c50095091484010b035154 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 998176582 1250 998175332 998175371
    0xc060e010b06042714061002010e0606041a150a0f0c020d021504030b040c14120a080f0412060b210604060f0902060a030902090105060f0909040c08030408010f 70
    0x180000c0c65149014034203800d214071416455001c0d2581312a0725240b510083c6203200b84e031055040300424114a152030310030000180d010303002d95415a410480c1d045008400481c004da4011001c64000440c00340d40f111501d01c80806c11615034000645200c14121805404050304813602103644448070200d06841c03c4030070169a100080d00310a0038842c0340018a0301e1404400c10700241d1944d5414a81d0b6621007152946040e5020f40d011400070500784144038120b0550000c20310295041c580c0703d0350758200309070b444100c404090100c00010505141083c88001100c00600c00c00d61101070450142c00d0441c0100060303240c4034465881c0000c01031440d0011100e0074040e26171400500480e80c0c2c0d84c1c071880b025200f01502c901c03a01e0340d50540100180d0700c1d9009040d50700307201c1c0c0d00090b00c1c444a1040c400d02072010f0f00141d210f000e080c8506101814000e0880f00600c0e010703950340800f82c98501c1d10040c10150360b0040340050001040118910205500c180250b8407030400900868290014191440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 998177832 1250 998176582 998176601
    0x1503060507183003050c1608061f0f081605030d020a03050a020a08031305010c02300702030604120207150507020d030e0a060f080c090a03030f1701060c060e01 70
    0x5a0148108001540c4228032401c8040c6202d4004080c4160b0f6041c180d010320b4040508401090010900c0d19503010104002d00300307420480f801c0d100403030800070315559820001701030f6280807042ca4882c011465401e07180c1001804507600401e0455205c07422141c681480c003150848040c1441400601d80c42c0000f240310560340e0503009020b01901e152030898603948200101e50941c4540b03031100c40010319005c0107600c9500e1107698000c00241510b072190a460340c0c0c0c003150046501c031001024045e110183c54030b007540b21004603600030ba21001c039481010f00446c84041c0d858040c2500704414031090641902e1130b540075600369841c0940b00d00444031002540024913001580a01c02140141481110b007002a800303818001c803806442ca0005103c190160002d100080c0c2c1202c900b140140c116105a41202d20b9024450800f642c0c040803c0402035540310150400554150101d803030360103684403096451145000520130f685501018060141510046410070724000302080843c0b0103102c0c502d40c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 998179082 1250 998177832 998177867
    0x901050d031419051908010303210902060a020105100e0709030b07121d0c0612060607030507050102220e0f2a1818010b0a050d0f1503060507 62
    0x31021501c0848002e91481c001c050412810000d80d14114400e0707a00140311101c50740c0b0166240c14800b0758042030402103070340304148468040103000098000180f1015008005000520348007141c0760170b000343c00c4040c0081e412104c0043c020621a50640001e03201d1000c490104940320f60b145101c10b4030f5042211118001a24410300380f000520b40384005800c42203a00d4010403c448015501003214503030352140060320900400c03100d0710b07034003800b000603840d40440c2c81c5810403601069020a94030020002803280400240f0a000c05002c0d4003580d005581120007151911440d05403840c4601c00e240c2e500e50410b912140014502d05985140c0348103450b4010980980d4441d01003100c50504d4400c0e03140e900b40c0054210541303038080d10001c0e1800d506202814800014000b003030200c507864001d03160810300d502000601c082d205801c100c0308030f0741c1d07107190240da965500162003008010303c208000d241030404040f0038202c840c0b02c49420607240202d03800c011075200c41600740c5400d021040140751 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 998180332 1250 998179082 998179099
    0x209090112030806040209040b121f0207030e09090102040b0c0706020709050c162303042303071a0904090f111002070b03100f08030a0207060810090b030c090a1a090105 74
    0x1460400746c002d050410000307440802c090f00f000b000140001d5121102d84101d51100c901c1180541400f03442c6110180500c40440c43c107003498800400100115034000d0144414201180b0504400d50441e001000c801101c551605810404552540c00a10a00b00144076250001c604c01c034052007090b00600a44c1100ba103000c0003045015440e80b403003502502c0c540e0860300c807081c40c2d03040f5000340354030040d0440165a9540c1044640704801100d03007100d440075a00191000c3c03960303c0000d402c00a9036002900da0381e66103600d00c48441c00c1d00c211813213940c0080c180300541c020086400308034400580300b10142c401203a104001d0103401040205c4620069000300c000700042c8118900454200e400304070300015080e1207a0b880b42e0500b46a41c04403680340c0c000038104003043c1e418002031003e4019072034a58040d00f4141400e51125046000e902801541d5409150b16035070301b0003032440098406054200245000d040d40d4000704503444488a503011000c14181080c42c080102605a030750040130040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 998181582 1250 998180332 998180341
    0x60305030403110f1c0f2405090309100834031a060a030e0f0a030f080c0406140a020f16050f062701091a04060f0206190b06130902090901120308 64
    0x70541e010b1002540c043e0b000001c201d02181030030780c0c203a03181e4284019040e02030042d01c40880071a02300401c200c2c900d801c00d02183d40280e40d80520403581000524040507140c841d210708040f100303242620224a0104607040198040048804091200d8103440405c254548041c4590b242044284100e0b4460420000351541c5802a031008400742144000c82d0a10510ba074266031030900101303410350108440d440c001d5580395006904a5000f8039a0503000c0c10245051009000da04080410524030f060100c2d8907460b6510810045116541c01d10407038004982c0366148400400c0d0380e029150240c0700d0180c450780c80782020003ca4034054101e003450941c04081540340c0c120013500b20100d9041050580000994880200c2ea030100001c4080400781c3d83c910346000644181b0606034048155006041004511018840303c400405440000810143c0286000034090721030b40b040e2011401301100301003024000d0b40e000e040c403500c0507a800600340c0d80350070026841d110350b408001c0000300c61a0004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 998182832 1250 998181582 998181619
    0x6040c0303050d140a0209040b1f2321070306030503030c0d0605130203070f0e01022e060608090705030102090907110a0803040b1905091005090709060305030403110f 73
    0x900f0758001c041c0000500000c040c050043c1110309848020302141c01181e075103840d151a100c0d08290007803c171001411501e110441001c040072005410302444440c030700000c9015060a00c41c501c000c00d0515042c3d403490340c4c180501701a804601d400c08000ca414000a000320300078130845061740d400c100258207503503d000030101d20344e100c00401120316489010001c0c080e2101f14075020b00c014602000341c1c81c1d252081303000b003c0d000005c0031002080100380c03c06480341d0f004506900041e040156600710740d40034208449020700003031204d8048503d0480700042d641e6001c01258028010a001c0d00c4580307590300c041500340e015044503164002e03a4413003c1090140070b50141929980d010090314030414154031101d134160012101614a440c56004106e0f0f10382c54805003000d1028540740402040c1007210074256140280d480500c18250307143c1c00b040d000c0204026110052010b0b9a0512000d0b4480c60015103d0b0001e200442d0300d182b2081415010b0300c0d1072140e04010340c0c0c02814040c070b00c101a0740c52 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 998184082 1250 998182832 998182837
    0x6060510170a0f1b0f05030121021f0f021203010f151e030b04150b040519080601060207031a010b070821280e060f06031f06060f0206040c030305 64
    0x80892942d92420039440144070f500490300d00c000910480350300c0c1c010a100281101c0555003036842044030410041c84082c1d40010b812448441d1142080c84170f00061010400c1591680c0c804a90040301d0040e4401d66540640984007908143d804d41d0300c40400402c2d15030441c0002c0c06002c200b02d001030011b105120805040d01310201852900070314040901440f17801149116800400094a030740e02c55056062a016001d103c24184203040c42251901408503014011405428800d9019100b511030004070407101902405a14003619800e581d00e180180d62840709110880d40c01041344100c00d40700c0c010100c114102c1c1c000145c500c1c5410442c0d640c1c0049540070403120200d501981c4040d15146005540c0e66101d5038059803074141d614001049010b0000e10205890421410642130380151140803503a584c00c0741f2544002060703a151600041c1c100710035600103d000d055000d4881102c1d0710140c04c0801112101d403103842d001c0ca0a680c2c120380340e0354101c9025001c0f05070440c0800009101d03100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 998185332 1250 998184082 998184091
    0x6060c0b040201030e03042c0705121b0d0f0e010b0607052d0624060903070e0c04030f1a012112112b170c0a03060504090b040606051017 60
    0x81c0d03480c09031508d078072040c070003a1360f0700e54041240c100540100312000b212080b50481c00d103003805810030521a0444030072400007420810449a8040c0e0003201504000c2034410443c00c2c2c18041c802c690840d0310070401003400070081d812075801d05200a000c0d0920504070750800390040090107144c2d01340070700c80800000b05809003002a03090000d61514210502c110f0340560030070324086007026012a042c42c43c20005841d550311800c1c0400203130080307550004402c1c0403100541d80c80000ea50710200386203114001c640c009404e420340551140200402220717110100c80c512484401141d80f681c00d0291070382d808000404d0a50032501c00c0101044500c003041070a00365514140c4003050388220310364101102e8425011800000008040c64000718100000c603040940c6406085030345c00c03070581d03e40e800c4040c01c900080c11000070f800112a02c65000003001d001e02900602c084003403850000b10302c04040350b09650b214a401e00100b220b2524514499005699076101c100341c00c01d10120000101001d417 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 998186582 1250 998185332 998185361
    0x3160b0a210c0c030e0a060914040212010b03100b0a0e0111010b100216080f0c100c05030a05030603010506010c03120b0a080f06100b0310092f0c0106060c0b04020103 73
    0x4498010011070040b000c02e58080c2d40c1e004200503451a0103400321080000c00c0344141c881c0700c0300b03100141d0720105050454152044a80744404004007003402480788008041d43d0000c01e800119050096500950048001d41c0150908550352880070100d8080c200e014000650b07840c0400c1d0043d8880d0100d80010300c90032000255580c204000104855041c0c0040005030f081010204032260700100c526009003040702c040c0c11464001c8020a40b9a2500e03449948034a00ea03844501c4543c1c03003240340146a079403100440750ba0f0484600c0c040d1803034000321001442503090100099095106550f82240342d41d15849407644810a200d0171009040d8030541d050f0042940c580c0019182d500304070b1003000f9203514006d020325007002000e42907079402a130000a071150041003407007804021003041208448240c84002840c20481c40542860801043c1c001505000314081e9a4000416001090341215400007004581e030b507210b051712a00c00341007014208202c000002009540640c012034070040485 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 998187832 1250 998186582 998186627
    0xa0f080d021c0b040c03020c0c01201203060f010c0203100509010b030304180501120f03050304031202130905100b1204020120030a0806010801081b031009060b03160b0a 74
    0x5400d8103007580030a954480c1003a12080fa41e01607041034464030b14101034502d0194a0b201d150343c2e04e155070b00e00d801c45260400070703054440f41c0d81000c0704003140c00c800d00410680d02c40e00c007240c0c07030307000f150b0001d8401520130704507107011001700c2d03025154001c0c5807503018020308100144030a03101e00a04c001030407044035540324400072015a030300b072001f0006081a02c0204808410150001c021500f05030450b564000c00e44486070081441c2c1c104901c1e80c81d905150596881d5031328a002c450f100c0544404401c040c0c004550064683c1203000d411041d03840c0500304004a60b03850030030700e108080ca03210b02034109404001070050040102d810315030150040c10007001c1d0101c0c0e01c7c00f4241d841342850350404a0342002c03a040c0700d4076600440d0340d40c1101091a00071815410841615100c00321890f196080f180e4801c940d42d01a1070a100c2058091f200c0d16041000c15a24105071000e040c111841a10070700800e001e070841c20281213440720603140034a07c403500300b00d810102500c1a402510350700c0c0280090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 998189082 1250 998187832 998187847
    0x12020d09030515180703051b04060608041203021b030307121817091908100b0108070c03030b030f030d1812080c0d051e06011e0e0a120b06030d020a0f080d02 69
    0x7017003d2401036208a00030000411091500170300b51480301c601034070490030f048040041a62082c0c400c2d403c160000180d1045190003031050f4003c3c4500b00c110108803090f40008010001c010000e144141c64689580142945110f00341d000c83e0b03081907601c1e40b0140003082082c04a0100c1010450b8004030300c640da1710702500000082d040c6450551105082d217884001400400790501036542c9001c2c40c2d1030144881884407002074004000100302104010b4006845414107100f0342222400c0722014095821070300e407055980b07403681d00c40c0d441130130210b0a1409188581416104c000c0700d007a04468202032001558504881085c00035003054403440e0f041c400c00220500d244a51401900a11900d416208802040d0001c1c0301c001803149041c00420140341304052081c00080c00d4092441c03400c85d0804600d07000085450700540c00030660300a80344070680c10400c5070001070340510001c070100c942d88955040201d9980000440080046502e0140311002070740741e5018189801200c100542413944 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 998190332 1250 998189082 998189131
    0x603020a1a0f0d1d0d121e110910090503030702090403120c030209182e030602071a10031a060a05040e010c0e01090f0509071403010312020d09030515 66
    0x148081d0350009a444c04800d0388011050710214040680d0006402c1c1980c4404000e403582140c2400e140c4100d485103c00d020b03130780c4084070955517401809000c008081154032002c040345c0040034420700450040d031945403000e000b46942e008480c402001103290844907404d02a1151015104405001840c07103c0081515980620007642006680040c0c0750050042003103041030749444100481b41c5018140440c031807155180f401d0000006041d00c620908102d0101c0301902c0c10341c00544903c0c4081004030070010840e030500340c0120148180b0a00e030300c0380e00403415131125a100090007600e2483e11034810079900c4004950040004004e00301c01c0359600081003d41d50078029009050f5900c05c02524240d800c094840c040c10070030718040c00c00ca81002900c008021080c02600e110310403010002c4c141c03030300c03410f0400840c00140410f6a144e59503031415a004400016a10000d8068403818401017481100748070112a00704000f0140c2101820508916032009444908100721502c2c001100c0107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 998191582 1250 998190332 998190337
    0x30109050604110406090c0203030402010f050415030e0709020c03071103070b040b0a0f020f100b0d17044b0504060f08120f07030807090e13050d030603020a1a0f 71
    0x10b010b107407424400f0f6401c01c10001114540e42008294528060242c4809a400012380754440e90a08000e05101e150050030384030344c0140d07800382000c000700014a2241c1e07a4035400405a12114004941110340c8031072001c4184e0040495441080e4000e0001d180480c3c0b00c40001e2400710406003c0c0c5030415103900b0008516440b940050b1003241000820317600e8140d01030341000100245101070842640c2e4850080d440706a2500650000b50701c61061340b03441c0d594551802081a030103403081112044020148050790020710406005070040d03024507241804e03c0030650644041182c4142d903d411001c00805000c405078845908540c42c074202040c3c40c2c407240b18402c013400040940310340c2e4602d03240d0340310b240a40c44a0b483d41c03440001d124011400d41c0d04c9003620025035040c02d094244c0d60746c9400807118200a41d000c0310707580300740505001305400d00225041065000d802a9802c1c12010031083e800d9961a00c402900b11918000402000c221040c3e190180913800e0b010501d01400c1c0b0b00d5504030794 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 998192832 1250 998191582 998191591
    0x7060f090f11030d140a0512041a1302010822050a0c05041505030601060e060d0c030906050705070b010e06040b03010516091a031909020306040f02090c16110301090506 74
    0x80742403103440090286070940c0002c026800c80c01089010b1004034000e12241580160070b617007100100f002032446010710156850003241c5a0500782500c1e19090500340d006802e03242c25146162400481e200d0400021800c1c180758040c0c51b140620b450309070300e84250800c81c0803010000040034401c0c0001803021300034807004134006c0c810220424240002c03c8129044141004904140954100240d860102e1850b045902c5810001040b0004901040305417080362440c10190740381110007034406405920400905010f20800c101c166581082611284030f4018044c02c460080001040101601c0142c280d2140002c0c00200b0384503448000320382942c400360b5091440340c00b005141643c5583c4109400001c01e00d103401d0300690068a078113440030380310142640326401e00ba144404517400142e00710401160b40a070848000e482c2c141090052562014000c80c424140b280104400049140540382100010b100141c0d003007820355118032002d001c44014541554840c420400460024045607105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 998194082 1250 998192832 998192843
    0x40c0806150408150a06150809060703060602250f12020306130305070f03050f04082d07050d020d06110307020115030b0c0a0c051207020112050705030c07060f09 71
    0x280c2000c00800c05050740e00603030101240e000380802c0040301800200884071032040b082c024026201e03803444001900307186d0051000802d9601408038010f503c0401944a0b41090054400549607040c4c101d050f100f00d07204000040e0b11080d10030450085c4d4250b002009810301e0200c0b078070f145da5480d4980d9506a2940103203099201c8102c98000c2d82020b00c0615842100c0030003804000005d0381d8041c0c010700800c000542030000012440b8101409074040b00c2103d0320310380d070540d08c2d20b5071a40c03841e64600903c9225165041c420441d0f100410240c52808203060040b000b07041818207190078086400d9801d032041c2c0c1d00400044022020403045c1c46610300307014841c400c0e1503981c0f80200001c2d00b968207008003045800c005860420120700f440c0245030300000e01120407079407400c0c1024101d07140780200b000648280034084102280d842c0a0300181a8540700380c81d03042030750750103040070300858104030b42d514041001080040c0564100e1002405540d208501c00512004041111800c42d1507070b1408840c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 998195332 1250 998194082 998194097
    0x1104020a11070b0c060604140c0d09021e010e181501210207030206010b130b0a052a07050321160803040b1b03160503070306050d0b0f010839040c 64
    0x7400ca0741489180d5206d42d0596040c092142c2e40d250035140107100403c00d0038084008105522031040f40d030030041d0036a4004005015041c001074a00f9808035070b402006001c00e4480e0303400c0803181049004c0802071041c0d9100441583d07030314410551031080b04c00da800c3c10000201c0f08111203000720780c05d60b52000c000f010010b0b16207510f4075010346400e1040c0c000c070b030304441c00384900c1034060074188440307003a1483c5414441d12480940010703115030107903865102d5603103800c4060344580c4290500902c00d0400301d4044038012556082450384404039481600c2d02904260242550940744000500400d181080510510059078417030f101180c000342c5040f1440100a814010031104880307001e4003000b071308880c547c61403c4c1203075040010401d180c01601801000310000e44914066030002008050180051540480c070f03160040b07412310b04031034010b08121002c00200d00500d00150a504418030f240e02949407400c940340342c008050528172400104030300040c0480e42500c40d401144421902600d4085 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 998196582 1250 998195332 998195347
    0x13020306040501020705070b07080d020906040b0c010f0c030b09010e1012110a1d0f06121506100c0201021209030715021b040509030724180606121104020a11070b 71
    0x141002002e23442008100c20070301281c000b25a0160488031031121540c00140d403540700b0750206000b80905e900c9100d140d01e01007900c001080041d0040040c141d00f0040c2040707a600755000139001c541d402c87c401e0303030400050b500510581c0d003095150364012a01e0007006412a1b62140e80c41c00e520804102120123060f0140d84143d58145061404094074181079000c00b840b90714030091100c1c4400401843d40709810501181080d00c400400d4481001741c070065469440d8500c50070f5203082005e890180c001c411f8150b0401202c3d2040c003819508070f90590280c81c607013600552000c0d4507004a507a00794036005007900000c10310081c0404602e1035140b500944040218940304100e0700900d00c0030b69020314141000c0045442002c400c613200c1591182c81e090030501c0800e084042e201843c440c0328035103840c0c000d050144c00400c000701c2003040d114010600c1241d03194080d41514800440000702400398001d1080711928081c1c0180460b42d5140c5480410000d504231414032b092041d034002c0d007000c2c80018484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 998197832 1250 998196582 998196593
    0x1804150305060c07030c080310170703021905090c03041e06052232010504030503190b06270d03090503010f1506030902060c030a17220308130203060405010207 70
    0x82ea030000d056006181040860b4401038040303603c02d03130000c00841d03001000902d10546a00310b14081d003034400c03040e507802880800c415910030680c00140e02c20301c034818403a48600317129002882600c4015040b4007458550203120035007a0005001202c000714856105000c2404145a40020038041c00c0045180c0c03c2991701c5042008890804c0500804810350390404106042502420314418080f811000681c0c0c2c840481c000440c07042c52500e5500300002d00c0305041d0b20030095805548010a4280104007943c0b1160403200c00d0800b0640102080c030004403540410814146404940d211070750b03400220000084580201001c110085032025a040c4a241400d22500440c58110304040003030640c0b81d10b02e100e4200c214811f010402d81c8580300e20003151900b03400d40304000c81c5441102d8031031a40c01400345c1844000c000303030048403c0d07180020b4408060f201c000c0c5c04030550641510b60303282440c1c42c110b50244c002010005448031f03004510340161820800d0600c694003a400050f00d1341c40500d8071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 998199082 1250 998197832 998197843
    0x60a0b0c0618011811030703020405090102220f06120b09040614090a030e122505012a0b100b04060c050106050d02010215191b0210050c07081804150305 67
    0xb0040141c1c50402d41404040643c6503984e282c6400106440301e078118400041e25100c1c054100941160528060000c803a0054000e00401e002500c46411008070940002e4030301a03030780c4603070a10311901d20401c0200c18020007800031910380708000441c0305c10b0010003003507070741e54290727022110140d490301c10a41826007400340980050303400000d00341110070340d20020840c050100003248950240c040c0219001030410025080120b00e03540c080d0205000002d44020000c14441d00303021983c01142000003408450041e4104009070380d04080300d0303c054880001d117900081811914040d074490200300d20000303502600041c00a5520b5030701403c51881c11509460301c40d4002d81c025603180100100503030b00403540d054142c410800b83c107410303030320381c440032101c0300d107003641820507501d0300b81800e80300d12017044494444c140030340803a400350b01203442100440b81c040302c600c05035160034000340300050b5994004000d5540340c041040d1008155400003030441d844480307c410000a4100c040080100c00e028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 998200332 1250 998199082 998199121
    0x6140a0507050f0f0c1501080a15020f16030c050106081b090f2202100e03010c090e06010c0203010207020a0f030209070201020301060503060d1b0b03010812031e060a0b0c06 76
    0x14418100742c40050500f04034020201d030409480400b06040b5240c0c4420810000c8080c17001c0c0205035556590b824031910b4903c694001c1c1d070710007002c03402408003e003076000f142c24040d21900001d2818210290700b0800f0044c0040c124200703d020342c1c0410108000b40a00406000c2c100090001c090203e50022070040100d410140608055410400c0040c0002901a440300804d04080703040d09207119003040c20075025000941c408215840b8090065019540040c008000d4008120141c14620103407400041071080b203c5c604d00500010f8403e5100c1e4002d0780081c0e02c040c00240c10b006003a40000c1c80603100d50040e12034241400d8082081d0b00c0c0c40317494260840c0c401d000031813665041c01c1009086200051002d80603000015050040000c402c8440d440c2c00103081c4800041522065003405580c800c0c1701d40c07881c0b48034884d64600b9040484046038040d4500310707044400c0c011510302125201400030081a4802d1941c00c0020759611400000c01c400b02c9030802400c41890044480b21900e0101007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 998201438 1106 998200332 998200337
    0xa0e0c0c030403080d0b04090b1512070b031e01080307062d0f0617031c0e0d2a0201120506060415020313060503090706050f0706140a0507 61
    0x102178261040d003094240070706580d1000f04426034a030450081d00c001d2102d4081620b0400700360780e500320110040c0c4141039002d1403408090130800542d0001202c500004200265442c03d000c24189080c950320b00c1034025410150841e83c1e90243c000014540c65030307030143e000300010414080a004140d00503010f060148180445c0184c086511600002401e214004c503c002c9041c0322254030781408070040d1308000c01c1c164103042200304001a0600250380c0d070708080c1050320900504d10460b0782034440300c44100d046081d8964900540d4000070340c1000c0141d5200c0141c0e808000001100743d621404103c0e900d07030034005a503e20596206a0018203040c4082100c560080058841040c180d409c80500955807403040c0d605120032a8042015002214240696401080500b2004028805072400c03e5140e5a815003103505004070546d08440440401030b0640560080700d50018072403 = true := by decide +kernel

theorem cover : BRFrame.Cov 998021582 998201438 := by
  have h0 := BRFrame.cov_init 998021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 998021582 ≤ n) (h2 : n < 998201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
