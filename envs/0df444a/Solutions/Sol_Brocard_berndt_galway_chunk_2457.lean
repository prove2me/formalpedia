-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2457
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:44.970786+00:00
-- url     : https://prove2.me/submissions/86c417e8-a45a-4c20-af98-d4edfff07278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 441726618 ≤ n < 441906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 441727868 1250 441726618 441726641
    0x1051c1802281a090406140405060307030b0105060708040e070503190216030c06150b0903161206050603120309060f07031a011b060504050f0d05070309050108100504020d 75
    0xc0c40d030754180a4500041440307925000c1d00d081c2d00195483c0400c20fa1092600195594400409100f00072140c0c6681c003445001d08040c126010001c480d0300c0511045890090045100303501c011810004540c2082c2ca060650f0019074000e42d03112090b007440c1c030389442103501845c0d074500c404041200d100d500c14081c50217031b038030030540c03c00c8181076800480c00d9005a45141c480040b05c80e99103c0040e02491060103802d204000c007048040c0b0000c03030700948001e10b07800560076080c0080c0340c02062038107020116401c455964a40c000c00c0c14000c0040c88800c95240042c0901c0d0b03a040450181c2d90200300c0701000c595100c1403030b40e903868281c5074251143c0003901c6040320609070760b003c990b08a019000c0c0c4041002c0711411908803085120044030100d140b0184400b000300340150030400b1076083e0040318807980c0a14020714a1000d00d42e00c00340703000e60a0784039408104080c05850f002940c404110401c4900919010881c1d0b00c1c3c01d0086060500c05500c2139038001c0c80041c01c600c4a10b400d421400c55100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 441729118 1250 441727868 441727879
    0x314090615011d0f01031416030c020304180e0115080c10080705122e0e0a0510030b0a0f09030f140c0307080f09030d020601090c09030b040201051c1802 67
    0x1400100559803510401224002c034503a20f035502010342007507403006602003414913000c20054804900303010b2100301594841a050440a511003005405019290751808244010351609140012588401d4544042d0030300c0d1545583c2001c0858400750494505e2901d540ba0341b0407d159101c04207941c842800400314007510a90040d58611400742c1c440c280304415684400e0714103612800e102c4011840240301505950601d5503500491000080400085041034001164141001c0c0b150448040040810089a0030582040014569014a0421203602030030045c100c0d150712005a01804001c40b5451140c0e15203003445050550240b040104c2c40490340302d5804800c1c2c4010308941c2442001d5503040b240d40100000d50002da2414020040b1044038a4028180001c02c80040c3c1400541c1049000590014005101110346442501703088600c0b814141e002038516601c0342040c0c4c03c01040641400408220600700079040030110007541c02c0000108116050502012042c1420b0a170a0b801032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 441730368 1250 441729118 441729151
    0x501020c1f0609090b13020117090304050405010801020a020a1b0302060a0519091a0a09030c061e0e030c042316030e01091a10030c030506060f040911040c03140906 72
    0x603001c0c4a00c1c4c1e10150080b90b010b28640e500e410054060528040890400c441405003800b5182d800358905d005e00c068a000c0c5d035540c0e281504000c01d80b401a042907109910401c58000d00307a40001c1c2e05811580c0c00661030800789400900d04c4207000151380080d4010900040c2c001c03506501000401d2070300d108000d0350142e0003d00710115140303192805040004400c0450f11980d02c0b140a01400c0b500b0b001d4a80701c4409a220307551200f08402c60360000b80410f10040e8400c80c2803581c0d5a038940d00a0042c504203070b480c1d5800001035661410500c4030341c0203d9844e8030500c460f144084080e115515840c6240b81c80341816080f607207000f00300d0302da002c00003440c2182c1000d0400041c050802926000791030074500000701c211969510034064020b403010290b004c0c0001c00240c5d0300100000841c002c001a020300d1424805114941500780900d521443c5898003071400a034a90080390403941c004d440c00a401d20405109800804150b1070019100039600104128840c0020b040c41c85003111882c0103610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 441731618 1250 441730368 441730379
    0x50103061401020a02131107060b01021c050306210f0f0120040510090e0c03010509100510030506190b0913021c020c120403060905060702120a0c0501020c1f06 70
    0x151181181d660041e04040032800142c43c200120a000c1e001c000800178550080c40c001d81d080b50301021007120000d803107040322601c0350f8041c001442c624000001c105031140803140020984d01c0700400340342c8103c1c421401d031801808103081c400482c1403000203e92214601041403592200c0000c0c09a54540c05e04184c0c85101c52900030403500c2c821150348003420075082108002c9003d84c010102c0080201c01d42000802620030160700e4050100d54400a550f541000144a2288801402402e1301c140c1d007501080103440e46103041002c0d0105143c0020b940d122200090141c54070f0303804112858000b048013282d018811801000ca03940100c5544941c1c1c2d0b90060071400368001d00240b01002c400c40e443c1c83d9010700042c0c004000071942d510943c0c00007500070340000906c0e0002d03001a141d880e500e038582c10401404014254100074107000410301744440a544002c2442004010300c10860180035010402009406413a1506840400d45003440c4a042030b0310003250345031104910a508000c00003d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 441732868 1250 441731618 441731639
    0x3090c05220e03180103110c01020a0c050f1504030806030c130c09210807050703060603200102060f0a0903090312030b100f080109050402060c01050a1b0e0d0f0c08120405010306 78
    0x703400d005010750b0301104e0400030041d801410001c04155164408008103400d5030020300c0101407903803090b15060640007903401e000e85800c0d076a864081160b40070904200340c01040d141c103651301c1941450403414545d20240424100b2081c3c2e01c420b6000318664016024552590b003000305201242e40d580c0541940e55480440b0f031550120a8517685d64010f81540045600c0380000c0549500036000c89086aa0707a5072800c0458801754015506220082c811400b24202c203c071801400c8005d200508590625000501000c2c001800410455030707070b00103005c109400b03001c0c41e070300460f0401840301e9506015000a00a050000180d41c8140c003d4010802600e000b6180340807094140d0f03503100c003da0b003445060340081601910aa90055050005800b0410b0901520348190420440810000c1000c84c188402202c416891824010318a245a02ca61555050348107190303041840c80740640d035076090031400b076000c0f90071056842c095544180401c1000c100104100c500070390781045000d40d038116100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 441734118 1250 441732868 441732877
    0xe1905010b180c070303050709150203040f0e101701090206030a06050415060206070503071b05010e0d050711060d090b0108010b030c0a0612110409290901060f03090c05220e03 77
    0xc050400713000a01c0824801c1d0f200380c2e4403401a0905102c9507440c0e01503501002a103c5914005900008045c03025160007210b08005000f0b0052452070b40c1801c8480700140381541c02004820340740e4900d81d00144c2800d4201555640d0083c2100da66402e2080810b03001d0001030040b140540d00700403903055002405482e62040f03949580c042c14580e21071910848050f40050200340400404120301e1011402040703c640310607200b2000000d140c010f11781d5242c1400001414641804410300c083c5001c100003112500041c031089880b41d41d20b044500340721001303003031000300074090b4400d6200104045005501640030910210100d46164401c04108401a185405120000313032800d100d14014601c980c01a1220300c070440d650ba8202038480380c840c8216040410102c0001c82d0140203806000354800c1e244071055020b840c40c000c80d60529001400342c482c090a000c0405943d000d846052103920340c0201c000d030000502506200c500460040c0f070010040614080d540d00d0040d034910721700c000000304c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 441735368 1250 441734118 441734131
    0x40b0424050a0806041e0e0607080105010c080306060d110703120c090501031a130b090109020a0c020d141002040314160605070c0b0331020906040e1905010b18 70
    0x40c0d1918051802c1160f030034501a003001e4029486122000382c0c40703c5602504194035070079400243c0074414100480c58400c0c050003602c240305201c00140200c0c0d0380701c80b00a020f03680140010f5502c1e1103800110b0410b104004400d524145810074070900321500c0c000614890f8041c4da03c070703d070284c0f60381e4114040b40d00946035080450381c840002c22417075000c0e0708075411142512000059104995010400640b90080010b1000380d81e14040d0035203190100800f405015010303000c40c01d201c000c04d40130303050420a0401900ca580000021010080c0040401c81d0f610340309002d61b0800980e11110b00080e41040c081250400d051540410800740002503c2d0081c46201d4903481d815450100103651030b500104c41964143c03002400407452144c620002c50040441c0c01400002d154500711440d01030564071054034807404010b03d190050798a64401c590004800c4500080d500e000c40c00c0d2604e0240913001095001094400280c24014190701c08082501e00742c0d1400c10149266130040041c54040781d56 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 441736618 1250 441735368 441735377
    0x20d03110d050a14090c011409030a1b0816030c09090c0e090a05031b060105010527040b1009030309050a0605182110110c0c010c020103060b040b0424 66
    0x1106070940950b040540c114094a02c00101c00d100d102c03044034800d2084031074032000e600041c0b07401c5003942e000010310780404000d40c0d081d00307100018000136201e00c00c10401078443c4080205c402d58001e02000c420009142c90401c0321107500395503802c2d407650b4000b48800d462400401c84002034003405402005215680560240c40300360500d01c6030740343c00e80d01030a400d42511078542520000b80c1c0810051a200440d03230705101071402c0c5461041c2c42c15505130082810003005007c2c00c103080580d010070012381d452400039503800c0c1c031400011900030540c110000f64000500360b02c11602c0ca80050302101a80d00a03074401641584480a0154030030091003404d0002c1d1041000010b844500c0c180e240b9042801442001d0710700070449030041c4d803400c1c4003005280d034001c00c00360705480d1210302c980d409540d6207251040c00c002e000b000007a00c84a11700e4409050081003a225001c580c403e0f8013100c0500034170010b103a00d4035128040020f06401c40d01038030102c03411044080d01c150070712110103c41c420f0103558 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 441737868 1250 441736618 441736627
    0x60605040b1b030f0d0b0a050301181101181d0c0408070b0304080f0a0203030f0702010603030903110102011b020a050f0714060d11030f0403180506161401050405070501020d0311 78
    0x10080785421042c100c03000740400c2c80b02c100031507a80e8004040014120030041162480d010400c00c5800300c03907100740d1203a03141a0340c028552400c1c9a403003a80b180c1007082d224642291900603101409c0d4003249040c2c00004c0780c0040b03408a401c1c8882c0f00b0403140b040041c01a41d4820107143e0141c425070007564040c0c1d22101042001441a000450388188a11400fa0804107170340c40903032050704040c5007000942c0020080008142090407007680c0036110348003c0c84602c1c40c43d1009001d50410380400f0340b44050b40480030506074005d40049030740c108150b001000f2000e5140c4003e4a80ea0712040c02c0703030380d401052280544003400140c1d0400341d81454841e003412000c80820030245a0010a8401e600341d10b840a0a11b03251000d0061031290034642c0104000d858145801000d504a04242800f0140340300d5050016448243c1940c0454003100d000b034014182c907090411940c444c0300c1c5091090760a200411040007008510481114230a0f02203851040750007006906076441000036080c030420520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 441739118 1250 441737868 441737887
    0xc03210f0f0c0a0c0515061311040510020309121b010203070b06060c1507050414090f01031e02030a1208010b0406050711180f0f060a03020312071b080105040501060605040b 76
    0x1401488400d49504000c4151040c4d680e5440c18800380094074460400704804103c4542080008246900c078041c20410120780485448501406103000c0d0f203004010114800030898000c00c01c590720300d88010328008280d648100110b90714022101040204424004860001c0d4000000e0701c081652040c40c00d107141e51040288052a000070284951f90b2248440f2180c954214052080c024105507480f07a03600c600b001c16031111210b40a0086008110b41d408121918a00e2008581540c3e0310488454442c03020300f06120744070010b200003952500a00c0e410500f00081100200300114160f19003000d81d80c1d84036801d0392207000368031401c00401c50400c4000c0001d24003921400481c5801402d1041d0300404890011042c28220340e00741003420700a080c002000b01c41d031100740c0c0c0b00c0c50403505000e1550039503000c29240c0a41c21003810000e1000f0420307a04100d1170b800782c1020140f9032542c8c0c2640c0e940e00c403981406000192000d5a05528050f4040b130000e210304211000c2c1c44620001d07525240e24113 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 441740368 1250 441739118 441739141
    0x3071205190c0e0405060109270f03091707090b03030306030a15020d06060f110f07120c080a080d0501050a0302100c03110d030c1101150308030c0c03210f0f 69
    0x41c400700c07096070321001e01050f842c0a500ca12801a030150008150640c14248203004451851041140000c10901141c69603803411280c400d43c0c9512004280e040c20451405940c00780c80d030303000010020603440120051800000d5184119041c00781c0c10702200541314185916803009032103103a01900640c0c42c482c0881e02100405840846801006180082c1c0c0c41400701294810b801000015240d0000901080e51001040e95040d09070301c05407a25111601d490340c1e80340110700c64212101440f45440007032001c00b4411200504000d4142c8007960075501c2c10341030341e81c040403015484c02c0c500b800202d12818041c42520581b6400b62030045001d8100e1415146940d800740100c041125100303403403a0100c07091101814031101e50310702150340c052201e805009080da00610744110f13890310101c400c80c940075203d01030880b6002441c030382d0350307484400d0120014450724803452800c6c0310000307010001d254000080c0c011203081607a212100d03160342c1c8405500101c00e60350107261405100203e031031100d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 441741618 1250 441740368 441740413
    0x60f0111121602090703060602031b01020408030a081806100308160203010608060a20041214030403210e010e010e030a0f0503031506030709031209050d0506010503071205 75
    0x36108032000e1004003400e4001c00d5001c2c0350011058801c0c1401841141091200e1507003000403410144001c9042c008000c0d503d0041403861200b202400c20480c112210079030448010b1b110340e5055035600d030b0f8980c4020b080c90409881342110300d9910365070503041c41004540c0074000c5002d40700c181e01c00c5286850300a050b81041406200388442e213005040140c1d0244118001800f01a02920280c0342040c100d00440c0e00a5841d5841513030102803145104c541401105e0544100691035080c01265050900f200341b800c2d1031404051000140100910a5a003084003142e0030b03880980711003c00810086400c05805681240494043e0454500d15809028582600d20002e0200d031104000c0c1e07161242c0c03c1108074000d07912a0400801d00400903100c460804452006449051540c00d2004004207503101600c0068a80d0303425280194089100300624402884000c2043c250020103042c8907489082c20320a09209111700000001d298045840c00c0c0319823504480640344081207284d488010805 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 441742868 1250 441741618 441741647
    0x303010e06120607030b13020a08010b130e131101050f0904090219030f02030d0806011b030212030403021b09010f090207060e2506140712200c01021005060f01 70
    0x85202c8844003071841040124401e101a64000c42c0c3c224800050114419545480c9100b2a00403c0002c898941050794181107888a1103116510711010389050b078014400e4000c2c1c00b40c1d000a0092068003403480e5001c9090034012464009410003450045d078141c805c0c080883c0a200c020310034980145002e0b40000c0340c01d400504600700c80c64a100c0c603800c0100c046d4004031540610181018154141000b01e00140e000038100071156003031a600180c03003046144480101c11482c8a0007108251003441804018004505106c4d1030f41031501c1d006c2c2d142c05c0000c6082d07070350740fa60154800003440c0a500c1070307040340c0864840d9440302e401c166201010354409132040d51200e4651350040c0d843c0d802002043c085481c6500b805860083c000c6c21484460b0ba9030380488100030700a20504443c0034074904440b40b03c0d070b01c9104000b424110400503642da00646403403004010714140710b0780c1003900100304c0300c116803802d03400d03940000e00408244040b039106039955500001608040d10903940035011010041c0c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 441744118 1250 441742868 441742879
    0x15030d0e0d02010908010c0906030b030c010e1e0d0309030311060c0f1608040905251d01021c050a030c02030c07090902012a0b01080639030406140709080303010e06 72
    0x5441704201c3e425a401400c0c0c80d00000d000c2070040040390780c144a407050b80310b0100d02900005451304d000074045020007074440e1140500b00e0b6110500c9540c030380d1a10801201509610803800f003820094410b004e180303c00d60114840051600c2c94242c003060903032007030300361741c1415080080720641000d480d00400700d030032010f244410302d0304040745041000d84003e01c50308034041090316008202ca40c0e0002091400300d9844000d01d04209101c1e000704089005162a04d016070082d162100101d28000c1c650b030b844003000c20b025000f00c0340607500030010031040c1070689050040c5d2044440c00c99492050484030744140d00301e91024403c65017103410104400c1d00514180420003d90040b104810710346440c1e103010743e04212004070412502c0d111040c01451040e000e4800d5140003111482c003061112144056492140314241120503180f160025038985e41e41d2058692904d0b10b4440000e241e90104c038080c1c94403807000900300c54410405801a00c0b03a00d00614107591130031584980114002d421141c1c0031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 441745368 1250 441744118 441744137
    0x3041211031314100c11091b030a0e0c0a050105030c0f0c060717310c09140a060e010b04150e040924061a0912010501060815030d0e0d0201 61
    0x1241c2002c20040980034809054442c2c10800003004050090940c1413003e0050021840b0041401d201c003a1901c407009941c0c0c0704495072160034400c00c00940c9100c0e8244c3c007101100b48484441c0c02e500c0b03248100c08070011291075001620030080e00d42c82c94802e9500040d41000050a00008280a0011450802daa050400d461072032f44c40d003010300440303848000030b00803440d4070b0880e419810204d401814007001c015480907900d0120901c1e00c424401030f1240015507151a04005402a0240c01403003400800c1000560320b503404150701c08140e4008124504040c004103482c5200c3c0b2800c2d040310f002c1c07591f1a29180c503110503081c02d402681360020910900078500c0b0143d440300d0041c00080c030301c81c0004081d042e00300e088a15003204400d80f04074915152200c01c3c020681c041000744500e0fa40800e42a4890b0744140c0003407403401c0c0c115210b04043d401c0030000179020b600111042e000b1506100c021102040031401d042d43c07604925007a100140304441c07140c040f4200003401100550043c546a03152 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 441746618 1250 441745368 441745387
    0x501150e030133140109090914030a030b1314040b040f1505070809060103020a0b1806070c031703090604061806150501020705150307030c12060608060f03030304121103 74
    0x301d420042c010601e9081000c6008200403011007683c028001d5000b80ba641e0110820008140503010300500504540e02d90303205c0c0a10010aa1510380301d0312000449503241c1c9400e000a01408200711841c1c016a00920202d62000040c00390340840342e42d8150348002e40d540c1d902d079248100c0c03018201362007464582500724042411464001140390150078003003080d0070614001042100018414005a0045001480180d80b4802614210f907401100b080c0c4503c1801c00c10700c0b05280139a0b131164440e200241900401c001080c0c050b003100e000d28a07200280150081c901c145100803100c01c95190002030009000403400d07440707240030030700c1907944020644495035804201c1d8540f403050200900b000340100038035030741049144c01a0170252010780d441c1c250043c51041900000c2e140509244e00d0705054401d06204151041d140b660002c818485195205005000b0803801d44d000ca00070074101003005510305000040b40c2c0240d610045070207007207003070f1001154150200e00c8500c0c517601081144102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 441747868 1250 441746618 441746651
    0x9050d03081801090f0b0f0f162d11030f030a0f020909100e010503030702150a14120403031401120210030b060d051603111b0705220f0501150e0301 65
    0xa1052182140824401d0345d03040c00d00854030004c0c00340010320f64850422052542503401203401150201861007091100d030780540c1c10484c0c3d030840030081e6407003040c070300c440303d40c01b480c20700008680c0e849400041c00c1c8030f12015160303c00e04844804a440070808507000c01e9540d1703c140d54444200c0001410072100000007440440c0030764140d400d41c2c00400381400341009107140303580184000c800452030805c80e50f020601d10f48a84e05080040a00810800700041c010f41d854160700c0108041e007659090300440500300341505540981c00a0710b01407200003000d0084a450f81070340d100049464541c03103030b0f80c00c005050040c2e446840c200b41d02e072800400d86446540240603500c180440114252422040e03030460b07401d071800900c0c01c042c1040844002101d0480c2211130b40403200007103403c60800e01219500c0d040c0941d021941000990003140310388180d0040710010501025010300126030b6090505040d5030082c000c5081c2d015160000001e40da020705a1800c007404090004191481602d483c640c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 441749118 1250 441747868 441747881
    0x9060b0712050412061a040c0e0904020f090403050a020c150f03130602030c0403020f0303190f090308030f0601020d090e06010309030915080118150b0d02070606060908070609050d03081801 83
    0x45041b80c50b00a07012841202500080602000341e404004010036000010181c0440700d19590041c1c1144002c00c0035500c8045280500840241460510b03090030f00c0c0c01081030703108041d0b0300014041c41803002c4440c50622540101502241d040506180703025002907029400645040d8120407c45000c40000b10036001031882040f41071003041e00d44d072850050086501d06002c48a10a82082040c2900301ca20358210b0a40c5002900c0c120f4482031110b00c06442c1d1001d285c01c003034010480030041104102424099078032480c42030b07003900c524500e01701c801d032412000d5010340c14400c0b02200c00100305502c01d501034030020b4024500f04100541d91600003603400383c1d0503440c50001d0021f00042c00411001c00019007000c6001c20700f00404400c031031aa04c00c50190307020780501ca180000703010480d41030b5601640d142c0c64010408001c5d0030765178440070f00701c1c0c9000d00c10301c1c2e05070090b01d02c005010340c0104840002c4410160200c0f005c0a92503804031554003004000c2542141e002c2d403002c000b03900920802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 441750368 1250 441749118 441749123
    0x41a0907032004030c0306200310090c0503190c050906070b01060e0108090c040c110312181b090406110309010209040b061812032203020a09060b0712050412 69
    0x2c440d480d40219981402d40502609200345081008000013000b1004080880b43c0240d000545858122969124041d4901c010300c13114401209001a0407851007418049030401c42080014280366070058a19000c11a0620489541c003480c00b110f04d416904071002301c0501e840c01070710341010708000071004c1c0c2103204162000e5801c10014022607030020680e9030101c0090900284910300440704ca666000308078180c0f40681e40781c2d00304a0460380504401100d508010701640c6c0c0398055400320305101141141c0004991640c4030340001c5c2a0030124559000d5031104103405800b401034010311014010281080b9030403981c444e0319000041c074040241d80070340403400025940d19a42010001601c444c1e414240c450a01040b1034114613080c003c003400d031110107941038a900f03510303242194114000d2010802c8041d061040320302c01d50035900d201e50306892084844031400c0c2d0b142d01407402114007600034031b201d224040000101042001e688a4260743d0a45001441d180e11003c0a070b101c8203214004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 441751618 1250 441750368 441750371
    0xe09150f0a0f090f0605060a0f18031506060503070509150702030a0b07120b01050919030c08070602010e0a1e0c09060e04030f0e09011703040f060c0c1202030a02041a090703 76
    0x1d2042d90f811340140c40460500070710a0103080e040000080140c0301d41e84000c0d090003014564220728500030429140c0ca10b840b40210034485a99003030040300351488003115080180b5111011a115019506490041500d90b4409041041610910505038800a01e41c1160710302842218016a42000f000c00d941d0302c138040c800c80d1030420603006040100d03014440ca050394100100070286136803000680e07611200485145000400045e00246048920341024205411600020824240002e010b40880719554000c111140030045840c2e1140c0241600810081100810300e168000804050100724011000d404403213a0781c0c2403810444409030f020b0041c1c407501100300024180c00450300c030340416081c1000101d4200c103c0004081c03003014000c0070a402314414030300030b0b408c3d020000c0ea0045d02382545540703502510b1300000b1304903c001d00030441d547c0c49291000f00d9091010340000551070350213070080030201420350803c4050480d43d0304450401412148041e01c07907461840c0e031406024176840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 441752868 1250 441751618 441751649
    0x702040b03121201080a0b07050a030e0d030b03070b0309100507020f012f0c0607080a090b0f04061503050a080a03181a01140a1a040302090a0506040501060e09150f0a 73
    0x1d041c0f164005a00050041d08089401c101048522050300d40c403141c18540076558040b458400c0d8003c01c4c990400d005184540320b240c01e2103907003650180b000c1120440c1200c0546560300c3c100c0f0500c0c40200d45802041e040b040d850076100354140c010503002070490065820700480c4d0010b031800c43c2c001a0600e03400390f804802c0f00c0f0310044d0304c164400a080c40c000c901132900e2460a8920b6481d013002e0511401c00480c100010045015503010902c0d82d40e009240700000c2c1040030021284410a039002e90f003103807130b03c100550a01020a11001103035844405803d41318000c3d190100150404e40c4e20400740750b12802000c410619804c003041c5003600c65a65070302c2100c10f1134650b11240c0d80581002c90090350b42c1c0c20000c0c06658401ca0202180c50764884c04a01d1030b003007544a07280d8004c0340d0000350440810f0052007900e521540086201e41c0096070104026070365030b00c04860f0300005035074036608488641c02240800c462203072000e07402d8001400010500007403401254480d02d09520036183d4000017107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 441754118 1250 441752868 441752887
    0x92301050a050106050a0503061516060e0717120a030605210606010e22140702060114010305070f0c050f03160203010e071401080a0e0303070f020c0a0303090b0702040b0312 76
    0x481d42e409011180361060420348a104c01402d184005050707548a070240240352076100890000304c0f07001088690301001b181c0701625192000d0591491000d00601a00d50301141c42e40b40c50301e00b2243c2030b45800003004a1019512800d84590000810300100758888901180503160001d0045041403240c2c20300707480d00408031085084c0600030b0101c90411031a10b4007481c207035903038051007045410280300301e69810b0004140c0d01c000748500b8045c18000e80e982c0c0100000c02c0d40115201d812240203210100c6070703490311401141150000c55005011a910381022440c2c64407640e130211100e44140101e5103502e45000c0d00601d150414070200b0740c025080030903e01141020f0150300c84070550307140100109400e0500d0441300561712421107041140120006d8014000b41d0031000e564909542902e0703803400e01d188001d0030840410404c20151090b00940c0e109030074610038103011642c040d50750049003810180c02d014590700810003070740c0c042e0321100d0400440c3c0d401e01c0070040840300085095039544190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 441755368 1250 441754118 441754121
    0x513090c080610140f0d0e0a06060e0703050106170612060103150f0b1311070606080a060e06060f01051b0105010b07020f0a0e2d100e0a1e092301050a 66
    0x2d980d0802007000034545400b0740560501600c80001c40c81180c5c986502189410100030101845000e08500c144910007007070180962201d82540d014064905240e0f0b18010150240e401c2840340720005001ca403440610038650800d030390703003024008103a0301008011403241c501c1c0820a80040e00c0011200540d0041f0a141b0f202c0d48101c042c5140c8180b0a4403601c0700054030310080019010042754a607002409100005030841b0101a0710a13402c11040c0d07226603c00b941c0e408100c10869840d450030341811400d0f40001000380c82240700510103544510310100454054000341c0703440000c0314589130107460b810001e0040502a00d814014940c40d28024010010040e000751400c41c014100801d05011003030720a40c070071398404041c02e0030300f01d480c05d500c03a499800d010b810303401d10b0722021940c1440b014081c0b40c81d8040442c0c0c030104441c034440d240c2c5800e0a00b204d141c11101c0c03143e603001880b880c001801540054124134001c54901c90b0440410f4122080d6071810080000a650f6540405c5a07001c0207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 441756618 1250 441755368 441755389
    0x3030b01030e07180f0e030c0307020f0616031202130b0705010b040608060c0f090a0905150f03070314010216080c1b0105040b03180d110c09070c030513090c0806 71
    0x80b50007000518503043e080090750f40444220440039444626820142c80ca641295159180307060803030350348a550a609544a80290ba401c0784071701c0208032030007003170721f444000d03103ea960300344051442aa64564041d5180c0e140315400c01c08203902800034020780c0b107440581c000140b424402603656904207140c02801c42c0c419118a44c0f01d04e2800328107001104001070216807001078100b070a03599800c120314a034040e0165940269108040c031502045401b56a00018012042c14403001c148001c1941007140001a03c0000d6415a00030031f000c00200d0700b10414030b054034505400040c6800318442c801403030861415410303100b404e0b0015003040e18100401104016840c141024001c020500d40001c040344074620540114480200109402e11183e903850168800034000f255100b1305450806000c0d00941201c0850034000c1c403c001c0614180f0450071131107514950344105c8460500d690503240354115603106640e418150740c02260000880c46004000c03032076500c034450325250480400c2034041d035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 441757868 1250 441756618 441756641
    0x10902130c090e0426090433030302060a0c0c02100f020f06012102060c060406230c0714121606050a0c0906050d110714250522020703030b0103 63
    0x5003820407012801c51101c1c0c180072003048417402a00c01107460040c0c490301802400e1680300d440e04484480d80c0e0745506403602261115154141548400000c84031045100e11010340580c2003030000408100705680300c07460303107140344c00c0001c2d0b10340c41c54000c903840b24004807108002c940e8200300000308540411403510402e11450092081e0360400817aa0484211406060070252145501c40110b41c7e5110986041c10707102c4040360154641400c00d400601914a1f02d0404038410004081c00369840c004100c0c4206410002c8034039114081c1d40e0030140c140208201c5101c4d0288070500300884c011213005100d00ca20106003681502901d0510b801241d1025000c0880c0514010f4484540d80d0885e4201040f01d02e941040740d150000b4a6120300540001d0681d50482607000a0700710410910741080a48403d40701c00b00c13180c02d410146194820304048680ca0060707220781e0010440b6250400c1c0e4000000d44480c80c0010040c6105890401c1c0c0c0c110384804c8021a407100138849a41d64148280100000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 441759118 1250 441757868 441757889
    0x30d05032206141311060a09082a010e0306010b090d05060703050f07090323190302030c070905101a0f0a05071202120423031204090612170309010902130c09 69
    0x484ca64a43d501501900c1901d4003411011420309540c900406003240100100c1007642c0c4115103822803d412081009050191311241c0300d0403800c2d43d4803903c160624040007078010083e41c1d003407420100a540041c48401e50040b6000c0b00c04000403003e00109016400d141c0b00840c40e4103000341d400444510042146040113048041080800c0c407502c4001903400a140b012418620660380c40c0d130400c01070b541840428880c0c22920401c1680c0000100042c001150659081303580f10f11900e01940c1080c0c450200701e4040000c1485200142c0300b0f043c00c0b840c00910050f142580c015140350190308100c2d03005003c02d070045010005d2000186000c0c6000007684080c00c0241c003141d080220714016030049007250700c240701040c140d105a1035040060014003d0840f2918248544441c804e50310a00500b040241403907000100d40c0075605000c40010392010f1071003c0f050740b42a008034035800003440481c0d50740d00d5070400340150b00c44401c15241e07255503250200e01e5030130441c80a080b6454540c040702c2787c41e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 441760368 1250 441759118 441759151
    0xb0112080405040207060e070b0706050c0c1f0207050d030b1201061a0c0106050307030605041208071706061303080a110c1e03031308031314030d0503220614 69
    0x1810030085809481d422540162a21140c2c10600001c16400e0178060044c4542e24000c60900000300281500c10b10614050180b1b6503070141b06011400b0b2403070000302326032051001e00b0560450f03e00300079400d075001e00c0050520003151202c903d050510144c410100307079914000c14190410303001c210706040c2100300a200700e6141ca120f0040000b0016140d600d03c03400840c81540d03550742034100c5d40050400400304c070342582d00ea04010000f0002a0b90454030340ea00400c50a251034050a401c52290400c3e86032514454403424120f10380200007002c0310743c84002040030710008007002c032039130000c0d60082c81c4640d102e40d5990750140600d00c0c000c4a8941652020302c290b641556000d03112040b050390003000045103100312000c41d1650046800d01d01c01340e402c0d44400300c0d11413000000b40549242071a1500c00c010350300e0040c4000c659600b03207000c0c0c058105d141c009111600031002550032030400402c165505884500094502a8107042202c40d562200115002d841503003c1072038010700c40403040e8411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 441761618 1250 441760368 441760373
    0xb0409050a0305160605040b070806010c0b04030f09170114062d04111603080c0702100e060c01020c16061713021912140d021e2401030b0112 62
    0x2100d40916004041083c0066001200c00c002e900349289036900040520245c241840c010544800480e50307240080d801600040040d8410341100001c2034102d2080c103540c2d11151422102d41c4404121002400754107280028840408041c2c101060000000005c50400b424640c462412000d0405840791040c4c44404d403a441c1c007404040300c2c5011042a000001c680080030030054024815402606180407440545140441e000304503213038443e80d40c01c1802c0c1d850004e494801d004603400a5000054024200010360203100d01c0c3c55517500003042c01781030919506166013a81d02040d80e144041e00131561800801001c214080060311070b600305030440420010483c9010f0310010044500000741506401c15512a040c10750030000740310244501030340d240e9440307a10440e10006c08440c540c541204680c00321101040000c000b0755554007074030102e80510040c4046212080481c041d40c044c031050b0b401e001c00d104070807503802050086480050b6241d0b007005401441d050b84038209484501c5100c100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 441762868 1250 441761618 441761623
    0x1b0303042010031512080309190809090405010605120312010f1419050a150f020d09061d04020406030b0a06020a051504030c0b090c0f18011214010606080105040b040905 74
    0x108190702d0b1034005095140129100f881c004980c0c40402c00e895401184c100b480b1090740114803071071550046038143c4e621800b40c410701801c0e20300007070b10542060120004603e01806103e8002c0e00990002c03690b25103800000c2c01c84255114450525800000e00401600e0160b80890050500034165000035213032000441d0580c8d07411114a05c01c07030600031119503c10646500703901419014144841c11500e4100c0240000c1003989100302140060340107003d010703c001420640000301d542c8464005140c480300780c9040d40c0d441520094203000310658005a102c0d440504010f05103580e01080e09000102441101c20840d04800110f406c00c00c140390119100050505003440303110383c02800c607911410221107600c21454010301c080d00180c280701c0d616000080c4140c000c102210280300400c4100c0c02c10202d01e40b088510f0300104a040c0040280c081030242d02554207020781c0c48003010030080ba803600c0c00c5824540248010517082c02c01072229042c070f4422840890703801c0d20200310041240e1246603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 441764118 1250 441762868 441762889
    0x60201050c0904020c10090c1403012a05040b1215060a020604081e0a02070f050a050d08070201021f06031527020f100206010e0a02071e081b03030420 66
    0x10700550300040c00542a017401c000c0114038141110082001c500940f802d0500034883c0d110340c08401c0700e201c07007107405031030107110380c1c0c00050320522011405031105030405186610b42c1981428000c050000154a003070000040c640707003400c00408000d07031a106445202800203d0722075801480140304146d5415000205560041d400c10ba000d43c40d0345890b12000080218680b010981c04e2004c00c0e521582500004c0302001d64003050b040c10700c01600d90003400602030151080a511000c0d00380c2c0748002c21a0303540148a850700610689200311209008403c0402d20000505c1030907544800400074440e5405d4115a200704d242018001d4403003805204100c0341a03401c408400d03803441c5170000210765030040060f404040240c002c2e045041c0b11040a07441c0d44091282c2840322500c00b0005423503504d2071003141c2000c0c0c1d1041c040f088034001c4200941110131031202c100d6080c00e08100c0038400c40d034010b404191034880000215660319040c130f0081243c42c0c040802502210b003080c100d40c1c540e501c0c01c0c401d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 441765368 1250 441764118 441764137
    0x30108030f0c1606200319050c0a140601090e0d050703030e0703150f06080a02030d080c0d0f09350703090b0d02090a0b0306090408160c060f09060201050c 68
    0x1e80b540300070110b080c00c00701c8081d1002c548036456180016030304e4116070011a035108050031450650304458960f9124401c441010001c0743c02c04028000c0e59000e400a410000041c0080300d0403503100c2c2d42c440d502d1040c0d212005d0380d03a51100300104074008081c0200040003041170041d00c1400710084010b0818020040300505141d11560390244240c000c000c1600215081400903074011541d05c070384002001c2d59803c880c40139041c038902040c142400691407051950160043c03259640c4504210b030884000351420000060400840c40022070701e020f15001030801d020009180310541c034150a0800700b690001580781002e0711880091408140d00000760040c080d049940c0380140e180071030744010030350443d406104010070001d10494030741d4007030044813000740e4060100c59200c00000c0c0f02c6001c00c5070150341c130901000021b0000b90040d400f422040c034131140135114408a0fa0b64a03079044815412010001d5000545205880c0c0d102c0140700003000680001c00c0b480c06c05040030303e5988504201c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 441766618 1250 441765368 441765397
    0x240a05040204022101060f0903020d2409050319030b032802060d051005010929040b0a02010506281e03021807020706030515040c12021b1203010803 65
    0x1015034889404a41d011181c413410081c4500c3c002110304040402030050b0720000da8000c1000c1b00710341c0544040d4080d650010b1030030241d110107a4950020b0500c206c0c005c1e05280e1800050036540301540111000184503c2c05540c651805810481d418000c0080202c02c040c2010140c2c40300d610040740304800c0c1005a40140141d91140f117980b01801c0c04240003d400100004d111120207081e40d10082c01000c0d0110400c060594510045400100c41e0141d403480c0ca10216010b0f00741444606c0c51050f0b5074079140050305066039500040d0f00c54108040140160b5141c9007040760a20300f1007641d00c14050481c19100c0411a81d00c0040441d10150041c83c00801e20441010401c403c5002c140004550090118996402119900040c1941521403030f000d445084008280f8138040d000741032203034410031a850501084441004044c01c030714060202805050020b400340440240001c10300c1e0b151080c01c010041144201c224a028900514005410350910040c0101140070080300d40c0900e51303185 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 441767868 1250 441766618 441766621
    0x40801050a05160f0513030614070305060616030e13020306120706020a03120b0303030403050d11070b0415150801150e061c15020d0e060a11090111070503010603060b03240a05 77
    0x109450078801c468030720b071014401c1d050000030441c50f0b811480502c2127400700310843d500e40c4e0006606542c41694103030351020f4180071040401c0e0149055100c132074004d1a000d145a581a8042603592403285803040c0c2081e000820031001c0d04080542040301e54240d00145100d03440e0402c000d450b0316489000604001c4460f41148803240150072100c2040e40080c19640e49080c14980503200354002d1a40c2c070740c16800c10310744c10840d80002c41034941c10f5400c80c00d01000e0b59034560f1100002c000040980d80300036942e0504130703c0800f020b202d01000d04407036000081c0034080322860300107907151036100030b00c00d1410404001c40364940c0000e250703c4180c0082031048038807080c60202158a00003880361500b610200b00050001300307035000a4010380f02c0700300780c800c60303140c10040900b038136059100000d07555400c2203c000703a54443c510783c03103411030307210141e07030b12203440741d00081c00c2d20f4a40d40300303845403038440c024011940740c2441540444101151034048100c1c3d444030050080800514a0342e10b02d654030f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 441769118 1250 441767868 441767897
    0x14090601062a12030c0f03021201050111102c032805040806090a02010e0319021c140303071416060b060705250f050609040c1103040b040801050a0516 66
    0x120b4241e003a0b000d038802c80d864000f4103004006003140441ca02c0012491000c20586d00c0c020310031104070411350003440404e0780c00c0100640d5407044040800083d841900c51303943e880c502c1403103848000d0303840d0452001e441c802129203148070502c40391580000e410402044c42e5490104030342c0c1c031400428060580c1e2081c411001aa460702484c0e0156036940640340811412a0010660711103030b5101340c0b1550070a6041703030140f55450031612814400e40101c000ca082c050301c4e240a4110a2032400f820320b28681e03c0507507407070094040401e0009220750012040c4212550131903030303560180b20100d6100b800c00440030030042c0c502d008110b010348155500c00d03040300075032074180407504219044421100d1030042860080c13041350001d0344040300c0c00e554800210314850140345190455800904450901070389404000c010b03c050307043c0d44184000c9802c080ca0740101803002e0710042c000c000c0826140e529005030f69080d5a001410440041c0c075103010002c03a0303d000c1c078903490951300b5842d14105466904 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 441770368 1250 441769118 441769187
    0x2006060405130c0602070501230313020418030903110d0201170a060f0e06011101060b180f12030c070f062001110c030901030e01022a120d1409060106 66
    0x3010054855007483c40089603041c1c00107500f2048800c2039882803200401400072448035000c0160410100700b041011400841ca149980b0118038001000062a8110000d88032000b9030440305c22000b2914604c03080040c01030004280c0d071024030946d020000c04a10b503000078503c040e580c2c01052008104008105201c80e41c2d44008043d00c5e084860b03a0115884a2188400c40c00480300c04d070026040100002080b481802980100d5840910700350500700c1038482c044404c007044503820b8102e1a00b004180241c0e41d65281031441d81d4250010350340c1c038141d00307022506000554004e1480c40400d580200702803130748501c5010310b070000c061281c0d5900d103902110902400d14640268000303d008100030812903004030040110300800d880030490741c149010200c0c280c2c003805442d091300b40720601880440d600703000d014103c2c605542040e2003a0301c0c20608002074a412828504100c1d41c0d83c1c800c1003420300e02c0c0b800c0194100c2c5917400101215850000c00038085c52100340d02070903030a03801e400102c0c2d0300c950 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 441771618 1250 441770368 441770401
    0x19171b07030c1e0203160605030a11121e09030a05070803040312060609050a0918111201020706020405122109031603052404030c0201030902150c0606012006060405 72
    0x11032520300c07103e510040584040340682c681a407190080d420f80c00c003208100702e41c1504076010380e15034a056583c0ca0300c840c001441040440280e000b0100400b8483c0310010301c0c25841080004c403003d52010303184c80103d24520f00280f94070146da00401c80ca9000b180c0000903500b0f03490340254400e69a41c2c40b8a0201c80044280f01909581414001d000c00d40b01e0704080701406560b4241c030108891035444030030750243c2d180000c0c0307284000c0488400002283c102c103804813071040040c0868030810740b1a40517a08aa0062001303640740b59000c5814040382c901000b0300c0760202c244000070000100d8030201d07500800a4041120039040000982045645051214000c045610000000d40ca40c1d00d003030568407540804005400481c00e00342c16040031030102c1c005070266401d9038407101d41c401c1aa0056000f82040350041e607101040c056003048034000c00c00100041c003e04809491181410350000d401041e48800c0310480c03111013084061000c4000803a29401902140d005c100fa031140800807810010707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 441772868 1250 441771618 441771623
    0xc0f07060224060d1719030b06040302010903080d111602030d031b0305041419050105070f020d03020a02071a09041521060207050313060207120b041209050619171b07030c 75
    0x40480d010880c9200315407481b8000c41143c6050000c40007000c10000346114a0000074040340d43d0010030310100d04040c02618110655500000b00415010306080d0b00d500181c00c800710140b012071090046003400d102d03055407200e843c20207000c0c00e031015801ca039402441d80d07c1c1d202055600c400050511000d4078031040e001c43c030001541e205000c200040d180e0558407001c00d032015030909002c500028814886202e1810381d56010300b003501d0822008501a500440e0003c0c214071070641c0c0481c6281c003212005e900d002d41e41a50503030310070b400070a00040d128001c1102c610311009807420401e0500607184130b110300c0f0b070242e42d020460501c1e1400700028000c40d08003030301c0c2e448040381c051907030126600104180c07001da4080b034010650300c0c542c0c200c1580c1060001880c144801001c034001031360700e040c0140071343c10300c0c10715500850b26900170420540044614080c0403425a100c40c40c0c09820a880c0c0d9040000924581e00901c1c100c034404000c0301441540886165000805c81c00b41403141e04080700310fa5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 441774118 1250 441772868 441772913
    0x613031b05030a210329010e0a08120307020703020306070f030c090506090d0203010f060605030126100c03091407060906020712080906040b0d0b1008070905040506060c0f07060224060d 81
    0x10031b500d20746141e900c42191001e022510100d0500050319089000d00f048500701802040d00f40091099902c060700098a01004e5110750b141c00320040c1e409100302c501c6a0b440d0383d961840260f112000034107854049150740309000208a040c001507c5400c1110703132001c800e43c0c91a44001040c40404c0c0107042801d51094801c2c549540818081e0380400118103c48801504100e01070130200c01c1d250300071040d80c2110150780a9440504080030f55080f12107111524180000c01d002b680c1c85180e00d5000f12515526660490070081c80055040310303e13400548858401002450b040c001411a10f1517004400b501c90040840c210300140e440301d0840c1c0180c00030500440d01c0e4002d2080344030180c02895013542c4140d01072421851554070650403644550b480c1d47e55800700c41d00d46414040188409000c0c0b942002e010001c00c0724031a0704100300c1c075251541000410400b41740001c02030034040044440c180d1010308440d440040c0030b0120030203030070140858594001d50101d00d854182c050b070140001c0d045a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 441775368 1250 441774118 441774161
    0xa030e06120f010503010b060c060103240c0e01091a0f0705030f1b0c040908031503071505130807030804030b06040216050607080c0c0d0305060613031b05030a2103 72
    0x400c0703440e11aa040328021740003440440c00c10010002540030b03400000311980d0102004101003602001202e004405011b02c04a102e10b5104510313090300c0285150f80040350000041488a50703101c446c401c002c050030303280e8000b01c8031307003512042403440f46a0030b10011010224529060080600889102072411304005c2e03501d10348680c3e903030b0b00800320700340030703001405040f009072070b1403c09004051455510034040f13842c42d503440506a03165580104026014440c8402c085203004800880c44641d01d442c1c0c03581901c401d100071507003070074452940010000ba00000001c0001612030815182602d901409986582c0e030f803200410020b0060700c2e0043c01c6010b15011150070301c00007203038a45c002d40c0640d642c90314945d03540f03003c00442c0c0f0960f0b5130401d0b1035205604903550f4034440c1d4040c5422960040ca00d51400405c24441600b001c919002901c03a901522039008208007201d020b4001001c090340500310030340030764032001003a2401e040360503070390b49900a20100c224440d60150000c11688248100030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 441776618 1250 441775368 441775381
    0x140a05031c02100204060504180b0418020306010b18060703030e0d110c040905190303020904090b090613020102060a090816150c031b030902060d050a0218120a030e0612 74
    0x1c05440074003460250182602da800344060038000c46082d01c03810303115107240070300d010042413410003000d100300c3c10507507a8400088071340c1c0d0ba802402555200300084101c900030740e00405d8100038040e4030401c62890200520400520003400c113544a4208641141d101c50300f60400b0b50140c0042c3d16480e596014141010078015000110b4a02d04d40c2200d0481d244038010805110481e004480d0140c2154043c01d51000c45000100c000b030055403181c0f8015007004102000301e03040c0c40400d0800c843d003d09020400190311300411145500113010603c400c402035a5030000b03926440e01426200056442c0c00c4e1000038820f11100b20b4030030450415591551000b1410318030111058406905612410100c10b01415807007402400d1030050b50f50b421150304c0501da40c0540041c5100882280c100d182031004a00803041c41c41184e01c907558003480960340d20b9038512032010300400c00d0441480750580f1000034650b0000010300c80482c641c58181029901d00e5040080c049004d41d40c03003d034002514504106d81c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 441777868 1250 441776618 441776653
    0x61e120f020d0503211035031312050d080103150203100e04050604030e0d0b0f130c0303180f0b0922061202030c01020604260f0d050f010b0a020304140a0503 69
    0x118014021030107007429100c03035032141800b500240c26207c50720009510313070402c0303001354080d000c030722030001202d00d4080350300c17000d00309140264032a2a5402240b0b10384028040180a140041811450220115030541d90740b80341107011003484114860340400066902400e140d490b0380a4041c1b040890498501460f021740d0718803044400314006924003001590300e04204a0009000340d11080b8108299100d20740c8400062004009400545200e466140800c0394020030402450082d80c0c2e0b180d428030720f048000f03890101c0391f001da505540d0b148402c1001842520507107103829812140030000c0c2c0080d00d184e01e0050f0f15540541e011500c0c0c00f0000580703006090182d032780e15100b40c05444201c22030000581c0c5620084502402000010b90004501102d4000c0e941100b103980030071070f06041ca112740b180c13040c1c1c0102c10000300c01555141030050314451049510300511446600502d010b03034550000f5107034043ca2181c0e41c24040590361184450399003c2d45400a4000941225040d4a040c1d54410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 441779118 1250 441777868 441777871
    0x71712070302090d0b1f08010e0d030b0d080712090f320405180606090f010e04051906050f091c141903020a14030103030e0909010e01061e120f020d050321 68
    0x1e806c41c1d8111030004940e14180168181c81540f0409010014094203080d0041d285400e0b02982c00f0090198900c00200240c005e003598a000744004000c007140224041c1018115401c108503a01d40324100f007210010800602000006003040c3d42d851824000499011180305400c0340d07481402c0c5010051102a0740c14190000007004003207402c10f44400b4103000c0c40306419162010091284001405103851040304650818070680442c0c010240e0041d01000d070799010075044680c9522801442034500c00311030826007000820700a4402a58107501c42140000403410300c2c0c0901004c102500e80d0100d6420039183d4001c6815880101a03444c5100103009520a040400200e00440f181240b8003a5002c1500d050703940c99250105805c070220100034034580e008000e0200c1e5921200c05100940017030107104001c0c50480c0d40c3c0207907041d81034045101581d00707420a50842903032505060100342012801102581c064503600084c07000c03402c0c00c1d41140f00340311242c400444000203c0c0030407000740c00c085 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 441780368 1250 441779118 441779161
    0x1140c1803012406030b090408031b0a090f170616090b04030605070201111c05060607050a030e011e12020309030702060408030d0513020622090908071712070302090d0b 74
    0xf21038840d12040250b08403050010202d40290440e000980001c0d2418011504030822462050b5010140d0001001c10b5000e002c0510010740d0343c040c01c12010008c0d11600001e0000b80f150410b8002032503020030b64820f0014100231811250344c0b140441e050003400b0540c050461022182c0d5195101e0600001410081d40c1c150300541c81d02c609281c0c3e500c00c10701604d41c80c0c008400b840e64a45071040100010b420041c0540f5403041b410800d0030009803080043e00c00311442512106d0207070b690f02c0c00152160300c5014407901d01d05191340341100002d07484800b03140c1c80c054042c801610f9803100d1440038a1409070703440003508500c0014012039a00c4000019083d040d28804080c881941e03130311104010000001802504188103100588541010340204070310740c0120403407401c0d0310b07588200b44003e46000070780c15102140001000e1003440320820340b444010803c0034400d0705d4810b4440310040240e0004180c2c10806038042006150741d6948111340c00c066410031403110380e41c20001c41800100e101e01810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 441781618 1250 441780368 441780431
    0xa0b070306211e02010f08090102090603130501050a05070c020d050a0c0305060a06050a030c03081c0c0e04050603060402010c0f060624030b100f031d010908070309060201140c180301 80
    0x2401c280c004204000d58540e40c103039a040099011b540c0180c0c1d00040182510100395001d101007101c0c6d890f0180518801c182c00c550090310b41a542c1406421600081c0256180311b09040402401caa0013034501210b196040d03441007044002c5040642c20400f00c1840203054032220040041400000a00c2600802c211513080011341c0d900c0d401c020f900740603440018125420803108002040c0100080c00c4a46000d0341003001084001e0f8a1200f2154451818004961010342404050525104403544140250300034445400d058002a2004080c0e00c8003d04120142c1c184c0e404100e980e411041c01402da500007580000e100080c00c03020407055444800010b4501900c81c0c1861034480c410000302007540d25800d9206c034035110700f14050300c4005100e0841d00d8056100c08841c1c1e100b441203004040c09005c0994440d95140740083c080c1c002076210208580c10404108040d400300d40b44682c101c040c000e24140d85515042042e111160a0700e4500e81c19480d110307055a0828040e001c0400d8984898003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 441782868 1250 441781618 441781643
    0x207080d0b150c1209130e030c070b04050d1e0501051e0a02031905060301140109060302040501050303391504060609020c1c0201020403020603011706180a0b07030621 73
    0x80d11103c0c064003540d903071513502031280303201c45013140c0004040d4450068405004080b01c006580c05403440310089035913641c400291580c4015080c424000580310080740c1c42d1402c0e2800c400281051014500944100d41441ca041c0724440015800c0d844c0f50362103c020f100c20301d040c40301d14040300c003201100e21010201c2c2c000225080300d18800c603440b400d895101d0803226008203061900620005000641542d81e410140c0c0740001804e039024000d101a100c0419000d0540c0306001c280d800c10307401a8043d80c000d2180201d002d0709150047d064041e068140704665154002507801801c0940e802c0c0740c18010030020141155500c0b4400344550b001c1c180500c00181c0e072f60ba00b00100d02c5214407207021508103840359084003840e40651119981e4510000d41003a4598000230502d0f4000e910900c000700b004a80d0b2060400103002959210f100740f05a40c030902011859280c86414a04005003450910302c0041c891500940c0f007070000d011001040b8015200c0c0e413129006c80c1200c01400da400d03030507602 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 441784118 1250 441782868 441782899
    0x30114010822020a1a09030c060910080c0d020706020d0c020c0d03080415020f0a03060905040201050906070c080709020c1b2d0910031a040209060d060207080d0b 71
    0x1400d89001c2c141c1c140035003412900c41110704980e20450b1030100ea0280700144005000c2d000b40c03120381a03591541d0320305660742628104140c9840d28a001c0280100c0b000d01204542d81d9640c0b124041514044c00c0045072a911080900e100d807203104152442d0724404500c40c07081c0f142a03405040e040c2d40c420420043c0c1d001c10b0b0400d9954100c07540d8001e501a43c1c0340c4e500000030384240311883c1c01c6407050742051503c0801c00c2403c000e9070010442c5d006404c801142c0680c2480c0d144c012040200000c41c8100400d08064000030254810a00c496004030350001d102001c000f40640404000e2207000252454151149a020702951200c0040c403230920407241c03540e44e0b824215074001d19040004140c258102107017404158401d940550071090f50400c0b00401c00580c9605900e5403045880c40c181a80140c210b2070b0480a804c0d00010080c5510014000c000068031565602c0741c12900440d00d048084210b0301d0008064411050001c052810100d032003889682160403510900f075049840340a0b044990 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 441785368 1250 441784118 441784127
    0x6090201030506011404060f020312010e041205030709140d12080a0f06180b0d060603030f0306060f082215050103050c120a110a0506120405010f02040b0708030604060f0b03011401 79
    0xc2c96140c0c1340d00d00401c810001f4034061342801010990a00641c0d04003001901c5510001c0d000764030190707851070765200f0002000008010b4a000410505102d4154100090700600c0d01ca4280104a40045224051072140d40c803444ac0041d100d03440105c2c102885804030004000f40c50542d12082500c1c14000d80c3d02c581030f840e01903041039860203660801203200003826100544841c040803034004803a6450b55010541c58007445000e90300a4403848000f0712000d030000c0c111082c6500c05c00030001524112514070b68410180354101c0c115115804801214605040b0503040030030000303101148003000352140c07038000c0d04114100c2c0c2c02a0280c40050503940d0a1182c40200b01c0c102c1c070f16a4103c002200005503200741c00c440e443c20042e100400c0c4645602c04500194030900c0d401c1410b10880c2c0410042100c00d00446100c000100004d40c1860302e041002071240c010480001c003402004000210344d6199503110800810864064448213661203400d0f00503a8005c0c02400c4a41c00c021040d038500e540103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 441786618 1250 441785368 441785387
    0x27040903022b12020702010c0c09060e0c030420060408100f0c020c090a090816030206270309130e120a030c09050603040b04031e02010f0b100206041403160609020103050601 76
    0x60b44503160a203210f035020000035400f0780c0c42241440071060b2460301040211000700f0140c01074080020700349003400c05069084070700400c07010201c1d204204010020ba841d144803c4105400140302d9001080800000c205005541051125216048100c0700e01005600702c150006900030b010051040707890022600c50301c02c0405a44c001060390046108803c842e840500300740d0044000301c3c109a800d1003010744a4520440030340c0143d00403c1400224804003070071810900c0da22501610003075030020b00a07268003404e101c5034401d40c00c0c4000300000300002d0304403140c40345011080d0746409407480701824254100301c0d403003c0040e140c0320040100500842d000d80688200070040350030759540399108413541400038022010040e407680385c5c003990400c101e01c80072603044503000800c2c000c0c2d20880b05c074200c80300c4141c00c5200b1803201280004107500410700e035402903000492100c1010100309807614620558040c66550084000760205002c02075009040042c03013660180181d4441000441e95061b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 441787868 1250 441786618 441786703
    0x6170714010f020f0303040308010519030b070f0504050d0506010317040b0301120303021608040503010e12090105031b040303080703050a090c090209040f060314212704090302 77
    0x900340600380d80d0740c041e024400381c6181c03034411102402040600c031400c0d0703002900c003140402d40d4800184024a403550b000c01220050342c0842c640b0920f9074403110380c001d00141c01c0900340400f420151115511510459000c0e00c0003820207800170040c1c2c6045a40d4050074801030f51451000700c800003042554070101ca003100c0200e0038a50550b401c0ca00c800e040e903c1101d100b2814141c1c200860701059148005881031a4010000f440d20b407494501410300f590340420f0485116081451a132640e112030348180d60789880c00b8078002d41c0700d507200040240d12070304007001880a03000202d800020036900c502c400c1d2003006c040d07a0610458460303800700c00075200048d01c0201500e200301ca0500c81d100745580a00800d4800130401302d9002802403062044440c01d8005556040d030384a09540319079030400c00e466089040000a10100b0b0036400e603c94680a400b61600500c20225040b00940501c2148440742e43c2000f0020896608240f801075036445444d414110407528101446050700401c0280100406 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 441789118 1250 441787868 441787889
    0x2030a260a020d0f0302040312090312021f020c0309060d0207111002060402090a11070302010b031506011b03030f11030a060b0301080d21290402070c0905090a060c0201061707 77
    0x44848006484d5140d00c0302c0d058041550900c0004007090b0100b051070342ca4038075902c40f01489411410410081e00c418540e402c00c0d540a40182c610aa09000d8071501095000c039005031a41c100a5000c0d00350700c00e04021640c00440400d002d821041746500401401d4030400c0300849041c0c41000344a402c2e0000e0b410f900c0941c124000080150521400266211800e01b00000c0c200800301200e1003181c100d41c1c025030060b959411a071105060801c5050f01c00c0b000e040f081c4805203041300000b003500c810b02881c0266005400a40d00c1090300940103c01038104000091104501548400c03840343c10840300c1c44420f0b410700c0c1c00000c03409211000c41c0e0684002c100a00144141484107036600701901d445010405046014215110640c1c800c104c0c0c2c95002103a0011011000c01d60101c044441c031513135030703c2103204004040c00203035941d50103411a01620000b00c1c065680c0300350a820300288400141c0300c9800c1c0207000c0a56641940004280c0321b1034682686001140f4040d42e0b61441e0078040c0c080c005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 441790368 1250 441789118 441789133
    0x40507180605060a0c0f06050709060822031b0204050a0515040506010503060d0507051203030906010b030c093607170603030d0e030d020409061502241302030a260a02 73
    0x1171180301d80360a0180520034800c14207040e969040101d80f01240c0d0400016000310092201c40ea111007082d402003000441d220300e4000345203500f48040c1030240c00509111015141c02020b044071148520b815130000c000300410300d88901150003400084464503002da60081e125003070343c50503200c1e1500074201a0348660840da503032414001410a998419074507403084c1c0c03000250a6540305246c180c00740000000c0e540b24101110f11520781501170704032910000003801000103058007007003680e20f00f030f0084500142c01018140024104a55611283e01801480b9006544110f00800642c000e2038950b0341c117209a15041034460598809449007541600200a520440d828a8004101c0003107901d00750cd00c0c0521310300b136007022a442580b02c02142d5803241410000d42e6005241525220100c1c00582918203142c4010051810291110903171120140042038001292a105510040e405002c40303c0784240340c00e203040900c40c036000d10030083c499080480c14008650064990307400036070b00200b400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 441791618 1250 441790368 441790387
    0x4120813080403060212060a080309100504080313050913020f040c211b080402090a050a020c010e060a0c111203040f060f0518030f040e060f0904050718060506 70
    0x1040405880c40410402030389035580400c540100600040d8496007005a8420103290301c03004c00c0c00010308452003a25003020420403540d0100c101da440c24001c552005101c10440415140340c01184c00000c5a48400700b54000c7d04040d00455038241c2d10111030104040e6a00010650307080f014100c001d42048503050211041c0c20075800042443e441070030503200e4000680215918100150144602240c640000c003070840714044a0030002001407502c0c00141c0303001d4001c1003028401910000001e5030310000180d0248003541030b642e51001c0d582c02404800d0424078042d5a68100f611080c000c00c0c64599613540c41c50184003400082e8a400b00648a548001c407070720303011600300900507103010f000c0580d5200016807511561100c108c140200045500381111040300030154100e4145036680100a20603000e20b4144c00e990468640105101c0380356240701c0031400050140c142c6c140c00501c1c1d02d041c801004404902d6805076851416083d0300c58140051000a880041c031809030008006c1100c90003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 441792868 1250 441791618 441791627
    0x1215041104050a030f0f080703120507020a080a0818030d0c0201060806060315040312090f031d0109350f060a06030f0611070c080309100207150503042105090411030412 74
    0x1180381c06140c1d000290400c071f0701c0d0000f06034001203046001a420403808002e08030244140c607005589072000342010440c0342d0780c000152283d6151481071100440004424201c400400f41204100509880d03c0c1d82015034140041d1100350f08290241d42022404140000700048161299500500078104a6203549111031030040c0074009030200300300d56a00102d115254006e0002043c895510f10361020b1580c100117042070047e07030b500c20070b01c690280141c002c0d80e4468400002d5030010705d50304140510b0030710f880f4030404084d01a102d0394504107001c4544a01d000c140f407071000e02d916051790690790b103914060044031280d01004003003103e49000140845c0c116480b20420f2407001000a140c4041502c0d0255800b5440d400701d44141d1002400c0e140313a09010a00c1500300300140000c1102c40c3c01e00d545070211000c5510030004008000c4002414401c0041010b00018900714815140001c0c04000508590100450034011400c145903038122214200480e417203590400035540350810580c00c00c45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 441794118 1250 441792868 441792893
    0x1d010e061612020408160803030f0a05181504030905030609210c0114040201030c0306080c060c1e060f010f2601060b0a0504140405060d03050a051215041104050a03 72
    0x8100802001c0140402c0200c0c030050000c0c001c04402090502017402120070083e01d00c0d04200b696820600910600c01108840310b9005090507201107920394901c0d0ba190006200b881e01c443c0c4901c20a42c03030488500341c0300c40090085010b913452401c40e82d20380701416501c45043d60390003d254450600925040712520030301d500958694800ca14009000307420340d0070b4400c150102a1a0098101400115a0144240d03001003445040030311905203820415601c40340740b01c80e107a004240010711568403882c24407213098190301014031503250240c200300140c1e403450304507500c1c9020380c0540700204413003101c080b4990440700384081e82c0b00342c001c40b0b000c03c143c20044040584469900c07070703e02107040c540040142c00c01c1526a5101c2e920303145000501508e040410400c00e000b645000c080c0001900ca40030001d403544d40509001d81d44500210302114544185025014000c00711818080310f10341d24800b0144c1e01508030b60078441f40c02010304284c10307445107104259100c0d04809040002450450241 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 441795368 1250 441794118 441794161
    0x6031203160309111002031809090709020304020a17070905070c0804060f1101020c03090307050406050901060c1110110d08151215010e01151103030c1605010c02011d010e06 76
    0xc002048a040c0410300c4400c17140e1401025800c046650509011001d40c10f50541404484209981c1040c440494036802c180c000d6035100e9030000700050554642c400780ca0001d0501820740551a88071280301c03034a501141c09010f51050800000c12402e503c5603555584044c0c001c20403918103480c01c030302a201052428015014020b40024505d003030f400a1021300740c2c003240f103c05150740b00414800c06003801c580c0d0300550b02c110f20b05442070105494a034001c41c150b81c9182414440c03c607081c14004460b5001c911542e81c4800c00000c054506588004485c40842e045c80071108084a0310105032038115044889011014040916620524080c004001041081000e0380e2521050450718850204e00740c2281c007610441c0001049014102800c1c600301460034a80300940940c4e103880d1a840b03200c040c1444005a901048001070381c3d4070800c40000465010000300403850b00000080e0107800b04841c01501403411014400c0705000600402000004032400341025070348400c2e24444c00310120115 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 441796618 1250 441795368 441795383
    0x601140a15030e120a030e031204080901020a0f110f09151003020c1b1513050d0303020904150528091a09040f0b0c0423010e0d03050306031203160309 66
    0x3d402d2502040c040c007841424016041c40d507a03080800b000c0d040d9404848003010b198070403c00300400150030f000568000b03030300000280c0d441180000403031800040c998045d2010459040400400c0044401c174030300e11605599030f8100786240d0081000002e01100c03d030043c40300c080d031200000d02c0c007851510302038501810010b040c911030034903043c644400c00b03121340408056404440c0071881d22140507030366524554800340c600340280c10412024006c03880360a00030380a45680c10300f0540203405aa41d40003026008210704e0851051802c1d80780803522400340184145144440189524141c1907865000ca4103104040361624402c5002000c108500c5070013030030700c400c50701a260785a4500a0140d0b02414144840c0403040c100410f8416024000140c2840704020410440b00c2030202240140c0886c1c03198416090b820b00140c0f98142000c034242d600050350070000c0105078100e000f950080c01d0030780c00c031103800d0b80f0071164000307520081c0c8680c120220010034280d446840307900005a950300c07402d03c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 441797868 1250 441796618 441796631
    0xa0618061d0a110d0917090a0e060a0302090903090a094503050304120c0b1302180108100b03031e0c03070c1502010b220e0c060706020403050601140a1503 68
    0x281d010280d00b02d00340b0801040d40320306200c5c0034003a4640754001c8840c52000c80a24090902002405e494150303c45d40b041074804c80009410360b6100200880107540107003405803a440c1c10084961250f1201c3c6079288140c840341d0020940d805e4910540c2160504010a0f10040c20610041c4d01d0038040e14806000c0e1829102280700d021043c51003c16606109442d415200c0c1094a00f042c0100c15038606102000000b03c1e1800201d081000029040303a1400c030b26860814090011030718220521019a0058001c0c500014444a0000300089810320200b020881851103008050700c1e0310403008400b0005030300a0144402c20003400084c00e076854104c0c11a807420045070749084420f4419404130b6602c1003020b6050400c142c080c010350302c501e4003c41d03480c111107000416a140501844040700e10321a40e4401025600c1c80030460341c0d88182c00184500d445a54910b0305501950180c003084500c0d000322000003480b002a00c0200d00c2e00800200700e410428240a446d01c002d0b18403d00410400d51240e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 441799118 1250 441797868 441797891
    0x112020f16030e03060711030906030415090c051203071713210308130c0b030604020d18020307150e010e150310150509130911090a0618061d0a 63
    0x1000710000307031103922441d1050b5284010142407000003485030040c0210b4a0b4000e41c0c0030400b0040300d0440608682c0152a52501d08042c1034805041c003205440c107103010341010510030b81c0c00c04003007100d10845807141040100182e4940700d004c0d19200a005441c49412110700e0490880644084800c0d41c2a42c0001c55460380d00d514030345840348686a1281d9000088014542c0c0540c0e107075401700701c8005200003000680d45840100420b48950443d1500200100d031003555550111040b03101046000d1142d084940c0e092001401450800c900c00c0c840c0c031600091031211030000200000300c42d107850b824102c0e5803005540c1540038001407030b0b1000d0403525102c41340c09103c01560080c00020141c441c901e00f01110a4402903070b803110001441001d03c415000c1c4d9841030301d104e4400564441c0801c0140152a00c0180390312250050782c6c1c005c500e0410042c0003800b9030b000508880f05500c0c0400f450041013a10801c56440d030040c0300d44550191080150708500b0405c0d80e40051040d000020310071030b00d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 441800368 1250 441799118 441799147
    0x714010c020d060f0605040603050307060518031b06070f0c1506150f02010f05060f06070c080304030b0403120b060f031b0409290a030f150f0522020112020f 69
    0x200d008607416a610010f4041103003045c0b042c0c0700070700341c00d0394100101801e580360555240500e0400500e0745495030300148000703070200c868000c2007030100304903500c5032541075014500310340208401c4014850303140028030252045040f00c600740307217948900b24805000d40350031101d02d001c40190010b80e030b21207100050075605040307040900f070516901c1c540958150340009094072140042c43d01913070709000c10f200495807508814070034260111031044c1e80e05c00350301d090088402c41c0e900040090002007800418001120603a51107144a036440803d10720015801204035400789008079040311050103022004c80c01d260003190031130b506000d08002c4031062030b500350180c1d000b1b401901c8440e899540100121000c22502c00c04001c00e001c03401d0788210201e002c02c4e800d0025220250514200c0b07000401440000600049442044c0805001d03480001144402400096030b4080200604100704041c051410040d00c80c3c1f198140e44100c01600c807000030f1030294000c0741c015411742c1c00c00c1200803411600c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 441801618 1250 441800368 441800389
    0xd060207021801210512070c03020405010305010b0a080d2a02090403050d0c031b030c092c0901090210032c010f06050a0308070303020d090605280e0714010c02 70
    0x610820070041c0d810b004e1040060800f459a400160340c1d07110411002071004244d0b503202a4103d4603c64560009050004605020340e0010307422914000000c0f0600c00306401502d210f81c0241c800413026592a241d640d5666841d8002c1c000051804403045414143c030341e0000100300b03560b810703814440440d0f00003500ca10000d60b8104d01152000400050b034003180c0c052039188803401d0404128111441c000301108802c1350020000300366607503141d0000320f40160340c02c07400b4203540546140d81151924400043c0783c030f000c80c0b104484507030034001507182ca414003617011380039406491000800c1c0120f07000d80141c50319801100c0c0401a0303000c140130400402e2240100c1d0b044680000c601c280360001240201c2c2c1281c0c01441c002d0b00c100c202400407071040c104a40b146070b810700d401a41e1f00b00499003000102400d15004000c0303402c0100340581c0e241c1c1c1c1d4403030800d124110aa500b00405c444000101241e281c0c0040e1111500329032000c001c4800300d0449540c880406061111101e00c03d98005005001c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 441802868 1250 441801618 441801649
    0x90d1412040803070528020129060c07080d0201020342060d0905031210050307031b0f080c030c0f0f1c08070525061202030a060510030f051b090d06020702 68
    0x4046e406803010035424000c41950502c024440072505460058034442c803039806142c28090040014255900c20040011000510601060760300c3d4400f8108001c5c040e40c0300381e61701c41204030524804030201c413101071383c16941083c11108000c1d05000f601c2c64660446180b407604d9000106229200007917046002d41b50b4828801d10282d50746281a035034503044200007a100e100da03042d0443e0140700c0f40c1c42c00580201039980041c862060040c0f891301102c40d80365690041d803008450440c0006400b8000248080034460403419076500c0070b40f071410300c038241400750101507104000160102803030420390314891400b488101307402c0d140152511040c0e540d6105c600101d131035902265021000300f2902c603414080c1c040c0c00306403020951428800034410079030300c4440d248107a40000803038001060b80d8480130003840c0150030222182c078000c20250081c10301d40b83c0300c1c0c40c1c281043c00140c0e01886041002040b800ca4000d280d060541107001d000c1041e03c0e940044400b99400c02c07001c005a51420000001102c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 441804118 1250 441802868 441802927
    0x9050706050409050912090904060b1e040f27020d0b012607060f0807110607020d020c19090e070f0b04060e030a151e05090d14120408030705 62
    0x240f82080140c200c42c030061007035107a50804074250b05c030020080c080328030b8443c0c100e40024154440b0b08200004101c0c0e80741040c1d004074905a08003202034100900c0c10944400c076410448140c0c141904010350f031444006800b11465020004200c00a0400a0f424039002a0082103404451341d908810580d080e0400880c01490b0040c0182e1440a02d10701502841e948026010b0b107450400d01500c0c0c0302d0840004001e1009450002d41c08034030442c00b0706d03c0410540100d4945080c020700c0a0340f210203407001c0c500103000d12002a00203080011869186200c054a1921154030b800280e02c0101407000d2030b0303012400788040000300340c1c04240300c107005440c3c40050980c4d21460700c400542540346540c4114001d8102c1000c04002c241180010700c0c801c240040085010020302d040080041200000003441f5441d143c28400c21040008200c0303000743c1c268071854110102c0d03080c03c108070300030714444a1001e55070400250000f50a074000d15040f44142c01e00d90b0500350140b524022201e0504107010114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 441805368 1250 441804118 441804127
    0x5060f10020a060f0e0c010504060807050d090b04060e060a0612120e060307020c0405070f0503041113021303060c08250c1e03030c110c0f0f031614100906120905070605 74
    0x301701c1402118000842424443d25241c42c0c8200504103c0000b040c0380c06203e00403410150440d6290448500c0c564080b51956051826207480002040200d001030810700c00c200004200707041502c55401a00c0004096041c0c04131140d9030040550041c041910070425460416000b5441d1000514003811b040d80241840304801020701c0b04071103000342044c0411880b100c207500b0319600001141e400941040400c280080d44c00080784480c40700e40e04000c43c00b80b0005418807002c078181d60701c078284c0c1d104010911850001d0181180d50440a0319080d980d02c65800d190407248110700241500329006050a0482c642d00751070741898032004418503c00004154400820075605104088002041c0d04002149000f1806429516040300c03600070702907056020401e01e10741d156030680b0444c0c400103080702c4d0f01d400d4441c070455243d142c03071080141361581c00200d400c2d00c0c506100b1003000820141d5841807a40c3c604101128420600700c1200d0816945603000e0020600a0006001030005600e60603901c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 441806618 1250 441805368 441805391
    0x909090303041205120103030f0c0209130c0b03040b0f0406060503030a0f0e010201091e02031005091e01110a141309065405010e01060e030105060f10020a060f 70
    0x11241c001c2449004c21100b0849000d031240c04c0b084441c1501d406141101c0003100c0d503d4160303100711304020f001e58045442c0c0704120040540320401c0d06024072400341d154880d503443c1446865070000baa8002c00541c1420300040c288071650003c9035005015490101d4059602c8021a0441d4441609030000608540d048000b89400c5039540e01410070030700c02000020003a440c2c0c25604c018070170041801005440142d8195603040103840c03118911048104010b007448403400c3e0b030b280c81c050000305452120a040310a0b440c818400c0326405841d203030000703240501e03051f070407204a079542c08051107500b8144444101010f41e5030840001d4100b840000803490706100c00503c001004040082012501039000000c003d0507000c0d099068445541958200c85803580c0155102140908020b089281000026a1061001c1c90504131001900c41c051901007010078542a03c8044500980248803500ca50001c4c1c282070140c80701605e0720780306030b0f0388124540d030301e00c0c050310b41002c89250069258030f0150030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 441807868 1250 441806618 441806633
    0x41a0d0606020a020a0504150810020c1203040c030b04020109150215090c03070b0d110c0c040609230403180f05130c080a09020310090f060501081b04020906090909030304 75
    0x81c00071400140040e4480d80e000507040411070060a00a0b40c580481c4880050004d000d1030252070001c054450900c1015030510094100c6542c1881d10301c00e0200d00340b60442d01d48103c9020704e400c10840503072581140c5441d502128091300403410007a42c441d000a0b0044140350b507851400c50b55000d0301215602c2c500100440c10003a010140b030750041102e541c0c03243c3e00001c40d607046487c1100c00b04d45440a0031a0000140f11095643c14030000c00034901e00b0b070501c0403d10714280312084034204103040d1140c1e03240003159011250740015440300a20414641c5482100a9200b403007842c00c01601100302e0291100c00d4650341c030030890307041d20350030a000e6464040400068203c1941c010880603904a80044c41c0940c082e003005402d0750303144894010344d02c0034801198407004000b0184143e0901b894070f07036110740306180c003695103e00c0c000003c01c1c0a0408120f522981102900d408089905042003200950009107501d510040401c001e00c2e454491201b031521400602c1d02841e10b034542400c0804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 441809118 1250 441807868 441807881
    0x2030f03070e031b010507020f0f06070b011e0513020306040f150f1202060306010c050712082d1804140f04030f0305100b030a09051b10030501080a1403041a0d 70
    0x604c80d003003074018130740c1d0381d03071200c155444160100c60106130400031801051088102d082d1098000c80000b40140600455400050480f40054040706075102030b01207041aa200900615621121408041c0440e500d140c02035074000c403000f803000a1050007000e01c5400c0310308461480094462400e010451094211800d400a00e0b0755211441601c0b05070b40010701c9840010700f55418484c070321040d2424410100544009040c903505c1200b0680307080e04284200d90051350181500c8580d104581c07006841c18481120104044e038529818a008100c1e0030100014401d0b1891300103545035100c41c0160b84411103240144c8a6400d140c41c58101401c1c01421162070840c0b8205150800e0140441c24000c91241000c450707040013101d0b1241c03030382120180900940c14000c0c21070b02c501c1c060515407012084440511820495080c05482001c0c101902501c009104442450b01f2411010b0003080303080010403161030100045e20310300340e11000004010707070130351114079803820f00856040d200b07080e02e1003000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 441810368 1250 441809118 441809143
    0x60b0112090f0204110c0316120c02090a0c020f03040e060103060f0f050105031503030a0e271f05030610030201030f0e03090f04061502030712090602120a02030f03070e03 75
    0x18480c03a2100d40b42c60b1610700b9800d00007401581e0364128080801c0100d4140d5001c04140030550b40e80e0900c80c40c0c1140d40304020300040e560025030303440700c8c0317181ea0003000e802690355406003500e02280d84401c41c110003002d000c034880082d030043c004070030341aa4092000784050240301c207540c8403500306400010f00f210a917400509829042d02020b000000ba1644a9022540b09107412640c95840001440b0340c0f1000d0658160503100115491500c6030304114100d444d00170a03920328000300041d00e5200c0c103a8440c002d5030403616101c04082590b0402504400f032054001c41c014062065440c404645004801c482c00c0c100d01e61024401d10456900d801017900a00c0880810300c41100c2042005840c1c0c856150241e100d2006034074110020b441c1c0390004070040040b841e8005842e104400c019440c0d600c1040116a845107503090503030041d000d5030ba81000c4d1010b81d402400e034a140d0b82c9042c1015800349203100c06500c01400402e804900c540d00842c4628615503c2985c00d4102c1810b15161918000c9413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 441811618 1250 441810368 441810371
    0x10e010608090a140c04020403060f05312117010909020603010e040c030203012f031006050c0f100605031b060f0f120703140f07080c031f03060b0112 66
    0xd01c0900d40c40000e4003142c0d5500813501c540c80d000344c115118a00308000106941041c0003090000500405500c03c0c01c1001040001303002982da81c1d01d201301e44081204000005621001001c8840c25012502c0308003580f0440e49545203526990f5000b40109450014000281c52803080a0300f03003243da21128010050700c0401d0000d042c460780001c0300703800305002e4480840800c000103828044c42281a42c0203640103402041300010400d542d105600e9280090036510344549903e21050050070202c9208800f01c3c44040300e0207003000700883e5561310215480d071062048000444070000148003aa1034420744400009100d45407000b071500344451084074480e1074000e0344a020f06030b106c16045030303541544d0404880da601c624004881490040c2030a06181c442d243e8100301c401c64040e0311521000c040e26020301c1c0390380d031f4890384107940c0a0110780d050002860400864208220b803006140c203c005907488070a02504c00441c2590f42c10158415a6096111141c40c166540c221030100c040c0755041a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 441812868 1250 441811618 441811621
    0xd020d09050108150303070c0602011b1107090b060f03070305100506030f0c0c010905030d050703050f241c030e01090801151509050604090b1008040506061e0612010e010608 76
    0xa814040f008080103400034610b42e507a141e5a80901c00c6030f0325280d2220001041303a8a5100081c024085100c95000d80d030301c200707007200e03489005503403291a500800005190789400c06035418041d04000510035003003c000d2207200b18840e03828001c1d511039140e6545c00681403401600b04060458190320040c01000d04005229035800700444541c0c0c003002603402d5550319040c40510714010407100300301030603a00002c14030581e00002c64100354018002a07070300b030000351112140c92070100d0058462641c050303120304055041d15042081110446801070400c4182002c100744038031003400300c940031000501c060089184a60b088100f0310041c03e4004001c101044254a45101e034508d94018850400e140c1d03061017450780e114180c2140504005000c042d01c50343c0e01c0980001600c0100812441080c07150181c0c15500c1c450303107840e4460782d0054020304031a02d4101c01d01000740d420701c40302000c401c0d4070303c940b2a00d43c0303035100240221080c2104c0320405600d840d410805900068200f0400c00406a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 441814118 1250 441812868 441812879
    0xc1515100e010c0209060f0604090212090c010203070308100b04030602220f03021c080406050a0e030a030c0609020a0b0a1206080d020705010807020f1605090a092301090209090d020d09 81
    0x980603c8969040d1a070b000140c440100060812204040c220382c4100c0020b000724000f4001e401411304c4005c0800c45a0890b12442103460716500b00c62101c40c0141e209100d4070b000700c2d01c950165a04101c80300700344031896485000301c2085900640090b621141c0000711000c0311202590f07501c0b00d01500d4602600d2103828030031107000010aa11001e0711a900070070203124910200d6840000042c1d010070f80c0d60381c45594410151164000c03043c09804200c41044443c2a401d01050309000542e15541d1841c444410b0741d104001045a00000d83c3c001e0030074200441e078001042c00030055401a622114003d542c8880304070195400d6403c00d00c0150008800d8411aa070005080300c1a140d003401c0c03070f0506070b40f8010200d2400a0850b490b113200c2c4980788200d03402c4948100600140c910580b4400c040c1da840c452040c0c00d945034020300506940080307400702481529100203241c0310440c1d10010880b80010340004650501c26120107801d80c100145000c10140c0400800000b5401820542c488905c0c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 441815368 1250 441814118 441814127
    0x4061205160305061611030a08070f0311090103020a031404081c02041a0c0f01140f09151801021c0b030c2e0e03060a06080c061c020c1515100e01 64
    0x17508003110715628000c2035503014001c60340c20800c0c100d04d000f125116900010001c02c14401039030341d11702040d5070b1003d55001c1c0d4403e015018100718241030042c40d003100000118001d500800c4900b04255660304040505013100f40c502d40030328051646551030b0303104009840080260301503401c8030300d0b1040200b045440030300303070115408010104100c1d4880c0b844201d0181048540d840d2814294a064224412403e0310a11140103140c00c0c00700744042e80d02c0f031600c00e0741c0700501d0402c4c3e006078821400107450004094181400c20702d14000140c2017407440d209404140e0401c04901c2400341e103518841119040c100684c140420084800c040005a441c201140c05006000d41d06c1140c91030fa102c03591024080c0400c1c541a84015003116110300e05042c0703000c0204543e01038005540100e003400c00b501d00e8004161025031203980d4450b01d54184181131040298460455403c080c003c07121100300007072184020310b200d080e0718286081d403150a20700700001c49074210100014800403002441907640d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 441816618 1250 441815368 441815371
    0xd110c01120513080c03030103050c100c140f1002090f01140301090506030a0804080a020a06140904090624060f090f14130c0507030e0303070201021c05090406120516030506 76
    0x207040026564940c81010750031614400d9028000900005604100c10700020045040300c5c092001d5a803149075000401095094510361000040c0d103a0b5285408191040c00c12441d01c00088216004012040c0c0010b007050001480c0340d180c1a408145c01a2904090000c4074000000b40b0706031510b003041c100e580e4902c1c0018050b00c000f182c1ea4000107201c580f03041003035140664001e03690503100c80d500e286007540c030340300500224054183c07401c0000b21079020b014516900111a00f0b1141032864141c184030042c4103980050307920a0b05ca103040b9104020b01230301c240110941880d4060346500f4503d01506c403803e6401003004028044004100d008000032804098801c1480e0b038100d0140c0850010704a403c1500852103010302c0c0184200308680c10000420301e0300d00c283c0741c007245104420200741e280d0040c110040e02582110340c600c5145c0d80490705540f602c910b00c1c2000381c1030103200c9002c03804407030b00b94012240358081d0210120900c8003c10404416110924114030314506507a2140d85a010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 441817868 1250 441816618 441816647
    0x9100815040519060501050117100603091b0b071a01050d140102091e0a12051207140d0504090614130c0c0609061b050c0a12120e0d110c01 61
    0x9000c404a010404144810344154000aa03404620754036403c1c103000401081c416140400d103c0c000d0b201e68003001541541c8140d100301800300e0806d02e415801d030094550343d00100d45510b140386e50315100d0603c15034810060141502144c0e100d112a1030403009c901c821440b507920700e0040c0001008942d03501c1520203030181e40000700507000030711742510b640607010303082180e80d03c4482e0002f1041242256241d265051230120b80d400402c2e5518a069460111502009800741c2c024001100190201d0001402c079a8840d10800c6020800b00d588107040c0b9807621040340000d8000102085041400d01032030010f0410071241a0113000ca61000940000741c51010703400c580d0f190891180024017411384140b013260402000d104001c0940740402c0200b1f1403036400440e038a03000b09292110792103201a01c2c2c45040610003002440d0103525a2040010485401010413016814501103d505401901340d000300c41d40003015040c8140c407000d41041c020200035580c95018103d17440450f0303030101c000c030034401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 441819118 1250 441817868 441817903
    0xf070b0a03090605070f0909020406091e080a0506070e01141204150e0c09010e010303202b0e03030a050406080c0c1c2606090a0e0f0705091008 63
    0x14a00c1000d070301600492002500891800c000c11198603007200744d000590310035135a0458102d46402e020b9049003d50f00400d40050000d403828810010202070410f00e030b92003d202d07468003507075802c00d080c0b80003071b050402c481c0340d00b00c1014040070b80d4000d00c1ea040500070900348041d00c8500c4403c120080d00074030b50446680200c15000c0780510281030809540b03901014818800095600006c030740c0c48545440e903a0044043c007000280603010b070840c050589170b0541c1c900d082139100303440c141079492002884030958000c0b034422480946000903911141603107444045036004811001130400502c2c0600766000740c1042248440290f4002c044405031090b03802e158001d500c424001861900840f007501c903007031007418405100c80f0b05072a40d01c1c070704500e20b98451912841e504003040c14011000d01d6002c824400001054117840c1c80082c2507404810383e940050401c100d20703250741c5800c5076600342081d5508a100180f01c6424103400f096404140d01112a00031454001241c3d0780d2404082aa600d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 441820368 1250 441819118 441819127
    0x60f030a09140105090c13060605030723070b0103050607111c110a0305040e1f03060902191719120e0d1205040e2215060b040902030708090f070b 64
    0x9480700303080c24150180c0001c00007882c0c46820103550780b01500007913200340d1f181102c0d1030700070619005040c156030055607060b08585078448141c0300031b66130704200c0e00c030511231b1000340321910001c002501c0308a00606840f81c4e19491030419074149a4064100c0c41000801c080044c41d400700010a01e00d40c800c420501003005038076400c11110b4008408400394280a0301c102001410360040180c0255640002484e4241e02c1c0d04002c5000d4413462084181c510701c00207010000304001c6c3c0e110782e6141340060720b035480c0c62800a540701100390058000c3d082c04840100403000d00742c01000359050a5030043c01d051030014544d107506408071a9078503280f0800c030701c0c0800410151581c5005202c001d034010a2643c5281000c40003400b01c0e002806017101d20044c840026402180d03041717005a00d4100d2100004c0b03c01460b44403608081c00996010714840d0310340c034000400116441c010030003829800d83c016124100694010040c80002d0841101c6922030340d09050300d050007080c16002c940c801c40340240c0d078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 441821618 1250 441820368 441820373
    0x30b01090608090d181a130f1a0703050f210c0708030f060d0f03030207051603081206012a200312070302011515090e16140702030f030711060f030a09 66
    0x5c00e0039400001410050b001c054040e040300c00d000d40040c61070713110f6071422140c4924051008407164070a0b1b050800019048030ba80051032001440d40c6c6000b841d001c0d2030540541415a4540c0c00b07201503858209407403030341c0c4500603048180c02da0005070441c42c1a1800c00d0725206d400d406e01001d050510389010100200d00b03c1c0c2d40350038210480950081c00d600702e802042c100500250410b140948403402600e034091040085c90410205803a4410405c034148500102c0641800e140140001d062260050f04901207900005802d030911094481c8805c16030154540480c211f0907000c100d0b01480b0721110143c0c00340d50302041108400b20383c03a6680b0344030f000300d040480c05014440c24400440c045000046a14088a45d42c0101e800140c1c580d801034503594140c454030b05000310f9000882120b1806040b041c00d2140a080c0d81403601c11554506050f0aa0002820050032a2010b042c1d580700145001c10040c0000d400750140100310380f181e0400c40000d900c1521440f00a0420482c15074406c8440d08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 441822868 1250 441821618 441821657
    0x607141606090b09060105010306060512070c0b13050c041b0f05070f0c081b0105030a090f050601080705150703020303010302040f0207060501060323090712170307030b01090608090d 80
    0x30480d0003160502001c08141000e124100040d14000151300030140042042d500034040d034800c9842558440d031a01480c1c02141d06050809400c110411543c951a038001c03da2065001c0c0c0154001207407250380ba200c920f40a4603051002d00f070719001c0c80c1020300c0d18910007107421079580b010b6250708200c201071088210840d101c1c40b4494004120707883c1165403d0034420841245000c1e51506001c86484441142802c00c140c81400502e60005108000080d20780f0348540140c00c0e07262040301d11442c01c4840e0f641e410300700b1401b6006500154042d2804000a00c2c05a0110548081c606242ea15204142d00c00035104d02c014000079000300d032241e10300101070060b40c1c12503c28070b810100810003545c5641c8010050444c440d5801e010340341826140e03401009821115001b1400c00c40107024035454500300548070100100d040d00d030207030040c401d50b40740f621030030095104591a56000610302040b030005416402c49410040c2002564000c00c844d56800007900c015100150500310f01c030341d00c0d20081c8038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 441824118 1250 441822868 441822907
    0xc03020c01230a020a18150f0c0b04110112090822153902090105060903150601050c0601090b090a0c05031503071508100b0c03030c03101d070f02060714 67
    0x2480e450720240001501a00740b81c21147c1d0303181c5556203880e20721440504442c1e6203030858000c0c0044840e5408180000c503100000001e41ca0103041c1021802640d0740c4220803134900714400d0340d422100040041da401e141e0a1141c02808041072601c101c10b0a00e035100400481010190b002e200b03075403244c04100c00d004250001c41c2c820200e811850081c0c80b082003020003040703882c1203000b581000004940351800c003041c0e520000000d00240a500c1c440440c00e54000c80262036181800340400100e08011405e10080f8042e010750a0081000c04490050020003c402802d00111928020421031016403110803290044085d4031844150302c913082c0064208038565001c10051070192454000b00da8010807510701c5000310000100350103a0313a03451311802c1d03c40e50481c01d41c150001c00000d03602c03006101c01340d504070b030007079400d0021182c4450340c2c82518084243c070b080e04044600c0c20801c1c1140e0202014090140034809801541002e840181ca00450450807000104000ca03950440303465880b00d10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 441825368 1250 441824118 441824147
    0x5030f040f120201020a02010e1209011d0603091c02010b010f0f1701080705031902060301030b070903020303040315240611011509060f170c01030b040b040c03020c01230a020a 77
    0x801e5814229011307000394414203c00e0099402c0c044400c44150010a0210305c2d28510042c16240419840044442c1004502d001e244540c1804012407640c4410002c0e51007003190700002c0c10f050b0b8001d22204000000c05101904580c108010b9031000d91340915013440058450400c07882007400c410095903d40e2100c070a110754000c2201c00061b40c0c0381c00049000803500d0176000e4421888046c0000741d0f01ca0251100a9000780080004100041034291081e41c0030200d032038000c6030a900c0b50300003415540181d0094885142c00c0d0344070780c2c9034143c0384190101c0f0800d44000543c8015040b02c1c2d800000f80c640714480034007007400e0029010364400c0d084035804620b80c8560303203a042c0e12001140c004102c9400ba060000041280200f04d0342c882035150310a40071300703000800110759250011070240000f205c0d07094200741c403002020240c0d112400384540c11030241e03d0140e2920317506241c0310300311900000d426144000c183c810850500540d012079406c0030a038040981e80e2011030000ba2141c82285800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 441826618 1250 441825368 441825383
    0x60b040903050901170f010e0601090807030503120a0506030a08030a1401080a032006011503020d090b0718030b0f0901061212090b12071808010c180504050705030f040f 74
    0xc14003003541c000000c01e901039098a0f6410000c03100c0122103c24a01201c0c000303132217100580140908081503030b031281d0008051600028170b9480d102410b080102e00e900807242c5500115106440012002e00507901c01102141000380f4034124001a55403041030801038450540040403980d00360250300007440e11b98001484400c95650340582d5a518111090240c0014184006003100200000c8420342907054a01c0148126428404088d80a440c000354043c00d16508002c09990044540601c0b20344a00801529482d4a03040c040039000c0020310b519a14026151882480040c041060564108034800c100201980c0c030000c0603401030400e45c121590081034030080404005ca03280010111049565a10543c20740e41d482100c120f0180710020510343c1c1c90031000804a42c840c14821300c1c500041440c1d240c0d9260380e10405404c5a01108412001581404440d4007441c00e07050b541c0300900c02a41d081041c1d20340601c000b0300d107000280c00440c0640152000c034040c4010086c00c40ca141c1d0300100d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 441827868 1250 441826618 441826631
    0x608240303090604080634110723040c03020c07030f080405220f0203220512030907170a03050301180207050102041202030d020604030e011101150b2d090409060b04 72
    0x2e01642d61400301d5076030465191594041202c0d07002d07420380347c81e51080b00100c00c44055000724281c3d104514031a102e42c0364810007000044009030480d4030700302d081c100c20315580c1740e148080500050719869841e01040c940100501e1200940001d0b40310b080b217410250311000c081d05494108054031a40c0d0126a0010346520544200c0c540c000d0000c802800700d14080014043c1020b1300016808100c0b00d0108001c2d01512141115405105041c0c880e4410000d0b03071181c2050082d1080e841d041a54014042d0340403035003e00404035244080d10080b60100010309150816680c01880340c03105003d104107000396040c211203041c03406d40591340b00562103002951260f4940c180e10b19842e0f41c00340300f60f1080c841c00b00c0e003168450000c41c0e06070003a038160360f030b104600030784a0054030f050b10135007641041c542d070301c4000c98034210f07540420b480580f880510055035402812070070340c0f8130684e03000030030155242036400d0010b071105e4074212000001c083e100412101aa82010002010009078858000b400c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 441829118 1250 441827868 441827879
    0x80f011a0906090a30050307020907051c0501140301020c1902030f060103050a17271c050c011e0909090c080a03030501030b13030509060d110a1106010608240303090604 74
    0x9082c288400c03601951a440d560404090741403170306a26009000e6810030425140942417440000340e111070141440740c40c014003000c0c1c183c503403144004801c540c03c0d40c07500103105124281d8103040600c40c1c1180207608080480700b4240c4c6a8010400801000950045600c2151024041102540c55840c01d42d8165039403820300544440c80007600b1241d0042400802c0005040001910300c01d40001e20340b0300c070304200d4030742035441c0c1200400129800840e162146440d10003461074242c03e00d200750090024914844000350800903100b01c4e190b032581010f40c0781c10360303242d21000580c1180c00552021034520468104010303910010741000e0744034065440d01030185900754100b60b04881c0b050a1841055840b4007007980202d0000b50000d00041e801c02000603d171901d90f000d000307545d115010010342c41d07030100124a0039030f218205840100310210300e10300c0300714814000a80144400c2c00c016040345004145001d030503105040801170b040354161074a8041c1c804006480c0ca0490103000296180d4488 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 441830368 1250 441829118 441829139
    0x2011403040b0114060a0203030403030b0a090914010f1b082502011d03030c0d09060209060406080a0c0c17030702070803040b090301230f090c090a02040501080f011a0906090a 77
    0x134061074210308401d044e03454040c2400d40850b905500551701070b6055444035503003240680395040c3d199a1014128001003011a070324130074207034200e20034085081c1002c100090a030945005081d0f110450307160081c001d4140004030410b00120071a45051241a42d40381c010790003819402700007c800c60000702100f801a42c056100d81d404009008845c0080e4110340145070b52403008a45420f035848080c001d0340c0c6070030101d410020100348a1080981095041c03808101035402c141c0c000d1b40010008800d00c10403185901c00c0c1c003139100017464400300f00c001e280c0710300600006d440c1c1d601d60707a00400000039042070303c20300440c00034041e19000daa556568801d00342c0b103141c1044032020311075440c00244070044020045c035580d0b0806400c0840280d40c0d05e0b400303c130b0300303042c4c0c014210380030750003400c415684640d07604689902c11913400d200161a0740c1008001040c00f107004014030480f003000e00041c898502d14501e00e030350000504400c01d590707840402c08201140664419079030000c0d04503178049070311200e5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 441831618 1250 441830368 441830371
    0x130308220c080f0604120f0c05060a0203060a0905010e01140103020c07060e01090b0c1c0c0c0b0d0e03120606130b0c0307050105060a0605040e103f0b0a0902011403040b 74
    0x1410122400f01c0d000065454641c481a50014105018120301540e40d03801a081038407100901c1c00c154040c1165910707414140b010807070740340d1041580041040003d14141150f10058004180204819810118080d04003a0180158289402c2510803149260b00c643c0444400800400036102040d035940c07000780407018064183d5010421180c40428481403280c10b4824900750b00c001081c040c0380c011681e41c0e030034804290803410407020109101c042a99031514034014650208030a41d103843c0ea1410718101d83c0001202140c9400800404012024003c881900036000b00c0f0a1960341111924140d140d980a42c00009440c03404035010f00c2098003c4054441240a02c00034809941c9000421101c04864090440882e0040c030080c0552504119100c0d07104908140c020041600c0c0c00c800c0264424040d211002001c0e80114440105001d0140c28007210046050148102856981c0011110300901c14203200b540d401b07800040d0380c407890b0603110140314001001d1f5242411305001150300c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 441832868 1250 441831618 441831629
    0x2070c06080603010207020d020d080c0303090703030906080c12060f031504140601050a0b030a06050904050a060c0e0a03060510120b0108240a0506010903050102130e0f130308220c 79
    0x454000141c02e0b0406000311100540e0080c440440400d044d0708000302c0f2401c01c00300b600e00350820b000c0071210340b0040000b140100f411500401c56245185001440d100c801d81045d0308000d903e4080c4400015800d09603111401d01080ba15290350340c0740045030440480003090342c0d0505c505a140802c90407803444050003a4010340e1107240100f40c0c0701640380d64607400c0c070a150300400040c01c02c10041c3c032050003664204107100c0020446540e200009000c908040e2001e03621900804014070411101e03201d01d44920b560360503d0401a20414002510001103200143c042d503120000107415200c007540c01c0002d01010a550b18908140e400c0c5400d0645003405900d20030b1080d40203000c001e40349001c4000100b00715401030109aa2141c14410103001701500083c10300c1248400480058400c0c0041c040003144c0740c1d296444c4070728026900b100c00d03401070f180c0c4101c044441c00740b1455020231030515052507050b040c250020b880b0480380313144000442a94141c42000020440704004a8a0300d0104030382 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 441834118 1250 441832868 441832877
    0xe010e01230105040525020a02090705210702030f070609050d2307050d0c050a05060c030a18080702040207020604181a060a0e01080c0903120405040e1b0f060d02070c06 74
    0x2a20b50b0188421148107a5407840500150241d000011b000e06c05640d070111183c0c41914400e0b1065400300c0c808001c15100c81002c11804110103204c240c1c1c4844c8960b1804003100050218281801c019442e40700f95401c80c00d04110010f40c200c00d20003a5040b00034140e038818100c55098001140081c1003610307000c00c003100c6541b20803104107820440000d607110607030008090444032096160a442014503080204c0761806101b02e144080740781030120a200c0d19510300724a80e640b900c1038041c4111170030940001d8070030060603150340c0403032285802e0721030f51903061728016910000d60000401c03501640c0d005140d0031501c03081c441d4400e10107411005040d01200c415a009030400d1040115a001b400e4003200014041c2c4034030441e41d031281c0a0b1030340140d01c41c0c0706149069455000300b81030500304d0210305481d04000504220300d080901c50011190258405065810307a51341d00c40d21034140d4444d6492081d0b0b8480071518807613946070226402207150307403411561039103640b500e40c0700240399108080205 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 441835368 1250 441834118 441834121
    0xf0303090e0108190c080a0f0507081506040f14040305040806010905061f090801020c01020909181e07090c0f0f03050c0403020402301b040303050406030e010e0123 72
    0x400d81c9011040c140c03120300c80038200c1000480c0342e900d0b03003a485900c192030ba42d410500008403500e090111402c003d0081110f4002c494480c00d00c180391020b0355028007155444480c200c0c001e40b00140c403082d04030400f11804113002181d40c08040180c44250098071202d00b801d4148010142c102d4020002c1310400e1054075081d03030341c4401500884100f01c4001e80c0011131510040080c18622001c031003480c8090422007003443c0c45d865501d003241c210044888003698001074101c2185000320165520814056070f413101d0603c1030031a1034403402c0201000c003007142e035090317030101840c030911078800035190103141003146908070000100704007256242440031414540700e482c8550f100b801074512403084196168506071840c0c1c2404000c0d440201401c40c03266070641d0204030b03510078001c481c600c07050302d15001086040500e9140684010410400c00d4010100010800070740c02030182c41c00c0710070350305001070124081944140503200490a80d811075107065001c21020042454003102d00e20b04005441c42c0e07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 441836618 1250 441835368 441835379
    0x1306050c0a14030105060f0903100f0b1201060501020d050a0c02030303070c0b060d020625170310090212010302280306060602010617070312050f030106030b1302270a0f0f030309 78
    0x883c402030140e240c11000c100308480700c1440d4000284405c1001604489840f021601080115030004104118054031135000e00051310305090341d04199013290008001f0700340b83c100003075035620840c0128001e0080c040782c80c5071244c1c05038000b15603051300902a02e55038508036070001c061100101c8200c4410300c0d0000400c016090a00d0020002035004e09a1407030100c081c15818072b18081c41880c054601442059000040c0200322504035071140c48403455241d04140000704a0a03000303400c860303903d51050140c58000c0c045510703098112501074502c06c03860741c801400c007010f01000181101b050300d91800300004201041e80400d04684aa9008014050700e417400454100c05000b07071040b49900810040c404100c8030b007403a04074074000c0c1c240705140c420070940c1c250450f0001d0b8465804070b41e840c0d01110303d9080202a8084a0074100411440d041000340702004d00604408034622081030442440d082d5194041114080d2804284104685945088002c045034060108400107443e0720400075a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 441837868 1250 441836618 441836657
    0x50a15090308070c0b07080a020c120c0606010c0b0103110a0902031f2111010c0f08090406171c030b0429040510090b0a09060303030504060b030303100e1306050c0a 72
    0x32507644007085c4503054645071411915a60040c1c03d00f410721380e081140380e0000008121242c0700200141440b03450381c0003c41c401c1d0030070000a00d0316050014400c0e1010015810310410760550303500081c049a01403d0034085820812541c2050001d14800424010008149030240025490014613014020303291005519079850002a9031040030b140494600062034041010ba60540306141403007039005280c550320344240769443c00b91124803000840408504280c0603580103081191001e18560101d55911641c0b1860b03640c040d10748070340041c501031007a8485c0c0c001c6584100010030901c0290401b003502d210103009950035403106003140803510800c0c240303405030520954001c603861001d8ae107401080303c003501440082e140d1201020b5800f10342c80865205000c0654060741d07001509143c240740100480c1c891042c114030a60090007006a01100f500000095911034042d03006640c440402e469824081002c004005509244c1041090070300070001d040d000f002552050701d0105020000103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 441839118 1250 441837868 441837887
    0x30606080d05071203020f0a2c0303071e08070b0106030e0109020112050603150a0b010e0f010f0c0f05011d0105090c220e030c0a02030613030815210304180e0a030c050a1509030807 79
    0x2b0f8154200340074007004182184d118409504100780c0c440780f050f545581e040c1840d03110002c200c0c5c80410800051000c294075100740c1200d11003040003001100001d80010f48071500600c2e180901c41c0d20355000074001c1c0c0301840100203041c0c1481c0440074a0800441c008040c0c60010703051070000341c1c2c0200c0c07065a0b01d00001301409041e010385540e42100181e103000c9036513900101c0d0540302844140e056000285091044041c0c0358a445049896134402904150940328058a902d6481c2d01c042d160446958a40b0724118600c4040400c08240c02c070910103110240449504a824601012032410340c800000f20351186c40300c0c03080741034030700c1c1c0e5491001101091108007000b84c0000c1d41040010014600d1200c0c28030f2020004100040c1007040c0400145034103000080c002c0c490304041010006081c2d2041c9007051003005071824801d10314a6058182d4407801c02201504211482050900780102840031007202904400c1240c410f160032402c01300604080c1600b01e0018221200041c02d036841000e010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 441840368 1250 441839118 441839207
    0x150b030114011e030b070509090106050a020d030c09081203040c23220e15060102072d0b07081e190e0609030d09030606080d05071203020f0a 62
    0x1075601c0e42441008840c0c1100b5000251001510103000710108050100c241e10602d065500d880d5602c00020502003c410107074041414064107000315200b854012030020502210b61030005032004149504941c40c00030b5a1061110f4040c8001d64000da0401c10000d44c401d0b0300410500413003030f0b40d4080d5004c0620694654164002240c2c030798860620380941003003002800e4450205214401450000445c0c000482c502140d86c0a0700c015103032000c80885c0f0036800070090029207400d0389406581c0c0c104090900d117080c40609102d0446441e40000403900e006042200d4105403500d40d1460044010303445480454549588048540b4091a03c1c000310340100c4280c05c040d4442c03885c2c1c0c0005448100840c00c8130f80c1c0c845400d0060201d1520304010b441401309090751102c481ea440e60814900311080d80c0c1264000380c025500880c1300c5030308081101c4055900000f00e10080c0c2d800c00b0120002e009410005001072000107000c50b80700e50000c10b1700050080c600102d1000004c006c00b61029005440b0700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 441841618 1250 441840368 441840401
    0x604050403200a0b06120d030e030f04090207110f0d02011b06020310060908072304062304110306010905280e011805010303090b0d0b030303010306020304210c0f1b03150b0301 77
    0x10340035408d01c0f0341c04c0b40c40240c294804503410300d031508100c9400da400c01d402c84420701d0340c00700e0004140401c814500ea12010f0642d0820302214441001c6203031a42140c0c4007905200343c0324500f942d100c01c100f51401c0790b19085001151a400d180801200048040c030810000940c2082c0220382004081011411924603030b042441071028500000c1e07001c0182c402c0b9560280e5071744030009140c00480b014500c95508411040c107030b08072200400003201d400503401d059001d0b092081110590b00400030f281941e108660701504000308608e0b4508420020341c0d18040c000b000c03400010034102c50346505041c0e456049040625510180f18031049800900c4080c002038100c0314200440d1714020001d041d6003805d400c01180c80b02d583c502083c03942e8000e80c8120b406640c0001088140103c0402036581902c010000e4082200794001c010440da40301c1402422519070b417400801004401e000b05580e10802c141640d40c075a41c2da0924002007100e80c105900c445050600042c1686418445c440061800840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 441842868 1250 441841618 441841633
    0x90806041a1b04030b06010302091e0301060b070c2105011407320c0f2401051e06030a090b1005030f0c060712050903100603111002060604050403200a0b0612 69
    0x494001704840075196505050b070800042d00591202e45128000c448540d155503000300d0a54103050031161a607000b114200c509004041c0040e0f103804903507088640302c050000c00100681d414054554012000070704541c0f8200710204201000c400c164401c680715105c10f52220b030f190306000071040b00c50701448800803840c0d0b031450340d8003a46000341a46080c0300d4200d42c5000241800e035031402da90314104040454001d108000c8841c06600030382d01400e010fa941849507400400c078120300166041d1945c0c40b412010000170070003001c0d0b0740989070040e00103a030306401741803081445450700918028203000e4040c08002c2d4002c10000204188031050142c40203140c901a9142d641800020405030001c1001c00c0200b03602e1030b58100020202d4200c01d49000490f189945441940c8051046000e4001d2403903a1100c1c18050300131414980c44203090300d001c510745d03441d46801c03290217200500c0d00340140014000300102000015801d410107100f00305007070310340e1030301000c04c92081e03104003800200e64004407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 441844118 1250 441842868 441842873
    0x5070302031519150203130b1c0207110d1112071d040c0305010203010e0a0f1512051216110a0e04120504150e1021020a090806041a1b0403 61
    0x400b11040c0403400c01000b4042031300c40c1d0100d0600a941c1d00303000c0059001054501d040e10068600400a2548030b0741c03581b400c1800004032100b1501280c41e070242c5903022402406026421582915030107004083ca040100180351082c0350765150601d2900aa036229010a04284c1c000f4081d801e1350003440c0245014010f00708074280c03c00f4000c004039001c200706200040050300074000b0310701808014441441c0340c940000e5440803102602d17a81001c09045c07110086204080c0c400c02000d4407070161503c00211400d040c038038030b040f680d000c031003d0a610004195001103101c0d204500c135244500c00c07040fa011503140030007200329a135010341c4211283c03100100700051074202c0c5401e9802e2a6041242c14142d5966407071003403101000000000c20b914a64030f94440c6030150041c038045038241414401c04003d850b19403104440815007801c26a80064030700101c900683c891002841c03007030f0840340b042c58a85071100d480c0c04021406890080c0300e0300440d110310400c00f811a980002101c2060426240d42c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 441845368 1250 441844118 441844129
    0x6180b010c02120105011a0f090f2706360907080106060917160306020f13030c0e0c16020112180c1a04061d2110050703020315 56
    0x2052640c10300000d69001e800503240e5031910704000101e0000018158500300340001e1117010b00c20300d190045420008480c212144c001545c3e44a242517641200460440c40850514010394414602d01c0c42d901d02c4038003d0b1804420030900c62801550303001044580c00a2460300710070106071061307031640d80c504145866100317044400e078810040c8003103c1c0d002e40d0300c0e03c00908448140e0002070020f0441d240510040300c0101004851400c114000c0c803080120011320488520f150000400342c80e000141c4a42c248032500658040014180d101f00ca450380e40d182c04803d00119103e403c856070b000c4c10016041141020a0720b000411700564039010351000c1c1d004444207110360706820b08482d510600501041c0d10028403c0b4034510401c03072018000c3c100030400c07601d40c01d00c074000d0301241d80c200414000c65500401074401c1d10988105512011112000248455100c070000c0c03001000000d00408184000a280c05001c91021820461501e403150101c05900c000c80300c4400301241a10300c2607041c00c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 441846618 1250 441845368 441845381
    0x10c0c0c150c0b0c0a080c09090f06030102130e090f01050903120406020d060b1201080d0207091109030102160c080703031b03020f1614060301052409040609060303120618 75
    0x10300d4034003800d958035034440f00c2c0c03110182d130080483c0760085455001d0720b400403075140d0000300105049042900400001d91045401082c004903c1311100100d202a1403d405603054410000c80e0f00c443c8588030030010120b044116078142161080740c0072140801c2c01807080901a05405d0007551400d080503180c0c009215001c2e01c2105c45580c03c02c140024004280b141ccc60240c0b180100565440c565a000c0310010901a040f903092600641000d00201c0e4001401c9002c54a091070042412030790080a100c007070240c08812030b0903500010380c415008918401030020349200f00c0512000720f85541001f0703078070042d5000c001d0128410b014a129401c61401e00601160701c64812624600c01c203c02c0d4a040c4815134801903102040d246051201c118222080c1d40500300507100c0c1c606542c0341000040c0b0440300a140f104280240740140300c00480c028040380d003000ca01030710074001d45540c0d4000310001c0c2114482500041c10340c20341c0154154250060408032210081c0d0001624a51380711940280003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 441847868 1250 441846618 441846659
    0x80d02070b120c1c02040303050315030708100b060904090c060f4b0806120a0809060702030f03070507330e0f090a020307020111070f0308060a080307060e010c0c0c 72
    0x20083d00c4e480681c00d00080001e1751099488589a0600e208100211040c0b00c10b07082c032030b801c81d0100348004200050a00281e40709048045040e15000d404207005204101940d0341043c2080080c500b80410300b030301c0e0f00448510f5511341c1c208100011007202e240c3c40c03810308040c500c10003401c0800188110300c05640c0400c0201c1960050204074460542840d070a280382c0004550020208501071030042c80c18100e0009040141a180b40150f071404c03410b1090ba510f1a2007018041461030954030100200c480c5100c444040ba56508a2070520681d42c104500c14080b41c020242e88000705003134040700242620301041070018040e047d119040e03c44840f911401500b241c03000715140c0780740d914046420b008503c130b6000142d481c180302d503000382035802100107103d40d100200003840c0091000713146500e010750540742030030700c40d00d030480000c00d1400c0542c02030100e03101c081151824008a680520403c00c441c400070441401405400e40b1802606400545000002c8070100302002e41d9150380c144003031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 441849118 1250 441847868 441847897
    0x60f070912030519021b0a0317031806041a07111504081e1312021e03030d0203071808070602030a0e030715080a0b0402031005040c120501080d02070b120c 68
    0x204e0540710044034000302c40c850006034008a500c1c100107030f4000c00403950703840c00c0c0c2d81e03654454216183c01d0403141031030b00c066001c0f01d00000040c0030700c121001c04100012240d01503070320314242824000240c0c50344400021126100901042c1c010b8000c01a081e100c441a81c00740c01400050681c0d100c0d0120024030584040000b000040384036102000c0c182000303425095000e484954501c0610000011703500002e6912030b07a10000c002581d038050705100d03041690902101c0d4900d80d180407a0440c0100d011110703510740084107114845800201c0000d40e62110320204000594850307106580761914490760b000740e081040340d521404d00c1100000741c0601702604464000d81d403400e2000c8458800c2d9100d00c0022605024031290403002d014000c0306080c112000e50540c140f5640361250303a500d910844e03200d140d035141c91201207409140941e00c0000c09610400c09503070744440d40c0c1d03160b80100f120314005019442011644542440a40b180b050ba40c0240980c1551010442c420b6980440301404800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 441850368 1250 441849118 441849127
    0x130f09020415060908070b030c0c0a02040c051b0705060a0f030908030a1401060203070c0e0702150a0501060219050a020405064b0f010503060f13060602060f0709120305 74
    0x50700c60307000d03910045580980184100d0714114005007400d8541d0800c903150f82001200304400c01401099a801c0003e00d96850350360b03078032400e000c0d240214500000303400c1400e00b402c02d10140c0c1c00c0000382c80b0a01c004c40701d078445044a207506940354889805000c0e030240c4c052105000451190345201c21160460400041e801c0440e1180ba98541045030400308250300e50741c9c0030521885204090340140380600040d401d0032801c0d03603601d0381d1600d2802900c003940030702c00028070101c0c420003904003136900001600000c1e080140c8410060602401a1340151156520f00c200310120703040d400507505e4000002e03096a004c140e00b0800641070190405a000100c04c00b00074820b014510441240c06002c2c102c25600c0d20400325030382c88107070b042c440036030720401041c1c0c07140d00358542d1034030300c0703040d40092800307541d40c1e074800d03001950708141602501d07003295a4030440750b00010703654414000d80d807494084034040d0743d5580340e01c0340c0381208075100000035400d00b07800c20070a6180b0a0780f02240d842407c1c1076080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 441851618 1250 441850368 441850373
    0xb0a0801050a050726041b05100309060b06070b15180a1a010c0b0a150f0b04030b0c0412031d06070515090f1b03010204151d0d02130f09 60
    0x949030162481c41500fa503502c14003000135040314150b5444126009000401c581c2054009518000104050507250181c2c1403000c0c080d01380c050420141c5030040030151a061900c8006004001d024401c40b80d8500d050b84c159031301c2c94440242c5a007540d01811200403a0380b0445801002042ea00c0b112341c01c0040720502426114507400d22034820080b0103800140c0200390011880c841d0700c14001541400941c81004010845542c0007540c000414000440c145211a02c1c0d040000c206a0040e503006c140c950300440d00201c0240107208490041e0000c18142d10b4a4050040030302c200e01c40c5d100e034000c100900d00001381c0610602092840c0104031059000050380101d20307194000c0c2003c039015048501100c4500d08039803c210b410040e40d00040600c080440d0316990b445a501081d803d101c150b0400c1c000850743c0940484000c2d01c0d042c054440c0d41d442c1e066020b004002c4020b1450940180d001180f60a414078100301003455800070300e441d40c0b401008441000415880004e489400c0e16440480c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 441852868 1250 441851618 441851621
    0x40e03070f1509020607030e1207080304060305010503070b0909130204110301150f09440706030b0a1406070b040b09160515030702071518050d0201020604060b0a0801 73
    0x100c9030095000c0003420107685864810005082d400074549854022210f0144e04d95030241d83c1c6a680c941000c00750b072000d100000b0110340f041e881a00c03082c4a05040490301040c04401b0748201d90f0383c2e440503c100d90f02c6400700341c0c94000e54003ca8694420038441c243c02c5d4a000c503d0190800040204403404806a4000c039043d188003035038075400c0d40380000c0104901c52445450000524240c50841515189040014465a4075216249400140040c141220800114000d0200070400d000c111600c0e40100c8030800c1c003050782e003100a98014880000b03942070203805040d0702080010a9240b005040000412a443e10040c005800c62001d010f0780c4000340580344154060760003010036000503e4900fa07928a08007a0200c1441080d0240001300150b48401c4405a044642e2070725803a00c0396100d18049140142c0b903032000e002521440c00c0c8114007500540e6000c42c14524000115119031104e0a020b503d42001c00e008ac016445000081d000c100c40b64009820b056006114060040e030307440c101030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 441854118 1250 441852868 441852877
    0x603062d0923090303040b06090711010504060c03060506070f06051302030a0302010e0607030e0714010c050601090501030209070c0b06190f030c291e09040c080618010f14040e03 78
    0x501e07500000403500c081d4846507254400f42520003189503140c5942d54400000c0c0280c0814054051600403d015500903540390001210000007001030707181508240010b800c3d03e4170400f01003840c1c10004603203820920308032511660080e0042806030070310f9807408024070000b0728803500324200340040c0300165010b111a00c090750199002060a80042014a040c407002501c00750038145000e0440324074100110b0270404a904143e800e520b1040d14400603610345030780d0079004107203001c2c4100114140c6403607030041c2d06881c000c3c0c40b0000d83d41c1d15094140e440f0421110054480007010000410501d4045020101403d800b00c3c01195940d503104d8440c14044103800031518074000036400d00512110082c10103d0311111162810252510f5120703c0941c8a0109050324100040c26241d090544d0300c400c031888140301400c2003113006000c0034014000c0c2000e0b90407a01c1402080c4451000303444245d9201c1c160b03400b00d10041c02803444c0401818240c45440682a045501d5a2464011080510151 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 441855368 1250 441854118 441854141
    0xc180d030503040501141308071e08041a030c03040b13080d0c020f010c1e0309050a08030a0e07060813050a0b0115020709060311121509030901090603062d09 69
    0x490b00c0307092914105080d41e50b0020600800c640180401030310030078800c0c5070111603800001c0240d4030b50142c2850301c0e5407041c0d0744050319034400c0d10441104101001c00188100c918003041c40020b0141c40ca00d0050a00c01601d0304d040c800c0701070020034081107d001599800104013825440c4401440e030b1000040d420442e0104001e90350303a440c0da41c14940501141c0031980303841d0020004501c11032005056909a10703d9003198928087c060500340303000c2d501c5071544c9a000070490b6200d00c6e051500c0d90380e60b4030407a6035852145c10240b171805252800100790050314066201c0381c0080d40c4500004a0310810709005688901c113160902000c5a034040049020341145c01c0d401d512500d80000107490310403a0b42c085c1d858640f8010042000c139000050640b030b8440d00b2a00035200301c1419000720702d09050400961011215007080c030445110000c010b103034250081e201c40c0400703aa6000f00341d049409512807069154039000d00107110103400041c42182000702d60013810a50303200c0026100f25070341480034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 441856618 1250 441855368 441855377
    0x1021014100506122814013803070e130501050a060807050f030618070e040b03070305060a090501090c080f010615020d201006140906090c180d03 64
    0x5000c00d030340344801000302400b0107850003494842046500e1440c003800520071003000c010310110444042030200303940796003120810148030842c4118141d0007095028800c01003441c0c81c0c2d1095010000110800c0f102d190310030860100400c40f00002214a64402800c2c44204841c008200d011982c40c018041000702480c1800a0710350f04080512140741110b8005c0780a01c1608410800d0b403d50010468002c0384404400a03280c0e2240008101e03214050000940c210301c40d0001c200c821396101c1c03140c030b85103102201d05000b81c080d0f0006043d142c0d00d0703c0c0005070060300b200c000941c48d1f014603080705042c0e6100b80c0001403601c040341c0315044940001d411030320064101d81c05c0009503ca0034090480078019018174802e1624090368041e55411803e0904424481c10410aa20320a40da60314181e11301251019101c809084115003401042d107400350044811400c1511402800c100a18902c68007018240e00c8850f101d9114000054100d010f010102c40d040d1702020006844140b80401030600c00d496 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 441857868 1250 441856618 441856621
    0xf170f0408150601050c03030103120e0901060807020d050c0a03320304030e0306010e1f0e0901092120012c1009080919080307111903030909050601021014 68
    0x2224400312501500f014108032082c00b041c104000013008603411a980001601000508a4410745041919080d070550000d00074000240f6035800a80542c4100841d900761180a080054107607800d0041584181c1154004182600028000c4690350040034212424a4002c1d00c03000c04450080e048400c0681028070100c14030080641011106a2010003100600440c1d8105425003d03100c81c014141c4c450380c0711050320702400d03484444410028099680d10a0041d1070b200100501916001d036007280c02440f02501203010740150896036914030044ea81d4407212001c4261012010641d03081490000e550750310504510515401c05001c018210021400c080c7c0004000182001d48100340c00d00c03500c1c18000c84000141070501112003426007100c800f201803003207400711034041c2c0da20342084070144800a004400e1000c1402d825401e43c0c401c81e00b00000405540919150340401e00c0002c0202c3c444003002d112004031500155805041803041f504403c0300303c500f0b90250f882e8001065107603880c000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 441859118 1250 441857868 441857893
    0xe0115080d08092e0c0e10030603170c12070c090524011206050a080a140718020702180a09020f0402090f19030807051005060109030f170f0408 63
    0x803403001400a035007850402807a02403281615504d068210350300b01c04104109141d03200e0b0840300010344d109685020040c4000e44d170806403000d0f20101400d889030b1204450490543c0c070034014841071f60f501c02d02d40790301101103446c2c410190b00189403240c0c0f2400707250908008000f4040140200501400e40b404000c0d24140c944001c441d4060007143c06031040c0100c01078458201c440c3c0c800f64100030719080101d200c2078003055006010503000b6642c0300c80214000540b20b9400038050301c407140980312909000b15551101d50381c90580d8400d03c140300f007244a01003204200ba50288c8006400540900d1200034400c0000c624400c040f5950303200c45564000305025030500b02d05441d964101070b50110700e44044000051584a0f181c06428480c5d00d9032404c607a00f03580d240f03c070344005551000e2190f884081c07519143da2524901100301d41c034a440c00c2c0c0090f1031507100c3d10390b0600300d94100707002d00140e140b25148e9802504000050b01071154040011b80c4500550100802c02440300034090f001004070348 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 441860368 1250 441859118 441859123
    0x7030b090316061a0a080c012307060e0d0e100503040203120a11010b060f120c0d020712030f0504030801060f1e03021806041a030907150903020906030d120b040e011508 74
    0x500004e40524030f01c0c04284040b0200142842e821902402e02d41103c1182c804a401d203201c01680040c1c0d090320104000d010440560403202803048200150342d450b00c1410001c076a1fa030b85001050384c0c00b07a0190801100c0304d020b03034000c5400600140c241e400000b07021342009126800810311100240010401c080c20b00020311507a18010400c8910500d03081292462001600a286030f1100c2284004042a54031601400702c0d03110f82078442c4195283c42d0107080102c8510040c00680c2c2c0800c2c103100c184898846613124280c030842e41a00c0d120016401e00728203d81c0c00b0840e050801c00d01c81419450140303c624244003442610966a01607990900031313015841c001c41d205d00300c900411040c4000d000204c1110054901c841c08000301d80e4803507030b881c040b49140c03028030340c481d00e04001c1d9a642403403003551280d07103039003981e000713940000064070384109140d603995070b03074412500247d03460110310148860340e00980041c0000a10109450912600041c01c4900e0a0403184605103042c03030402041c0703001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 441861618 1250 441860368 441860411
    0xa0e031803150c0a1206080f011d0d0804080a050d06080d030e01060b030711030d050c04050f011d040f0e060a0c02011b020d030207020406120b070206150307030b09031606 75
    0x910b1140042400d010b0f81003052405401d100c0300a000601c00e00c0d00300c220482e4004402440d00c282241d0003514100d24850081424811143e0342c544801820f41402174005000c0d4105100c0e592614565a61501c509145410000c0c0703030b0702001810072a00c0b0416a803802644003400921014060100000d10064200e034030000c060b202503414a20b0401000c3d400b0030036a41d0102c40741c04c112203038280c0c858000b03081d0b2082d01d480c192020302d0f00301030156044014001d4415a40c0a44803003051116400056681d411070021883da000c90126804985003015001400d00c1c0501e079001092401c0011845401c054080321400d0601c1c1e501c40c20140d00b19424003810b1065440000f148941c0000c2c0c40c0000e490b00d144004140c145900010040c085440300d07806000109078000f001c5e0201c00d01460704400c0c80106994038801413007424081600d01103498900054140010300820302113245507150002c941c8010300c1d800282c0028880f03402030400101c2d45900c07081c86540d0028440d0301550b20a800d0400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 441862868 1250 441861618 441861643
    0x13081305100c21051b07060e010e0f0d06020c010c0305100609030201080403080405070510050909010806071d03070312180e01030804262514090f0a0e031803 69
    0x300100c1c400089030240300440f903180003500001d44031000c1c01e901541e042c80340f028070529040d02090544044280031401790705554941d41d41c0e441c1000500011a66140c007651401d500c801019400c040a24000350b142401a200300d03000360400b00b010981c2030855007074a41e500e01080e281c0b0b00b0403203190707030131a2102c01500c3c450030030740101800c5400080a13021300800040c14400f10303c020800f84a4100903460060100600f0240d00c1490110010059004900014090310f684d800100b10064003188552080c50140d8400892140904480c02c1e01003000000c950503001e00d44012003c9003103080340700d404091903250300080d440c0744518640141e10b958000351405142500510001c1d00c900102c501308c032850380010001c80e00d80034011207905210703c0d4001d214403405c0c5a005150704d50385684106030058504040d4034581d102d0101c84400d00c01d10540e90b1064000c40040c1030345450300350f05508810f02e44400108003088410b6286075030300c109032444035440b50440040e40ca1404008001c940b01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 441864118 1250 441862868 441862877
    0xc0f1f0506120d050a050720010807111209012717030403150203060117010f080f01090206070b0702190b01030b06030d0801051203130312080615121308130510 70
    0x41402008680fa548000c2e6940b0411000040040300f0703d2007441546c0b43d00da04028024500749541e0a201d8440308407000d414082119000080d1180b4007500140d1030089035013010f444c1c1020388107140302d02ea5014018941c14400d0440c0f2208805005440785407814420141c5009040c0c14454006d460b031141d4451001705078801c2200344005107114a8403546554011000740e00d0361141c1c00165042056402c001c0c2d40700440100024202241e4603001d01121699400d590410b020b004000b800d0360002031020b504000308024001c0001d200ca902140e0110182c4182c4181c0d4840c50039003496484000300586103141f01c9401801484200403815804c998210001c00f10041350150241c42039005115281c801c000c0c81c460102a42d9041c4101c84015071500120501d103901ea140c1105010a041076100014200100050145c100859505500c12176089114102035698801c40d0601d000103144100407070422650f0000902c0e810f0180c003048420b0700c0d81e01740041c03c0a091001051000c00e1400401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 441865368 1250 441864118 441864139
    0x91a0109080f0c0d080f0a02063903151302120703051302120f0f01050a0506120604060e010902130c08060f0a060503040503070212070311060316050c0f1f0506 70
    0xc00000b28072002241c00c0d03c03001100112030034100e0fa50b0040c44000c000c001400501f998203254041007561094002a01c46c1405581c2d080d0311441c01a61034506480d10301982c103003c81030311001c01c0a16880b19604003200e180f14448030118110980a07030f140099a40c0105502c90040c040346005c0d0361001c060300c0c0401c12890040f10a180c1094002c4019000d002a45c0d0908250340043c0204483c0f07032004000c92303201c040400c280c240204070072601025494a01408900903207400600080f14aa000000f40700d56111070310f90b2402884400c00743c4025643e500071a00046e164441c69500b130300d000007400901d0300075080c030150414100409403446032160105200959603040c502d141680d9407481d005d5100e9070b4610304140307035124a4402a500003203601c448402c0c814001000e1060b40d20541094508040e5132040c04120301040c0c81d00c480609001c9006d641c4c80303104070060b04c60101200203c41d480b0542c01e005900f001810400d804100c120907107a41e0100c003070b501030036400c90b40540d941c2c1540d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 441866618 1250 441865368 441865393
    0x106031112070e18070e030c1f050d180317060f03100b0d060203091c0e03030a0e010215010f090c020a050a080a0908070b070303050a020304020a1e091a010908 70
    0x3403801080c55042c8203c00c0d000440c16120a401c05600c440464005085420600001343c012108502c038180b1078460b14003541d499044c003081c404411b120505c2d0b071900c0881c00b0601030f01c170307074000380040c039400c550710745e01441340780e1107401241c101c03500945a00107030801309600114400c100a0120b40540d078404101c1030130b0784000400e000012800200040d208800d000010710210441e2409042c07d030000c814010301c1d15000c00c1c3c000c0c0c1c5958524003010354041c902010380c1e2940008508030751581080c021407031014064014001081014416101080e050307601816824100303810248110200b014107200c580300c03901c2180230389080c0c0c2c00101034445640c1c4c0c40b1591000c240000401c410b401203010700d045402903604d14040d05001042e00d07186e81c1c498018030f455820848064000030308140114140c1441e6201700e0b0300650300a4803a2900504005600144403080180c6490b40e9012034400140030041d4070074418585060a800c004444101d0001400788a0760f4100d03084030b400101c205000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 441867868 1250 441866618 441866647
    0x507060b0306070909050c090627091012031715030609030c0703330203060103060b0306030604030309020102030f27060a051e040b0f0703140f0f03060a080a050601060311 75
    0x4881c011704012460340c0d1003640c8841140039500c138258110074045822000d030502407054070202d03900008000c8000d00d28000304411404c0a4642a90304050791509003c9400000003040701c450081c00c00e0045040d026103640541e40702280c403c8105c41200761868050b2400348100d58016000b880154105003a0035200d6482c1c0e959480010b015001d03903031184134140d02c0141d802d8408410404803003841b441100c011006580125145030002c0c0c030b41072011901c084840162406083d0141c0140030b280e556540643c0100384c0010140e066120030301014004400d5403000b844060800d414191190801311494004143c1c201c101030701c164418020b40060960003c00c2e01d0f010800540c4d81480311001c841401c01c0b500c81ca07040f42c5c0401e240007800802d010221002060782e284a83c0c0d5026800e9140005040f49008134841034100e90f000700500400c01e22007801654101000822038100b85564020b09031074884440f030100c0c3c00c2e0304607030010091127070144100d00d07001c1c111501c0b1524009001800c0306 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 441869118 1250 441867868 441867887
    0x901090204140607060e0a0819020607090513060905011409090d081f0506040b12100b370915110c0d03020a051b040f0218060f12070507060b030607 65
    0x60243c540824200c0a000c0c0641050303100040c00400c1d01c4003024a41409030240d0300000303d00040c480c4070390070024038520026000d84258065540e80201c14200380c10049054414150441d4590b15103102144800c190710640d0300a01c00300c0110020f44060700305100140d007006002d2486600940c0c80840310035007048003030350301c0b07020080c4003504094602a40c2c6004d03100750704019080200400e0118407a20301100408207244254074140c1941d80e980038001403a900350040038803120080c45542c000c042d80d1040484140303030803083c01d10784101c51050703565030101071a1403d0001d01105420855440c06203040c403a486854501020620013004240359940700e40104213003d0340c1d00f64684028184240644c0c104560b200c1c042d90401c06021503e500c1000b080d12085110710310340030842e00380342010710132200442014030410342c0394503104c020490305410415618406484c1000341d04554884191200d10540c0d15486054480e00c150030100c045881c407062302c50288e48907400b804105074200b400b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 441870368 1250 441869118 441869159
    0x10219061805060a0b12190308060a050607080a09320402070503030702010c090f03031e090e0f041a010b1c02090301062607260109021e0901090204 65
    0x1092150903540760031122514503001500c0c50143c14203010040382c50303030032000c61356200f1101079928442c40c00780e094030b44010036809021220b1441d0362100280c0242d0347c181e84907000810425045039580d001c076280340e1001c0c1040395007440008c4d2038001190040440000740800c000102c1d10061031020301c0d405c1601d0180b81e09120b034200c0800011507a02d9404859013560b0100607a44c480c148504082d028044034035a11002c1f4640715004600711213404510012242c047e6290118850844410429070804000d1103003080514500450740c141c906142c01e00030304002c011080e00c0e140a0070070710030140c0c496040f410303448050b2004124898a09042e6101b111404000c00703125030680708418024071031105c070aa01075007000c8000880900c1a4110360042d15111980c026503460180d9858940491340941403a044604055410380c020000c162240c2c00c1e07102d000001c01004c9070b00000c6a901c4803c600d89820368120200c02580d00f0045680c41c018441c182041d41068240054451103402d07400f0706 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 441871618 1250 441870368 441870371
    0x51b060402030a1103030409020d020a1d01021009020a05030303011d0c0a120c11100603020405130f1b0f0b0306010f0c030905040b150708120114010509010507031107090b040b01021906 81
    0x80c130300d644d42e003417084800400007000c0442d628401501c19001a4000e02600404140c0800038001e4200e070949030981c05e10416400386c030894120107039020050403c41ca0a9170416100400460303252000c2008501804000c504015601c05281c08021998401417800c1150b9200740a4021130075045449011601030040011a00380d044c9442150b22403e0b9100d00c882e148901c54400f09004200e07484001940c0c001d440a00036035494101e001503c40c2ca00400419200c512800100829000340c1c00010901c03000c0c4060300c0d82c6645000c001d5119400760014800b80c0d40c00018400e0075070308106403031541c508030300700451f0300c004940f000760801c0b070303030344600350046454003e24580c507038690302c421081c99401400c0580321416402c0c00c00c1507130480d0846003440403803a00082104a01440803d141c1c1505960741c03440d010500d4011211900140000c40522044c1c800856042e2002d0241d0806080004000100d0704090420801610700402c2100c1c159007100402014009140600603686500f2140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 441872868 1250 441871618 441871643
    0x6040308030a290f010305060612040f0c06030c200c0108070c050106030521030c09010f0c050f0a06110405010e0d0503040308030708090c060a020a110f10051b060402030a 75
    0xd00750060a2080f50040410b1451008880c2e411031501000562680580e03a04141e90242c1c001981140c01c03d4500d02e80c00300e828800e50750f00400070040304d42d1141c07280ba0341038403000c826555404da08a2913089580070a458110082c0c0312b81e40b10500f5604100440e0386040110200d045644d1104808400e1078100204100080d40c0a801a4040080c595004008100c030f40da590070b0258a0b0440c5110850a01c0d000011190b141190441907034060100d11280381e190804110055840d030b4040d0190505024541041101007030b01800182c120548a4019014400c610310300801243d400e0800100181d50500090045980c050009844840c081d12100b000900908009143d4000c03030740000c00100c030000410a030280e12008980c011040c403022a40b03e802071b801000f040d030103242a498016848072550b000490086100401000c2020f841c19110907440c07000302c1d82992504c44a4800705000043d00c85420344025502c2881d544890080c200c2c5041541c00240c5984054901810300324609a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 441874118 1250 441872868 441872881
    0x1080c09130b0a060507050601060c0201120903020c01030b060414010c0c0e0c1b0307021003051f0b0702031c1b06150303030605040b0904081b0c03030a020115140604030803 76
    0x804852000e00024200000990150741000c080c001c103010460060440c0f040014509003c1e10646103001e0f0304c42c3c080c01740e030303802d0031011036000c0c40d82c10040c1e0402400000800b902000303032107091021350099004c2c11031080303003600240030790301d80b2501703e40103003070801081243c030050004030a0036807424078008a68141e0b03400c200041c2a07135504032480c44001e503410700440b04015401801c500d42001301c402d29080242115948030301503107002a400084a80c1c49110310f07446030b4445644004402c6025030720241c41d14211510880319000804002400640e0100f03600e4100011501d01c0d42448201e035801342c0f240c0c0000c000d0344400d29403c2c0098200061a81000740c075401034071995103400025980725984e030800070702415107481014012031031301203420b4007801c20f958018840ca4205103075924107070f403100c0140403030140ca2040000501945811084070b90302030000301081000e603800427461203e0729000011061103031384198050811720f81800b03542d4031020242d40889411080c4d40c1d45030b0382c0c0c54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 441875368 1250 441874118 441874141
    0x9040804060c11060c060121080301060f020102130803040513050c070305092803020120060411060d0207080306040b01050c0d0c03170910061e090e0309060301080102040810050c07020108 82
    0x140f241590149001c940200818400200581200d200901040c0d01c414802a0369100171a0300710040c100400c00c10050255034041c02d5041c40107006880014540141c2034447c0080038480e400c0100c1c1c80c2c00000701003190340b07401d6406c4d150b03540d41400108071504010400041901c1036102c0102400004100070314070b40d5804a11607035050b440052242100d41d03044800500c010f0701e0004a000c900f025055203843c61140032010100541e80b8002d0a5584494451074200090440c0b86d40c1d003c4801c005150009100b030028082c0d0500c030f005000d850b800e0820800c010b456029586c00c0c1000300a000d81808000005850384800a140c01c0680702e921903414200d8141025a1003084185110000d01000c0c3c180042c083c58403034490801001441d40b0754000b8030baa4000e94094100d413820000052000180c154003d1414a00c00b0085900c4c11501c50003085480c0c001340d0000c212a540400c04001c65441800b04010000302d0000800c1145044c03080aa403030300800401a040280520014071340d482d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 441876618 1250 441875368 441875393
    0x90509040602070c03030305010806130b04110310060603050406060e1b0706060302211e0d050c031204080403030f0c0b1602010b121e1c1425050c09040804060c 70
    0x20610003035a81740c807400e014006d443c003807198142c1c600c103810009980364454410001540d91100d165000c5407690380b00e090f42c800310300704502c1c0e06020350001c0384070f0030f507451013810020000c1e40c4020070985400c1c1031901c1120080d0748117005603441c5000700881d1131078488409541d10151414182c444100342084030051015802c004c3d080750382200c181c00841003010003c85080000350441d04503101584c8003220410101526400e194049000c1100e00c0380564058280d4a40031801c880c2070401000d2180c001810a45e025102d90b40000740520038103501481c07402d00c0c810310b400d28070f14441c0b031965561010700d00101400104442c280b80e0915140c803e4000b50b06141c00204004000e1135001c19040d00c58420500c14090044c142210410300d00c4081881c0038050300504990310442110320064607400d1070312540d0030742070108002d0400704811200b03091865516107004407031241d040340352441c5450000e1540303d03c516074070300c100702c0060f100b10204c0b400d8440ca894070382d0043d0185c1c9800b5060450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 441877868 1250 441876618 441876623
    0x602041214070605030a1812170a05010b031302011e080a0b01020109020312072603070318051e0a080f07020a0e0c070204200c01061a0a09050904060207 67
    0x100090080058203020206034055030461070201410740050b03650301080d12915001c01c1040c0009100c200319540701e03043c01910740b20040417140c01c90b610100f1000890304800080b950403201482c00c14201d0b0300c4940e0261241c00200304030b50500c07144002d9404020890039107022500d28203406c59104011810412044000c3e21030f100c2d8180d07501410305078086407880742071454084188411340c414050b0f44d0029030003034007404151641403130040860f8003007001030741c00c20960124640044400394400300c0d510745540c3c03429224103202100806451003501c000300c20505c0c13651284c000c40c80100b007106101285400380c480c0c8601052565003030091205010300340a80108040120560f448020007035144201c0d480341045441c3c0a410741841d00a480c028001d01d000d0103c5001030801c0c1e445002d580540100642d4030b12050503507444140c1c8205c002780040d9444500402c0200c0c6040844074001008204207030400140100c000c01241c281d21a81303200b070389900085014065607174125940545c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 441879118 1250 441877868 441877871
    0x1b0b030f0103060c1b02040b040207122114070810051e09090312010e09070302120a0b060f011d0f0d0f0507090603020f130b060415020616200a06 64
    0x5800d00d40181081824801566058245490b06450078801c1481850004600c190100404c889400b444010441e851303042d80c00070b908114031804241d0003038900c120015503030b0b21030751840c0b111000440c40c1000314096040f13003030130a080340354600104a500340d44075009240c041038a6440c00700744030b5200c1656000e00c0d0006100007004100c070005910340c100d51380080e20824040d44a0640c02940c910401000101d0014400014040a00846031050704007840b082100d48a545940010740e04641c0d0001c0884207a0145c1c0207401040081041030fa4024000c0310601d00118031000040e0111465020200d050303142503841080c2c84d41c48203044580031401410a1052200520341038411a0ba00c40042c0d655100da81d5000407141c02501454054a502402201c085214403051001d4000082d4440e9221521110000190b44544e80a00001c00d00c80c0609400c0441100c40607040c484040c0043d15020307a0f110515044030380003030188000c005034805101c22506250300807810070417100002080c45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 441880368 1250 441879118 441879121
    0x2040b04060609050a0e0108030304080a09030203031219060501022d1903120c090905040f0204090b070905040509150408190e040612030f140405060304080d0e0a0c031b0b03 76
    0x142c1c002400c07800d48005031498074401d501c440005c1b070103410074451903115030300c00c00018001520100242400c0011424007500080e166030000c2d043d50405426000c052031a0010080305681c26a91864440c1810f0303000c00201c0c2c10710000079104d04c0800d40d440c621008002c2c1140c142c4091802c100c90103a280d2060301c0780c0a45800721642c806403603000680c0095071039004178402c05020720508299000f00d4480c859140e15280d00c000c080c10000744195040d90b8088160300150704c5502803040800e01c10908225245440324000d003443c011900601d020790b1030704041144620000070007200e5803680c0c400801c83c07a61130b460268124480d02c3c00c15400400720a50a0040301c1d0000078031b54010f442100c052003065120170481c0d41000c0c00b04400f5000030300b010b0101ea8560700442c1c080420340c101043d040e14103034403440894000d41c003e49080b940084001a014254584d52043d6460301d61040d020b0800d8a25075180c08e01e4003200d41c000a010f0303820000c21280d03540740c4140600001d0400841c465200d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 441881618 1250 441880368 441880379
    0xf0f052a0f0c0d02010b0102150604110c030d1d0d050304150603020d1b0b070305070b0601090807080c13050c0708090303070210170604060807060315030b0f1e0f01050d02040b0406 79
    0x84060b00000e0303c1c09503003080300d000032540c000314510580c00020701d003014456480c4001c03c009048124098a00f00c141089402c00c481c10600c000d1008045c803840c00b04284682d4401c3c2d052203c030a0b59541d2a940105018280181d80700007204c3d0000c2d000b48900f000341c000c483d0f040000b05810781c0001d6201390041840c104001c450030b00000c484154200c0010030554945011502d0304c00c416005001a508101072400a4002010280c001206140c98540503031900344142c81e141d8a80c0040e101540074484068542c0f41000400c1500ea800d16420f01c4141070840d5601e03c50302880e08018a00d100114084442ea01c0400603a49442c0e00200310003020402d908002e8044078400c40d000e9014030400d000141141800d0285600710381c5001e000b090381da442c080b01200240158060400c081e04211400404030301000140c0d4000d071031343c01e6190744c1400c26800045160070600d035900f451b01044010094040320129840f811940286c4140b03040702c1031403000130000e201804c1600e51180c035000b000300c0c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 441882868 1250 441881618 441881623
    0x90d030e04111c0c0509130903020f100603050609010213120602090d08030f250f090f0b370302030421020f0c0609030a02120a050d030f0f052a0f0c 65
    0x10303c0306a0410480c041503203808aa0302c1c03240c42092500080c000807500c9094020340c1c001c52656000b80f050700d0044041034031090401420558440c84a91280390074401d101042c010941c00c03144800085240029101c0704580745e02180c410368910150000011050184540444524140041c80c88404070b24629102ca039580003034a41808101b0305a0000d481803060b031045180042840d58980d005086003d0b0403242403280b00b10200c10006d06000020f03d0800080810014260891005403203d4008040720b00c0c0200708504a2240200007030009005d0b000e108124030940135908c4c02594a54031810100b45c0481c41c0310001321941065900f0b001c8844c0d0103d0401c8190491409a401290700c160400056010303d117074496040d0800e0752608014509909002c0100a041c0e0940780c2c4948203858803400d11ba500140480841c1d00c404002c130050002c2e10038017047c04a4400100414100000c24203100b080300c88846103c0c041441004264000e841c0075584090b11f0104c00360f940e8a40005881d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 441884118 1250 441882868 441882907
    0x307091205070312080403080402091803160209070c030804230a240b032d03040e090d09031e0314040b0d0608060601080c0d0b15070215090d030e0411 66
    0x19150041c04c000c6052030b038462100a40165090703580c0f841141c0303850302041a002d801608400c024941c00f001200801d0741880542405a20044030b40548000350041c0941c55600038590001c1110072203a500c00a0b4210000742e812a82101407280340e4070004003501d00100302054140c45a10a40c1c1209042143c0f1502c030804484404000441c03d0b501928941c054642c41c40700e0f1545500000c070700030a00000304060385010309155040c00b06c009034046245007140d00036000f00a070034006204100403440100001004000d4624210514034550340b21030b048807000d140400b00b40d00d018110a0285881a5980341c0003d0f004c2c482c040e500c6075a0020741e4801d601440c2000c8842d41030110020f9145c0d40030898520800d07068565414599a000325140a5481a0701c1300f0407003a0364026001223a1101040c0c1080c1e0001d03c0615030b80c8048500422003a40c00e540c814410108c5c08200c10004c13915420888460b19605003088200c8080c00c02c0084c0c00b80c07002100461141101043d13080c03c6000d00d801c80c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 441885368 1250 441884118 441884123
    0x60e1617010b100c020d02040612050708120a08040f1502031e09030a090b0a2c120a1112071701020a1106040302060f0a0f050a150503070e01030201030203070912050703 74
    0x70804072901c2400e000f8561039041c0c034480414099090600941410648031004600c0180001801a00c4152811083c0755154003556107a000920901501204005216141903a07004076400c004507890000c003001c00040005145c088030814800c01c102c11820460b1850003082415910ba00d40340345a100d00d0300e50b2402c1c0d44a840c0042020940c40b140120440c0d0110140c4d507a0491200d00b418ad442c09107521280c250400c0043d4562038500340032030021146201408594405c20340d81c0c004003000b50500095a515240780c200403180000500070b0980044200015a080804000c0040c826810010254800c0340f0000141e0b5000340b001e0010760080c4803002076600e516151060740d0f842c9a960340400c503401409a804040494803803507800700302503440641400c0100700c0c4010f188004080d40c400f654598011070329003590b01203c95684a604001e001d00350020030b6502c0c501502d280c4050018400a03050590020100e01103074403071214107016000351144098515124540140c0d2204d0500c400e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 441886618 1250 441885368 441885371
    0x12031b12030b0109180c090810140618010611120301080706141801080604090f05070f080a0f020f0f03070b0403031409060d1a18010503010f05040b04060e161701 71
    0x1984582d44c01200e032003090311900c03120441c2940c480710310b000040034451051014030010480001e00c00c902088a1803901250b00000700b401c0d50006c1701d0807000300001c0c094134864400c420240500c0709050740e00700c0c11540e1034074007080f809021805850420401102980c09804d000001050360007000456800b00e030700c1961820001a2002805c403100c1c0203951400104400d0401d401185610171181c0d1a00b02c1c1b8010070008000003aa9190141c0300c003411822501a002440e0421400c40d00207003e00c011f1503c0b10183c03000c082a07540c3e194a804420b1002071140d1524440a0141c3c0c4038140613010340e0001034104c910683e1160020308080d0010700c01100010702c01d1402001d1140740c1b0701072310b4200101812460820042e0040000900101c504001d002c03002030703004503225940d5031400c00c0d0415041c0445840b44d4100783c1450300f910960060919120f0816003403200148414420070350103074102e84000340d48900109181d04000c0c51104490003c1daa605000c00d00030802101c101007060314900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 441887868 1250 441886618 441886631
    0x70209010512100e1903030e07171011040906030c08060604061a09011829040e0402131401091a010e0a1e0909060c1b080412031b1203 59
    0x1082442c080241000e1403a40164480c2a802e4146401000c0241c0151040e0784c0c130303603a12504281a1841e2130200b50300181d129240000820700c1400440080c044440c814410a80303095880c0c3d82d80d080000f000c4080c5640c59500050111001043d41e000c1c041240c8144031103692814241a01c400c14007030900c50380900301c0810028038140c4a04d00031110465402c0c480c591020412000a411440815051080d903049112124807910303ca1009054164185a00c0807694040b48030141380680f21116114030401050040c0b450485009a01550454150102c00116107518000c1e09175072820415407810707440081a4240c09402020a2030710030307410410001d048a0045504500001c0403d4000c00410300034064580103075203048100d80d408600e1017400d0b554a40746811114045c2003600ca095480104880b420792100721003207a0380c000d54403181005195281c4550700c6c0b0844c401c0e9800724280da41510101806014640080c14154018400c400704034200035983c50081f003148000a443c018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 441889118 1250 441887868 441887879
    0xc060f030203091504050a0204060303230715150e01090c0314060109140117010308130b03011a07020a0915091512060504031b030f08150f010e130e0307020901 70
    0xc01d03079109583c0d0384000c004400e100200c1810100300500143c5217801200751203c00750f2100e00030030005501c0390355940b17900203c5481158455607440c9010600748000c10040c000304584000006450750b0a98001500c1c00c410f0710101035003001d5500c0a070003141c2080000030300040907480b00418174015281404101d580c1c00030190080301c22650103000c01c10240041c8403000c07841501c4078a242d811b0510a0250508550340d0465070802d23401112081d0000810000f0b91301d02c0e800c00b10003000a0002c050942d412b0140a0000c4803503441018002c00b00031074007506541c0ca16000700006d05501a0810800f08a40d1491412030300ca80202055035041c0302800700c4c2d80400300c0c5e00d0b00450308501c4001030703440702d15134902c4040c0c807002d801681000110091642e01e8003119a010182a00ca52100c541402c2e180c400a41710090081c54210103515840742440103031281d0002108800007441e0803c407191341440001c0030300b00c40e4140b0070305007440c14010040100d40000200000c0d40221618141a130b0b0343d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 441890368 1250 441889118 441889121
    0x2031e07020105031f08151501020a0b0c03040c18021314030a0609080c0f0a030809010c120f1e090b06060403081c0f05070309300f0212070c060f03 65
    0x1020090000701d0030400240c41c045540c003a0f50a0030040b40d0344d0f2450540d86c030384a0346003554503401400748031958800d000d85101070444a2076603c8003030000c5d0401c6a2680c840200709000100001112040000040c3c2040300c00e00d0310740003a1407424045d1440c402000d42c50002500002000101781ca4a40f0300070800c09100d58040022500040050241138aa036072a60041c01443e01e045813040c2c018060001d0410381402402c8020b40c0c000000d00c24000709040040c804240230301201c04592400c8280e6284503441548100d1580c0e24004c08160303110882a480010510000c01c40b440e1020078020710756100300e603000131901a006107440c0c2880d4560004100d00c0c0c0c859480010f00c1202e0400c8400c83c10071220456410a0f0080c81d800030307043e15014031070310075102e0842d60310b00001e46ea11012000c00c4102d500718441c1000b071103406141c551420400c030816190000080301407104804000e1380551080101b521a144001d150545840c1175261035002c02199010720004038000c44d02150241e4403e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 441891618 1250 441890368 441890377
    0x4090b15030f1e0c06030a020a0813050304060f0c06050c1c3e16020a06030c08240a0f090c020a0807080310051e0a05010c0305030114010e0a0602031e 66
    0x2400740c90740c010941c032402c10400c000c40011019006002100d100d6640d5070021b1132298074454070150750f544450f08010680d04004203101410644d62070090041240001078400380c8046040000300b2000d41c10003543e034000043c4004200604013003c200403d0b601901400e903a0008944034546540c10b0a0104140c50750030519030002c003804400440d40720002e900744c4801982460308843d0a5100c000f00709001e6005080901d401201200c081045052100405e80282503616003003004451150000f4034503c000b4005802c90010000c025008241f1200c10b140001740043c000034002c2c0e9507031034007012941e40d44210010507290000c62109070f0300106401506a51000c0d105282900c550f48074101c90304090105078607c0d00c0a034010525844402510055982c1c40380e0407c04868181d040105e820100d40107503042011948407000020b40000a617819510802800c8403144d900d50300486100d0318040340f49510070300e035100c002246600400104411304101101a41112240d90b2400c118400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 441892868 1250 441891618 441891643
    0x41509051c1134090b15090603041127040c0f0303120f0f18050c1903080705010902040c0c030221030718081e061b090904030e04090b1503 61
    0x2031601c800f04415a40090005226001c0d12828503004007000b2000958950000e103d0305035140d14460300c1c3d252502000209502c5070940e00e141c0f240d50300119155000162008246030445c46000044c2da90320311000140810000301000c12604001410304074840c166802d036030109005c2404a00fa40c1c02030780600980317415485014031804581c5c0084010b100c5030148505050b5100001095200d10340181548031401034101c0b4205034407414a5800c00540020081c030070300c1e0214003131404001d00c400d00c00440e41c00800d05500c4400c1410300502428801600a500c207103410601c010094020441c1103040c1e0290b4215940900002c4440c0417910b1901840e1003480d5040c4005004184159801c4d003544451000c40f40801e5500c076a0742d4548805131140710203800005801e2424010100000b5901c07241107190400500c6c980605280d90b4170600c051346004916500004041c18000d11029138a5103010700200141c64060400a42e40302e0b007569021200e620855000d6101d01d4001101c0fa0f0901 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 441894118 1250 441892868 441892873
    0x60c210603020303030402150408011107052e0c0e04020708131208070f1e12110a02100f0207030c18060905090d0e010e060309070501020105010515090603041509051c11 74
    0x80306c58003001a40504080d520304202c40070000440d00c0034085c040c02003154025500d1544404561a0030740c00c140800c0c43c040310300401c0b4600507120b07107840720182d1200900210b0010306002044011508a041103051541040c0002142c2d401c01070b10070014a110b5135035140152220f600c80f0101e100540c07a845e0043d01000080c0070500c049505c8200c8480200d110381c900141469001d403003042002a0007806036107803240e442c2079100c02504a4101a42b080200c805004080c1d05076000901042c01c0440b40e00c1008085c82c107507050315008004820107590001c0e0301110440c0c2c0c4c2d0700d00c44c003821410102c89440728240b500005800703800d0f00665001b9410100903060a10042038100c1c0c0c10003020f00d40504002942d0b0041000d0340301c01e002180294281c1001d0081c041c1072400280c251401a4007072070142c1c07444040721960701c201c0c4055803540a02103031a10b0352911941001c0070890032510342109001c4c5001c2565042040010301c1202401c460b0001a40f50300c60150103698042c1c1e50704c01c0d400c3d142c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 441895368 1250 441894118 441894121
    0x150402030708060c180616030210150f1701060b0c0d032d0f020d020d02041d040302030d020f1c0516090f0603180506011d0a0515060306010c060c21060302030303 71
    0x40a000101705c4a0100509030a003400e407510303c44991401c1a050a41c050380003a44c031154a11014005c84000a903048004110b1600e064444a00740c0c20500c182c8166404d0100032071004442074001000628400c000c6503101d000034801e035911440c001d100400464038040c5003103403c10078022600703000c1c3d088000044003910400e00c0b000140240d0360410541c0ca60030000c8103030082c03161001d070a040c43c50580042c0c0b9141041c0c114084022003001c060707115491402044002540001156059000d07a038016032030b107050608200b403e01403140c42035000c40e031212111002d000c096100f5881214070031842c0602c0701c070400069510401c00d026036000e00307980200178044140a900142c09003007100b2990040b021154031280d0401800780c004502207151111022000d011941c0801c1e000000d510b0b0402030382c100500038160040c0d00c41007150003180c000c0000340e0300703a024038000803807a6002041848818040740d00189280e82111703d025a09102c090403100015492080d203054035400f80055185 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 441896618 1250 441895368 441895387
    0x90f010e15010302060c0705150c1605030303070c0303090b01091b2a0309091401030209070e0a03020d081b03040611150606160503040306020307030e03130509060102030c150402030708060c 83
    0x955221140c4901e00703204547c400240340d200e01028000b9000a1031a840e00d407843d5400c41da091103c020540380700c95984102c14030481e9004803c80e074200005081000744d40c1041e19054024215190019055484030000020111205d4001840e8821044461541c081c1c20240660b4018006001c15510401c907110401d480300c00c510000142d1030003428882c0d08039550340903c4042d2202c0b80003202d00c1103500c0004008608086101b103400c00350302e0034042440e42c4050b01050403a0307690710001c0d20900e04408080705109281c3d003107a0314600184030581e60202452072455480c1d01c5031190800007680c9a015001c009070125040d0100c0f40c1c0075400f1a01600d443c41040f07001d4101e00b03d2000020304a482c04c2c00024410070040c00210300c2810096103030b1801500140072a0b4007070f01c100b15503400421084c5010703545035003410182c4100302c690b81825102c00c00103d2660041c041a11424414080030020714001c0c422058032840c822003c0b2104151194003417500d810098590041ea0901480780e80d07003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 441897868 1250 441896618 441896629
    0x180114030a050a0515090a03320301141918110f0d0501050132030709240f030501030206030f0408160b160c050601060f020c041e110f1b030909090f010e15010302 71
    0x4161150001d4096040c84240c121842b03502c20f90044ca0110301107960b42c1e07807504000e8100c864040b0074140c00c9a0310b42c0f60500410384c0700c40000f03090f07244075503694000d10b518507184c2c290b880e0000c1450b10261160082846940140028040c0d140851030b140480e06455042507020042d441c01c1d01c408101408030301c00450303810707040a402130050000e4401d01103003022100e040d5940342158001040220480b80e04003a004003a405034034010541004010300140e12241d003207d40058107405418515580d03414a200280030768038150f10341e581d110440c0f03000d104038404080d0117158100014002c00c0701d44d240545440c8508036000300203030080030040141c140980c1ea441513941c594015102480302c100001421500003c10319169210b19003040700100311345100e860001c07002c03040b07410700d484003400144c40700f4060500d100e0420240010b0070044103006105850007004050030b10f021506000c0c0403e0b80b80d0b4001105644190310305a40103100f1803001903490406030300200850341907401d5809014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 441899118 1250 441897868 441897917
    0x4031227230d020d091a120613060b04051807080112110904080301081c02030913020403050d0201020316080402090105010e060c06150a05180114030a050a0515090a03 73
    0x180440e44555440e0a032001c2031090800a040c26070292402160b0304202030b04030340b62034001c135140c000c800051b8060366444404954201c40c12885003000d5683d03104c001039140c0c5a0172171000e007403400d1480009141813600e01500640304202c50f4610040003540b48a0a111422101000060b11400040244646450105c20328500a54440312511000c0010034255801541d00312803000d400001001000800d10078000e90150a0410445142074224003e6490007190009841900384c0090340359002050b0781150015a808025140310001044029000f0f4008035a54401403031a06810112544540e224a100700e81c014201c1215034200001114035800f80c50300c15402600410090700c01e1101049114802d08010110110301940b010070300c144542c8580c40b0034020714800c0908026a050600b0f043c0c10344988001912031204054002450582d245c040582a40140b43c2e0f0702c018000c010aa0030101c00748101c003907002d40c0303410300c0459a4004014010300000e6140c140400540004600b01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 441900368 1250 441899118 441899153
    0xb0f07060e030d053303070603050603100f060501091d070807112b020a080409090305040320010e090411221112090609070909080d0504031227 63
    0x10b03401c3c51450040c2c10102e90095811101403520a800400e60509640c9141d161948103003503421003a8201e00483ea545003940035103000d043d12000050382c2e41e10100401c20700605101b00510400d4036954000004120b80d008660000301100b10114000c101c100681c034100520203114036041c0d60310001124003403000340c03010040013825640d42e02204010403a907002c20b150080044c125110941c04009141c0c65200c4020a5421070706002000c25510000e444c1150100c00e00410305075118a0222114825a00004d0500d41c10203500e1205a40840c0c0c0171440020a803210200809000c0410001407000c44004015401540c0e0803001070501007049501c0c4654103d80d41d401c84036250145054504ce9908141609008184074401d01500c0d4422604100c1c2c600103441d0303504101c10b10544a03043d6000d0040d400f91905188000c01c0069070442e940780119110800090500e440c000b00a4070202c1c00040d9668103001464944001c40d848425190080709845c50b03194501d03945000c40100f00304243e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 441901618 1250 441900368 441900373
    0xe070509060712140309060610020c0a05010e0f030d020d030609140a0207060b090117190b06100c0803100321270e0411010f030b0d03050d1506020f070b0f07060e 71
    0x10785130b4040000f8055401083c1d404060902842d01c80f0071310200030700302486003003154050000070000ea102d207e0281c0c00d480c400c0c43e01014041c104400b00c0e103007a000d070803501d030540310f4981c4100c4100c1d03010846c1094009180d605024a6544070b20200a0320626040f11b84c0003034145020491071440399008090b107620818020908031048800120790f400e09a208a0028104022110f100b19042c441c0000d115821340c1d400c0c0d501c0c0304503100c1d0543d070391000304804c1c0a035020045910000e07020701c80030000585d000d00c4042c2d803807602c00c3c0d0813180740c5114482100c0f001143c0d01c1c4e1040d0078228030a038651590040c2d448080ca9030b8100c074007031309102603000360a0303510000309008a102100c0484440c4624014452540420341040004203082c01c0d036040c03281014580b40300c3c00e40c3ca41d80d810f1a0104541c0601d85251074480006908000742461942c9000eaa0010040000d2490b0007003000800d045541c1c0945642d0b96442030900b006104510f05c44000417810803000e000110079a2100c010040035004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 441902868 1250 441901618 441901637
    0x6020a0c0b03181f1425020a08041e081f27061d0303040308010501080415090f0b09070803090420130e0105010e06161e0b010e070509060712 62
    0x20680e0410401134264044204d03403841c1052101164002d085041082034920303507075071408003006458580101d45081110705a890207a01b220b10070403030310040c2038000700b00319665540c407254030300420703102901c100c010102c1c004000352006d00071514440c0910511410048450b00104a01c000c102e08044071061011942441c07240003428075030409400d204840004826031980039903058903000040e0399500e644100704100001e503104c03140c00e0440300d0a082420403a190740c035089448003088100b0101c400d203008011800d00890214850310076008401800054a80d050156200d50782030242c508203034401c0012260600303169100013040019011030320501c4014080170992584002507203184c0c11401c07042444100b98811101d801000d0034242620b0309608403001c07400500440c0304056410021283c241c0c180300340312404e840302610b00350182000806902c0e2030a0300000c28000c00742d100c44214005000c1c05d018000303c1710100001410241011001d03a114441c130350640d002c00040201500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 441904118 1250 441902868 441902911
    0x118390908010c08091006030218040816050d0e0f15071b2303030901080a0e0705031009060b04151a04080307141c141809040b040302060106020a0c0b03 67
    0x80750007400d9032a56148001400c2c000d20301451b0131948460908101e140820030001039441c03c1c040c0b0405690f10170f82440301c0c2d56a092001c002e025140040c02c2403903010007050104400481c01d0005041d090700d420100c0360200c0180050b0010394001c0701c3c0c101e040310001d9843c148401c8040c24145d032054011484400280001000c40c074460781c01840c0780925403880c0030324459081c0d000d1074030002c144d00840c288008070000a20a0744080d01c1c108090360342d501c024000b0b9100380280d2018140190895507946c0710302c074142009003402c00c401c0e107005240146d00042d500c1d15016014100078100403000c0303524245548840c1a0003000c1d8104020710b4200301c001003101c3c0500240950f207010b080b138a4400745400900e82d080000384054503c607a02e03e03c0044010f643c00c1220f0900705850030103061b0300c803540700684e06802040b40441c22341c042203910070041000128604580300d030f446507080d18002c0e641c0f1041030383d442c0303d00000108014004601409900400e00c080c561000d00ca002980030981e015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 441905368 1250 441904118 441904121
    0x5030c070602151320190305030904150e0106200f03030a0606020c0a0312050d02032e06020303070c030c0803070f0f05040605070b040614011839090801 67
    0x5074840000350308501c68076248150b021581650110308244821041c05007980c0d1320b06240300c170000b030aa080d0113080700054191101d10250010000100a117094179480c0c0c00c0c031564030b03008420254411801c00d4260741c1c512089040b064100c6642c0c007029041a401d01c84290b544d20403024841c0110041007007903038454803041244044524481d80038541d01c3c00c0c101c400800340ea0203034004909660019240c01d10a0702c0d03100c0c1c40000c480e0042c580c46100040c20104403010710540004181c494004001d1010608030141182c0d07032050041c208010135507101821140c40318203440340c2400f40c0c00c01d10000e14014012021a02680c1c820315110844074880d0b544c1d4940d5800969400740002d4240103440e0300340d42c010325001d4241e200340c100070b401c0c0307858801e00810303602c2502d0004160120090200b0208070003604014400c0c4c90240d07a10380c0560311400d01c10101034401240c40680c42c01c007200c2d000d203041d40c1290078031101c40d40c0c841d10000c40c1549182840800c030b0001c0304001c2010010300064400780a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 441906474 1106 441905368 441905383
    0x1e0606010f1e050315090c030106210f020a02060105041107080c070e0103050a05060a183203041e06080f070201110d02071203060509010501030905030c 67
    0x12004100c940c60381d2000341c0302c0140012219810740c0c6810102a510074030024112000039103c48042088001302075900d00c83c0010708100620403540700e0051030405070040c80102c0c4298403114503401c101c614441124900d55404140c5440065040c0b14840c01481d0480f001d0049654042c0c0e5125588599640204140303030001d01c501400b902803100380001e0001070465010303982d5034140f60f034440450f13035411207060180e80001600740c0755520a6815100b02050108948030035680c0e2580413a140d10005107940c01030340c10b640103c2c8400d0030071851421171203014540300c41c80c2101042d4000c080000c95403a06401311424080317980e00c500c0580e8010140703603c080e1141c60301e14040c1d0051040000d418880d20700000c0b0050204503640080807c14450000400e0400008002b20200c1c1c6050250541c40103911004004562098001305d00d05401042034a29050410344444e207400e50 = true := by decide +kernel

theorem cover : BRFrame.Cov 441726618 441906474 := by
  have h0 := BRFrame.cov_init 441726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 441726618 ≤ n) (h2 : n < 441906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
