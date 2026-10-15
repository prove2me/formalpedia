-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4456
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:40:34.924978+00:00
-- url     : https://prove2.me/submissions/b4f139af-aa27-4d4d-abb3-5fa219d97cee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 801258992 ≤ n < 801438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 801260242 1250 801258992 801259007
    0x15181b070501150f0f080106083304030314091906020d090203031603080105030f0d03090c0302061204060e19141f0b01030b0f011220070c1d0420031606030507 70
    0x1240070342e4102601009460f0300018818800ae60240c044049101e01604607030b4510400d49401b003a20115104100926400da4458401801c1d00d1201c8001070f51481c400584850550f00e00640c4003a0841c990800700e011075014100007070440e1030002d80d00003d600001d1454104500c401d119903601c1c07504400b0143e01504440c0100401da00406001400980c59a101c840f0410200101036580d00c03a41d0601c400d0380d0031500219000351203190780b0400100c10408062089034251121402c280b03c004140707000090380e980300805250f110514500681d03070988486100340110819100d04454041100c51400114071030104580c03001400c0c016043c0054240c4421440451107201c9038101c1026903608002001505c561900002034007080c51030303142e412100080d61b84815800c02242d00000c001c0f82c0c81c0c23000c0c1982e5118001c141060800c0d80c4083d01c3c0101180c00401d40e03000d40388880d09074080036031079081200005040e901d0303501c43c0c203404e000b1280c41c40d8843d00c006910741042c0420141c10829 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 801261492 1250 801260242 801260249
    0x30c0c040915110409060b031e1306051017030c06070e010e0904050f06090303040c051c1b0807060509040f051005090403031116030f110318030304030204020315181b070501150f0f 79
    0x4a00800740b4190b0fa40d52180340a9000c05031002d900d42001a088049a4121001419002d86c158005104c1c40e00073b80ea40f50001010158144641008103a8850045040e4401d01d20141e5030080700a0f222018020a41c01c050720407641380c0300340040e02800c0801803003581c2c420308000c00110784034075141c00c1001e008d200030360001d8014507040008004d00700d0210006220b4035005054425484071141c0601100242940180d0031030096080100f400e41e448401440a200116014403100c22001845800c0700c500303492499040c0c0ca1a68100050300b08401c1c550303402802410f000841d01c1d42204480b8542d40040761802c0380701c652100c0c19003019005030352070b00c0292251400c0803110140542c801d176240f00f45024210301d25410320404079140c2c0e08008490185034041c00940d04c0303040c600080000000003e003a2480b90081d2801c03610700006086409109601c411a42d0340524504184c2c150140d1040105480c9952100407040c140d140aa400c00010045030541c0c2c20103030310300089503003072000580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 801262742 1250 801261492 801261541
    0x50301030201020a0308060d0b07030e010e03040b1b2a011e0801050405060a03140f0f0d1215050d150506010e030c0f01031d030c0c040915110409060b03 67
    0x520240c3da0008503000c0807a81030601c03100030b0305d81c8000610268889a0003d00701c2400d01b00300042d442c1d15810088100c91600c000f03000308110031001030340343e0040380241344034103406200c0705000d0401c02d08a00c01e070b02d4240080d20222000d00601080048011503181380b2230000211010032540d000c80305110500301c1c01c02034614440642d400400920042c451280301c2d0391a04017013075807641e032000781d100296400140c07814034604212589844080c984951581c030f003e100d0480709a040042070075070745407400b0fa0700e1100c0000300707000d0480208000c1c003004010003440c0070f0100c0d46403600d402c0565000d0090008030700d103800303d014202c240c0e500204401d0400c580f00c400460140c400190426140f00304403100500c90001ca40102c00518420f101c1c025441d90345000b218510202000030654484c107001501e480c03d040c18241300650300543d8000784048480251241d03000c626038080559000032200366482e0030f64500f1100c0980c3d0035900711508803400002403080e2819016405140810100b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 801263992 1250 801262742 801262747
    0xb01080609040f060b01050c0d0216050628021011030603010c05041508060328050c060a050307031503050d020c01030b10020c0907030219170a1b050706020d060306150605 75
    0x2a40c0e843c1050f40c040200070a665140e0210800c141c0c041c80c01c0d074910000510448942041e40103000355144184180751980505401021a0305d04109041b0b03492800c4c00400c0910300100c2e8130058040030f03c0700001d0070440c0580c401c00001d42c5506d000c0c10400d025040506916810541f08041c2110525031001e814010108020070a030040030050382100d03a50760802100540e00d0f5400700e41050103641900c40502c108110101914914801a2035060700440c02c9425200801c000d0000b58840e40c42c031940450010720000f05801d100b50403c8000d1026814605240b031360b00d640701890103014420740c101513040040d590308156494420707501c0e440d2040302c45000e8428118400fa480c3e00102c1d070454041c45014000808040c081d4040701da901e040d14040750644480c90000514a0340500d030030708800e6403e040030980745191805656140c00a0b41401d1f079100a0004054419610480c0100c0b07101e038090024070040d454601c078a0000314020359020514500f011602d0348403901035040f071030030700006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 801265242 1250 801263992 801264001
    0x30a06030b1003110f010f03091a04050102030412031137270e1614030f0403030b03010c1e1205090105040309080610050108190e0c0307060c03050702060a210b01080609 74
    0x15200010700580e5040004070f800d5075003805200131802e000346e842c11501d040184001c00cc0305500452042c0e005055501d041c0b560201c007102a500000881510000c0900c0404824488e0034001500c200c0480c0c1c5410344881081c408131940785c0130007081408034079070503040700411521b050b40c54500c82142c0c50002007941001e00c0400c1c0c003500070748140e8211004807290b0b07240c1400350007049411800018007a4487ca401e03030a41d0f08547c0129012800a4107240340c01d00642014080d4100004030f84e1200b24048807070700802540d010710a0b0300441044130843d00340603403010f2441150700440303485001240602d4a03041c0074120140c0ca0344802d48a501482c1081007c2c24540050f0090743d800b481d1003952074448100b501400c07807911418001d2185403102c8030790044400a620003102400b0f0342034504d240d50b20b40301a035078056080d41c0900420000c20015005240400040800c1c040c64240780081c0ca0508414003081030008000e00e8140b5034514011440d581c005408540c46001180c0c021090b241 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 801266492 1250 801265242 801265247
    0x50c06090d12020c180403022b081512151f0b0313200901090c0906030216060914010e0c01050d1e1a13140408030a06030b1003110f01 59
    0x800e80400b80102c040c407003450382c080e8400d10502c0050503000304041d04407081c510328241c841c08251000c90141c4650440c210f00903101151100042c099101c203440700c030591840940c3d1104001705100f20034680c00b1403504441d40c82a01100030302003c1402011030711201d4903603904000e4043d01040d80b00311801c191200c0f60200c010007105880b00850f56545903118a103c4071248030f4404402030944506151036042001c1c8642c0010585004459501007039a84420600442d4181c107038641c0000c4903400203022807806178001300519484104400c14058041d01c0d150101c601c409801c491055a020161b03d100500740a1035524440840240c0405030a080001e040c1d44030301e000d000210764a407150b84110030072040c06005014401c03541440109414842c2080403a000b11016105044060320400c209400348a60111030041c1403111580341c48a490300c074026040181020661510b80a004c800a50320901046c0a107031420011701086048d89001041c031190786114500400074540c88040b9681e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 801267742 1250 801266492 801266509
    0x80703061e0807120b071b020a0e070f030c0e10090312050c120903071703071a09150c03010909050f01110904050105030606031203090106081b01030c0f0504030602030c04090f09050c0609 82
    0x850780d081c0358001f060401481283c0c0742c40c03031174080c0d804125102d0000e41c110501c24843e106001569480035411403440c029402c5036003200094000910100100761103003024801d00440721051304000741c074259640c1e034401d000d0420f988200d0015030b0114002d00340380820042c20213820300290308281010003107004282e1b11199032050302c140c0c034285480c1c812000c509000b202d90301da41114100450341c0c5452038000c08094282e9521210344104070600c802c2030a088100d80c010448140d00b1413550b46005e009002820b00580e066515000740500d8008001c82403142e004a01c5102000a841c0c1000310100300444005070301c01c501a40000040014640d00402c442c0511400e046582d41c4075107410b00c5440c010400c6801644483c03140303289c1c01080302da14015010b03001100b40c0c0c2c28070440000b2081114103003c1c0301400e43c0030800c180024400122140c0103194400d11500c001403d10395a440e04805481400301c4404c81c995031041e520080c00028880c060049100f6651180340488070700100e000032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 801268992 1250 801267742 801267751
    0x2130f0b120c0c06100608060a030b01121103070f0e1302090a0903020c0406062f060103110301090b04060e010c0912021e09040b01080114010f06080703061e0807120b 73
    0x403282800001c011010402c1030381c58000028040300d5551500c8407290400d202d10780120b10101c1c07901c00020b0301901d8140798150035654491000c0040c0e91030640341c41c003020341e90882141e0560000c490144941c5003044900d0090040c004500c01051900c8021038001c500981901403003001d5006440158443e2188203402c800310900028802034681012801c1440d1b04540b182e10508101c00003982036488400100b413407041010a00d082e122a50315a00030b15150311103d1f5094000c5001080407490440c1040d600c00e50181c0003041215141d07480b0114010200c40446041d80e580c81060300d0724000340b1072000e4204060601022150510714802c0b2034105017040284940c1d40406011040c40c0c1c4e9149980055401510038502400c10b072400c1d07228090300b4002c1440562070301c1c0c050203480c0c035075007000ca040390080c803400100c05082c004100d55805c0010f00b14400c1c5a00c506002602d01d8450503590003409454980c0003c660400c030341c5500348280d540c0310020340e00182c0d40b00d0001c04d1911420a401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 801270242 1250 801268992 801269017
    0x10090f1a060702131107020312040302030d0c080c01020f040305010b03070e06211524010503070309210e0f010306181e0e0a2102071a0d06030602130f0b 67
    0x2c5060700c0c400249200c0c0c207080010f2400b82000309104070307261403401402400d4421010740c0d0180002031409002030141d440003940c5503100304c01c900c0095006403218180d9a0180a0305071426004000381800e99100c12210000003800207070800502030203100ba000d407211300f10040c1c4502842c102c60070380c050388081c007103c1c4030b19031010b00c07250021142081205580d5254091b546034a0402101c1881041c0455002401d4550040c4c0303800181042e02d0f4060013010705031540d0b03045480300d600882c014207141c001290f04260f1400540b01c007211030b210540074031089039a0322000140f2101803100068007980781d58141803e0040a1000751441a0340c0001005070050014042400f1840d501c0041c254049007080345140403841c01d2195800b00c0d56080c164059030f1035229401c005440006000310900b46000107030841d6806000e000c501940381c0761000000058141490a1003480c0c6c02101e1a5600484165038001041c3c5c20300c051b9148c6160042c8040c4003510304243c03505030044414031400000c03206 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 801271492 1250 801270242 801270247
    0x70b07120507080f2d060108010e0103150903050c19030914060301230604060809010b0621060f180405010b15041505130314060a02131e0e10090f1a06 66
    0xe4004030703000500e05280e010098000d640c620070329800462442620b509000641000000c2b840204218403541225405116206544182480b250040403140d2046081000410a0707440c028404c014040004000031542d14401219190140c03200c0320307586c004e140c0c16500d50324903601907540105490441e214540103080700301c1440392404680d07600440c23850f40a0800305010900d1540b01c0503c0d481001614020403031001050100300f1540103185036191382c6105000303400c0320308220142c0e06030003000240958030710f480002e0000f00303098201e10310081d20081000400041c403009002e0048480c500ba40c1c01084402d5410390115135100b9402908403c0c25900394040c0c11b00c1c03040e001c803034281c074100c440070203900e80740d143ca840d14050071603019103144142008116003803000d01c21138514003010303100d001005152900440e090085030b4414130600105280025030800c5081807240318512106004020310304000d08013048030624181c0001c3c0c80d02e001c0c800417003c1800b41e5824145c1c901210080d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 801272742 1250 801271492 801271501
    0x105150304020a0f0b07050d09050d06150f0b0703020c04110a110f1006050f010f05220b0c06060907180e0a092f0603060f040917070b07120507080f 65
    0x401e65082c80e4030080b001340600c07100051038000c0002a1a6070382c41501541c0600d400d64104698a501c180036165000c1c140480b8540028125406102c416076050b080e0f000440d502c01000390481c80740d070310142c1c100d440000e1080415030b0600c0607030080c04044504001d030603245400c10344640203800702c501c01c1c0911803c010250b19000c1082804210707050003203904403030301c0f01c0c00c2c0030152403a0705c1018010382c0300c19841c002d25070060140400500301a0713582410324800316075a000b140403210810141c2544490b001c600d0710102801440030f850000014075a80c1000ca00303100c0c1c1e14000a107c1410002496003446210048640b42d00899a158089800e60b80302d02030150001d20200e100101402c940301c14004003440e00408001c5c5039002c441c2c40340104c02c480c01c05c2c41344a110407108540d21182c54100030b04645001da0000700501d01501c05049102042009011203900c042002d843c0d82c406c0c0d81c100811185d00c5252504410310b07160b018815800c008501400414010300100000100240003c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 801273992 1250 801272742 801272749
    0x70e01030f0516030507030c242a0803040c0f1d07031404030c050c0a050a0308030c090d0602071e020d020d08090409030806040b010504030803040b130b01090209030c010305010515030402 82
    0x3040d20355007803122402c0944d601d15046964014500c02182c4000e00c04030001840080080e4007948035105004541040075482001c80b0311183c03203000f0601140042444091800c2c2c07000c1d049110740c0c401e91110343e0324146410100c1000b15554401d5095090114007404141620480f00040c0c1d48025219030450b10b60406c142c01401d103402c031481c2422070f51400c0000703041d840464040b40034007840503154810201d0040c04542011030003000c0d0414150202000014500801107134010000074507582801e543c0c4001030046014002c0c1603139450f8012072140d0030302414a200560043c0186000d83d0084100d0f4003254079a503614102905c180c014294020078051700c007003214440340000300b080020760079914001e01240015215580135620b04550304030554011002c46080c0d07030b089040242180d440703640c1c440500d0401492101000e182e0380f00030b00069000d07625140600b10801000da01c404003001414034191043e000345040605000c0100800d490303500805241c0381e980f0741d0382070f50307070f0b4841c00071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 801275242 1250 801273992 801274003
    0x3021c060f05070c0c05030c0609191e06020105060a1202060313150614100507081305040f020c0105060904020f0f040e0d0801060207060201020309060703020d1b090611070e01030f05 80
    0x5072400380e0410007000402584250300a0403180310f84088540c040c0c8800c20b05a4849a21072040e401440402910000d441c00d04a070100c1d01600944003c8481d44400ea40d41c01c08080d5005510030071820002888101d8086c001d490340080103441c04880145011700d0106001070000c03000e80169000408141541010b0010405868101d24a004501d850500800080001d481031004031203940e101d49500e45044ca4045a003641e03241e6956090948a031100c194940c02000042503503505800c000480388c4440c0618084800f507802c0c0142c076840c07001d103041d0940e0310007050720f4499450034041000581c3c45007a8480405000d4a040c0740e1242c035400480d0013091628600d0040d485800c41c11880654003e4080341a551158265400c030ba40c2c42c0026402d0740003e90f002c030340c03503001440040da00d948658064015821000d002185245560b90307070040904040d8001800980c222038248801c2e6000200b03a201e43d84a400102415072500361140010101804002e050000c40031031481400010001d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 801276492 1250 801275242 801275261
    0x7062a02190308210108030304082a10050603160314030403060212010510020a03020c0103050402010e10080f0c0c1f0b0310021c020a0c02090a1d210403021c06 70
    0x10003210a88a041c1144143c1141c905000340c589600d0004c03940c10100c894041c102d80301035000b18119240c41c0e0f10400660016200440c0c0d101070303811003051805d00f0030207030021101c00f4400b400940d40c23400c1105c0150744006000303278000d034401d051103d400482c58031040d04682e00006038010708070760168010f040d4401d81c0c1c4050142070010402006840d8601000d904030b803001c440c1c0800140368201c05a0f110f06100708094050380004d0440e8040794002c3e04100e52240c414506102060b4000c00014500200f96002e90006550501040701611170700300c1082c0c102d070411031414100040b500c0c56030383d59101d204401081c00400104c5107512102900515080e04004080d07032041e40c0c0d4006004002e400035090070141d03413480040040c80304590f100319850520240d8445080754007503002c1c0300e140c000140008080300e81e5000c0e0601d00f8ac1d043c07a06103081d1003444002e00100b115154030103421081c1d22801e04910b01c0300f04000c0005985440361000c20300c500c040007118801141c10180c005002050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 801277742 1250 801276492 801276529
    0x3020c030d05180315010b0a03060b030f0402030c011e1209060606050a031401051f0e1c0b011d06010c0303141501030e0a0206030a0902040902150405010207062a02 72
    0x100d05107990304000a00f54040c08025440b0500c4000340030160350700500e040700d0101d5084000107100300a402070040502c61014100401e0b01c80c2c2c0c4018041c0b00c0e500480d0320701082c0102e1002d10003140781c01c1c8004543d000d02403070281c284180c4946840b0b00c0407503120303100060042c0151115420f1b40c41b50040ca000e01d8205200700005580d84074003410580c0700a90001c00a0301e8031281081242c80d900320f640c10384001074405010501e4040d0032061160104a4150a000e400001d180351540d407090703059681001074411029402c583d1406180001e0706820032500054403c130303084440040a0303e407a0f0310190900c0c0c101c02050705420f0540c010302449441501000340d400404c070f0f000d0b250041c007094010b820707038003008206149007155440328003501d0029070100c81000820248103076500061403260000b0710010791070075030f540020b0100c20b640d0101210910040b074204519a01840301000519003400c054a910050094000b00b40b041e00c00610310240001e01c80005645031041d040040c1e00311034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 801278992 1250 801277742 801277753
    0x114090a0c0e10111507021c020c040504151b02010e0109050316030909060303020d0914090415021b1506090403020604321e070303021b0d020d06050a06170d030903020c03 75
    0x820354408855044443c0005440303605408e00072031205280030b0741030f03600366070240180250703000c108030191002610075036030b034806003511010410700d5201c0d44541428000c81c1c40c02d0180c3c07072040a420b4850101c106102c41e490310340b440e00841d00c08030449541c000f480b008149042140d18065800c0e00450f0005030095140c210040300700340e00060085203222090701c8606140d0f03501c60410340070040344410b564000c103100011600140c203801124400302c05690016007400401156103030301341e2113210344140c04c1e489840011180401000f18a41004041e01d0380200c0b440c00da100a55518409031000b005054802e0f40b000d0141e50200d0542e0280b00710419188800880003200c60361141c3da44806107040c1040800140e80340000509201200d6068000d001d041c0b10144418507001c01711041d0540000d804030810005aa030400009051032044d00002060304094107418100c40701501300402e40b21000c800d200000000003403844c06200c407840c01084050252500300d08103003150705011380601c0380 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 801280242 1250 801278992 801279013
    0x60f0a0809070e01030f110f1c0b060114040b070503090907020a051204150302090d0804081e0c0f041a090705041802090603130302070e0114090a0c0e1011 68
    0x480010300540201d811100159141c501021280d10b00f032100801100340b020300310340044c0c000b84114640302c42c01420702042c11155004a002d092100905481612040140d00100a952080ba0740c010034280b03441100c503141f0b00181d070b41c03501c03c43c0142e201c5128041960010804100104d40500344c0242040e8411b040041e4043e50340c0d407d02100b200d450042d40301d090305401518050310111088035852404144021801390003e5200940140c1c004010f46000004241c2c101e00030310050580c540240a0315000e410800103a2842c6000c50150b60482c681c0903109913902e00c0c0c004444038088500054035503910502640d0001c0c8040001d070032480c0f80e01009031454105019000705d402c201c641160b419131a400e00000ca102c0c02c1c241c00d41c05001070000c01c0b0880001441004c8042c46030044842480d1a05450b0b11010000d138071034951426071032491840d41c200444140d4214207503d10170f001031403006001414480300030407214068518040440d0306203100340d510500d40e0040000303841e400c451 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 801281492 1250 801280242 801280247
    0x90905071a070312061e0608060415062106080d090f0e1b090915120105160c14060f01091413080309210a0f110606040c121b03060b120114060f0a 64
    0x1b441c3c840c08004c10400313400200c40d410940180f80b800007041540707505441c144141030340d101c00440030001032828030325131104030403140348181d1000c2c002c0c0400500c410300c11401c0c0100581156001481680d0100034204440d60115001c15086110242c2039200c1c083c0698184a40d03011381c0e208943d11400c05018001c00750b84024900c1c031000002c3c3c50307241a0a200b9980c050907104140c0e161114901461500c20740f65228404140ca951312984690301c0000425404074580601a94408010a03441c8010410b14485208899603602005182d58040c41c2000c04502a10304002c4085e01c0301000000003000c840e82444209442000c00940750885940381c84403551903000850b040000c00c000e01c9207502c80e039001b503040c1841a40920000c2640c0d94680041c0406031291411030030512121001007001103000d4000c0103080d417020602803881c0064104010b0648820b0703071201940100c00c00400da15a1410050541510211991200c040b0200e1020039154460040c1e9a0150800840c440c0300090303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 801282742 1250 801281492 801281549
    0x90b01141902070605040b1207020a0b041202070f0305031903180303150506070206042304060e1021081606020301030f0b0c090618010306050a090905071a07031206 72
    0x1450ba8200c4540b55152201924548034900a5001d088002c0c0040422590041031081e4030501510507200c1008643ea6046040c40003a2003c90303035025128058520b090b8108500c10081ca040005505620b1542d00c4854aa103c0c520140481c0071000106810090080d004481030440d01000c15a0802ca1410300400038201e00143c2038054460f283c0c00030782840c3c0341c41941c2d00260001c0a19181074680340c41c0c8238a0038441c040e9254045c50101030070f8900e07a11307480b421004100e03410941180d0b00c0d08000c1101c4806071908114880c1100d1b600141020004a1a2226080d4407080032a0342d4441840b084507005420b02004084500000002c0100304e840c45155000c07900c00d107000e84054640240f01c1219009500d6115089407040c4143d5240035040c0c14903040491041c14001809521040460128101c54000d40305080c0c4882c0d02074100041045100004d01002c101000c0c0c8104081e050300040c803810b840641002181003641e0326052060303012a00a0600c2e04403502c203c140075201c0700315030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 801283992 1250 801282742 801282787
    0x210708060606072d0204060603060312080f0c1b0105070519080f060603190903020d090603090b01030201180b13050901090b0d0b07020a051015050105070c090b0114 72
    0x40c012000807900d94101002640d00312a40703c545944510000ea464045005181e8100c44801d11a454540003603125841107001a14456501050003400c609200758144da000640604006400702044024070700c05101641043e103000c1c0c416a1001c41e250300c12800b200707002005040354640010f00030b01c01d8028000b0901da07101001f4000141500180c195008071044500204440743c1000103061480c04c08000c0d50b0043e03103a48518034810400e040202100e40d0340804501680c800d5143d104d452350408a400000d1502d4076040c081402565100f5103c0305c03041c88024144495042290610f200c9120204094a50310804949034032401450b00d0f00c0300154450a801003540c0c01c00801d850540f4003405e004000040c1880c0340c00720580c1d94250359810001d00c050118003c0a47d8840001c04c00d100c207401400c80294046a0940b011254200074540c0c1c1c1d014a041c40000c100a00019104100c40d100300c844608000904448140050b14500790b040340c000d0740b0310b1001403400094002404c10704401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 801285242 1250 801283992 801284009
    0x3080f0930300c030712090503031e07050304120503041a030c2d0a03090c3201030b09010603050a0509030c0c122e050c03071205062107 60
    0x81e08001218542c40380d410058150b04411001d649994803020806021942441d4640c03080c0f602c61107000d00340c20b5400004086584030f1074642c030200d90711b0703010403c100641011405146030410124907181009000300426032080784c08102001400800d2040d10000c2c0301e00d0341d602d04a400d491516039202d901c640030300d04150f40340c6140803424007a000103482c8283c2140c04400d00e8803800b00d241050007995804a903002c00507000e640c0840103112000340081d240765031004900141185000b0344040d2142c0c011072a40796812a04c507442c60340026110842e00301c2c030001480c1c021181740c012006000a42e02c0940c0041d545000040c0341c0b1780c140d11461061007030303202c200416125481c259899100d8401c0f00320303c640c02a50403468620303004880140c030030403072030481c1c030a8404114010140ea011040200a5642e0b09201680001d82405125440312200b06c001d0b2451600841c00b402c801c24421030245840c0d56070000030404c1d111340038408488403406120108a234074521071259502980e02802c00ca = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 801286492 1250 801285242 801285319
    0x25030f020a0335071e150f0e0f0a0804060c0c1a09030f0a24020c01051807090903080a020304080d0504080a0927050721060608070e090103080f09 64
    0x1c0fa031120710700707441c14141d02080b0036203103525890400758410300c425401c1c1d48441d69801740400789025072107088a04009040045901c00580052a0500c4a6020701100a4200d185c424000803003100072a401d6469605154445185a060000201009402c03a00d4411514008811200b00c40009014400301c02c4080366030000303042c4c03902500c2e00300369070300208900a1100c0f50b480d2294195490911403200d00d1005090841e250300d420309440003560034400d490110546001c480009000c1c0001a1688120a11010300941c0e0f004003100340042c0814000ca0f8080082400c1040d84001c0b1055001c111100b80700504140c18480415809508281c010401800002402c002c1c45088003c4442c040e0704040140546482103001400303005000c04100006407001e0505841003e0b2860411910100000b0707041d030030071802809010025010b0014441311500e4250550f8500364520705482d884440b1701d0721250340c00440c05040c09103504030755010031405103429004000110820b904185202d9261 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 801287742 1250 801286492 801286583
    0x9071203030f2307030e030d110a1e05030402040218210105060a080a0609020a030b0103050d08060409150b2101050a05130506010e0709030c06080925030f020a03 71
    0x90031000c1c14401d800e4003c600d040000c11540c081d91202c0310019003c0140c174900410901c00c041101c55100552030b5612010900c09020340c0c0c409500c3c0e406664a00001c1008000e0a034013400c5400010002031150303400194520000e041c2d240c03070455550028100c5960210000c5c2e42c000d003d03107240818401c940c84c0c500015414602918590121110030700603042801441e203480c40507104580e4281d0700502000b1001001a45100b1110300a500072406007095004c502c000a061290203040c042c8550f0420b03813440b003c036184e941496190010000d0008036051500c01017141041c0440c080c0a61416280c000d01b000181900030a10840176144100155611800c01001c0b0b000010790140c5558407080041c0281e1141c1107105401c04004e0508004182d5240d507501b1031812550040c00004200b00203000c3ca1750000c102c1e24065001081051401c1000640840c5814089100241100140b070302003106648440d54000c0255800101c114802035076200c084405103039512241180e0402c510000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 801288992 1250 801287742 801287771
    0x412030e060a09051228030806040506131a0312071e0b0606030901110d020405040c0206070206160315060905100804020a0501050d0b030703030e01020d11031209071203030f 76
    0x441e6400c1143c1c507211022402c040611003048007810080e4103e100d0280004034520000011110b00c984110242c020904607240003080144040d100d103028134281400d0007101d41e00d4000c0c02c01c036000c1030200052489d850002e00302c00c110915400c2034041c001c0c0f0911542201c40240100f10140c0220b010701c0c40c2001001041c1d041025841020780800311030310100344145080001107410411010020508003681c0201c83c46a0384150f4160095030707030014041005013024060044801c405002803e6076146c1000041d44603800280007071201c0c142401810100d0b40070b5031103035003820920039241421545860009c1c007411003d000313352080316242110405a031003008244d2007a540500481e40c2d55103005c00540301d070b41040c4606600b090302c684044505880070031420000318007035915610843e88202c000790038a14200041d90401c000c000c00418513003400004c54100c4009031b50031001540d0754003049410000950040c1484004a981c00000e050f4141c010f440c0c100804003040040700d203c401e04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 801290242 1250 801288992 801288997
    0x30702071406030c090118181103090c01030e0f07030501061a07050c01050d0b091e070c0305041e030807050714120d0311040504020403080403060f0b03060412140412030e06 76
    0x120740c40b03941000014008a4818045d042001040c10100c94094403405d406550f010740703070000c020300c05040c0c6030343c02c0e0200d16000d110b2001105a91a5245003406c1c0e4005841c2c010041c001410f040c1c4502c00c11034000320801c200304800410006950285403640f422a01034059880341403181c04406e126003880341c240800300d4260070752110080040301054001510b1a4000285004850f60f60f50b400d034105031101c0090912403882413824141114460707012420010000e071007002009414440b500009402204540650300e6011344821400851005003842c100950001000b04a011800004001c8009402d078152500c01d1402c0d2020401d00050040c40080e501d00ca001581c004005045600d00070f03400b4403a980b480320022854251164041016603205a001b1955240002001c0060100901c2024045812500c1c00c3c841c0c540000f00099417100e02034000b234503180c1030524040c4001d02803444111080e4401c85603030f480c0c5a0b28150f140340c2c20708100080e00410700303007030380b00ca06442c18404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 801291492 1250 801290242 801290279
    0x30d090b0610020601063009030507020a150c080903330c0f030c16050706050a2a03110f0604030c110111060c0702150c0105070909060b0306012105040803070207 71
    0x1d80f02d400c00a1762040c0e0000702e5a4000c000011020a13207c0c2c0c3e000040c50107044a07180c001d03110156503256a20501c4a821007546c05070b0900141c811071500361035400900760310101c1c0c00001c0540c9503144040081d0401624800502d0200000441c10701c140c21183c010144612420a030780440d50b480b203000801a01ca00c10054030b00f884100001560701243c000274080388408a101c44045401c3d50f510a450800981c1088004c5480480c05030709450f40040c00004450725a1548894941039100091a51041d034000409210741161404c0c1d540e0402c0200e4240ca04c5420304403034190801e070801400032414824107a6041c14034010300505940a40b8419404061900040200c2e0351340c04280740c091380115100b20303440494808407154904101010301200e01e1715000001c5e003410f02c000081c207003202581c0201d030000d090690402c21090600c080e254011000c0c2017003441540364503a1085c28001110301085039616000500c03080c0040500a18425020780e021126029120f15040055610508 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 801292742 1250 801291492 801291497
    0x512071202060a020c03150a1a150f0d021c05060306040b070f09030609061a0a030c0506032e08160e1602032505070611030306010809030d090b061002060106 69
    0x24210350060421500505030700500707205540c0f0309180c281c000380c20a1079080c00c6c02c168103841010700c01d15120521840003500110803c0010700884040421a8080e192207000d0604801240d54015024038004a8040c085429011542e86c080c0d5800c1c201c0718114070340c598107076519003000111182400203030079026903004551143c0c65034480300102d030287c545003071100030400d90010001c002405401520710240c03044501050031040310101683c01c1c0301c90000f00d8410481e1070010000320703d01c0d0346900151403040d11107554a95030300403100c15602000c2d02e04009414554240e26803074115290160540341c0484c20342d140c00306411900303210003d06024030340c58003241501040d0090340410b11141c18031610b005076400c0c01ea9110581401e500d00480c02020030422554540820009201d0324015051030b04040c03080700c100401c4190b40307010062980f4180310a990115548041c20010b9503480840d2107424403035003c0d41c2c5004001d00f001174550314043e4105464048480380040741c5203060b9503459 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 801293992 1250 801292742 801292769
    0x212071b060e01061802194b0c020301150f06050912060403020d0809010603030e012007180b0303091c06021303080a11161502010b0a030c051207 64
    0x252684001841c41042240482d07686000008a0103140900c01c2080c20b801c500050b21240c101449440d4017882512103401c2100c030900e41c0342c114506d423440b9529042054003a524007080900728640252090078103020f01e14854680c40c2d551a4000101c204e100d100350020b01410101018140a804050107550081c0001050030f00081d4440c902400c01140002e19101150007170841341410004266000c1c1d0058201c40b144044060701b1801d583e4210210400030407049241d0b440060141165604007810401d0500d2060050040203c803421900a000151900640e40d9055101a656810b42c81460749040c0090213201d0320303011040c8c1307150100c058940d854018180111305103805a00004964159080c4040982d4036050308214000e51b104e001e2140e5140c05407580a05915003414441103107500882c03ca010302c1000103403000c111481000080155000035101b60301420701c4941680e00642090400000d000043c986c220466009a403400500c20a010080b5210301c524050380080c1e0790304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 801295242 1250 801293992 801294047
    0x2d03050a021f1e05311a0103020a060203090d0f05031309060f060203190806180a05040b0c090a0311120f0105060103140103050c06280806090601032d0605060d021207 73
    0x84012251171000c10510f0912001150781c0c0b1000c0911020b40810400b1910500601c110300341001003401a0146000560510b92800009102d0b04a2060300030100c7c4001540380041103020403e540c0001843e2100116203625090355400401c00b9108500107414003280c00502180003100701c41d103100e841c03821840754002c890401c0e94a40303005850550040c105603103140b500c4c1131600303186000340c3c0d091401088600305801c0807440c51801030403946000703800704903900c020390700d0040b01c0d03044a030b106401c0703151041c0240010b614444082495440e82c00303106400200140f046d401148600001d807010000b0500a04801d0100301c400d001c02002a44200303000d0166142401c0682520040c0000001100c07101780d16040c0c070514070440040c00704049400348080b500d080141c5680c8141c0030701e402c1042c85030010380360311040000318080d281c81c0715807003000b075109485400180242802500c0a60758000383d080410003503104442403e000068400810b462921403180f8130200c3d07030030b010000d00e107891 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 801296492 1250 801295242 801295291
    0x30b0f011205091606050d0524010e01020c120105010f090c200a1505250c030e0a090504030206040b011a0304060b0301060302090705072d03050a021f1e05 68
    0x15103012090300c1510051084e01d0310f144658800780102e644d071b00d611a000425131304242d40000e044601003071004608605941423026075254841703000d281c030004105000c0d0040c4d061604000016402c083c020014254810701504000d0413912400307000120245c1c0e9600c0070045900c5010b031000016451116101d0340960141c007006d14400e1101a02c503114600e40d24034440092844003203100325251010041c0074881c00184460364a4884400c52240650381e2009000e40d107411002424032120030250021600c1d0000c11202400142504208500385403c01951b610003c6078101d4210441d0703c00400e610040200b104040400503640f02c2c11901e580c0d0380c101c0504190a07450b5095965014000056070300c078441d050040d09551500c1341d86042e5801c2c2003405880808080ca100744015807044041c040c007605521040e40c0510300a5107541d42800c0880c1810500152842c440918014011403c08181d03c1110380440110100c0f046505032507084094a40403100c91480510300c690380f070020031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 801297742 1250 801296492 801296501
    0xa090e040c1203112b051c0213030213090201020637060801060f08070501110313081c0309030e0618031b01030507140910030605060c010507030b0f0112 67
    0x1441031900603041a124001c40c00410842c20007030f40094145000074840c00030600089000032404009000000005464111442c2049800c1000c004c3d0008000080120501d00c0210900c600701c01550b641c1400b40c400481504240016440340c440e5080402c0255004d205200100b50b06070007030507042d034031307000c034030049040d000e001c070310b0300000c01074544400284404100c0d2188084100080c06c141000c256908540300c54000341441c44050106100c41003000a0800444400b40b80003800d5510030500175055000e0205003d4a01c01544030218112034041507203a204c1c0324903c101080300c00b03458021003d0ba03046440103000304501804242d05130500000403c991012072010503003290000380402d103064401d4044001002c2d00180048056905014807504000d6610306401081200e098026440c40380040203880ba000801290019501a4020f44001d0070018200ea4448085d0300b00c450180c9000c84000f00020f00d40740788500e15192131030401c40503800c180d40c0d4110542d4540307010402031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 801298992 1250 801297742 801297751
    0x10e0a020d0e100606110a03120203070c020607030c150b0d0b0601200f0724052101261209040203100302030a05031902120f07030c020901091a060a090e 67
    0x460300d0700440d0340b2081e410054400314180003140090038526100c0020b05940001d074540b40780d80c1018a40c3d00109a010107032050b440300006005a0700e0b02c03002001d0b0341b02618a0304c001c0d0088000f0600006050700300241e4018940035442d0703142102130310020a0100c44c410441541c2c0042e2841c102c00c007040130607810b540d0004040c1480c030507007485910004080c0ca4081010748095104500b0440500300501c9581e00411000215044841017600c010783d510103003202003801c110012501946100310309103180118041817484000780c4d6154001280c001d001420f40041a0313101e10400510180000b17182105030b2611450365051055140c10080a90710141c2000081d401c0d0100201c050b0390244904c8424038814802159100c0c405110003115200c00c1010300e09542040c04d0030440c042c6840b0440d41039400c01e81d03030141c1d1600b0900d030030765910015041c0a90440e112000101d0460520781c4011103030644400800346d944000720403c099440b40290500c0020b1040608004d4260718071125600b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 801300242 1250 801298992 801299017
    0x260d0c210e1207031b05280b030f150108150f0a0806010803121b0405040c050c06010f060e0f06160203071e0e06120a12032703080609010e0a02 63
    0x1c1055103001480031410b0280b001d01c260004502081048a0502000318050505081040c8280b61a000801c2001850300107c4102424045010070001c11102c10001d42502142507880e410070b00c10744540c3c01030441e14042140d4800e01c600e4010740c050204039104411101001c82039656800a110840c010145910b800c1551850041203988081c03100c5070182414a005645442081842130b0941602902c008402050324456584a00d9000c040301e042d03c5095402041e8540c2c817010448440c410841c074001c031801184004510344403a003c00310103c1d03629940382142c0e41644010003a0100f03070310462613444a0100581d01c400755030007480128442c002000c0d038100c241da40b13140881803001075503d6035210700001c10a2040646086115412000030303612010840f030b004c4075540c4c0e87e0803d01c602400395003240c01101c45807032103a008003c4410b595203c48400748480e00c60f072091042244ca080b40843d40e0000028494149906881d040b1028000001019254285910000c0d40907481b0081c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 801301492 1250 801300242 801300257
    0x1e1d0f031005010306090b060a06050708030402130c0e040f0b0a03121b06020304021c020d020108280501080607110709050a1d3009011107260d0c21 65
    0x4401c201d40c440c1c40e00940c010200426920403038a00007a514000a03c0301e440380c820b03404140991980281a07600543d841101140e030f944035400000c3e14480e0940c40c2c00354003410440c0e18200d09501401c800c0b440704050fa800c2c4140000441d1445c140c6010a00d80c540007840640200302144010380400c20460f06400c0c0301000c50b0340d010103014200d0b1140402e0303490319000024803085041000515000410040ca501080092540001c1c0c40800b4400c001c0e0404c107205000c07802d28041d000280082c804c00060086500c0c02080b010805071030241305180341406500c0000f9482400707018000c11100c08580135000307c4c2e00304103280c0002d2230080d28050b040c958030000c80c44030a80c0c40411080410845c0b0040c00c02c2d14282c0700c68455011110540d00103180350648800040c0941c2090b1040d0540900f040100c8915030856603140ca100750740800701a401051401d04c1c012a1f400703c10700b40300050400e584850f40c602c4021395042c80c81000c01003502c200e00c0c0003408003d10300114100c0e4402c0300c0c68403c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 801302742 1250 801301492 801301513
    0xb0f06071403160c08010c050706050619170601050301050c2704020a050405040e0d050d0c1112070215030106230d0e030d1811040b030a050d1e1d0f03 66
    0x520b141c0082d0030150043d01619031200910540f24900300c001d0009400070310040c100c1700d800500500800100920040c2ca030f1010800564400d0700d07111f9005411200f40d08841da48030030050b409202c54120f51454011000041590706060261a11441c0704c0c2d6001c92600c2e841800400300c004034111401240c4010565201d142d5407540000c0c011021143d40c0c080d266810207003007000701d44600b181c10340c1c00d03440b00351030308821604803065030f00c0d50b00c54980000e14480300c1c9000b540c3e07001c240310480c28540611030b400109604200c0240c008180203035440810000d81c0e4808507900e100078080c0c00041140e43d800400c802c051148008036100e2102812030406d603d4031908410303a102e9018641140d0008203000c2405551441140300c080d41500c00440c0c43d8a19484000013800e1824805000c3d5407100d0041e50652800c001500e07100e640102258103420121324010320031440d88910400301451098007120702482480070040d0109096104030b041054182001940590485010380601a40d0901c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 801303992 1250 801302742 801302783
    0x3060d12020616020309030a12170a05011508013206031003060e070b0d051e0a02090405011a2a0114010e0603030403150f0209040e0c090a0b0f0607 65
    0x44540d015400510007401c0c22070000310068849150030302190b00621104a880e0741c005008451140c100da01c2040c0c0350030403c41219820300c07200008041405000900286960560005040f1080803c410300c411b541801e04540402c0d0a10528540002420f03440016242c0800002d0b00414100d000c01c05081c00341c2c021692907002101c0d8065841c0720310908100b40f04072800794018410129000d44040340c00c1c145001541d020340d408580c034083c2d0790130000e0000200030088030035010212080481501c0d041d048030020f0b600004507103004034109070002a2141c8058070400205240800301824040500780d51104009002c04940301c0d0141300d00b500c0042c240a10503800c000d1141c417642d107140d40c104503d41040e0480603000c207009a00401040000c202c640000140503940180302203071100440c10440c001c0e028040f80b0a520501e4090203000110000400b41461002039840e0748269503400d2188044946030030900750840d032104008140c51074181d0080800610a007400001520b905565 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 801305242 1250 801303992 801304013
    0x20313020a0b182209140f0304240c0b2502030d0e0c0619030e0102040e06030c090606030c09060708030108010501031a090705010c060b151e07051203060d 68
    0x500100b800191145807450390030329040b400315055031588600382d01120306034814003402c020484419076490310101000741441c1c0301c9050002d08003c6800143d141d43c4200c0c0c5907842840352604c00c500312040954512030344801000c00381100c0c1c89a880380c0419481d42c641c4000300404155140c0700d208112030014000f041e07000741c02d402d01c0d070007035484038204036010048075440c00c4078005039809002c51f604141d5800c2c0443e00316003819054801c884100060070b50103032400c40b90381c0300d540d4008500444c01081c00c0c0c010500c030390805c604071191144010140518a8020307582c080d040841040010003e03003500c0c004100c3c1c5400a04564a071160340d0b162400d05810a8004690f00e94450004106010070030119400510f06000454010705050340d034550307544081d00c16207061081007019107050003526485080fa461000e00f0005225451080d0003555511043c29200e1040c070001540d001da0f110310b401d071040c559000004203081205844450f0305a0401001c180d48820b10000460008101018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 801306492 1250 801305242 801305249
    0x30304201806030c0904080d090201020708030309010207030306170714010e0d0b04060c1103040509151e03070603020403020f1e030a030e15070317041b06020304030c09060308030109020313020a 85
    0x5040c0c240742000000c00d420031007000221343c481d0358282c0078480410f5214084075060305031850b0000c0ca000c0c3c2c5100517030034000c4a5108180d1f40c0004020880096019001807040d5807080d50f08100640d2514a020345045000280840d1039104500c01e20809414031000640e190050410180d4108042c0004100d00d13020001200d14903281418001005502d01603000b00d0440c2c0e00388480300c58581d400b690f649000714414148a04c18100c00700d0302c078404440540c00f10b040090098220aa06900703004000c50030081a68003034400c0c0313480004c1c424400d2080d6415217034000c1a104012000500b004006505009040d0008116103110b0b88190350070428030b28054803a440704441e060a01c010403900c540300c01b040d0304075510304000f03403000039501600c8414024a408103d80640d201c034200b50400c96503101112103000450940030441d103030000b001c0d1045a02c140030f0491156110f007028800d580c030601c80200b030101c0c20f00051000d01080d80186a01004824080980d200c0341e17000034844406075031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 801307742 1250 801306492 801306529
    0x40503030406230405150a031d0d0f140d0209040e030c10060f0f0608270c030f0a0314030c091e01081e010506070602040e0c120106030e03030420 64
    0x410b5000c40c101048000c2da2580c2e5401d03c682d084c40e19220210742d80b8600403010911a18000410581d000c1c000c0c6d010286032407100307072150326040c80d100b0791540c0d4020030305045011506035101c2e000131600c03420400c042802040038503410a440108020040d4218500c801da100340c44646038498001c01b000540006048500182405140034000300221a0180c000e00c00d2204d00341030600943e1110103251b42110741c289000300c40c5980301c80542c1e284003211307505510750303035400b004280a01000140b140703807050084080d81d0f41810400429545e41c07030030003001000300c2c803d4a420f40008150b64040c5501408010010b45080380c4000000e05401215282140c1c00401281091155a21039065580881c04100301c6c0c8013894110349088288105101d00c521401e80091590200880c0e60150b5000340300002880119060a629500781c540100b03030a1120740212200001c2c80314440e014070640d02e448040510303d50b07240ca0b11840341c180c68000c0300009004020f901c10019848041e4082d50030303503600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 801308992 1250 801307742 801307757
    0xc1e03170a06030305040501080a15080c010f0206090703060e1005010b0a110a0201140f07020a0906030215070b0118140f100603150b03090703050f28030e090c040503030406 76
    0x40050005034a0041c1030200a1890715030280b0029800a00312000d807002400c250034160741e4445490050b0034041000d40b5100c2204000150030310300000d2015004000340c0343c2c1d04000e145003900301d035541c17800c0341c069040394803c0c0002c0011032035961003c480800c4100540e0b5076017203074000c40c00594a0a9004c5146500006400c0000719403041c09000010603a5018021035411130300000e2845541d0f01c10261300607030004140003e2482e40301103a4415502404c1c2c0c03502c1c1c654410064005180074441a4041c0c0c0d0880380702004601d2076011507000b6030748403140f000c0607402c103a07104400c4010202656209542d440000620ba075006480c40e205085149401c021071428101d0b141c81c0c10200d620501c14141003062100a0008291102090319070444960f030f2640e4441d05103e00d032184561000d00039000302180a1080140420480000d4045009440c1d0f4804c1080c441d41901082240140014680e500c2c3d0b4192481e04440c0305420114100c1614101900c40303000030700310350260740301c40013050741ca = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 801310242 1250 801308992 801309017
    0xd1205041d04170f07350309100e03040303030905031201080a030f03110f07020f0d150b0312091012050106090f140d0f05011404060614030606010f0c1e03 68
    0x1100380500d150300c254483e481c00d200900340d10301502d02030650000d03c5142030721581041c8000ca460035500300a49140c20049081c00b100d40240345038001d54003010180150250850f940e10640146000e003500300303000794030b02031868034100c005241150049030180410440314202d0348080f00b00354041d000c28000b40c40c203e00ca91030040e11408403c076107441854280031940b01c03404203810a8464080d1151030566a40140f48005401d11411185450b886204001c1030020300c03540e015000081e40c003042c81008103040c0c0f802016664042c442c0001c40c003020400000c04c990900305039100250441e41419032000490802d01010b54409070400700c00911103030810403065240b5010b4000401c003400d030345480030309510042003c0d0003808d08050700803400500d11f0b00400c04258022404c8072940b00110209082034038026028084910424401c00341030704500301c040c68081f5595001d02c2058480400204481c11305a070404100c4805551800e06200d80c04080880c0e07050f514a1507101c0d0b900d1114107802e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 801311492 1250 801310242 801310253
    0x11062b020d1a0108060d020a1203021614100f0309050706051e040807031112030f091f2c0406030f0507150f180b070f1e020d1205041d04 60
    0x71680000304442d140400a1000d0b60041e078a070317800100030b0b907414003003e000340042004140f5a610020181e6201c010401c180b5902142e5120b2440d58411450790656940207289003400e0031000b03940c2e1020f180c0d50f0350600d09016040b074514507000703402d0114802c0f070300d40c6440d41000031680c030a101180c0c0c00140000a90340c00d41e1040050000040308506250619607280e9079a9003600004210040d03200c01c3c006c0c25518020800700f40010401142e56a0701340c14072502640c0c0203101c056001c0c1c9a903000d05800c0881914461000c50701d0b50740c07201030742c100844800b03100300c000064100704141e050b40d01c00e40a8499018800c00746001d079900b007145840900d82185015041d5202015042100c0c00c12114151300c54200180100d240c5030400708030290120907848030316986d10607000200001543c40420009540c1064020701a980040d041c100018495000c1441070600a5100e0301c0d0f540c2d2440050703a5500346403241900351a01508054843c002c9144c0044c1d030000f03201c04007141a080004101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 801312742 1250 801311492 801311501
    0xa0305040519170c0102190e01090e040b160315030501050609010b0f03071110090b0a0c02012c0102360a03030c0b090109121115010311062b020d 64
    0x628035142e94644071294450040c54501e40040c0c1003c030000003503071000b40e0b000350155421120035801010103829808400341c5128a03800404e0301141c1d0f16900018a184070f051906d00c12504600039100540d03600b0b4607004010304158480d020b15035218407080310b60a293f01c07810007451042c400046c02d41072000401070312800c168801d580310502013040b150310700b20150a0713a4000c101410a03042c1e10909102050501a801000500705072030b04402c0c105014083c19246e00441e20440d04211207030306050100d09072140c1e05043d80744031b210040c0096242000288402960b495040010b082c0031805101d080360310100070034903020303200c0c1c4401e0061205a040f5000d1818400702c400104052071564094154068140b01a20b001c0d03088000801400d070a421030901d4540c00004164520030302e11019100c03064580c44078905206e507922600c030a000032100c25040c1d94108401400440c250002c00503580d100100706076882c484042490200b182c440c01e0b0700c00b08051000d001d6101e4218040c00c50440703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 801313992 1250 801312742 801312763
    0xc03050f1f09080922021c0e0c033d050415050121050a0b04080c0f16090905120409091202010902090a2d1b052803060b0a03050405 58
    0x46181c00010030004800508513681e4000030784184e10035190800e900828008070083d203c814500024000c070030b000a0440381c2c0141e01d0120030401c07001204e000d450b60b03030f0901038004a4055103e030b840d04140324125203040da500d60402040c00640ca544c0d02170704220459800c5a103d42948800c103000400000c0c2c880016201020702c001c0183d903140c40300b2180000702c0d10465248061980350340c602400414800000380ae604042c02030104d003014600205240e0000c078144000b030046ca00c1044030712101040307006203498001104412142001071880060a038400d0403640e81c45500802458031013100301510080203041000141801d01d4248108012540c103601411a49401c00d42c0d801a0740b01c800746030b00b00803d04000900c0c0c0580c215825105030421100400108080040c03441034a025040f100301c00b0103460044c0d25003002000f007603801e030045040900604a5802200d0001c40144644000184581ca40421065502c0340340803084e5000400c0c9000213505d903001c004c18458200500310a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 801315242 1250 801313992 801314053
    0x705010e1009050f0d050105070909051b09060c0c0d0b01090f0507020d0e0f1302031602010504021305040c0509070f1d01020c040e03130e010306050c090d06090c03050f 74
    0x5000c1d030410010304034030b03041c02800d104209242015001d03032a40c1c0320024006030711400800550500600141c800c680c0c91103480348040c24a4001040c2061141042050699001300b00b0308080ca08804c00c035081d0403407207600c6c405116082484016030b17035010031510424010b1440c041d40d0f505140d181004e4403c074024018003d03007080306001c2803903400140c1c3d594026a510b08140c00c544070600080c001036121a11960110161804600c1a40d40740e0045000394074044a801c01c1d0304006000340c0c2030340c4045902940c49024110340702c1c00030485406c803a9006100c0d614540c4010b4940c00010000304040d60418001802e1000d2440d01e45c0e04032612180c08031400c034981c040d41d401c03100001e68030141070800b140160740350344400c8100388040094544100f58641000e4601d9210ba500360a030300e10903c416241d050901e404500c0700d00c200012680005409012a0b0381421a82c0795580580224001101c0d00300c00460000080790080c070200e00c7e2280c048000d031101500a01d60105000110f0a88060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 801316492 1250 801315242 801315259
    0x90b0901120201050d0f0c0f031803080403081e13110433090603050d080f0709030b06010509131d1609110f040f051017010e0a1d0705010e 61
    0x5528880141215060740c2484e05556880420078801c0c00703014154030171114281403100c0c1c02d0850360842140d1006107416a070401c5418000f941c0f8201000f44c108002d4041030504003c5002f013441801031503804169808105441e00d40307450948500001210b030b1001c0c81110203421002c00c08141012003107510101e03000e100c40000d8164400070000002004950010201084102d8480552800c0018031a00e42c0c10400383e5920706009031101c6610794090006082d21000818507950000118015447d6a6454203d81e00310780e54410458005040d05040c09005e024148403542c40409200d00011460303404074849400d03100320020a1100001c1c060240c2003030800d40b0005044141150131502d00300c1d000f080381c0304200102c80d101c0c80307a00700e80350f012100064081429800d18081404603081901d90352504071441200302c07060652a0030302c1d800c294840004219107581e5000c036a40081980800145240403001c220b080e8450201c2d0003141500300982c1040315617001030005414031801d540106 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 801317742 1250 801316492 801316499
    0x609280201020d0e0102010b0406081e03180409030c120c0b01050301111c1803030614120a0b06210106090b09060907030e19140d0219080f0f0a09090b0901 68
    0x7921007a80f1202041008514100180b02d80c0c0300b50130031000c450001d8030401403245c4828066854228054480144150320b500c404010305c40002100e4914450245664100e00800300b00b00c05000214000e80400901c0b00744031020611000107221845a551540000a402c5182590700c0b40c0c0146d011600c60b916210100e602c09100604541801c0009421041840800708500c4010305a0141c0a1081040d0300b44c04420950168000380581e0550348800600c41c1e00d440401c80800c25061240d1801d8000741c0c0c40364005511184802e070850350003000c0c030413100580e060140000c40d0f040b44003001c83c1c0d1074520030000c9000c0e6109100d2901020340d400c0500d45850404a2810380000e4400f00030142d96000d040741d05202806001d242d0801c01014082d94039150410154001c03080802d11040c1c01003285413445c042c00021059506913a10035210304050581d206c0300c100381c0103910300407025803007000540d03d40321402c002054074007000e850f1110442c1c00c20496000f102c030759201040c0210408401031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 801318992 1250 801317742 801317747
    0x30c140a0f080c0609040609111809060a060309140d03020706060e010e0112050a0602130801051005010f230a0503040b01120b010b03040807060c08092b0f02030c0609280201 76
    0x81000f0340e06076445a030f00c082c02d001007402441c90341e001410903843e10715410500045000200b0407480b04030303021005462040e00700401e00c2819180642d009020340d80800c501ca01941015000302c3c040c03072280304604d6222800030f08001d92003284030002039000941c0b0f802c00050b4071680024110f00038001e080d641c1003c004000508040c0903000300c0412085144003085010041c08684950140081d519400010840c0003165043c6c010080507508000000e032400010b06a000202c880503907a080a5030071008042da1000c604c9400000300110380c2e25014495850f082c02000000705035500d4aa41b8542410217021004041e08803009000283c4100c3c40881d403407081da83d05541c00070440a1b5241c48030714212003140300314203004180c0e500f014100ea0510b600180c030716101c1c6440c502a101c11641150700c2c40841c5804008012440402500d0b42d10b103188515071140ca0a030f1580122468400614042e501e020300c212003641c0b2541c00712203a07030b40901034440d5040c2c1c44900d1800040c118403266001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 801320242 1250 801318992 801319003
    0x610021b0d0c0f030b100603021804020d180c0603140106020703030e1804050d030b0d02011215050307090c140f030a09020f040e060f0c071208040606030c140a0f08 72
    0x800d031007444605007800c14000216080c000a09284001800c020780c1c074601103810342011612030980c8440b6990000381c89020340201e40c4d200041c5603000e807107843c0c4107007080001e42200ea52a02e0103683c0382940309120b10b0460154240c40c1c00740c007401c0c03009032514038010140c9021000c0c1030301c19540c07100100810f0707400045040c103903545824008021641d650100f0050b004000155042041d0002404144074001c02c084902d41c03071030303078050004415000c240310004050081c000d00140c03a40543d40c940d0120359028042d0541c03128038882070b0b5907941001074075012a48c0c00c40101c5075501d17000303c2203e503004640c4016500300d11100605004540002400380c2c0401012054140e07228540c410031940c5110703449401c0c030b40c010420040008200149542e841c4229504600c14045e6004910754107440c0090301c00d5503501450301c1c1000b500c28041120020405841110b4250322604084001034040c89640080e010804440d0080708841713081007860240c039407003003041c0880c0714020301c007801c0007003032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 801321492 1250 801320242 801320293
    0x9141525090605030a11040b0c060a0b0d061d01022206020601050901140312040807030b0606040e062707030c021005010b0d0c020309040e24090a030f05090901060206061002 76
    0x3c0403512a17550701d9124024001071030401355034401c005070200ea0010502c01401110380c8602c2201d409030390740c514203000c41d4610130020f0382c807420724096100000c4e240c2d00144901d00800d50f2a144002828950138203a030002003442c2480100d00c440f0b007100c051004d00e00401083d030b52004018030f51408000c80ca0b40d4506000c1c20045807101c0c40c1c82c140a4404100c00a00e082803d00c586035903079641c010040d102c3c031041c001141c9000191000c02d11038501082a00d040d140b0700724641110743c803032204000c0340070b524a0041103414800440c5120603050905414810401d0751004070b81110030783c0f0000c3c101104085440001490071006020015404c0144c070282125450300103044440500182c1c9580100315100e5071103400c00400d02c400072800302d58080341c1020210b00700c40500c4e00103e80303a4620000c488080071540001e02c40b40210b0b2059441d1001c48109060041c50102000d0200700c4040c0e00f40c026601507406842400300e1414940121002c042941c4068041d22500c40b1100314030003003584 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 801322742 1250 801321492 801321497
    0x101b0c020d0b180106080307080d0e07030c030c050f03010509101d010203150a05150a0c030908061812070b0c0912150a0f06030201080604091415250906 67
    0x504120441d01d54250040701e040c2c0160502c4160f01c2c01d500718500410502e4450b50681d400c02c8400038401c440001942e0669074810022820316140007115401000a140304180511900c6000400304180007403032400345002e00a4003401505000a000f944200f400b400d038040c1c0c0c502010003070322801c00300306814064821140840d1443d0a002c980545201780e00c803255065200105000e40005010400d40224500350b440031650355481c4d04001102d2007240c00354050450800c03030005018491250110900c2c82801c0424001d42c803410541d140060403903441394850051281c605c000c2c4410480819908504a1018a40000c40c3e0310000d01c8a40904680401c4038045885440f642d200c0800c10758688150085030f48050403180034503c880c0080e10440400f07440c101c01440d80b0b0902d4002c00090f2501070f1900380311a02d80d03406000080c0400e107400c1d14100315a01360f651403401c00b0301c0030801c01c602c0341c00401d00700c0c180800c2020030843e016145190380710405000302c2229400017181c00441e265030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 801323992 1250 801322742 801322757
    0x506011b060b150a030f0e030c030f0904090c03140606061806071514010618150e01020a0203030a0504090b040203070c03050304260a1205010612020c0c030d080108101b 74
    0x3000440e880c86a421000788080c04040307004c50303d0b198198802c002010841d03009001510340c44561039181e209100480c80030303400030031a180c84800503000400d0404009400010001540e49507540c40c1c11194004489100130300c90107075201101000226003202c01103070407514041c08403001c11064614030213683d004040104c0e43c0028802c00c0c0e803d400d41c150301d02c8414480241c821011a90b080024000d060101d01415516145090801d04403001d13166901901d404400c05c40109454410700e03000c65504520404800ca4010f072000d0015000d44041501c401e5110760a1100190035691003884181c0541e00c140100103117a54809400c2c401650181449030b036a03229400c18016810b4100311180144426003860404072105034020001002d440e038074005004094003030081590028030130704000400c40185c098602940d0750080119003520001c4030204102a00400d0603e40070036515804201c4042c01040300c908140043c0c2c00c000703008802000340000700c039002600058254110010400e0781c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 801325242 1250 801323992 801324011
    0x7031d240f0f190201091101031a0a0807090c020a0819050720090a0b1e0a090608010609320a0207080304050a060b010914090a06050a0b0d0506011b06 66
    0x4440854031004a8a09500d03070310640e012080c8240d0b0f115101403041414505003621440b481031040c21503641d8000e8850075804001401100030303205032180c4004800720403172070300a01d0740c58290400c0146081c001404090703192000c81000c60b1841301000e01907404c90b075104000101d0540131100f101d00300c14a443d40c40e00c01100211444d00070260000c0180103941400e07001d490348407410407810390b002c640084c4203545064440040c0c03407060a8041d009070300c0003021340c104001c000745094100c0010b03000f800035655407050342064580f294429003150b551140d007840100442d00039000304010174060b880e40118000e5081e0b07003014203440803c40d90031101010642c01003668040351030943d084035401d5103a003001e042c402e881d1050500216121482c10b50240d00d194060200d8400b100c101d0028506d4020901003444041030008007074014103541d0310b401040e5645c1c0c1c100e07654081d200003140c040d00d4480d0f51091408039003024200c20b040c004150211082a04624040114580e000d0004120300d00c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 801326492 1250 801325242 801325309
    0x20a0b0c0c030712020307060506042c010b04060e0402030d050a120209010306090204031a01090605011d030304080f0601090c091401031820041401060806100e0d030507031d 76
    0x3d00000104500306552807105102c0c1d00201500c0b050b40202c2d0200a1500d070802004110703420100340000b89078990344010140d5000c0000c0110100d0306900104641c1c01e160000340c01c98645030071501901c40302d441848190704080001c2100030030203090440c50403100d0540a00344004499a0b602d6860300002d015240c0e9110b608403000800341c002c002e40d15036482e85440b03101c3c1c1c001d41501841d1030040800004d0200c05031701603c0300312401a1246009914001c17080c0750401e100ca202c054061008100c0042c030b0030340800c95030406852000281c0020b506001104c01583d502d00640710401407c440c0500c5030511340311152108240900340028042c0500d0081c07030520302d12482c0900b03500d9410210550501e069081e4070078010b41198100b000d101480c0e000d00d0389074028092440068807010002d11982480700e4250002d04c9541001e001c0000c48000254000e00010403c500160010a0084c101504143c0048a03400100c1042c1900c5912001058003161700342c81910950307601c0c88040b2080385 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 801327742 1250 801326492 801326497
    0x40e031b070b0703270b1c060b04090507110d140306040905060a05010510180911130b0703030e0a0201210f09050f07050a060e0415091d0c01020a0b0c0c03 68
    0x24403042c250307140c82c4a07080240c10b55002c1084802c120f213031269808191070125800c0000d8440f208000c0f030070804045425100716011050501c4071030740c1c5180102c3d0a0400314080d1004040d810340100d8203103801880240400c03400319980c003e65100d00340184001c0d8015044244035001100e41e40d8403a5107a20000c0e002d4440500e02070030600801045c070078460b404d80c01c100d05980041d128502c00c4807654070200d4101d60b0101503910003410000007401007060540105400070300034001d84d801d0104a02840075000401c1d4410f81a03180c000503040100740c0c0501480f1441d03682035001d0000c040c05500040d0030311305400c2c1030103280d4400d00071503041c002c142d03880489032103c58401004503a685241c8551745980400d03490030544a54000000c1601e8564403100035181e480d07403000f0001001c04140005408440c201d00181300840b500801e0920052052104001e427038100c2ea1904c1d001401e10904045203000e24a045402580b506008140c440e48440d4005070380f0540c440d506c40b4030204545c11030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 801328992 1250 801327742 801327749
    0x402012609011401080d0203030f0705090901152c090405011b0503011e2117180f030106061b050a0507060206040c0503190201030b1516060506040e031b07 68
    0x26690410312903031101c150321010500c070803045885032a90f00c5400040d41c8181040e00400140d20400c0011014000210610b8012109007001c504081b0780000298600409801011030382c2040c0314400089a44400080341d442c0c01440300300384c500c1100010b418441380c89008980151001000b150402c802580714801c3d41004072a20007000c0d10700803004000354400e104520984220f00700307024540200a81d8841140c8072148807030fa40e070039807040b81007030f032880c0030020b55455820880c00400310111340000c14044100e00788040030a120581007082120000c0d03410b40c000e80c9071a20921400d50415100c00c0442c1c01040c000c001507015140c210b01c0d064000384002d00c1c60045000000b451900010075900551045d03003011100e50300c8202b45665182c01114490421014201130030265020b40d014010401019060701010602c28051800741c4d0300218000ca01280e00350f8942c014000346100d0190010000c035020700c0200030054206560b802592103007400400204644101e502c5c0400081008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 801330242 1250 801328992 801329057
    0x180a0b090d0c1505040608090f0a030c0318090b01030c0305010e0105060903010b0d080304020a060f020c130e0f1e01060e0411131103010f0518010b13120602090a060512040201 77
    0x440c6280e64000749190010f10450002ca0140002302d10000c00100b908150340000c139006000d40002900c2c126075030b80071440140c0600001c10314200d090900084a2009040c24000103c0e5520201c00010110f5401d2044202098504030050022100200c0351504440086500588a201d900b000a00400c401100e803903021004d5040700301040405000f03107100341e000b29007040110740d4910080d0340c101c000782d80c0070005030040c0310041094901801000402410071400207003585580d9440c0f45090001000282e00341d001e10b01c1c00c0381121700c00602c5280e030040301c0000c0c800c19190880e442500800603100800007410380f0040e081e1502e55104005503418064000c0c0b00207003001104002c1d83d44207028405844051110104260500307190304a82c100075000141400e030b29004801c8001d070019641c0c9107840242c0e01000030348031003061071001c105008500040c2d591411a042092040803130380500140b00007881003061160254004607031064085c00c00516400401040040c20b002e1079111300c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 801331492 1250 801330242 801330269
    0x7030911010810050f21340308070f0b19060603060e0a0b0117040b09010c0f02150907050d0b01240f18051c0201111f1107050105010b180a0b090d0c 65
    0x5803010300084c0e02c11010300396015130740c00301d4800503000d101540110030303503001503100355042000448220042600c0c5002d00a81c15a004bc1640c40640900040d14030301c0d0f84407c602e0002d203001042e480390100602c0340b401e0802a4601d014804154a000280741c44000d179900da2161400c0d074001e0184410340c0702001d81d51840ca140c07600d004c5020b080d0a448041c200e40c41c1a5404c0f24403401400c0780c010b003047c6d80c0c005024082d403c42d031285d14400c000f1700c2c8100342d0144100004550b12948c020489261081040814640c1400400440703c68040c580d684440c41e415070000311030342c201042418004541c90b1050344602080e41004049145611107504070039840781039506002c116000c240014401d80e04d40d403a001210a1207580d4904001107403405020001407198a40e541d60f020020f1a2101c4400d181440e1090b10b80908440090f4004490b5074000034109124007165a0461a46581101e0508a040c00c1c903103604174502036612090f000e00c41d500340c4101807020340c001c0c0c00000c0c071000140e001b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 801332742 1250 801331492 801331549
    0xf0607051c0801090609021201270509010209010305061023190c050d08041106160609030503010806101d07050705070f140609031216060507030911010810050f 70
    0xc2190b242403285132801071402e00041020007082c001c03038010b21031389401e0911690070005981e4003d02c01b0b81c010044441c0d144d51840800072103024040c424030720880016110a1110005025118000c00e090711401c13225403008125500260030b800e020400403103002641c442d070f1410740264800c510030b41d00101c00f00340040f221503901220105225100e0400d641540085401c1940d803404191002000f0101f50311401c04a81001006085446c5001200c2c3c1c10500550700c809088070b01c04c100503000580000010300140303101304a01c51b0080030190070034030380501d803c240703030a0140220300118000700420045001c50348143c007903a00321500076054640440e0303030782c1102040074440d1107000300740c80d541c0800c55403d2810005032440810050041c11640194200940031035000c05251004204021901c5010404a1041502c942c0654900140c1b904031418a0b01c01e2841d07402811381081001010048400d1200c4e000400f1100c0954020513000140f0000070302010305403048440f056104410070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 801333992 1250 801332742 801332747
    0x1b03041506030c0f090203280f090609110a0602100b010c140d0e0f010509151b01050601020606040c020a030809030f071a060a060503040b0c090901060c02041a0f0607051c 75
    0x1074080344e0341c20001c041800d655120041c16404204c030580444c0200ba940140c140e007801a613100c0841d03c1c0040080c0200d114240350040303805c50101514a2503840380c3c400c00b0041400d48060402d4000c0340ca03e03071407030728011000b0340e80c200081c40d140c140303a141e50014010303900500c441340c0c60304c1c1d100d6038926220940b031072900d55621a504114000403210405e0f1516824245885015400306943d0a4030b803003c5d040500c4001051200503160707548081100600d21220500601210100480081064101900024503250025240798072451601281c281e545400003284141d65a00d42005070300d030b90700c1c09885811800b5000d00c1480908000409000b049202c0c1d008840c20003c01c8110041a2125001e0003400861402130b240403400030400700700400e54903246103070b00c0b08960712580c7c0b03440c401401003220b02e4030a03444403011a6843c164002149042e00681103000c3c8200c01c140d01c01010302c4001264003182d401518029a000070701d03101844002c0c0700d101044040014a000401004d1500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 801335242 1250 801333992 801334013
    0xa1a0a1803170a2a03032c100c050906031f0515040602061005031f020424170610030b010e03060f25020309010e0105120103060f0e03031b0304150603 66
    0x52000089000c0b00c4a000b194140c070304d000080760240941d0302d0710809a40d0a500902000220400f8140e900d45154244d445003042010185111005001080c02c060844c20070750310044a4081402400e12125800e61503e0041e0b130f44c000410401554219002c5180d280720540d02e4200c41d4010719040f80103070441c50850b006104844040d400c0710082d40d55103131405807501c15401080da06400101c4064000700e9220220b50f414020040010f28150307550071340d468810706060242403007408044d41360320f5a603004040120680e8608050f0b580c00c1c5407000004000e080000035000074141d545076803840c2a4820030b04258054401740884086042a001c0e141c03407a141100c41480c0c500111591580c0700184003e00203090755603400950800740303414010340394039103d590340904004c2c090201c42c0c0c03180c001008a038000c6004000000b00403445a0342c01c015184502c0d404507951b4001c0051040000c0794080d1108080b240c0752405440c2e464a140107040c6850760943c01c0310440c1060408000c0c098517908 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 801336492 1250 801335242 801335257
    0xd0f0c050c0d2a170d0c0809061006050a0e06040909050c060a0e0f0d0b3105060c03040c05120607180501021506030f16050a1a0a180317 60
    0x211803001d0310507201290080780900c412244040d070748a003056032440241c0500f6015214051079070301c81d0500040c1a0264002c1113061404a841780c02000d802501302c1076007904003074924042e00b034501c1e102e41541c842e880c0c82d1182e0070400500003445c2d512284222286120128001c10a41d5902e55030810301300a450364400558550003161440c1d086031030480704550b04010b02e52140306541803c042005030518003814500e42208107582071200088090038581e21560017011304d0340f00707400307024005e0001044642c664460ba580c084084004600001400c95000b9440115503a817541d45240201180c8440d07448560400701c84c0c44c0d40c284a0001140c21403040c41580d84041c20f1154071803000008020620649002d60044138260b00c0307000f10303010230607841000a030885009000384010240f800394a181f0f101b0a64040500600c070a01c2c0040c8414000c09904560110350040c8000c4140c45102d0030095100f0f125600444a07111114026440c0045800050b0790260200000001050398840d64 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 801337742 1250 801336492 801336517
    0xe0c09010f06081803090d0f0506011415030c04080328090b032d10080f120901080a0f02072003070b1c091b0518010b0d020d0f0c05 58
    0xa0000c18001d01041a207021125196a00d45840c1c45200850f00b0500c0100280389203808100070820543e01d6009081d004076208030540b68038400d05040042c10800182c00c174610101174500641102c1da110400c07940c11807203040403250380c2c0e103801030000141d10495111884a00010802c1c00c1c44616a4110030300350b0481e0341c80a17000d0f01108004854012a038015038550900c140b0201e601c210350400385003e40c0c00d080d043d101191400100b0242040d00c102c4402584c0c1088210500091100b4000300c00728401da44000e010340316014459081d030740510507409042014000005144100540080900c01c600401c11582c4100d141052440003030f42c5211302c4206010000030b5461410300080e14811108544d00480c14200b200c3c44200041d070303825101d0800b1503114201040425590230f0034820f500c4c51015442c01c1c1514001c140a50480c01c1c01d0304a11445c00c00b001000034001040864a80e592480f90059403101003500010090021a02031000189401c210b404501c0d0800000c105440a16 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 801338992 1250 801337742 801337759
    0x1503050a12020703030912020609180109060602010b030a030f020307080f0409270b070c06050c090301050606043b0a0f0b030f070302060f04180b09070c0f150e010e0c 73
    0x114402d0340da0340703560300c0010300007984184208214003d02038482d500c144020501450001144000b0b5004010320304034242e10740d040300c010003403c51544143c1c0010500ea0009118200700c14000039100c85064402030f05210b00e14203814203041c401e1003190380d0b159016a005840390f810051800458005014042101c0d01d000c202d5110407080c003003450061001c4103807100034254240c1da241c280c1ea1001d01010700b07014940300e449002030712a000f254401d8032030320f260344e4031403042108240c02d4410203081c6c4e40c080c0f0030820052040140280014141e01c00300460042c003141c88149803043d003c0c0740c030300c032507010b814413010f114107074180b90008400800310382400d0105034600010142c507107005080c811001d900002c0100300500703080e000f401030a4a40d01e00c442c2031680e038522418654076121810400c443c0d588520b6081483c0004100390881383d01d240101036200d0950350080302008506002d49055441200c4105030791158101c420500404c40003407000b0410340003c030ba5503039880040c4078410301d244c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 801340242 1250 801338992 801339023
    0x20102070f0b0a1409150304050d050c030708030603190308090607050a090e040c051c200d0209151509010908010510150e0d0305070b0601030902221503050a 69
    0x241e62480c42610302c0c0c008201d141000c140e1003a2000031940201010b030308402c0c00b0007500d681d903001c010b44900c292200100d0740c0349010725049007403a0300300036682c080c4a01840303040e16082000081d01c0c00c1503441440c60703aaa45400000900d8502d4890703a506200903116020000c056124407010302800b41d42d01184c5907601c85860690f80e901500c1a8080080d040300c50801084500c1690160002e0041101c410142d4441c03000c91011094454954840c001c4012001c0c1003110108038040c4001c3c120036440000300c0050b00140d522074074504064842c0c00c5100200717542c0c6162004044030101c000b0800f00c18490002003661458001902250221341c0c10b440010740402e06018041c881d00034600c01c01084d9080c00080b01c121901d4514040030010074041d911415250098101070703d41c002d03210b850312071250b880c0141480030000c00007810141013040f07000058941080c8000030881110080b00c1c10a9402c54040007011076442480003a00c0f07403040001441808100000514090102503594060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 801341492 1250 801340242 801340259
    0x2001020706050408180d150911030f0606210607030b21010f14060d03111c090306060504091703181e24061537030b09062b030c02010207 60
    0x20401b001c0c040740b070200c03034101c180080ca50001d2141407280340102c1c2980440700109160104030300c4200c20a60124003402640d2400900b4140602001006000301c0360110841d030343c0703490001c4c02c443c0030700d515080185082c1d0f580f0051480140403492100e0003010541c1c150901801141c100039104910b018084004840c0c0c0316060b80c418500a4607840703208102d690220b03290b2a4401400d8040d000d2800c3d01e21200c160211404015991980c903181007600314146282181c070243d111910907403601045100142c401c002560010a45d03200b81c03038503582c80d40804400c1c01600c40b004511405a4071403540303d00014552104c0c0c4221501c120380421030410041c41084a090403985150b80701180003d51500d42160701e052000e101d001c2d00b5042800c07241180310f00c494195040300407840d00c10390410b80b03001803d00004a504107031405110380f503071075000f20395014000b0b0015800f950f0450904000d0700400c1c200d8030581e80350405d05100c26049410000e140c9503d01e04100c3c014066064002482d08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 801342742 1250 801341492 801341509
    0x151512200618090406020909010f1508040510200a0203120f0906340c120302180d0212070303091701020306010f12090209010909050c0d03200102070605040818 70
    0x640030105280204005002c110072280e00602c210394880d0204444c4003203888070742560b8001d222049581a0b50342c03c0a04c0b0342c1000a842f41c1d02010010660204004200c1c000b500340b080303841d90300c00003d5800c0706030840b20340d2480b0b150281c1000c0000203a07070700040d40e002000304000c2c96480d803940c2c0e55464030684407c041006071a586c415500c070102064a000d103402415000c00174400c41046008203072400c03405000050707050b04010412050040d401d11400c4541d803854001107107011031500c4403502070a240c490004400a004150050503802152a10300f030051010b5034240842c0c2c0800d0b030701c0c40c008228150700c1c058200010340803107a0b4080d00d1303014000d43c1d01900050f103a0041c514a840070407610840314440c0741c04034070b498211490162316408401e60180240e01c2c1d0100b40038401d0b00300305180540c12500c0e640240d40021818010960090b010100c6100106c0d04244603800701041d00d003e40a2180050000d81c070304000c5c401084001d00041c271740c490041146003407090300081040b1084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 801343992 1250 801342742 801342757
    0x40e070e13050a17130306051806040201081f090f0e1204050607060f020702090135030304240507030c0e0609011706120a08030103060b0603041515122006 68
    0x83d03020300c80e90300c0014102c80408042e140c128a804d811320901440b10040c0361810b0303005480301d84d03585041c01400980340c0300d00c0302040c003188020481414240d0009061400040540c040f07484174100085040340340e000084024680780390180450900d000300c2a00a101c047c4100344a8840c0d0310884241c040c500c3c00b03407812104010401400c0001d607440711000740104210382249c0c99401c1100c0401650740c0440a4080c100813602110359100158800280711824510840d00a280418154140d4000000c507684941e200041c8034001e23100c6c1c2140c25507018204240b80006040504001c903103613250303015541c120b210b0368904008c4900311007849050712801c01043e00007090310305241f80d0a101054006d81050700501480c0100501c1501c09007000c140c02d2040302c400340c000004006025481c0981c01400c00b08907100c500d0344c100740d45d034644100f010048020003262203001e1580150052994400249071031035400003446060715040c3d900c1c0103002e010117000d4400000310720a90a00c0700c00d407001c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 801345242 1250 801343992 801344003
    0x151e0503060c0301050607060204030623060307080c3003030609241005090a06170109050105100c0201021e030310090c020a03030e0c0a12030f020d080601110a02040e070e13 76
    0x544c0d0030001402019480340c10141e032455020880040001d40a22030700d03900c11608c0521200c1310141041404000c00041c0c181407081e400380000384414100882e80c881c500404542007402d00107050350b0020b001c1d04401c1c1d200c3e040000200010f408000104c0110b126510840d40003a2aa494026a41140f807448160107800d0184004101681c20000030301e80b07914101d400c04134203041d10200092000c1206410410024004a44002c0b048a50030380f49400341070f0079207007408150b041c0000701d4228513480144804000f0108803a034296402802003204d80302c210b800c2e0101e070040250503c1d03a40d61095801e1504010040c00010348005640b080d030b80c0818256000d031102c51690b49088004d130030b038800040c40e180a000c03410080c5a5464001c000100780404a000b0011070500b07010301a10002040030056401102c108040142d10908940d440721003402c0521846c2031a0341d83c1d920b845036581c8004c0d04149403802d1820700200000b00c013402c8941da40350201d0316554210b2500d601d0303072a16200806 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 801346492 1250 801345242 801345247
    0x20f070e010608072d020705100f210f020703110a0305041802250b0c130e04060914030301090c0e130b0102030c0106060e04050f10090f151e0503060c 66
    0x1020701c110140354010400d442d00680040c0d4100100140c04022006042040016480d00505d00d80603c040001080c0454643d181a1034800c03010380b2040024210b00208162a510700324100907000e40f21310f030002116410441c030390b00824000029407100c1030a070b0109004040100e80308000140c5240780356415501c150519180080340c003402d4600c101e00c0c43c0e81d40c0d000d01007203c0c0f24008201102e0101c468111070240401d4038100310700c0243c0041e085800b020803c01149002c5c104644070039044900d010842c480942d80e600b40701000b440c0d40180200005212004102c0d0902d0000285060341e43e40d84041001c001c1198003940c0c6449086035541d04000c0b05074445465588035845011441d5042c0180c034074000440c032056085400e42c1d001400032402c005240328040c02c0510403a41d10a03039030040040541000414210304285902c21800003136200c14000e4686007094205902d103d00c00c850f4483c100d0f0315100b0135045840c2020240e2261802c49000161904d00090304074051811081d81c2d51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 801347742 1250 801346492 801346499
    0x4090c03060f2a0f1b02101403070815030d201e0f0d030b030a0b070201020d1121040c0e13080409050601021606020c240a050703020f070e01 62
    0x8018000d070b4890544920b9540a0242030300c2e1455155040303502e458441c01a0080c3c08800c00342610000f500b10004205041c81d1341c10b4080008101a003805030103e4201c00d800120260494002e062581c44031980c4002105200070150031407025801480f00911a4103000c0302c0b6030034113a0f10011100780710300148172070403008620036907603a50880b083c42c001c0990b04250340944544004062070780c0d804841d980041b0b807800d409a8240030b04441c03454a45000d01c1501655070009548204011001d041c4031041d2002c81d840c6030003507044603070346030600e44180500252081c0b40c1100703030020081c4880340450803240000340e4220132007440c03055600c0b00301c5020850611318141000701004010100f1242c03541d604402103101d40c0d000c0c0004141e5003c011441d4036101f03000906116800c0c081e5041140c02c241c0520501360040342d800d010100a03101e61142c6411409448400c0480c1c0c2d000b091003d600089800d052548580142917680c080d4084821142c034480c1c10a5580490703104051101d160381d401030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 801348992 1250 801347742 801347753
    0x504060e03010b030304120c060c0f02100905150421081c11030c090f01020c011409130204090605150f0417031903050114040e1005060d05070f0504050604090c03 71
    0x2205120800341c000601100b082000ca403039a4400c0e0003643d0b011640300b5290041000d40c05066019025600d4480d180e681070b030740c4028030140c45c068002c0c882c8500118030102c462254080c0401401c00078403030900ca02901c031010f4903a40c000c1c080c44410984059820102c542000d003c001c00741e030301460032807402030030012810081c0d040300c2d0080319070b9031540051011110064080c50041145810240d61003803900f00f0020a0900c0810460554200c4410110030360b030841d04002c122907400c0700d01542c0c0d141910024007030103600040c10741414404500450a10402d03030082c41656025900078548200c3c040d003c035403500a025100e001000b00300420b0100b410400701c1d844080100c0402c590519141d101c1000c4589099051000000d66078001005480301c020158014410189e40400001100c0301529840303500c00d8101400c455100d001003005a2901911460015000425201900e4840d448000c00200c644a840c1c0305a040201240d010300c0e00e440307196110340d03000440d200168550b96170f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 801350242 1250 801348992 801349007
    0x90e0c03060609010504080105040606050f0102061608070c0f050604330c12180b0c09130902030a0b0a050708011a0d09062c0609060f15041b031b0807050406 69
    0x10141041740c00d2000044254090081350300440c0b0902c0c01040090a100a02c40207141d050211411036001c42c0c1440301d00e0458520040f00c000140c60140901d9132a1031055807503440d0950000c000064460011081c054017084c81d9009600c2040d14807c0d00e4107002c144440110300d401d10140f480d00d00e0701100c1c803429056000e202025980c2c20001008551044c1d001e003141d0031040400180741090b030a11040140d000c08507a03004480d19001c50130040b0210105040401035070200c0100c80d0b54905440941d681001007641040d4007911902c0d051900100303803800382030140d07412004104d0040003c40c0304c6680480c1c08111288075004103080200103003125000c0c0111942c142c60240d560030844005800c600300314103400080c00400443c4a400043c5546040030003001c809030f54109070180808040ba0358070311070700446c4080116811038200400500280b808000072265800c5003e00f0a22240d0140c118400c0705904440440c2500c03804401030322032010031180f00000a0040006102d501e019010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 801351492 1250 801350242 801350257
    0x40905101e1e2301030c03020a0e0d110409120801060f05120a060906080705030601120c12140703111017060d0302190c0f0f0b030c0c0f011b090e0c030606 68
    0x107004500320342c1e61004600e94080c03d24003d5210f0925440503143d5601801100200c0e0071a150842c0390602e5410010451360300d0500c0da5118903401c0106500384080085041800319000380f0402600406142c0fa03080188030a1030540443c035018000181030f030080d0308465002d40940c032040e2030881884101078032100002c0c4910802c0b541c90780c01142103400ca1041300040d01c1c100c0002c1400a040500309885c003c3c0503030081c900e440125000500144800c00e100c4119009080407400a114500d099001c0c921040c04802d028805c5803400800d0000310113170218041019605441c2201c5423076403c80381141c0c0346180006032241c00011500600342200c1e8001814000c2c13056801d401c0d42445d2001d0031818070b802c149c0b010514280b003030000011000c074502c0100880007060380481d02d00742c1c110b28030f0f010090078402c2d901000300c0c91125284040c081a101800c0a40003008911500542c0b0031003081101100070000b2101c5802295000c118801940a5110007c0090840c0d4400003007141e154000035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 801352742 1250 801351492 801351539
    0x90a1b0f0309050609210408030a0309051516030c0206090618150a060e0709060c020d020103060b072a082119020105150a0b12040206040803040905101e 67
    0x81c2e000d00415030611a440c059900030000d000c00300d100c80d01003000003040606080d00d080e410081080a00c00001c01c40e407401c2c00a080c041040b05031806c1032070400031500301810440c010502008100501c005c0d10010404041e1010000441b16142c101e0303540f0421503c4502d1a400040811043d041e03014081d18030303c002a01b25811403040c032445217074070081607071080d032441d4071460b040c002c602c600208030381c5c000e003a0b20784080320600d00702005201e5000d01c1006030040720b0058104055900c81d420043c040d00700c1c2090169104440e1620000c0b01900050407041103144400170804201c0345601d200443d00e441000f4403c03d12080f400c03a0a2501d800e40004488c40304000d5015019a80303404d9264a400c0380c0c000250f10702c3d02102c401040d040c2041c09a00c20420703698140300403500d0764141c511108800103100c407159240d20100c1c84602c91500700d609644000311700040e8044090708094031030700a010030b0540c181e07643e60390020310510010b130102c03000080503418041c407001e800d4900682010b08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 801353992 1250 801352742 801352751
    0x90b0f09040212011a09090c030a060209060d0608060a0c030e030409052226071203020c012418060501050403030c08071e0515090304061407050615090a1b0f03 70
    0x121003e81c01c4810940001103149154082ca005524200b60219400001000581064083c0600003512061048402441a80c0c00308110a0030b40310700050310342202c0c01c02000c10000c3e8503000265610343d421698890780a09211080c1c2289200740904240e40595000850401e400c094901e00580b400401c01445040c00c200c0e21594a061500d0340d154a60180702d42c0060f0800c2144c07000104c602c0c5800e44200c0359000c028030800180000074814061816203030040e03d400d20012200c2c003410b99221211f6941e001040c1c0d40c00707443c214400182c02c0f2030b6070b004100002c1c50049689400e45413140f1031203002c12010722080003c28000d040241013240306d03aa100e41341101a03620501c01d4140580c0c0c48901d000c103518054108001088a00242d246942c0b03003c545180005600303a403442140610b80c1000040482c81e10090015815168800d904c030094a043d45080010500242d24011b80188a1640a0080740c0c99460078402c03681e0340088903400c45003a6100a10a03100ca201e20180740c0200b5544 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 801355242 1250 801353992 801354019
    0xb040b0a120f0902010f0302120402090403020f070b0406030b03190209130804080318040917090d06020d240e0106050306061209101a010206060d03031503030e0a090b0f090402 77
    0x240c0b04031424441d1603040003e0000003070000502d403840200c850310030301d4410070901c00d10400d003d0110b070b84554112a050046da4440c0b81c00c0342401c80341052070700355104510010480c00c1c05030001d0002c0c0d40a980d4100b10b0710b62070380201941c81c04456082001910304480c2400541060044203611002403424107059020a5444070240d511543c070000540d0800b048480302c44031960811180020204d506115585440e00c40c48071a2940c0a01c03840c54040c00141c104064030307440400c10009070030007070454841460b0740c40c600c082e20401d03030305842c10841d13a0004015200c1c2c506556003a40c2c00f40c81c142800307a00703008081c1c500c4d51010b0003050748000c09100441343d842d420b0000c5840b408204001d0460140c0400255041d80c15105c0c042038000745210380c6a00c1660700081441d0b11440443d004031b42e40c580341c03d040c0c1c000c0035070003284039145401c08004410726801039001d585c0100c1c02e0b60340401c2e03182e845108001310ba00d1041030b10b51101305182c0200140c0340007880d45402038001424904110207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 801356492 1250 801355242 801355277
    0x405060a020601060219050606040c2016050307080d0507170a0c060506030102030c180a03050a0c0614040b040501050c101d12030f18010e030f030103050c0a0b040b0a 73
    0x40e4024500590251005000945d4103202d191045a2001090744864005075522625404020000d50141c1d54412803000c403c3c1c801e034030308040c54800c04c51055901403072440c503c1e00e45d904c21521004181803070070001140c3c2000107001c4100d0700340601034a1309140700403082329194442c3e00c0507100b01c11303001c032200c4039002002c004048424090700c0d40d19500c2e116190050035581300a000320701c6030344103104100f03880301340008441e0950000020172848166920015140300d54642001e800c4c0e01c241e02240d403c000020006c0800c0c0c4159440e1031042c541c11210401403845240200c04040d0002d11081025502a60187c1800c3d00e01d4015541e8800c0c41e126102d084410303192004461000d020801103808038244030061040c01801c030058658909001c01051459010b801c80e6200000c41400e03940000c0298019424088500c041c0d0741d070b904034440c02840542003070000303032568068009030903441c0c5449503210b42250700360b142c810f061519000650416030804075103127081c00388003107400100c0407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 801357742 1250 801356492 801356497
    0x7050f0d020a02011503020a210b01150809010203101206020c0d0519020c06121003080c0a03030e010c0818150a0204090b011d040f0e031306020c0a05091902040506 72
    0x6a140c8401038864480800003400c1d0380c04c140c01c50704825120f19091000d40c0705c2996001c141c41c50314003003034110f40d00c90a0008420390b1204015203160b2501c000070581d850405045d680d40c0140b513032070550380c2d100c1007410740c200c3c4010b84140c2c040c0d0290070010021135288490201d60680200c10060400405400c030314106450405040002440014018045030030030b80307060b000b0055840101400c2c501c070804594580705444040d407a13501000c00140c480a00d0980d00c8002d0359201040d80c0d21035101542942d40d03400007200440c0840d05251050081d200c0512039803011154030fa03206c0b4955102c0315020501218142d010b582d080c00b074034240c0c0403074082c82132080d070140310081c0300180d40302e151038070762401c60701540811410007100d4080082c80210480000c090740300100c600090004210304140b000740144000400240004030340f502e01c14144145202c200d612a07000c2d03c402c1c0f82c071202008003c5415018581c0c1c060200d00205042c50540c00000c55128030801c0300601c0c243d16000010400d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 801358992 1250 801357742 801357757
    0x30f1b061d0a0c05280e0c1b031c0212040b07090807060c021201050702060a0213051c0512040b0715140421230a210e1c020c0907050f 59
    0x8101000e0030004d5042807400c0c0001c1e5080d048842a09240f0f0884e920b998820512400b000c80d1134510208215020b0070707040300d034010b06110b0310440c0e9484c1d400a45450b0b401400c00002c880f6003803a5200340700c04a90080f80d4a0755101e04e451022607980e5503a0781c0903100054030000800144890100301e6807010841c0030b0241c42c0e540c13143c1c50320204a104018a1410322042400b4a90511040c40580d40e0002151504140600c1d009602e80c00c880e041c001c04c94000f544013991000f001da694200300810742d413407001918042e60654024481142c1c80c40d46611070340c46200d10500c810401013000c0707180b603022540365242d150404030f04504003840341e90b02500241d0382602c0f10f80b20282190002e070740d41800307022081d007941040c603c03100601048242d1540c081d0382c8650755440000300264004c3c030514000318501c1c0303240070003c0441c8000c00404010400d040c07038a03681e8401c1703c640929243e2501089408459a640180b100300c0c40743e400e008400a01405841c144941031260b10307030354100c020283c102c5d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 801360242 1250 801358992 801359003
    0x10090e07030e100213120303240528090b030a050105041416050d060e0c0d0627020901030f0201140d050a0b100f051305120a030f1b061d0a 61
    0x40702c5400c9a80e909080c0c40898589110744100304018007040c400c1d551a00700e440e0451a0200060030b4141034002d0205030000d10380322841030310b5000c1101555110308054501c180c034a00090b842030007800c22044180c40310795050600b8600100110603441d001a80c1c0e18001900b51401740384143c2c0c0f2107094580c161000c0f1480700c0c0382c404040388810700f00004030400b030003200d01480743c41c60324001c11040c4403294800380455231102001103901c401003000c15940c1c00040c001818443c00f031b06000004024808440750042d4041c240b009001400030200d001d00d82e00144141c40d26440c660303030070345485100c4204034144045070f029030b90304d1000400600070700c1803d12404107240c944452404212031040404d10303c0f4a52060f0b0307902e071081c2d00200d0040b0050342c90800c2d5644512071182001e0b898082d522040d84440081d059000c64000400c3d44884203100ea00d40560824094800755441030900c030050b91052107680280001c03851507080401100d800c07120502c0403944902601e8101400240e06844 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 801361492 1250 801360242 801360251
    0x90b0a0e090307062004031b03140f16060e0d0204110703112a04240f090b0a06050d050411092a091309151e0c0e01050910090e0703 58
    0x18482540a007084c2c0c45c01068428480400c0541944040d008a010140c050302844508114540151404001664020641a121075150030243d41c0c0c40b40c070a001e8070401e000c0e4480c90a045d10610440702d050740c81c0c640700c04440340405c5080c0820810490800da81c0039446008910003424200001d100790780c0641c1d201d000101c9076030f501d103181c58021445284110300180c031000395000440e22102a001d400c40340410407480c1c0c80411501d5007401c1010b84440003100030001504003070503a5803c11107019400130f0081003800810844600401c1c403484d400b1401c100708031a0401215484a076000f817290102450010a41c404038140d481c0881d014101c0c400c48110f094000c0c80441894004078a020001c07614194035039001c500e241d00c0405030a51900e855448100c100440b1045100504000160030480107441360761b036180e00c06040e00c4010155142c550402c4001c3d104040f10300c2da815040e143e6601e022221014003145011400d852020001c0c00d201c017240c4900810403071401035059035000b24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 801362742 1250 801361492 801361507
    0x80705120a111510060302030603010b04050109090501050105030c061909120804050301050f04170f0d11040e07080906041e0c030308190b0a030b190f0501240207090b0a0e0903 77
    0xe20706480b12003c0e1880d0303404141004a0400140d0042c1c0580d8030500d00941c032501c2d2400803d001d408a058041d91182c100700021038894042d61002d6400c601600c000d026503662602819140d5a203406002c1c0c0115042007a8000d100d060b240310400500b1070714020940d660f0b40c009285070007001c0c6034200c800c000001001c108503d401d0080300d4115803900700416980c10f00d540c07520368001000000386001c1300701140c12007a602d100d0003502d114500700c5034240a8021000007a6000f58418000d032004850300a0100d1926407141d0505403152050b03500604030394441d0307126604482010030138107000340c1c48203161600180704a117804c4001e40c1309031501e040508014580040500a0030364460206143c49501c0501e40c0c1c81207002c6040b65040240c000c95074550605858450000c40500100c160500c09645881c009a60102c1c1c1264500400420103002c24540c01c0344000b940d19841005901291050103071401c3c5074403c1710041c0c8024010003000780d55030701c1407034600012142000c15800200304203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 801363992 1250 801362742 801362777
    0xb070b090105070c03030c030b090109062909010305040c030f3512040c030c0b0c0706050a0518121506100e03030f07020d0f080702030f1603080705120a 67
    0x4540004415000b4002440d1001c8000c080c0401600e02030201074940e4403400382c95029a00c2800c0031000608003010359038460001101034401c51095035002c2803604c1d141400382c0000106c0106040c0c0c072411540c43d010b5002c0045014180281003606c1d0030b806000000009039581e018808120721960070a00c07040d207044802011a40e540c4010343e22440f5a50b980a00e10740c521040740e03190008089880804d0312a41029681c800040d0401444500500f402040f4014030b80c019041039200b403800c644043d5182c4204403070302d024000080011403002c0c0081c606444004407102c0c0c0c042c0d809490007207600300f41e095035840c122402c00196400c0380340b2810302c030050074107440f59403c032401410400c0c3c80b01740316030100ba43c030300c203200045d2001140402c5007011907403205a2042c20f20f4110f0004d0034654264100703800c05905c9110128441c0c400c8600801d134555000c0b40003a020b0035140b1610762443d1070b58030369903034603440418122020b0040300c0e205405c44060300003a02e90390f4290381c0d41481310041842314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 801365242 1250 801363992 801364013
    0x60504020102060a1503170f03010b070b010f0506090405040f0204020a030c091403060f10080319031a13180204050703060602100618020c012901180e0402010818070b07 74
    0x43c906110300300385ca208102d007165010030045039409000c0d0001454503611503e0742c0c0c00b9041e03800844200000c000100e140c60f10f0702410302640501d040d011540d903504c038600912003a500c1040d4009505005041e682e01e40380d40400d42c003502a1011829000040d40007808136407040d00e507640440d507951520740c0902e52106e8070402801d003a10041da80300e001e140009954250051807101120314590000d030060032034035280030041080300100c0781c41c1c05003403138408464202214940002444c021607590400c03840100c860500102400c1c40662403c0044150041c085c0c80407032440300d0304007401070304c016113580c45074501c2004203650000305142044c60003400c0100c0c11083c0c2c1207090400f2024400c20105d180c80310307100c2c456a200169075040300b01d0b049001d066490004442070f003001041c03408142c08001c0c04902480c09a03109107941c469840fa081092081e4059500300c100414001030055015a0060703401414401680c842c003448084007624000054000026416002c9403050800283c80e64 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 801366492 1250 801365242 801365251
    0xb041404050402031c1e030504171606021e1303021203070b13170c0f010c020304030503040902070f0b1801150e06191502062e0e0c130306050402010206 67
    0xc060000d0704168000964541007584141981200b4070500c200c1c40b030240c000300410303400c06a2034803a191540d8502900920701110184c411035600245016034400350811540c6920405022402088041d04c1e408004c2d001040003003912881c18040d0306000300310101a1102d030101c65030b054600c90961050109068091200d400d0039030060091070300048021041ca9880256000d0001d038003010f5081c41d41c0c0c03181c404d00f41a5a034800002d00904400d00c041802221000000b000b8030240403c0e00341203940b442030703200107001604144000d1003480302903002440b05500070f10b22900c0a42094889400343c041c151500b910b50900320320180c2128000303006050403c0c0c15100021180b9260044903040c820700100310500c246000003080245d01e100c3e070700410103071400d0340e9200c01034000e026020356100400c2da0200d21000c228102101403150103035080340b10166109504060a2401860100744807010700364402d1aa01440842c001c4140086410011401050301240a0030f003030002a007014000703007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 801367742 1250 801366492 801366499
    0x1e010c0c02011202030601091701090b060a05010203070318050612010312031104030f032a03020631060e03160212061014010e1008011a03060306010302040f090c0b0414 74
    0x1100360003503038101080800589a0f0480540d0326920352004030b5240449400c5542c07860f100c55800e41c2501015070080e021240706802c80451600c4850400004001d248102d40c016801049a0000640f007001c44841d10344055400a0b0720513140c0c800980280c00c14215031404121100040051124000514800c0010b9040802c0043c0c4028694441449607020103400311504517018010544640c034445150042100410059050800d50001e0340031040010f80042c440c14000c12000b0b10403601ca60059408407001c4c1340031464044003180440c040035001c0d86d034241e403092200070840d0280f0003094082c02880f007640c20310701144100403a00380022031600c080d501c29030400c944108a400e500c0c05407512040c1d2041d48504000c01202d01c400090b90050304071341e12007076881c160b43e00040c1c2613068921035210014070015010381200c2a0000302c4115606521140041026050550040d0b107440707405000424a8002616411800c60056018034003c410000e01001003240c6440702c9500000c044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 801368992 1250 801367742 801367757
    0x1b0314180a14030d09110f0103050f06040e071a031b071101081003140705010206070c05061501092303010c1425050a11030c012f0705031e010c 63
    0x80c00607a503610091000a10101d032810303882c00355001c10425110000240081807080700a1307031600340035140701c18603e81d014010b40801d47d0729a40c042d0040b50710401025410104c42c1c1c2da03810070080508201819a5221302138440301048546540d246038101c12401d03801c080e41e82c10708910100e030100e0021440b120314141840004001424021210f685c2d03002440c1c6040c2d03c0e2500601c8036200441980010b122841c0b502c0341101410001c035002d0308032682602030703441c9940c0d0300c0f500f0f4038420511a0010001e40005c00090354085034042203c00480d4185410345410f5180c140da440302e0211000700d00000000d02d1614082c0e031030700340900c0000c0070701860454482d0044843d00d01d0540100e4582004040646122007020001c0c80da6294130380d03400404650705100356003020700202c85454032050080c0143c004803940303135004405c1e141030018003480c0307800d8050403807441c603120950b00e810416550203017440025050780c04000c1480c591012040501d03004800d5151242114580a11a000d00410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 801370242 1250 801368992 801369031
    0x3021216030e06040b12270706031112011205070f060f0c060902030304030c0e01052403090106051012150605032202090a0204051309080a121b0314 65
    0x46942030321065454140750840112400001d40d16002d0342d08140c4a0b000c0c08251400406c00d4506814040d4080c01c000b45c120521403d00c0d02a100004200c0310303420f900c010801c20080f48a90311480c0c2c1594140d00507401c040c2552008074503e0030a0780900c65001810200e80c0921600b0700520001701690a080c5030114a000d030090f055402d0098182c0502c0415082003040c4a0250068524030780e000307042c0c81c9e44980b05e2405d602c030b030303000f500030940e41040d888008125400c1c940008802001e0170342d0340d80d03e000f1140069020796440149001020354858400043e282c45100c0c444002012a440d01c15210103001d000004407404480902c2d41000302c61810092150440f0480e5000340050407100a08107403003400003d4000300b0440250814508410040707a00c0c4198090402d84500300d440300042c2001c40e00003010380d6502d01018200c84001c00c204c07040f0314015036400c26144541c2002080804a0220075645105081400350100f0346500341e1103031000d244662940e0002070050000c0720200d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 801371492 1250 801370242 801370267
    0x1e180509010b0117160c0b0106080118021c0c030f320f07050f1e190203070203102007060b040b18041205091c020103050108210f070f05010603030212 66
    0x180039142c030b030081641c0345ea00700b8030324407564401c01c0c0c0d10f03000700004c01e50f545e59440091900e4002d00c200903808002004002602080c1e0003200c4c2103802c41c0301c010900d6411040300c000141040e801d00b20030715075100361070352100300a070003031004070a05c880300f40c015418090481c00051450041d0180039014000c200604c06084803440c4c0d030001ca081c0b0301030b61504415030103044180703c0c02034161000400c0445010f400070060004241c4014031040d100000714120034181d03901c2c000e080001f585a003141c800d0240c401905e500aa07420702c202078801a07080c014060646081c2c2c130458040d9140d03900c400d2190792509186c00f845003040004d50344190100c403100d82e81c0341c44100182006115a074000044182c1602c40c03c180c0c0e030700040c02000d0f04040841036804190301c2c201408100d011038200b0000240464012030040280d45212208040700200c0301c00d00342c03480d40010420480310341b0603c403079408214100d0b000c100e0b4520030000014032a08509000c0d06d1f01482150740c400544041204025004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 801372742 1250 801371492 801371537
    0x50f060417160b091603060c180b180303041d100806090a0b0a0917090405010e09070612150b130b09010f0509010306030203060a0c1101060b041e180509010b01 70
    0x2600003255010315103604030024117041c03c0324860702c0b80c0d4090602c00f105000c16603210342a102116214020204e0b030307805800780026024840c03003a0383c00f0309201c50b007680b9a07105051102401300034151703494541c44049440341c0c01c0300d49840b403429407002010070072003014050f42c65028004003030090a15180c65805035980d04070149004198040c0a4042083c2540070340003e44008e44c4085101500c0303c600c881d1807081c1e0410441144518100f1000141d4241e4804800c2e01030580403010b0031001e800e020064602142c0510300207a190303501c0d80c000310780680c205409006000500e100030741d904c201c64620002c4904030341208100c003204016405a60703810840030402c5043da414142d444000301001680200071503031019406000341d0041200794481036020542500964482d0759004c280c1c1000a401c98009005000000c2000c21050144d080b0032071807403802d8404001d031a0b250a40784e28120544a0007960202c50309a2202c0c14400d00003402c2c090040010000c0c03820040c101d080c01c1c0b0b40007050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 801373992 1250 801372742 801372787
    0x114040314040f030b0402010f0305060a050d0503220f090209240904110318060411091909030201061706040c09110403050a1b063207050f060417 64
    0x80c05401c48030014124600382c0d00201410702e501008555681024009144202ea080b0300194002c3c400f44070143c06031258034082c000140c0071000c2c1c03e0070201489040500840b060352070348020b1181c484440c80402e582280c030011132920790000c03403402d1060070300d020107a00086811401840341181315128500601a440b0043c00040202024958180c80601c203041450b9002030900000300c907516031300c1c4010350007107c034520300112140b0425807650700c0348400c2d1402051407400381c0c0d40f0206403074a0580241c0003072003510b400044800d030704600c03022200040c9044000d40d44030001008080a00458004079480101c080c003c540382955810366a01c03294000c22825a60b60013a140c4080ca03240e040e03d0113594494119403541c00981809410148140895581c0000304d80380428414403d05002c00e0120f0b0b113504a00b044104251040c1c1103000e000c0851541a00620044e000700d1801c104900344185100007030001820203050010380c00043c5440e46031060300c10001000307183ca1035207800340717103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 801375242 1250 801373992 801373997
    0xc0c0f031e0a022103092202070605061302130902030405012a0210050c03040f1401020409051b0405091801141e01081f0b13020c0f0c09040b010501111606091701140403 74
    0x7e01c0d549a920100c0d40d00d500c1c5031102c1030b00c0402c0050400000e85d103ea8001e10048070078495001a0b1940c4900f64031038010302c0311101c0301c002010410460b00e41c010359080f921500004c6482c00f0190a2882c00b0244102c01c8000c40b2040d41c202203500ba0148010300c000d0b049510240114980580308451920019000915000c000f111070018804400c0c502070400702c000000703542d0b40303a480c000040070300010f4900840280b0b4a811030b100701c200710b404036412a00040c1c022011540d901d0488140040920080d101554a80700600240c1c0400c1d19040e00c40c244401d42082190314442c0382880840c0160000902a8049501c00b4134200030b00302415000d45902c030300442c070300c03805401040d02d480c55000f80c0d454203400400c3c41f01d195940460030408500c40780c0100c509006100b0204102610141c802428081403880107000b0f075441018588a081e4003941110f042d15403260541c24200d180d68050000228001402d100e03801c0380203601c0b13003140b0b01d610081c0404000401880070804010700f00400307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 801376492 1250 801375242 801375259
    0x2011413020a0806070509040b0906101b02041d0c040c0e10030e010504060b130501050109090c020a12091d0c0301091d0102130f0b0c0c0f031e0a02210309 68
    0x1c40d42c4100b00d01c00a04080019640507040085014106800008419100e10304080a0030a00c1c200910b540344110b1005003095010341c542003098030781c518120310b000c4a480144c02c40c24051b80b1a4040c8c00301d1f40301a14480c011048650000b01d0406841c0503040d80700d14104103201d101540e020f44000000801166050f409894012080c0c0040402180001c00c80d4248020403040c000650b01903080c104041d14840341c0d4180e02548201150824012240801c90509051110a040b0360120440602074011540002c3d140e441f698041080114003c00054841c5000d00000c000c4211800e01024082c405a805050881c0c5022142c0014003414a0240c0d13280390b0b0006000d0030385220100240d50400856544010303d20b255401c40e21402036204217960301d40002400c00240b42211249527019000d05000c0152104014540c00101010340c3d00d40314030829582502135842031010b40300a0034009104004192050005542149045001d1115100722001090310040100c0384819030803201c07400b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 801377742 1250 801376492 801376531
    0xa02090301060504180501110a020304140f0913060c1d040905120304062a0f0c081c09020306070c03020a030c02060d0606030c110c010e1e031504060c020114 69
    0x9005042c035601c40c13a405410014810300d0803200034118800d5a004030001c0c80405078010022840e44958000100181d0040100300081100310b0743c01040004014000c0b240784603881e002501c1072205640719440b0141004070002000798620889107070480c0303410407403c00400c4000340740c0c600f50141c4a07140101d44402c40030080020a02501103041401c1100c9500c034141402c000e03004004403149200302c0050118804e6000411103010b414000550750740300740c41008684112009a280300040321130314000d100c1e405078025000c03100c1d008003c058500150b0f910980c01098074003074001c2c2c81174082c01080b40c0b510f00481d60108114403120740505000b05400f486102182c024810b83e0450302000d403514001013080c681c560007804415031142c0d80c20700c01c3d25401021540750703601200703454042a10514500223500348410f00c10800c504100c040c08040183d00e011034100812030425440080003442007204002c600c0c45400b0b0f1021107417000f04054640f150034035502040150070031110303100e812000f2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 801378992 1250 801377742 801377749
    0x91f03050a2412061506120f060f05221d12130509070c120c02120c01020d1404031704290f0f0910030c39030c080f0426060a0209 57
    0x1d41010280548284659501c1000510080e805510400e13081d00b8090178809408c072a01484d4156800d1a04c80900b240c41c0c4410015030080c40b2040822801b0f141d844001e0602180c0f04043c2003061211104110358280440f285c2010000215030522500c240038060030079a640c040c04096a40c15a10410300380c841c9032065424400141000b8403071a803032206c6d030910542c17010008000301d01c00c0d12400702420790140310326110703089819030900591281041c429900d03c0742c007001c0100000c03d200c1d203181540301d03224543d01c10085c1150b590007400000d810007580000000c11001c40c0b501100300f4007101c8001c4902e02035440b4142c218a8242c1000c0351102d2403010700000c6a5007040018408003481070340c2da001a02030a10700b1552030100766031412100d800c2010040e105d0340304589a040d500d032015041d00361240d06007440d009804212840440c000041c08000090211258007880903440302d1030702d0300135a03002541c5140e801060190503d550100f440014100e40c04c107681ca00b0240e241c4505130b011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 801380242 1250 801378992 801379001
    0x60801060e0a183305070c02091f09020c060f010311010e0a1d0f0c07020306010509070c140105160c0203060402010f1b0b0a11091005091f03050a241206 67
    0x4d04820445040d40001d900d2030103440004200c0c00503c85102440301003410211401150030101140039241140014685110801c0e80500302c1d15100d44c45030789201d4911158080381e000318141590001e8003540c1a1000c009180d030100c8008a088401e6065541342c0244102905090f814009501814945039452400a9024081e8030f0340011f49040a00c000d003409030b00980c0d2201d11b034240c920100f0140358140c41282c060540180041c1866403a00c0144500740300c0c010030031401c101d4500c41650001e403110000c0c1030910004400480c40c0c3c2000c8102600f0200c00c0320550042c0b02c5544807003001a103002c500c00b5440364090070500c5500c80d03c0e01055444603141410305401801141d090810480c01c002200d000d000c098400300085420740e140c05105100e4104101d5006c2030716001680098840c00c020420018003528020f500071602d56009031885200c410a4042a2900c0400c0b02240c0306e03120f244640940d5507403a0050303600541c1c8545c00000c0c030b0701540c034034000140e40b20000d1100c203410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 801381492 1250 801380242 801380291
    0x1205010f0c02030a171308070515040f0309080601050907052a0a0b01050f061207180e04110103060b0a11030f070c0e10082e0e070603060801060e0a 65
    0x400740322107100d00c40000e403643d1069184201140c000107a503075980c251104120311814001040d0700d80c1411a8490750819048070004880c540b0800811850400c89044002d016911500410560390700c0d500d0085d003200ba007070f000300c1d140e5886400104160354a0030a80303a0051b2250411554075508001c000c940c036459080001e018805410040d600b18100240d0307865181e020b04168070060362524108040c0108c2d03649010f84c0001e051189068204030113604680040040c207204240000398440f04c00e400c18250300001010025104000234031178840343c1e9001c808000d2030200480703400c1c442100341038090b4600300410020f2061141680f2141002295041d8140705500c94846541e89000425428280034200110140700f02154134003c403241e806d02030f0382807100500700d14090024112106405041d1005450305813107880e00c0f40c48075074422803402a42c001c0207482d805050000150545a1a92105044c3e030b15140c81004140140c2c1d03080390f00800d008002040c81040c500d5812840101c054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 801382742 1250 801381492 801381521
    0x70b062409042a090602010f060807030b06131e05010801020c070e06010c061b14040f050d032606030606012307170c030717090105030a0e030c01020c0102070c0f0b04120501 76
    0x450f0703900280c0018115080310350b954001d0100303441080e040000c0d60a0762141c47d00d60750003a9014170008030180c010680c0020040d00c2d442401140101100550754900303070381410030500011009170fa01440c0992400740c450701c4000c2d4902594071160980d035044900c9225014000032003ca1420b13841292440a42c3d608900300380070403c1d29004880c980c80444581d000850341a400c50a9202400c10a94080f03c0d603102e5103030140e5103000140110001010012800c2160868280b07011154880002800008940b41d1640c00e280c143e040c146400b0000c3d10f02814001046942c1400000c103010034800010540301603034440d081481d00c0b40c842c0c0300e4204010016203011610711800e10b0000060881c843c007034070094400b0300c01c00580d2420740c4505c420132400503104000040c054a95500058905055a01201d103804500d013540350890b0030041e6070011607500000c610b02440b000a210601810201c1c0d0045003c900d8205030300520f119071301c1a90032a00341800034805111084d40410880b24020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 801383992 1250 801382742 801382811
    0x120308041709041109040b091003060c0c060e0604031211161b060c05190c060c0c09020c010606090519060807110d1106150310090c0b070b06240904 65
    0x4132003a401c5100214096868114800c010340781450302c1d58003443d81d06440244a500b1a19120068069100307280d050000d00b0000300c00090091141910070300c054405032005040a00c0c00500301d0843d540201003003824515240c2d5108085d074102d8074100010090a1008856803824403148520450074480e010201e031700001d031881c2c1002542011038420425900d071621134040c98244481030794800740200005500500c0040c0c00f4a1404812502074a4407000f43d9076240b562f2001e03070384055240f0401c3d944807441080030701d07008410302001d0308003101c0c4100000c070341f8101c807035400c0030a1080c0d42c20001083c01042c1454044d0403a60070010104056130b90040000d800038010365804138200d600c502c1107200169140c0038508a40d031030a500200981001e108617201000a480d00600503503030442e0120000504d0b907030140050a01c64441d8811145520f80302c81000902c1480303902e00d4006464682c079141040d2400c4040b039940d034404480000c0d14000101c041d442c4040c1c0c03880c0c40c103c01c42c8407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 801385242 1250 801383992 801384011
    0x1120b090f010806160e01200607030f1a0f010e0d0c0305010219020102130303050c030c3018010309060b1c05070504091502030717011d0112030804170904 68
    0x650052a05a83e0349000311411074940e10703802011440b0a0016800191640111036410f61042c130000400c21000d040c0005078844a0240606120042d5420b030b0200ea6101c11905294903035014484201200316032003500380c1041d001103101040c8100c0c1c200e041100c5804400700681d100c8200f00c070501d03046044407038800c0d1a4500603000f03500c004103112000c0c3c040d0454682c035601c14000c41d817203001c401c1000c001c481c1c0385960070ba5054100c00d5032070304140800c0c4a82a941c0b9003c200c6160f0803441120b101c40300180144541c01d8000012160040202040005000250894081c8101e0b05420701c1c0000d0088408d0414400030712010718000d0b03001240321000c00044910884594120b40103100b40ca13039880ea10010130044419440c2e000304074400e40b924032815618140d0140d5844045401c00e912500401c9880d5503e0540980082c002d2000210790b000003a151101003601400c80d843d0000752078201920040c10106005000070094020007450401103c070300e0040c3c03a06240c02800138802d1049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 801386492 1250 801385242 801385261
    0x2190c0305070e04120305070e030a1109090105040816031b0f0204062705100f17070608010501050912010b0402040b0405150a080708040c0807030614060f06040501120b09 75
    0x940c0c03009568601c1520b101144400310303528140d009a07809242c981e000b4108000a90140070000c1c51101800309003204440c0c107803420701ca9480305510551010183c1d030a840201b05a40030b001e0b10160b0641c1c9804100f00c001001d2208650b4952440180720503005510f1404850340b0307030a108540c199220501a0f0000c10450710050041148211002d00000ba1660703c240c0010554841c030114862490780c0d0f15085951075803009400c89031001d481c0c00402c0e10782210400c1c03810242d000070324407104100c0581d9001c40c01c3c8071000140c11a071130402169490140001c3c0103000b408440c6100d8003030b4520743c1842150941c0900f0507640d01420079511603950b0308503600550005d00c6210b01500c1010b10003106108900211182c400d05503c4003411034980000c00c6a034004010801c4500c0c44c015940441d5100040115000440c412200030030482d0010002100100000d041d07a030042e4510503014a90ba640c900c15241030714000c1c6044944101c1d0304d0368107009400c400900d150400c1311542485071010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 801387742 1250 801386492 801386513
    0x919090c0e030f0c13020a03020702030303070504031e03080c1b0d02060603010b0102010e1b031e060a0c0f020a0201180b1b0609150105130912030c1b050a0605070219 73
    0x154100c00340e580c080141e002c4035441310340c0c0c5070510780d104124011449101c030b415400b038400700460b0301d001400e0ac032060740400d00c0c0d58000d50300d682c080386010804108202d01c2880f00c00c00b0220041c5948080701e60355034050002c050140200403c40780110701d002c1203000500500c4d0110200f40121088811000b5020791a0402591f02c1c0303008c3e5080031540c10440d401400340010305503440e00207080c04c41a05a0311040058001410ba038507005003440d80340014101c18405444841c220050243ca0a294281804981448503800c0a208141840c0115160045002c40e269a02800e048244010061034010301c18078036013004c04603a4000c99001111066a10008030100006040742c0454460403c855a517000c214645561040020011312050818030382c103101d00000c032200070030282c0320356a03500420070040c40740c50700183d030f02c40340e80c024a03903c240d980e20f001a200a03004c1c25030b00381d52155501d90340501006005070791540c0c00726101c00d2080006100c81b0403035441003903410900d0301e000b40040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 801388992 1250 801387742 801387767
    0x190804020f030115030b0a0606020705150702060d050f100303050702191509150801180c0210020a050904050f060d030c0507050925030c09062337050919090c 69
    0x42d81b8101c0081c01c0079001d486035400b55000364000b4224180f400e42046810080540c00c0f14501006010005c0141c0701d103c0a0898020765103030109003481d00400071000c1c0c88005040d10078046212800700046900002212220303501514030028a070901440d0880b82130b0541d11940e28004440703c16080c055200405e4001d84001c24582d00199581150489815000f80105544104156484440f49006901c070900000d501d0050b1003960108040d06804c90f004040e2080c0842d17000550548140b03002d10405130700281d000a100c655040400125540d08540d89000301030042d440c14100601804000360300c01080c00414084607440d01c100803c0c51503220103500c80000015030f200d400c4140c042d0060840210300e513a58520b80b986000c4c0c0466400c019840d1001e4807a415a800c51110104680241b5442070280c45c00c103145200f035500003031000c20250103070013884514140205400e500008482e90080b08071650f044000d40c040d02038580640c180d0002d030905140128080c4400e81043d0303001c030300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 801390242 1250 801388992 801389003
    0xb0714031518060a050d03021c030b030c2407080d02071a01060804030816121a0a0503070b0306300c040e0a03140a02010e03071b0b190804020f03011503 67
    0x40c0c50b0b0380540c41032a00192441980020380110a10035801d0104400c060240a48121880c26410746040c100c0d9021a213180030000fa1110802002800e0401400d0700000c006c8d554002d8054011000100f101070f900311000002c80001421030030301c0545401e0752410110250115520705191801c000c1c829003482c982c03081c04040c0d8000103a00b03401000c50704c2c400d640585038070b401d50b035030000106000c40d02c0680c02002d000743c481d076074001c00d181403041e03c0080da060032540001203070a408021641407140d20ad03034800da1003d0000d1001421040540ea0001001d0300c2c040d402d0050f583d030301080b52140318a02c074541c051050200c03640401c0004c8680181400b1390f01086801d01034100507446410042001e00801d0b2070030310044a06602c9001441d90040c0b604c0006210440004c400f07003540c0c0b01000c161502c24400344482421100f074024100106221400c071480c0007450b03080e44451156511003401031015050004040d51036600f014920f40034010f000700010741c914840c2e64000b00560000703894 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 801391492 1250 801390242 801390259
    0xa0e0c070c080d0c0b1008010510171f0b031c030f060504020a05090d050f0f1605010201020412080c03071a070e191a040f06050417010209010c0b07140315 68
    0x3180b00c030103d8520818001d5603907180ca03c1103180c440150008018006c00f29505e10b044c0b00060401c020700ca410300030078440c0b030f110041d80e181580795800c00002c50710307102541d0402e14401e84400130401c000e16000820081c04176400e064040068105031202040b81450040321400500d034a6065112000400400c6400c005082d1194180b0080340183c40c0b080c400708600b040121814942241004499071140049850503601d850034503090441d4145c3d688903a5104852600c4041e180c3d0074400c010700000e20003103040c18540000702c203070035802d201e014050280000d140c00125038103000f2188000d40101010801040715128074034a26003c4400100142032181e11030074900d085040c049900c08001d4090384d030642080b84030500b04c03e408082640e00c0304100030001c0c03464007600301000105900d403940d5440c5c2e032602020424100031140003000c00e0f48104548045aa00030741040c10f1a40c001c03e8542d00ca035540b01060f614960410810310340040007008102c1008a03a40215001d00d5081d1076004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 801392742 1250 801391492 801391499
    0x601060f0906050909041704140117040f120909290108010e06100203091c0302061003080301030b09010b030a050304080d0302192a05070608130506150a0e0c070c 71
    0x31015140d602402c0001881002103c03024600b030f00d079264105000e848000c00114036184800d00340e40c016803103030902c5411142d03035201540c1c1010780300a180c1100070882c1c5440c60503a035000d00d01301d604103000307210701f0305400d2103580244620b4001019040105041158000d80c50042c1000c0034601c540f0345441c0d0034140f4103822540b0840c41c2d241203c40355000ca80040e1a24800c0001d40000b50b6008421071000340401e50560f55200349150840032641202120340c051402d000381007040050001544100480c81000041c07030420403a41100c0e0825140541c0d501c910100c0303409400400700f500c0d4188607048146050040c04402001120450b5085030300d42d5110a1044e420b84c0260303081807082254403494500458011030070781800e90042401c91504201940151010343e140400548840e400100f090000301c1c1c00011003074021000d4220407a000742d80d81c4c1c0762643d0b130314001c03c0d01d1195074540e200281c0075200c034030303a010141458003d818400e14015000d040e40303400c1400151603040303403040e002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 801393992 1250 801392742 801392747
    0x1905070b0a150b0f0f0f0c06010807031101030906090f0b010810090201120f02070c08162420070b190302040815060f0a0602031908010609050909010212090601060f 72
    0x2c404040c01da4080042c860719110000340c01c0e4200308084490301d9820005640c01218590040900c1080c0080c2d15032603d0b41c10006501c6e2a5058100c881554808071042c404900c500e1515100c921003441c0211300c0c0006450501c1c003401e1041801083d00c0080d030307079030420009041c2c0c609043e0f40140302184d080450701c04c0e03000b0a80355800d002901141d031440d141a54112581c20542c13140320103013405440c0c6501903940c69040b441b543e100001c603821040024201200e084110802003120b0781e55060030800036804448090305200c0c10701309104c4480070b101c00000c242d030f407401d60042c3c8040644500980c0e882e180043d5501c46800c0b14920300320030240c110258003030310a5030196107480e0024030036841181414440340c1005003255034803000b4107216645507922091060041d04942e4091502d07540d4100b03040078080d10f80c403140c6060101c01c600512a080d88022580103c4a080350841c0c0991900c06c071540c024400d030003818080c00d01800400c039410000041c6503040f918076580d480328034146150304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 801395242 1250 801393992 801394001
    0x5010225140c0105070605041106190201060e063607230403050604080f0d1b0e2418031c0f030603080f030c160507211203020c031905070b0a 62
    0x241c3c0032810500015001c6030f46c0e9130019600c02d106003420900c1003d4000094400c0e001841c60400183c050480180c8465082c0103c0703004000c035107aa400c05080c8000020190100c0c0405151112080c0540700310088004100c5000c20501340150001c1d802d0644004215040d410010b003d0600300300d03000704070054048200e07000c0303a0300000a00900c0e10344d641d6500703441e030010300807454000c1d050000b103060f9032145c0b083d0b0b090b2101407142c508103000c260002404403402d035520315224021403807048080000074034400c1e10071a01412610350304c04d84546044440c4401d12030b19600351040009042d281401c950714130b0400c100303d84a07172241c12800603046043d21064080205a50342c14050020481d0140019680140341c440c01c140c240141c41c52035140400c924442905d0343c0d1700420040100c40541400c10301115000300310005c5030041901da24800000808071801007660005806001600600580f08080040503000502c0c25020030300801c2d54000c40303019180d10281c2c0d404a91040f0700c41c4034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 801396492 1250 801395242 801395263
    0x14240306040533100e01090516030c050f120106110a031e051b100b0102010b031506041107031706060909130501020f0a09080c1503040f0501022514 65
    0x2040399051081c1e01101d1400b0400c1c4018441440d0b010300451072040301c0c0780c1440313800107030a40000c0c0c2e032816103a14182c0c54180c0c40781c10403500d843d0603c64075040c41d48030030107861414100400c4a484032001200c041c40307030040a60000b80c0100d0062614143d182c4842d0480c1e803140c0c0c42d111030150030318415848540c80c90005002c909803d02a100c41032091071440d0704441141402030600594122140100b8009216032105410584410f06024028850035110b4030b03081c8002c008001010000c2070307945441504201403048900000742081e5030f580c108489404400310f0341d0303448450515000e4030899101500f2032140c2c030500002001810140180c03807203500c00429080040d2240d0390180c07614096000180d0340e654003001825807100d02c0d400140b59070001684c8902c0310616103200a81416210600e16200b0368001300340c201502007003415070303410603081201d061a075000d5103025402445901d2501080c508902d407103030303d0040c01040220403c1c0c060000c544548600803201519040000c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 801397742 1250 801396492 801396503
    0x20405060d0e01060b03090a061b140c3313110906010201090b24060a02210c0604030302040504050f0603061303170906041214030115031424030604 65
    0x8004482078290881400082840000540191124038102d184d034000c41c0e486c600c81c1d11920580081010510440552481540000101c0301001800a0074000c1140041600c8980850507120303506040c480701f03081c180c4070200c284081050000001d11107200d0350030340645003151000985001d4446e80500c805a900c082c0c803540740100d11040100405020b0101c6045650302ca0101d400900482d444034091000b214084201900c603103008040d0700c821604540c00f58105020380000e460b00001d110109501c1c125807044080c00d41e0510f142c5601030451180854407811040c00181a055401030060b00c5041c2ca007030280d641c1d4100c80440103030054a040b505a40000c00040c0022103415292901074440c0c40c2c0b6a51b08110b0010b00040002c0540702c0070301f940c00117424401086000c08110041d0a46400c1a010100768000030303000c07038001440340c0d00b1650100c3c400d40351858460307408091a01c80786540c1805a0808134010811100804030600f20003e48032180015464005103042c4284da104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 801398992 1250 801397742 801397747
    0x715032a02100507020115080616110c0d0201050f040311121c14040506070b01150c034b020f011505060d0b0d0303020a0314090c0d0c12030207090f02040506 69
    0x1000b201000b010b00519250465603200c01030100c06104030800320081101c6002800780703003050002200c815904513842d405210480c445c01e141e00c00082403030b60801100716002c004601c0913000603102d9100f140f414a2200000140100410608540c084071520041d2800d089036a4440d400569030b9000080380741c60040c112885404081c840c580e00c03003a030a241000d00d810103076214040b4081c0c0c0c002190890303856011000502c042c114101e11031171981403034906011500324984014040c000d1113140c000240340c5a00c0b00c20003141c400d040289103c0b200c031144080c0c1401d081140b00018030702d0040c3d2001406003007200443e522050040030025500c3e6803158040d940b402042015981c00300b9078000c1003a0b25020321211594919410640c150300030f4602594442d007605006048038400e03013a40540506140602c43c003000c0c00141030303448840607501c84001c51400d00303080030601da0a520130005008600441700c10160302152610888100007400c4c0407013080d80382c00b4404c6c4d0055008154204105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 801400242 1250 801398992 801399013
    0x203340e0a050a11040305060417031b03041b14100323091219080901023604150f0e0f04021306092a0918020c0715032a02 54
    0x2d6000c039400c81907070503001495010001c0c3c0f0103181e4010b64029140790b00a01e01300002d000820840391445110401c800386146040b0351101c000840080080e62080c4c00400040c0030071410502e483d00d120010b1080310100c81e907904104000d66804004107000340e100742d000018403030007806110f942c4040140303552042d0324040072840c0078070401480c00a441c07050a0405010850300743c010000200102c0c2c100784030081202001d45580c0019120f010307607a1040120300000440c0320310790a00580c007a040c042c422030019444144105901b584290300038035000206600140e101c0600088640c6116040c40301c55a40f400254440703011100c0b283d183c60503c00280061800783c43d6031003884c030309400029159441761082c400301c500c1806a1181055548421b10b06c0103c0c8070102900300c0924503010681c10b0414200500d040e0210a001000c0c036008141c90003202400d120300c030b0181c6000c8002001c803180d43c00700100540441b0030b0164449e103c8041e81c04c680512540300031144452900100455040e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 801401492 1250 801400242 801400261
    0x82a01140403060906020316090f0501030504060f060b09030d3905010f090309090b01020c13020c150a150b0405130209030a1511090f06090d0203340e 66
    0x2035034a106109801044080000303400d07841403900560180500585a02c0c0c881134110b0403000c0c2820340e01c180030802c0d904215076034950803030302d003510001c3c80c01046903111454100080c10714120101501410400d000c180d040c2c8403000391040c40c201720b00715540310400400c2a03c0354030f00e1104d4401c1000c0c021602e80e5121108011800784810880140d025600c0d05440d03942c02c55007601e01d50342c00030f501c0d480d0000038194000000000307420a06c0c420480d1000100000c0c0d60b808003400c9140c0642000b641c040403290542c1c3c107803640e400d10308055480c04141141190300c1031004960b5100303400c0c503000702c2c00d0302c2c0404821840140d4000300c6040d8503050400040000004281c00b07170b6840603800700300000250b142030100150091041c80b01424501c00424808140c600e45051a51545802c0c059442c0c9607841001d01089200162141030f42c9104c8080030070452042c02d43c0c065050310425541c00164208000c90004000c8010391079444400c00f50b0601050b00b44a226403a543c0c00f101000c1045840f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 801402742 1250 801401492 801401507
    0xb060d02031b070302010b030c180a1104080703150e0f031206030c100c061a01020307170d09030c0b01081902131506090f0b0708040608040c031b082a01 67
    0x48400c0c560341065040c02c41848116480b5800403030050351a4940120f55050030825600d45040444043c2d040200980c4480d00e01c10303000307104054294842e104102044250802c44010b011120151075140d40c6070b003091076240040001c90028207240c05c10007100c001010a50000c1c0300b0780e07000554980041d09582407841e1034042c2a00e030b410b014115110701642d8481380640a02d80694407031104503d60b500b845412521045512490340b0345850030520b45030fa000c0101c1f41d00c59408040c00e43e5070003001202c61500c1c05203998280c015440c1c500f6440034180c105040900540c460807500d107081c0c1c4c0340c6290a845410800d0102d6044400038031071001031800d101c2502d0342080c0c0440c0005c141d100204d0004030420654403a90115140c41c4040c09a1469600c8200140c8807040500e4a002510741d01c40231107101d03911031041000340d2880030404100803c11389800031a0031022039a14926400301c5140780121074802e0b0300141c841c607601c0d01503c20b480c000100c0b20b2205664480184d107010801959840d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 801403992 1250 801402742 801402751
    0x206131205031f180509070f1e0b0406201c030207050a06141006020a0f0210110f0c120606130e0c03120a0f11061501030207210e040b060d0203 63
    0x107040f030741c2c910846841c0040050044c28200031030070400f50801682c00072070b003001e0019102c54000f500180f242c4400603401380204c941c8540c0e040c1c59000d02d60711404050005800c55a040b54000600003880395000d00c003000c0030f07901954075450310501c101c00140d48000c000c2040f40040f8041b00903c1c45607002c0d5015002d264000c1e401d6440b00300c907558564080360413200c81c6480c030420042c00d000e9094000300c0c1d15000390182e40000c0c00124401c3e2160300c1d10705020344009110301d0100309200c2c0c07200d10481c4002e0b0781b1008441100c40c1800381b125103540364012440c0c0c4901030200004071082c6031a00280340ea000c1e0001904401081000034441000b40c03c586071840030034400c0404412198030b080104604507043c05c0d40094455041000040c410030060081c40c04001003050390b42c2c24400c0104645d81c0000c2c411008030740d1041117400580c06401038544c003a0841c41c14882089a031580d0009501303052080356600f0000c12a110b0030082101d10149000350000801d204002d164043c0f5402160407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 801405242 1250 801403992 801404011
    0x40b0c0a050c1005181b06090a0f060534021216030c03151b030e16090203040b0603011a04020f0d0203010b1201151205060109090e0c01020613120503 66
    0x42040c03503002c0b14030707000d20303140c03071400480e0358004001d03d05405003406500000c0031340140912100c82d15002009031900c510581c03050000061034602651062202002003860858650030680e07610005401c0341c101c4031204600300d00309041d050b218140c4880311031002012415035140c1c005544c00b4443d00711700b0084194141d10035080c9042c004403004050100840c4100042c3d03c099085180004583c60528007100d000d90403e20743d801461507100040c0e01e03043c01071031b0000711888841401407400e110b150111880309052240420031002c56001144a032340071b1404214161502c405050032680003500c1c0c00c0b40c1c040f5403401d40059243c1500200303001900701002604003803415052404990084e4803196411400041c0101088000034610b401081a80324400075000d0030784d07028010071000748003030035060394600025140c2d07070207100c3e8803000d0400c80c04200844a039103882c4a0f9146c40030b1003098058070400c40001c804071a404a03d030300440c1d04c07000c8042241c650810941d255007014040311613 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 801406492 1250 801405242 801405247
    0x1d06090601060f36030309050d08120405120a0e09060f010f03020f09100905090a0903080a05060607050105040c1a0715020f04120c030b010b09030c1203070212060403080609040b0c0a05 81
    0x10321325030212802d610350036240d00c0e861380c40c03851401824500080d8010707409100d0300342000011482c0e20060b640742082d00c5082c030342e40d507070b940c9071840c10180855540f0020010200781c216020741e0051304924444801d440000c000d849200402081003c440b0041d0300103103101500b004030303a00c2a0050710b910b0303480790302c41800c0c500340700002080c12201c4581c5000040700204100700740d2a00c181e0781504040010800c01407603807035807030081225500400740a115520b0b5070122b1100e413a004102c0d000c1c540c115000700300300d080519080f00c00100608c0703019518034005c0c0f449e40400c0141c5044828442d440100099440040341e543c502a42001c101c00401131424000010344d048248004a034413441150203594081c11403512208002040e0070180d00300d0000c0c0482d075900e03200042d07801c040c0341040707644102c2c00c0c0111400c6481c6208610000b500a00000301502c003115000031002e020301e1203500c0d01440390f90b400d03040c412004411503003d40300641030300109008500c840b00602440c44d00346421803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 801407742 1250 801406492 801406547
    0x30c090e0706030c0e0a17210a0507140307030c17040b030f360d05042105071e03020411090d0f150218040f0b28091d06090601060f 58
    0x180c46900941c03081150350314144011047c0003017480220400d6400712603070a4004600c4205920301e0086504013024810001b41c1c2400f070003070f010007404102c12440226036580e034142c0340c010810211507000f11a203142040001d0b2098100b00113a4050300c0340914002d007180d48010741c1140f8442c0140a114010220074078280f1444498145034058502c014400c05084c03213000a9980f408110a064108002091105000c7e181301c0300071600220b04900c1c8242280c540f02e04165003000d0482e88844001348940c908020540310b100c80c0c51003201d00884042080c0c45140115208520840d580f659014400d03880300300004a1140603007030b0f010701442800081210029007041240c0c04041043c0c0010040300503510145058003d01001d44c00340b500074014000500f0116000c9040011034032860981090103840d403041940782100103268808040c40181e0020700d000d0a4402203032079207901c50080360f000035030a000000b5194125a85a41c814035030150240c0c04442032440301d00e601540310031940500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 801408992 1250 801407742 801407749
    0x3070f0f021f0513021f11070b0a0f0e0604060c060b0613151e03021218100f0209150702130b0f0603190905010507020c420f04030c090e0706030c0e 65
    0x402200001b0b600710030381030b101040007401e1035905941e905100e602a841c14444440040103990021112303003040101513010317440650745500442031154125001080010f48150700202401ca494060710040103900b40320310600100e03208039800201182400403081000c80240940200c945845d807404143da800c003121840320440030801c000c03000a40225003030103400c0968001980002a90440c0c041580c590084241c403400040842072419070742da24060305842c0140c045908880c002440c520050240c4c20310014176411074003043e4040d040600003019058424460403408010017040c0c000000d650000300011580010401990259000620080e49140d030007000485032040002199602d0802c200920b41481101c40c180304000c40003425520709009007120f1455054045a014013038101d1813010024030011007001c060450021b0100078881155001d041964031850561100c01e0b92080080181c4400a005013142d8000440801c002d60086d40003020305520744c1002c003000b62008001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 801410242 1250 801408992 801409009
    0x3080c150c13050306070f11011e051501050c0a0204021602060c0a02031b0105030a05090c060318060711030307030c1110020c060f1e061503070f0f021f051302 70
    0x448040c000102e0824602060500d440300540416402456145003050004209022241c0703101d0900c81c00c0010a07484110039000010040d00c4c24018000309680c1010a4000700307412034071003890703c207680c2c540390007584114103c4604056000040a080417141c017000025800a4115000b2808000c801d03c01a10b8600203004900b180b500541840d050304e0040c5410300c0740980391900c0a2900c40000d00c060707038121041c0c1c3c2d040300c60601d001030155580c101d0945411501c8586070303800300c004404c0000000c00019101c59074120203066070000e07101c0700360568990800c5403030203980b07400500009007007602c07076848000ca01c8964981030401102a092480c10000c103055810741e5640c00003002d00d0440b00c01c0040c907800490074402da807542c2c50504610304042c0c1d00c2492a0300c0e5400400b02040c0155194202100c018081c030b900542d49042918010340005e06800c000000300b00d0344082c5030691800401c43d1544116610001007141c040034400d0b90003040d008028000c0301c100c01030b029000d070301c1d05040e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 801411492 1250 801410242 801410251
    0x70f060203130501090f120f02120303100b090915041d0c040b090615030a09051504050c04152105070305031c02030402210109050a0b010f0e0903030103080c15 70
    0x619034035010803103084403607101500101d05210111208100d10303080031b410307a011221070440b800507006440c0b81c81090703001c0c4818040d5202e02e824020842014021008500500d00041c0f502107103565104464003078010030700174585c8540740000156140013040e002070420b5100070000120394112520503102c40f201881e03240061703800b00d155107806007010310490f0b020120032038402d20031380741540000740c114419a0304411500004404140c00c4070f501e40050029a61200560b0f490240d01260760f9903410741280c0c103540d24070034094400218100340c420b0585038202c580b844402c01d801d00c845006084540d400c4109856000031410010510038095000134602c50b0f005155550b40b506c1259009410020855400910402c01d003c0182e65042f4030310054108448682260460080518010124040041c01d01e014501050003000700c81c5011506070707500729200b503200d551036403c2c505603c90122014445a881080148003240000025010720384041085496407603c1c0c40a81104104c203a8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 801412742 1250 801411492 801411497
    0x30c0307062309030a06020c12030a0506040f05160807090b040f0f0819020405060a090e21071e020a0f080604020f0409030e121002180f0102010b0a0e0702070f06 71
    0x24208182000c40724003644000850605241040349000c0000d44611455000610700360340040c401142c00c1c0c0c2481100203249d040d0304400e07100d160110280016020448540c3e205528001c2c0c01e140120180c03041038003800c0100e1800803070030140314041d210b4070383c06040481800811480041c0e40c05441c001040502803402030100c5462130300300d0b604115000ea802416103034110300b0303590020064520f020010160120f402264603110307100407d40700461500704240113414a803040e401000e0020300102c50b0043c3d80c4180d00b0000740c600d8407264134004d01200904449c0c1c88410420701d404814284509140010700031030710142e41e00c52100100e600c0d980701600c80d8100368200300552805070f00c05020f283c0f0965042c03050b450b035a6402080040c2c10b00c0c4a5106c2c03140d61689101c40e4408101e48440320260420465940e44d4145410f6031031341103854050300c00c002c41210303103245500c18007414000e043e0180809a569060060740380090900510343c2c4214464000005040c20218480c540184000e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 801413992 1250 801412742 801412757
    0x8031b0d0e01091101080f0721060602012c0a0320030313030f0507151e0501060c06271e120c02030d020d082701050c0405090a1a010e030c030706 64
    0x5141002104c41403d0300141030200140420403107401c808001d543c0f0130310502d8a030050400c060940300b003400103c800c0b203204d10314144c0040380c030230340541c4600c0000400407044030501d0000d1011303103000911206142c0590f040385685000181c010000c0102c900700300b0624003038441644810780e196420450b400000c5075034090000062580010a240c810001d503e40f03180b41c01c1003a00c480e440c0030400d503500b840c07031583c500702107103210304610384403000d0000080103200d5941c0d142001072030014521801c0d41c149150a0030f9180e103508103003034501003281c6140309000c030380c480e510ba141c0144a500300f50300c0c04403c40c4035540000f13020000700b000c15060340d88417205031081c1030051502d0603030008031100c255031011560a80c4690455841030b8800e400c070302c00e007040d0300c03003a0442040f0f0500000314414941c00d000610401c0c4006c44041d1040d80c50581d4080d000e5030307491240038162000740c400c00d50400c9802d9140d51255201d01e226034040c840c081c0480d01e150b100b040210703103041100d504c64400a1040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 801415242 1250 801413992 801414011
    0xf0f0d0603020a1a03010e1503060f150607050a020f280e0903030f0f10081c02010b0109030b01181811010e0406030312091103070303020a0c09060308031b0d0e01 71
    0x40e101d41001380c810403c00301c4082200c202d00c0f1000d440107005024101d6440c0f400110341a0406400e84050704018040c1c510342d082010558814000503540e207a610f900e81404c20316175040020a580e0160340003030003010009215004e104000000100060700002554190305034050b4811802d000d400da8511780a0100e440c00082c6620510003401905094008006106c0312800c1c5210f810b03081700c8880d15501194039241c49290400e0040d5001c1c042902810451500c211140f45410a05081503002480030720f41840c01140c0490050000805a009000040c07120400300028030189003c1c074140012118081108840f00000c1d6650031500390b41d08442560807035a00815184c03051340c05070303414022513086640140141d103210010030340075a615960320091020300d14407240d0910300030b410764a0303083d22410000e4446906950684242c10806c100041025036440796808480d048035655045444505405020b6409200f15640b0030400344040c919a01e11807142c6080c00b2007403800012030052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 801416492 1250 801415242 801415249
    0x50103060905090c0108060f18040b060901032004090204020d090201030f0204060c030e030109120809010501150c02010302211503012304032d05040305010b1f050f0f0d060302 77
    0x2481d400010703a4508020a10040100004211460707510900b002811507840c06d012644110600d0410f9600c01d00700c407040c240c0c01e034141c40c0d0325000720b004e00aa0401c580d684024860500000e00c402490310f41c2d50501f156a42010103548a55010000d0011825540c6034000400f66007112890b140d07142c1d60b6060250841d070f0180304029541c2c08852085d41454030304038010780f00b0b8040d500c01400303011604500141c15a000e6201d0340d81541c1c000640e05065415001c010804001180c40410315840c260020442c404508915207146900d40e039a00a500d1480d401103011b900311410044049818111541d94803c1c0018114810388040c4403003203503441440d04150039181100480e8602c180300044403130301c0340300800d0019070142e054107095500390800761481051407070100307921248070092120b062001d80d1001c000d2003200e00410003440503070164400c102c0858034000300c0d422201503101c21111002c0c0100c025007a00340000b51450304101d0544468502c41c0d00c90440703618446c0d55000103108628 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 801417742 1250 801416492 801416501
    0xa1a070b150907020d0e04090602040e1006140c07060e0d051515040b06030109051003050105041a0601110606090a0b090907030302070605040b031506070813061d180a060305070e01050103 82
    0x81044c40180074810614401605400c5004021401640c81d034108405000e456012103000b05400108500a440c1041d90650080d002d8007805000070708000c10044010180415548040c030070401a10300b66103040410b0301c0c80380700001c0e8280c2001b00402080d02065041c13108040f0507483c2858007240380313841e9841d000e40601e0038a17400c0c400d0f490200325881c9138840b031003901d0648440c4a000a0180c036104000410401d150340000d1042d03007080704010802503001e06042070b8803c00501401c035901c460006541c4002004400102c990121001070107a00d40341c503c15412600c013810000d04240c400380800c4024400320b8980c1400d50003140c0400030142d040192000901151030204e06090600001c80b02504c0b000d8200d00400c5504504400c0d9030b03444104640845030b0290255981d84001e000c038282e050b2045c4200c001240c0e02d020311207180c10000d08400c0c50120001c08810000da003200c0c1c02180c0c0b070f001810540d0b155907030b0140840059000c0100798094100040010801d6240c2400103050300e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 801418992 1250 801417742 801417751
    0x9060506090106050c10052a07150603031211090409050c090f0f01030303091a041a01080316081308070605180307061209170409021c0207020a1a070b1509 68
    0x80304005c1e641c1c40d448007041514aa0415080100d05500c60002a40c3e12400710141c450103440d00c940040007003400c4000402c1140e1051400e9450303001c01c90118001c4030910303c80603020652002d88100c9940d0258048501031020155090804060320302240817105880340455030b9602903030481809240002800d0740c4000c00c2c9070760003000d213840340036103a0400b41031000030185034880403440308008844a042c3c009142c668401912440c1034100152a5068800c59054a0a20800206003108084119140e1080307804e106090340744a44c1d115525035100310f6018480140165000c20007070701c140031400041c001a0b4660303403685501c50f05900e51200318003d25109a1120008112103038001901d10b001c070540400016407a001d40c10104c20171400c07030030314540d05180002d0120f004030307069014080d24032105580010809950349420f04920445401a40c8128500c2c82000764005c00c080e6401a812488002801c1c01c00c16603410780100000d48901903580803031200c44000342041501558070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 801420242 1250 801418992 801418997
    0xf1b0301090c110604020d0209042a03120309080f0c10060e04021e0a050108071206031419150b010516080301092415020703050a060605030c09010815061309060506090106 75
    0xb85d08266001944502d02003100038042e000c0d1000060501846101000403517002016440600c41d0000b01301c5070094245c00308450b440d0314100e030480203602c02e1041011040d40300050614044d01402440f840e6001990385203003070722803050b402c9100c02c81c074091903004151a004101a6081c43c3c8100300e50940c06c05c161038009209604000300650340c2d10342d03075000c0754020709041909480e440803c070390300880c0288004010b81401000000c018070481209140c05244003030303509214811081351040b40b42c4131800b41c41c10030b1229614540800d1a804441c003080c050400c0c510b00b40800c80741b4410100c078a407041c0c40107107002c00100000b21650041c6e04c421001407080c01b0904041c12144116080b4900a56051285855400300841c0c0200554409076130404100ca01d4808a0302d8040003401a50140c107004e4010703601511018105008a1810307101c3d40406007400b51681c850300e94083c98024109a4040d0b0824600c81c05c0d4a070521821503e18007032000411700c2c2c80c10b0380c14401d050f4012382c8a0001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 801421492 1250 801420242 801420253
    0x30204060b121306020706090f030f0203340506010905010312050408060403030f110d1505060c0709090312020304060c141903050405031e0c010c0302040b030f1b0301090c11 76
    0x482d44420000c03076102400090f20b4481c0d81550078104001c0c0100f500040a5900c0e202c510400e200641c90b07030314806031107507843d40168083c10508a84074050308910302104020308ae4902c1641001da04a40081c3c5003545070002d4044554607620320f88802a0310412105075200c2c01030043c00700e100d1036244d1000131810b10034a05803a16403066600c440040002c0c042556440c494204600c0300c3c3c02003122100340c02281c58403410718520403001003803401c4440d120904c82c454002103d0034042c040d03a4424801c00083d11a89143c003201c04041d202050f01101001051000700b499480c3e6440594000e50041c400020041e035131282c0604a0018520b402000c508117110242c0010315107044050b00d0701540c6004240c0d0380b00c034038041707180d40140020300d4441c12181681402c030801c1c4101502041c035000d0028000005040c0003503049100f64012030030844c904000140103c1c4070320720b0702a004448582c103c022402111404c0019400030381000e03030181d8452078000c12055015201c003240c080154064032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 801422742 1250 801421492 801421507
    0xd0c0f1803020901180906020408010c0822080a02030d0908070201080604050c0f1308013305030307080c0f07090e1209030307020f010c120e120f1f0204091401030204060b 75
    0xf030605005100b20200c54400c00c41c8011120500c0d00700c500c1150340700030250340311522010140e001c1e00d6840f1900000a52282c0040c000d84414070000210b16003410141c1500041c0c1d8640c1d107800d40c015146001944000c00850051091901c100303100907001d441c9807030f243e407564030005007981030203000c4500c55424001800344980a400440c0c085611200a203550350605450f6040c000d581075108841c00d52070303d1102e040c0d80c003075040f0a810030700c404804082c2c8001c501c002d00704511141c2c0510380d0103610030b00c16800094010070091280000203411600c48000c05c503149481d140268204100c3c0030b4480c846440803041c108181c2c141c04030100703440c80c10300c01c0450120780e8170b0142e520040c1c45a412619240c2d000d034094070591382034942088410000250319000a0050118020403030301501d109540344440040216480c00506200000b0f010140d8280d58400c0325034151900034115540e08200020300b00e030080c8242c155087c8010b441d10301e15132450041004881960380080340301c132030401568 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 801423992 1250 801422742 801422749
    0xa180305071a191b15090204050c0c0a0b1003050a03091401030207051507090512071d13060c12020a03060f051c060f06031211060c04060c02010e03030d0c0f180302 72
    0x5030764030407203468540d0008480305009403901c0d803004c0000d000003010441040c00540d640c0c010410081c000c0c0d90500190312214440ca80c10b105d00c0c154807445810000e401000100c1412240e03810000007601c00c043c190b100d4540a0400d06400b5044000c0341d001d0604001804400300e000909000900b004c6080c914103072203440c1c440807a0500c031503030200c0c480000b401c1e541c09030362a000680000b6155401615141001c0c65840119008071300038a02100c8034040300c958078005041c070400c050301c6040068040c640d40d030750282420044002c1407045004114000c10800d1025104500995030b0204021b07203454060395840b0100e8018600800c60b101421000010071808104482c0e0710840005808006003c2074004000030340000341094180788507840305940c859180c1d0701c110451030a403010ba03121515071043e1841580300b4840400c00c1030390503001640c0600e050b0f50b440c1030701800b40e134500408001000219500d41010001145000700440c40c00c83c0d1142900c4c90101a10241501540c10340c0c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 801425242 1250 801423992 801424027
    0x1060206010f050904141617120904020315091e0c070819030e0102040b0a200c100e0a06170a0e0709090609140105070318080f0a180305071a 62
    0x445000785603080110b0100403055108000b54144901610907d4490039a0030030343d48403d2081702e00c3c241c02901116564480442e1180e80103102000c1c062038282074605020203500000c00c4041c003440e0010201401d41c4a60010500c0b501da0010411520b8003499550503841c00060004560400244070910001d511103003203400041100922044004030807a04901520009034210b5195001180000d41030013068003a25a100e4682c541c1000b2956071040310201c442903007000e410340c1e0300510403900d8600b000d2511107004042498010780441c0300802150043d2001e900c420002200c0c02860020b2000c02c00c0043e0f00040202e9003400804070180146540c1d80040c0690783e00a541d80c45894100800d5600004500f0b90280c0c42403060080408020300070305044941e200801d00744041501841c08000e00c80200550104d0742500309030581079103039031540050705410180300780d4100d0000d0040740061044000c611520041550505040300d0b84007406a0310152a2004e030140318400307002190415 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 801426492 1250 801425242 801425249
    0x1b08011d19140a0b04060507110a0308100f1217130303031104080a030206090c030c0616031107090506031002070f030f12141014060a110c09011502010501060206010f 73
    0x501900c200894180124030086880b000c400c40d105410042d001c014420110a200d03c1c0110010009036032003107001d5840c0800905104090b8100141c8070b400a4000c1d815a83c00500b4050401000354070340300c5d480406500c07074100a036016540f0700070104001c0c41280a03c0980d61100003030382402054801c220400d02d860100506254880418021000004060b10020b03d400401c648a5460a01703000e9200c060a40d110640e85c010707402c0280d854180003a2024500a01520041c60200e0b00035004000700507d100c12010429050085000a0010401c0360f01509081307800240c28285582018581442a288402d88034014044400829003c0000d0307040b5a0700b6003085000612014000c0352035a12507041000218900030743e2802654854140502c90701103055802d4556444005540e0740d224085074981d03101908200708400070b407103010a24006042c0804543d840a9100e00080149809030000801c3d0a488020107100316030900442d801800b280c0050302241d4140500415560309500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 801427742 1250 801426492 801426523
    0x3091003091703090109080d090203010b0306010f0b090d140714150301060806030f07060f11030f1606060902071101170f0c0c0a1703010806010b090108011802071b08011d 75
    0x200040ba01c10081d0002845182d1041d1f44c0d40c0d4805205038408002e0071082000c0e0301a46c68110b40da455401c0000c1c14a040e113060304004904649800b031001e030a41d124401c441d80018050302803100185ca030300340900c58010000060304205003001c10081652601e1482c81e8402c501c001d017503000d0268500d049074151215842c0c50710a81d91140d0100340340030421000115944a1441c1c0060f190b40d0081004441c60119904d0070b46c000c120104299803801050340c1d01c1c1101071304001c0e281e40a0b070143e005284542c443c40002c82d1290707481c90100c0c01c0783c100c1c4a0986254800301744030001980c1c80207079041c201940c115010401d080142d104000d01354001c0150015000025117002d2035801088861505a401030b802c40307402c0d8111a180e1410b81080c411a4020300c02d4030f0011039280ca4440913a006030300c040e900c404d1240c0c80d016001e40e15403100000c03200c001d036081051a0224070103d0380115100c40e0b411841c8030716464045564211805c03010409058001c000280c01c00a1000c80c0c41e10540c0100c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 801428992 1250 801427742 801427747
    0x611010207120e03010b130e0705030102180f1203030c03010609121a07050c03070f0204110c060f0406270c051005070609020307051201091a090303190209060a02030910030917 77
    0x100203e80140b45050100e80d00501c500240ea804951f04d03042800700455400646030000d0341c032814182030b402141181039041400501c105075500b04010781781400d850080c0f801c070304202c20700840c40c1145c1c0140e4215000c90f0001006014080d08070715800010211f80340803480d402e019031500129081a0304c00f070021040f241c404240e800344660151002c941c444d006890b030307441d524504903030101c0003118203e000754280b40100c210601a9015200b0942d9030401030107041c1e503050075402070170034001c0048402c1543e500c2c2c400c0394840324100a02a060380c4440a200c6c00c3c169080180407000641d1000748a040c0b42c55050941541c810700b5591501e038404004244060b10344002410800d064110710340140322003243c400c0300c8a054008524542c0520b1411186c100440707108030825004484402d4142d1041002c14410341c6000161402c21400c180014101082000041d08030f501c05440707500141e20106030001c4600e090101d003107501205090401c03090a0b90398401e01d82e4043c4115280c0e106001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 801430242 1250 801428992 801429017
    0xb030a110903011107050606121009211106091609020304151407081006080402060903100e030a0206100602060601050c0f0d2d08130302010b0907020601061101020712 73
    0x81801e841e03031070314010000e1101140c0c80082d901d00da0000e5100342c0b418859400401c00c0e9042c0326402d1504502141e0140890b0320740c00f444e0302e020b008010000ca074803e07484005039250103801c000303c8030340c2401a43c51018100040300a149008005482c0d0300c041c2e0840c001d42c0601c01d114030518012110101e4001d42c40395105d0818214004800b8808a1098101400712400d42c4000300785d24072a241c181c83d407000c11389482c406400680b10a015000c04901500c001c600540790400c00350080c4c010003012154011362460b1100309442a0f071a14941c0c81c0c3c0041202c072100780d010300405601c58086001c1d4004186000c4000350764580180810b03050110001c1e400d00300c40e00c28400904058006012502a0800d03010024154511061050740c01c1040368840030800c240d05816022103d42c0d503541c00301a8441c1009903078000f22516049082d99a122070005070b64884200c071600c80e540c150058103540d0714216001d064901070f44d80148042e4410070642001600010340105060078505c0c00f045040303135 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 801431492 1250 801430242 801430271
    0x10e0c0d05070b0304030906020601170709180606080c04111207050310170c011704020d0303050c12040b07090509040f0f03030e250f0513020904021c0e0111040b030a 73
    0x2a036007184103103e00000c200020f054010b0041011900035900310b4020703a070388000c012080a180c104400840e0080c8100f0440081e8642154040c16180315988691007515910201120400d03803200312207070054a00b210a625092151501410301c4221540c0741100e640d450340f1350580002c0c0000c09010000c40481c600c002911100d002401d00714030b002655809040c030407036076030050020b9240068110440b12031100c420700004e0740615030141900707002c3c1c2d1269078290702608000703000e005070803001e00901640c00d1040002a000d5030040c0710303080403403c004000030121000e50300b089000c0c0c2f5040c82070100055203401c3d07000070301d078020044994041152a04401525150300ca0f990580b265210200394222a8203410002e61030f40400c1d42140c559034003441003107005c94820980e00000958552071043c8440c5c00030040140001c0c0014038081c01e082d0b4039a01c610303d101c40c0c00811650f41c00a410141c609104a00d00748403900720307007410103140c060048050b1100a29006816860f483d0080320840c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 801432742 1250 801431492 801431503
    0x106030b1309140f07050a06140901080406150e10080303101e090c020309010210051b0d0906060605030a050c0717091809011e150b1309020327010e0c0d05 68
    0x60340c0805079032101c406483e1299035450107019032481987d154100041d2103010b40c1c071440c800d01441740e9090800c50070100541e58040c006005544080e21340345e0b1a413540c1050b6600c1c60180000010709400c500f00b8500b03000c038684013900100304690041050101000c100b18070308048a069020300a01c540c012481d24002114a500585115007401c1e450445150080090b001000303080e0f00700d84900c2c9030802c05606690b0180d0b00c803000718042800c048040092a802081060b2038000b01103403c54103581e9a0b42180c43d1a44802c0010742c0102c01d101580c0528012207801c4070390505845c0c10005c164442440d51500a40c0401c0300c0140041c050329140c403182d0408484000340c0100b58082d240090001e8064021400703000074456036031210808040b42803007100382d440d500751007070014203082441d502d400741d1020318034150301d055a0100044080c4140011031180810100f00c40c4211881c1a0700141c410071511803a4036641440005500c0c0180042c2c20b640301c040071605221035540900b011030174036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 801433992 1250 801432742 801432773
    0x60305060a0801110c301e12041104050f0606071b080604140f070e060319060e160f0b0309070f060203070309051e060a030f020304140f06070c03050315030a0312050106030b1309 78
    0x21f2030040303004e203290801c42034a00c0c80b480c01003a505080b0010002004200c40d03044428a09100451001c1841c6061a81c0580155407103001e50f085000303001108a5440140795000400c203900190401c001c11214562221030021003000401003802c0040071540c48217002e004000900075640c000407040d42e400c21000c00c414442070703a50710030341d0300f0f40c200a00a0b1412014600d40d40c8101000c1c0d0000300701d80304040c0112120300159800507403e0075040600d0b0781c400b8082c000d0034803030340f00d020503400205902040101000c1d0021030790703800203103800750044459900462058600f202800ea0341030201d0084002d48004880c0155070b000803007401d80040080300b401d012403e1000c01008200300112810040d0350000d24100e50402c001502c90a035604000c851840000340b1040d01007000900070005190040c2400c0504801001081c020900d445203445c0705800103195500940c1403000300d4460540500038914061014004000c0411a02081b9000340c0d003219030f480c3c2592082c4400d4a808610b80c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 801435242 1250 801433992 801434047
    0x70e0d020619021605031b0d050109051606140427060816050312040b071b0b0a030f06140d02011b08041203080c070c060305060a0801110c30 62
    0x34040c4030380009503134001080c006911071400c1040030641d0f1400103074441d2450040300034440e030b04c04880c0a20981e6003a01c1d00c21a5550340701c501800014400b80883e440f00c04100c090704101914049008104030441245032880b00400c0106008005d001c50340c0c1d0742020040311203180c80c0501907503031071700810f003a80c0b00107018006c0c120f0340c1c2032441150707038000304951089080342c0c04108506101c4940d031040c3d10441003100400c000d81c10009a44e904a0074001c2c11130601c007805559510200d80d140c0d8050320300b44002968a50302000301419610688001d400080010400304080384042007840003110406410321001880748946c0d00240d000003541382d0b07407007280346458a86c0d0b050f58240c0c0c2a101d503070403030104080c0b0000034060010141070700c0302c594201e21504101072070504113400601d405008036400c08190a004140e00409000300d03444200d140f01c130b040d07949114500e00ca0a02040c8504040d070750780ca04038940e1082201002c011002c0cc0081c2540740d9450040c0260400c409145140051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 801436492 1250 801435242 801435277
    0x60e180a0b0c041406090306280614040507140307052214010f0203070f0807031e0503090d090308040b0c1e1b040504050604060203061804060c0e01020303070e0d0206 73
    0x180c42840c2c2000d07108940c00003440790402c012600c108203440c0102140c1c550560f0003000041c140030380c80d0011030040d40046084020901c4141a07220a5030035641101c00c041c680b998120149040902c6200c3c3d001c00c191524003042400d504082c4514440604030f01c2c20003401290812028150811a004c0c4e00001c0c2c00d03400c0807d90b944c115100c10080c0703040090201e1503400d1100306050000c4100c03500c02e94000c85580c42d11405035038500042c1c01c0068140c0c10400310002c2d000106a540007112012007050b1205d503201d02d441c1021900c0c01c1c01030f01400080105400c130401c004dc0c12001a141960440c82c5029212041e0315040c41c40e013000390b180c800c03903840e01820040c004030001c01c03981c01c007116030315039039502a400400340001c2d0340c400d880081c01c0703030700c4240004e0104903113038061a001b81d0020321845583c0c000d0750216011000c01d507010b443d09651444c80c0440789402420000c2d404000b80051811880e244401404500309031410b80e00403003880c003036403007190f030745804450054100c0c143e13241 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 801437742 1250 801436492 801436501
    0xc150207060305062707110303091009081606050114180c030403031e1a010915031104051e180930031602010c0207142b0b040308060103060e180a0b 65
    0x45406400d41d0f1501c085013030304c441400511f4010080300c1c41502e0341401021700d8961010b25100034500901e02781ca0320242481011181b000704849941c80f40c1c002d600204081d41070180e90320340a21030080c05c82c8541c1071810000c081c0400c2c2c0e195168046180124a80c0f29a00c40c00c007900500708090907254250382840c40710482404560140d043e0052030000e210b40414110019151001c1c58000c1c00b90300ba2502c40142c0c1d030584240c00c090000c1031982c1d81142400d0f912008218120b0a50028004210480c025400503051140c5540500f065001c2c0200190500840300e64943d00b8201891041d506131444804e4800500c150445182500301c4105a0320301d081007400c0300c018420a030b0000154280003a0703d4155200207804425103c480c1c2105074907030011f0080120f40c94984402490005141503030047e840c3c00e160603003200500a0288140c01c1c070742850001d080440051074141414501241480b80010301035209a1145500c00c2e483c509060003442c00d440c0c941c10785001090844c820f0b0400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 801438848 1106 801437742 801437809
    0xf030b09011205100e100b2b05030c0d090503010b010e100f02120a05070c0f1a071a0a1d060f06010f1403130c15020706030506 56
    0x184c441c000003a0110043e00c4000940302c40c5504010030100024040340a01c02c0086003c0b500031440a40720700d0004070240f607488030b8440c42080760343c1e00420007004208a41c1040c107034104943c16540900c40041040740c6ca0b0144a019500b0240e0040065010741913002541c84000c0144a4a100624080b500c40c90a0340d80c681c214410344d683c503100b10042d00c008080703559540d680c5d41c1d925055414403070555801907001c0100300340104410440c070031303102520b19184038a121303030309941c0c1c101c606141484006101d0300802443d442c800f4440c8064003a8003001c00111103c07000140c58040031b0440e40c071080121401e000402000001407040d61040c4510b040d02e01907800e21181f22451048041015042107507105888800045003a043c03014242002c0c2c0182491031100d0348138070a0150003900c40c12184071303010034076413140007049507565400c0402000d014940d01d1a92002e0058610 = true := by decide +kernel

theorem cover : BRFrame.Cov 801258992 801438848 := by
  have h0 := BRFrame.cov_init 801258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 801258992 ≤ n) (h2 : n < 801438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
