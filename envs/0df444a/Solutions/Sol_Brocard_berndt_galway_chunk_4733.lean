-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4733
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:33:38.850829+00:00
-- url     : https://prove2.me/submissions/38b26aa8-66f3-4414-9b30-e9bca0700fe4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 851079136 ≤ n < 851258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 851080386 1250 851079136 851079139
    0x10060308041214070305010203011e0b0910030209030a0803010f0b090603180709150e090a0b1504060b040801020714030301030507050112090618020f19171905011a0f 73
    0x800c4204000e210740c4118042c154000c481c046016100c9030505414a01d1079403041e503c980d00071005004841e200d4882c0d0001d158024200d281252424001d0b004a000700090a8030400b030024102203010f003c0e804503108528020149c034007044a0740390158450304203018001c42806110800725009a880003100d02c0443c0c0103090b10704681d01d070b00b40134401c0200103000c0f04080c002c2400018132142180502ca6000c4103105e8540007007800d001803003001130401406040140d11502002020a50154800303400c010010182c460703400c1640049800b900345940320f600030040004000407106c0f01036002e013030081c0c071400903180403038070401d040303a964042030002820701d82040380c0401c129802589010000b80d04088040350994598079848103c4400c0340203001401e03807040c041011803038180c0c581403031b030314044450081440d51241c22524030800c0d070040d03402130758003031a9000356038408001502813001800880c040341d00c150719140f03000e0000889080c011500140038000d1500d000108068003290 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 851081636 1250 851080386 851080403
    0xa030e0f0114010312050c060c1e0304030f0c02040b2707090312181814060a06050f030c0c0f0f060105090c0315012001141e2e1205100603 61
    0x4c50320303090b119004185030a0203000b410011105150002e0007030600c903c0d41c0e140750740d44568046802d4014480208400001e4090070070400000a41221914801304250b152889207000700e4400710300180700340880658850b401811415910304146402100301c0200c1c028031a990b102c00c441030760003119600006206000110350310140d6441003100d20410448092a603101554845e55180041000d44000804c684c0b80d001010a4900342810960040010303100014024901030380281240510814001e83c200000040381c2407070601000c0c0c3d12485140002e8403003d01d05050415a106e46a0348400303000c1c010400006030a20341040c0027481030b9140c410b4039180d642d812105000f14220b031220276040c004220400600800fa07541c8510208010100000359000714004c03000001c0710042000b43c2c1c500d6110b20755251090890002c40e04190b44429124400c1503425100ba840300c0050300c0c0400e04417403410009281a400103034017488034040c90075526160700c0003540704180c1d481c0307000250901d00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 851082886 1250 851081636 851081639
    0x1209021216090b090f0c0307020c0916021c050406030f0603470a09260d0e0a0f020f0604091401090614210c150a020105012711040b0a030e0f011401 65
    0x6880011030b4448c4840c0306036490740140c280084c202060640384818a0b10300a152181100d030100071844503500d0442c100607a040704000700910381e20032400382c2405c154841c041000070400d07540040014542c412043c86002c07200d0403110b80c82c0203401c40b0780780c0039000000c0d550302c100b0007008143c11a5801075041c0700850b580d040e04200944600303c008c840e00700766807102441445006451600303805482240650b00c1841003400c009846007140c045500d604050380b11030004018440081c8242d81c1070714800c0c1410400400502c0354052503015003881401c011140c402140c2075607400d41664004a010440c035916911141c0c2c405c62810406904040b00001c1c3c4640b6001242000194200c10300864800c0901c650108180d00400440400142c17000318100d070b19250280a024090250b13110840c0d000107034880140080055030401801883d5202c2c03224000c200c0f02002c48014102240d80c056561b00b150720000c0c000e103e411111406405004000e07010101c041c050820b000542c803107442c0242c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 851084136 1250 851082886 851082901
    0x60504060203032d070305040b060109080c2709030703030c0c0b0a05090319051b0a0f11030a0807050318010504080a030302280c0b161209021216090b090f 68
    0x84c8034006002064071000d0b01d4050000600c011407254015680204103401c0500d844000a90041c0402d41441000c0e001800243c0c00010500d482038401c64420307080c901180700c00210150204004803140c1200740411515010000051410034426641040401c0c52508121406101d01c0c40013801c0510413000315190344202c2c0c018640113007240054924200204d640c81c2d01d1450b4071010600821130214980c1c840110001e031014a600125012700b41c00b0041d980c07141e0410741d01010040164108070080666510100044162160300405080c1c2d1071042d8100f40c0c1c2d072a004541d0300c50900034054080e0002c1d5105d0300c1510211665500141408140c5a4040c0c001c2e4010300341c60341381280f80b10140711721908141c526500844aa860340c90f01c011440c00c0c40200b000300107080307242d81c044204014200303560105901400040f2100b000400c0740d081d200003640c09d500e010100041e40b0804207542900e403045c03030044040300e0040c1c0d001c01044013071304140190301008030343d10081d100389003001407100c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 851085386 1250 851084136 851084161
    0x313020609040f23010902030103050a020910030213020705060a060837060e06090a0f0611070b07090501091a0a030207021201050c190c020904020f01030e061f06050406020303 77
    0x10080d00900114100a0a04080c0c007203038652107460b04d002c0e02c89607402079501818484940074080e007a80652556045440d0a0b90b9209908402401500c4220000d51b004001e10b6151001c1d540c0106540c1d0b00d4003152017081b01941145100b61010701a02000c5000c0340c0302845000100d8101001a03c000c4009400c40d18840c5815608409088440e920007800100c8000407a00c581e440b40e0000109000e07034007034140c5800070007402c0140c103910600004022400b011106810150303c410049043c0c0f0501c1050841800362041c01000c0c1d48160081c4410160058113013000d8580a0b43c0c4d10700036907901c525003034400442c2caa4440702c5000402050200a2103a0000c0044500152003c102c5002c1c0d64035003400c4403401c0320a8a04071401040780180c140c0220140160303000c03140380601911400f900003c081c2500070384000e02c10007840b100c5002c140d02940100311000080e01c155030b4079117000081e2280c0080784c01050002d641d081c00000c10b0f203501400c06e440655102c3d600070360031640c03002e916021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 851086636 1250 851085386 851085397
    0x1106061f11061f06080f06060901050d050403020a1b0e0c030718060906080c281107060903020a050306010f230d150e1b0d020f031c120203130206 64
    0xc0000a120614201904019090107100490701c0401c030f91400404240c20f0341482c4c1c000000300050340c070034042110b4102e091113800c04012585d50f03503180a60b800680e032500c542c12500c4010b90400701000181034000c03800007452401459903551114903004564a0840c09000309100d0702801000b180c030001a000c081c551110366401e00c405800d15880601c95560358a6118a000550000041c020a40d01c88070094000b05100a024140b51003c20400c404000240000440780c41104413040614401e400d1001103131500b40c19125910b840c0c01008020703110078042070780244c030b00300300c0010a800c00040c02412180d2415052881c90700f0520480d13041030003130600402c208294062a136141e1b84408807084140e10070044040c6094900340c5120984044001549143e00f010010880c14141d0124a00c1d891030b08603041000d60015100140b20842c240708030a030144501c4510501e98042d6030343c00c1c81d0881403030700da81c0c02c60115100144260f2000700c5403000080801440c02005041080c0a0807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 851087886 1250 851086636 851086699
    0xe030d05070f0228080c0d02060903010b2115041e0804081f0f06030213020a05070b090c03161212021e010c0e0f09070e031f0c110606 59
    0x1400001d82d81c00140f003121483c0040d001801001c071441c0010046059004010038000f0060280c03000032500240d110004414082d0103080d00284005076683c081d440300380d10780401011030180b285070094029418141e150300e40014412204501c0380600c1c90030115208650040305000e5811000c480e8000c13000310b640c0111810031083c800072445480500c0322140c0103468265101805e4080c1448006696900e9441291945081d00c04d2015031540400c070100004001009640c480094070102ea2620501c840075043c40000c0c41844042640464585070452040742165401802c4400d0300c9207100350345c0f00700180c8640070035681002490050440c011481c09005a61038400c46425260741040b8242118407107955a03480d00c80410713013045049040c80c500b514407119940055000c141d518401420001c14400c0c00c4010940c1580c0c20842d00759207400d9070b112135201c000e0f0150030345c01902c2c003c035405011400140260301035201c00254203200c4c00700140b10314541d0159071452141c00485642d40e8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 851089136 1250 851087886 851087903
    0x1104020714030c0102030604060b12070e0303130b0702030105071d04050411032b090e01050d05120c01020a080a0c200f070308071a09100f140a0e0601060e030d0507 72
    0x50310588042c800b81480000d1240096920301d050703810003003116101e41000c2e00b80e140500024400b195800b0800764003c81904000c0603030b402020020b890341c01014000c074500d5a401a012400803008009052014800d80081c0810303110300505962200840c54103403c4140d40c0d401c042c01c140b5080d002075030420f000744c800320f0091040e20046400c0200030402030215280b01c1107801c145c0350407420052035080d502d01d8410402400c03c52203000c2c100c418452288210000008401401000d001c07003484159002a003641c0c844219440038040c1d00181030101c0031800c402c00080b0301340300c1d030b014448801809a80340c0e007046070045400d003090080840205023030700c18080c0981c130300c100422180001d0340c081c00407140c0710601485c001d8500481d03c16481d00c0402c1d00418080700c42070001d1a00c0581d4456000071441010a89420004010004846400d00c213088180014054250b000408016107803003a50f4060f0b0325010203403141000c80d0440d03500b580c0702030300c00c010300d40c0716001800142d445012203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 851090386 1250 851089136 851089163
    0xc05150d1b12020d02121305060106030b240d020c0601080d0306030b040807141f05060402041a0a0507080a080415090c05011809020703080708091903030c111e0706050711040207 78
    0x500d06c526004491070000d10209a0308807007805007c2000c14014001c0d0f140038449444a2400316003c9085102030315250400ba002c040c10f5005110309540d50048562811910390b0041c1032150755400307080c4034009080c09084e15400b0a0b40c801d024001c140d0350889501181502c607907a45003200d501042d0b080d01c6865078145807018894046c000440da03410514400750346082c0b001002c104490001d044a0304c01c520400041040e180b41c41d0f1051040300d800400551501c1265605995038030601c68000d04107400041e07000400e5401c1400175000307074040d09440e0101200031061508507011200040c21104481c2c40421442d1320030500c0c00f0041c00081c3e500349035075a441803510300781e8025440c02c40114008404200c2039039404100c80c0d42c014550002010f1036098000c900054000e000400340401d603d074211241d44500940f042440e22030a04102c81d16002c042c0da000303000000ca201301c004103016011000403803910890540b5400d030303041002015020a540b0820000398010602102c1040b4070012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 851091636 1250 851090386 851090407
    0x90e070806041506110c060c0d0c0212241305071e0302040603120e06070803040602031e100f080f100c0e0306100807210204090c05150d1b12020d02 65
    0x8883c010480754940d41a010703000c02d402424a0030442c4164040d410600000c944d5400004600744c80524608207954101290700200c0d48041c9507038032031181d078810b0f0141c040e480f04000c00c0d40d490344400b225003a16107444660100c190b0310030014000d0099440715606000501c800c1e0b4040b0050701001d03580010300c0c0e590f0390118003500c455030720a940c4011b40c500d4a02e4000d03004081c955074041c1c100c84035851b20f002903840200a00000e00f01812003507020000800c0b0044001640d213480c144032450304520b10700306048914213000c600035220032400003103000504010004803842c18600700710143c544801c2d004205001000000c008004100d4282e080d000191418400f00b40034140074602c06a0031401c0c10102c2c0e00e444115448407441c4884600071100c0b400c041d840c5c03000d2459044801140c04900c90512583e050143c0d04401e601c0500c040c4503c4850307501d03100804e240403241c10140f24152020210f0209a05001900c1010420303141e02100c00c201c00e44c0c01416071a15070b08005040014220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 851092886 1250 851091636 851091671
    0x307090f0509120901080f0402061b010930120f020a0f02070b040609051e030d1d090c030606030406060f060f030e160504020d0603052506090e07080604 67
    0x81040901d5850051280444003403108007807000748a80010b24040030040000c00e14600104074010a206100104045543c2ca00031a0308864619031403c20144402407030600800404000b1a2113580324190207070f54000c90700175800000006603000d03c22141d481c4066600c042c4428403a14800e543c2d001c0e071040c140d001e2010300588292940c0f000901c2c10b0f1603501901c2c00b2800d070480000d400c0700748030400c0301d258090b1201007924415101c0415035030042103102803840c0281e401561601526860003515035120148140a5038403000c040c2c0c03249d44102c14002a40d206032003034058800e04100007102414018001d60700b142c0704000020b01039640d8061250300001681101b8000341d03142d4440c0110075494002d50952201c1003001d040d8041c440c3c0004040c01c0600e100d4540660303004031b81c08908501c4c55000d21b000356044002d41b023425100001c0d031a030420212408800320403481d0301c086846441100044d040c1d548514500c0c3d05074440340380030758903a24000e060b2a032060711504508075841f00303075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 851094136 1250 851092886 851092901
    0x90d14010f1b0201091106090117070807030609051611030412030c0204050a0b0d0204200f07060e0f10020912030d09140d1b11060403080301090f0b010518030709 71
    0x200001e035100801c80540080742c4a40d001900716810301d036103200482c0407003400024000044071941e031b480c601e148c01a0f60000300c3c00c1220002000d610100003a00e0303042409540b10710816a401c00c15161100350907002c0b20400d40307030000380600f204a1842c0250148840014400443d41100d060079034078034500720700541d103480840c00942c3d81040c140071400d1034000c83c2e030070002d80e41c8144a0710b0103031004164913014401c0e0182c0b281d0f0300d5030000c90780340c230013511038003030980d85000a281c2d2041822986005903100030700440d1400c0c503040104243c0c00f0007017147c940083c0c1000c041e009103021910410040d4000400e107607070100110000c0035041c20208010013440b0303510800410124418100604000c1403403d481d8016007018a01c1004164000c010030b03e82d000c610300a95030800141001d0303007031801d940503032600a9000113020041c404c0b1100518100c0d00d1402c810311054200d00a10300590f07902c0c1ca4128003140d0700b84481c0342c500890050b41d168030301001d011030f841c02e40c0e07a0032414241d07400f8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 851095386 1250 851094136 851094161
    0x906070f11190302030c210d111002120a020c03090907030c08070206221401020c1c090e150f060f04090b06030403090b030c04030f082706090d1401 65
    0x84001c1040c203820905a0740c509100d607041c4400c000c525680200b81c84441c8032441070b11904a0b6480000f1071012420344041260380441199400c400010300645201141d042140451044a151342d04e170380303024007c0b01c2c18120703c1c40808119494046d6000c0c0039402031700d80320005001c180042d0782503449815510340b0907501c41c0c3c2c0c0460341000c0342c0c1d00a02801e9000e4003090444d04000200a014008400800b800f000303c0201042044c101e8144020000003200444529500000e000481c40340005100d00e210014140c000300303038104503a01079800a440741304c0c000402400390001742480084031142001040054030060b18a0183c0000500709e500c140038403801141e011a00b4001c6155a12038104000402da821a00d513040c10788010740907546602c6517039059000000000d2042400c24180d1300155442102d0701082e08483ca02582e0981010662020114103501d6040e41110350700ca0003500c0da60080c213140e1408145006011031081e107901d050b56500540c00e04040a040e0911482c441e4145 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 851096636 1250 851095386 851095403
    0x1b021e2b1e09170c210705190f06080702190831080105010302060d090314160b070825020a17030609060d05101a041a011412010b0906070f 61
    0x4200300f8030040d074210003620b07490783e01c00c2e54109000e85a60040c1c01144038024244080821000f4000e4900506900625004401c1c00300c0802c6100e20a24503e0668440da40c45001194848008440b511401c1320168010f80c0302c60544955030115224000403503020320f0819280c10301c4031160250417909142010402c41c8694490180e4490300e00f47c03040a0403c0748020320203945540c0014405002e488101305419640c3e5084808141c003c0320403400320705082d01c04a450302000510034078407102c0c00d10160b400c5841c03140000c075224800d070300442c4a541941c0b43d0078010451035000d409081c5000d01d000066111710180040810741070042d8000340c2d0802d500140e928600007091103000341000e02010b00404403043c0080000b07201140500c81c3c4900310000181e60040020000d04900014495540081c81c0032107890660301800c2e0483d028800a803a8200e0744070030342d681048188038a494280e01c01c80d504c0014028036a400000b050040001000642445c1039600c5e9003a40c0c50200e0f800b241c0562 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 851097886 1250 851096636 851096639
    0x20307092402120309070314010b011b020102031b010e0f03450414090f0d090b0a1206091104231e041b021e2b1e09 51
    0x12401d1201a015078086216140c545411031000395880320741d03407000250030f240400042d012400070000c0c1c600446d040444034104403621801380740207000302c0003000e000035001050340551000349000401802c0c2d060b4000d5180202c8100c20410303001920301d00c4134503035480c1c80b07240840d11010030441d0764a2408501550f5918400c000f0f00040c11000051021030055428200c5d94181c46003414880c1c400101c0c1b072200107603806100280041c140c2c061075032140b103403200a00c1a403160000b40d00003403095050031100c10380d403022005c1e03503409640d01c40c8540026041125040f112300c21503540403c0004443d010a501e40c035031100c2020748030700095101d103000010804022008a0000148040ca07005402414182c00c8001040d40c2d0783c00d101e8032002d0700130b80b020010b00710344441d480544d0b126001c0251490041090f20001c2d150102e42410b050030203a20241c1c2c80b036202003c03511620b0032600340c0c003907042420385240708204412010741c0719051114010110100404a0404001d00c0080d0f0796080c0006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 851099136 1250 851097886 851097899
    0x3010f0c020c011e08040210030e0303010906031217070c060e19150c090905060310091b230111070914070f03020c150a0b040207060615053a02030709 66
    0x100000c10018a100d0309409500d9044d541184003590030940607100740c104000ba400094000e46000c0440030381d9031200000000c0c0882c1954805425244036041490741218203440884041a00c02652141040c107003011a4100d8012504641e032a031140b040860308400c003950150814045582c0070b104040e0380c05c000001c1082c051010381ca161920001000001c100c400001d2165a0794041c21104560f9040030032815642000702d11b40d402c0029000b40082071080c0f51a20140c1d440f1603170205050030806001c00c00d000c5108514000110585d0801030100d04007004490201a00341d040059000b9402d020990702c880340100084401e004401e600e0a04200000504600b203080e0b40d0020180f060002640c42100801c040b0f030103600080d400075464451070921002491584c0346035502c40d20004010040082c10b41019040b00c101034040d10701d0b00000ca900b40c40d44d00c140744554644181080301070991682d103401404103c0150300b0540e000200c01041c4030103da105407080c001041d4082801c0090f03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 851100386 1250 851099136 851099147
    0x140f0618030606010212030f0a0e01050a0902100203090609060714150403080f25050c030a022503020603040605040302030f0a08040c060504080304050f0d06050c1804060513050603010f0c020c01 85
    0x3c0a100900152003802d00c00340c0349000140480040f40484030201c0c05052240d00a044510a42e5001b04200c0c200886034800401d00041e0480c010300c80c1e60a1206075030700210507110b41c10400340c41c8914140320a4200000c541c05183c04554801d9035000c007400b80700c002c000016126096200303090b0141810704019000d00030092120a03c00103800c03c0004107826601503e82607800740c0741d148080300b030200b02511140110768110089100104000e11025130014100c02c0002d4100c0d07260303178851031188401651403020b0102039008181000070500188596015503881802481030b40e090488800e0403812962050f40c20400248540c0d0510061040c1084017400602682c100240307020714208025440340924801c040c4039400020502049490303010200b100e050340a4000c1005241208141081d5080119008041c118800b10b0f810542047d01c11710f02a9030000308007007851340d54444110301800000b0031080e015500c0e403c0001e101394840c02410388503551030300a8850f181406000400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 851101636 1250 851100386 851100391
    0x607050d0507050f010c0e061b0d0f080115051207030f020301090f0c021b0d050705033f040e070c02041a1206040f1209230a0e060901140f06180306 65
    0x507450100300420150300420080a4180191000740d00e503a40c0c4602c4915a0000e04459900d40c02402c2b1141025a440035100c2d590b074021f926000c00b0740c0d80310018500f000c070a00e80c401c4049030041101040042403150203a50103625071801007403205c041c80c2c4c1c940030b80c0c10070f03400090425200c00e000107009009018019004282d407000300760b4004032582925030140750607400340c003c1c0700399014903040c400306000342c501409001c1c1c00c030b4640140c2f00e02c141da01c000c018041d2403265220080a400314210360b00001c2014000b00510a0616091004c0343d03d0b46a0040c013408103101200c402100161524029081644078600b2150614034200e4240324051840803840811900084100070014401c00720298440d034101520005981017810305072644191500b0403031308460008080074070b00c80a000c080c003c111003601c810821660720403100110300800e42d161588118400c005000020808113219031030400180a0002ca801a101140311030f0f0180d04440c2100b0425452003025040c100403464 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 851102886 1250 851101636 851101663
    0x1c031a0904020109090f020708070c050f152203050f07060e0a08030313020612011e0501030504050312100b0c010b0a0e011d0a06150c050d020f070308090607050d050705 74
    0x1441c050b4002000700c042c03030180220860352440b58030000c0e212981510340701540403005c41e54500d41070600125029941c450548101c5c6010342d254040d040c9000c84401e42400500d51905142e01d00c601201454140a000300d9810035812002000c550b00300003841155181c2d030060301246003407150051014000c42c80040c0180d0b100402082401c03030001c102c03503012450f00c9000035000e50b684001006d034414a17020703230b12034442c550011811f0040485004032603e40045c8200080c0d540d03800540c10368908070b40152641d001030108402c0d022800081650218a049031010303000e8450070b50300b0b12500300054064050303540f4000045103041655104003e041207114500c0c0b07661400c2c41800c15205e180b4ac011140b140440080b03859032030385401c894050880100040041107581c0d81c0142960400d900c196034034401c180d14000740300d0000c10329444074489003001c0c00c215400c50701c8486465114074001d40c2c10140400c070750004601c4c180000d200c1040107070380325503850289040180c5400e1401d203014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 851104136 1250 851102886 851102899
    0x6020a18060906030f0204030b01180501050904080313150204061d0d02030c010f030f09030f02010510082d0d02010b0a0e07090302130213060819050f040807051c031a 73
    0x3030040541100072401201c61510300400d5170041906440081d004640c00245a25a400700124054040042420545480700030401c43e5030307a100d040001498003039402400301d80302000401c250910303980580c46007074042c070302030f48940c800c106008089034071035403001d40001d00b441d080c041100b070143e20903600b000c01290309070003207102c0d030300060f440f0049901e02d1410321003210340440403203019810801081c450400208040096401d001c0c0c1318100e1150568015440c01b00000c80c0d0307507804010002a105120010400c51400761001d500c60000000041040c40c61040381e81c0f044102000810b0320110643d00100f4400d1120003405820851904400036845480342000641030340600c1307500480750103d89070591a40c070440c450000b40301c2c96140744072211120170003013615178120803a9802000450150342d004000d0300510001c5507030030f42e00d4600c046412400700e0081100c002c0600751041c082c00a592550a4102003080b0740d0303060041c2c0e040803030384648a1404000e51021a8040e607401904c0a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 851105386 1250 851104136 851104139
    0xe010f0e031c2001090c170d2304080a0507061403060609120604050a0c090216020d110901060c0c090b03030901180810061a0c1c140706020a18 63
    0xa516000540d1801c400035242003072402200744a821102e24a0a030845801c00d503080d2640464003a01c45c001054550030640b0070001100600301041040c01800c0c01e01401c10441c0040045134291910450217110750b152845c2032010000c000000c00060070a40000c2c46c082040d4a4020709101085e40300310180f0a041e145046000b078800212a44124120f401680c0c2c0c0441c140007401a5004c145d0442d0980316a0040000b00040007d8181c2c0c03460080e0f108068496517040300704140e1050442c9003036100f60580420006050802004950a03c03806107001d11004400110710040404d91040c00028100b503042d4081c05250074910020340713103001f8188103445c00107000c0380e80c07032107155030041c10018041c085400c54a40c001403480038000300000c0d0350780c44c0c80000400e400b41855014030400c3e205000188080d01c2c1d18901281c49011006002d400826002d5140c416034041070a09001408110740050640c0c130b511400400030319215450040c0c40d421104402841000010300081100e00c00c14030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 851106636 1250 851105386 851105389
    0xb060d0203010f08280f0b040308060f040c09140a09020a0f0e0102010902150c0106030507080304080c03010b090f04110607080c01150e0c0c03040e0414190201050f0c19030e010f0e 79
    0x8440c1c800b0400303d5000ea0400103c0c50b10710306d0049040b070060300c031080140a000400d684210918041d02c402c450800c007845411040000715005818114003048601c3c3c42040030140c101008a400c0200400e041c40c080d0783c03400a00f059910500845c0c00150345c0381e0800c0d8805410441d00e90004c5000c0c4020031000310300d94045a658261020071070a107400c00725030895010001d4101e032014680c400b05071909142d0f0b400e00183d07241c2050190a4083c069000c1c013400e10b0805224045100c03400070406a0581c0320000c0390003001c1f0024101341e03081c81c00c9030300140c610745039003004005a6108154180c1d503041c41d0400c00d42110885c2d03009414002e10582d080000c10b40c7c0e07c09683c2c01400c000e00b280d81d91400744452500e1072149a00210740c0042e80b100300f0007031000000c1ca41c040340f448182641c044c45000c2d00c020204862902000340891030134402c20f0050500c24015012408010040703950224011907650640c2c00341ca081140010304000c1300c80390035640040c01d130020840d5801e0004038018001c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 851107886 1250 851106636 851106673
    0x3030a110d14030a0f0f0e0708070801110a180e160305090d0903080906120f0402030105070206011802212403030c0a060203060f10050322020d0f0302010b060d0203010f08 75
    0xa15442c00c1ca174031203107011071002c031543c014500907040010402940c070701810180e480344081d110340100340c09601070001342800d041c003c1070007049904a40915200070f141c01541c0e0050b004254203d0020390941c0840d50101118199020b8942184c0002000110007401000d440c00280500d98036004815a105915000007044040d0f07940f0010050b11a90b206002c07983c0c90007580f100c2a0340001a5003405428501e0100c43c43c000c9000b94002c3c000c1c0c1d030340c0302c0c8266a510020300c2030b20594040c10160000b20b907281d5000d04280d034118150901c0070900c0d440c1600c44e415090b6807262900099072903120740c0ba000c4104000803508144c01540c20418001d00060320b5084006020340002d07000800640039944081034007000010080c1200c0111030380b5080200706030030840b41490110198912454500b1040f20324240c60b83e4010880480d21078140c0e500050004550300031010f540d255803c00c512035642c0d402805240e50301f0700d80142c0f42d61402c80d0101894030585d010400d45d0300807440d0403101c0080d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 851109136 1250 851107886 851107891
    0x120308040b1503011e0509010221070512070518030d1b0501020904020301080a0308090109120507060605091509010b04032315070903060b03120a180503030a110d1403 73
    0x228078112560744403500d02503003141400341c07030b8507519000c410300042280d07940110160300c002c1402c214503520006000e00300e114082402c00103007401c06401c0075080b02d9100036544107580e45440342c10700035521500c13029044299050302c0400d4002c68000e483e03400d11480300307040350f108600400344e030302200b40e0183c42240300300e05000300f40701020224410300c1803d40403100d64a101602c01c541d00d682d1440e5094031002006421000280e0600c045140c264050082440b46038011301d520700c80e240e06250603910741d4084142110381540700c4800040580e582403010388200d641c02003908a1941c500308200c030480c0140c110429100d4144021f10101d5401d611516500008035240c81e00c901c3d000c0c2203e0b107004a031150300e00e0460000d804012440c0c0c1d100021904a91184030140040301c0e812080546a0010201086201c50140025080e0714480d000c079107188104055400e17403094030b03100030134155484103000c003020400c5150040040f50302008101694089482c2140640050359203614403884013 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 851110386 1250 851109136 851109143
    0x504020703030e070e0403080f070e0d110a06050301080f190206071a1302130b09070522031209080706050409091109090109020a060c03020304150c02101812030804 72
    0x4108034081502941c02404010b18100480b210640e454402d2600300d10f048030200e00050222012038080c102c0038448500807810b0f91500324210703031100d0a01410038050181036448039166098110f280d00e51901020182a80d41c0e44c499407581000c4500e8501000a02403011319032002e1000c0207001601010358804980c1200d030156161a24204949800755698040d0610b02c40501844110307001100c4a0014506c29182182d00d07440c0411800b04591612495940290aa0300007070b00c010f20070310081201744403016801c05160058400302d80d4805158004460000f45441c4280d00e4507080b000060003010b52030001c1c80c00b18248000101680124420300407070f6522007940508010381001c001c001e4180141c0ba220192421452003400ba11201d4000c3c1d0040d141c6090200d0100d20500400d000103800d41c0065140902d854008200001100008010007010020060060340c5980c41d4496250030341d40e6800b21421200101042803600b07602c000070b594a500e0351000025041071000354010341 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 851111636 1250 851110386 851110391
    0x13030c0b090102040b031008010c09030b13020a0b040602030d050f1303080705040536060d08030c09060f0c06130309061110020a0906030617060c030a0e15042105040504 74
    0x110310401c1d03400790059811080c00c00b04040704200c0c1c0300500c9120b0408a42500e002031007840007040c001e0751300405070700014040c003100000154401002c04440034000388003509403041c3c10707910b014481d0982c01a40009005801c0044c268072148214050150440350080101405090202d140c49000292010040c2400b903900e00103550240202c003a03070000c20300038100138683e07150040c015041c218155440d43e040c04080780100c1d0314448180909100302c00c040c1035081c90005603210100c954100a11461750458204500c60170b540b120800703890142c048550301a110300700041c105050820040c80102400130349c85060000c03079400391100c4225181c0f800c0c10b80c41351000d10070041c102041000d0641c2d180f400040c2e66015130340d0102031281240c421740d40c108241e9486094100b00c074012501102c115038040008108400604801990040ca0352140080c0d80b01140c8840e41c18680400ca81078621030302c44c2c0812040c45024040361b0325420700d8021512000460100240c42e44c0541c1c041c40c0e000740d9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 851112886 1250 851111636 851111641
    0x70501080c04080a030f030e150c07020f1c0c14031b120d0203040f08030c1e031303080307090b030405060f15120c01090501110309011209021f030513030c0b 69
    0x1400042110702500c1e031142540c504d4001414081c101c058101380650000e8503100e6806c1c403034038000c0b602d03140d400c001d694400200d0b2140c042c0c90080d13800034001680d004606070074100c002e6448502d00c00c3c09850741110f00f11034192605003a0301800c0c250703214511183c58510040d009a07008542800c81100c1008003091307a4084101098401c2180e0a00d60000c3c842c9403c100c520680000140003158903002c141001b054948550a41724002c20a012502d40e01a6829120399880394900c040d014051004807810320441929950320078915a2098910281c00000d2100195014070f51034090840f010304140f0751305007603031031503039483c001004102103c5d90100491446000c80754100c68000c0000c0103800c0c0c0c20820b02c4d00544403c41c0c4a6264082020044002090f5006090030728a412000002e10704249010006540a00e845014a80107690390041003005a940400401004c401d50080d402544040d00c0003408480000d00b00000341403000300701c100045c2e8000950b02c01180d000c0140260754 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 851114136 1250 851112886 851112901
    0xa1419030c1701180902061b25090c050c0a0312050a0212150f040c0815032e1d0c010e010e0307061b1406330409030c0212010b040f0c0207050108 64
    0xa10003100d0080d800680041c0310017503200d8080c141211050010149d03200c29102140000315030711010801c1d010301d40108010000508a80d11894010783c803030606e1480c0030240c00030729003403000c0b00d20100c01141105014240c003034000d1003182e0307028501d10411480d040b03146440d100f20305802001c0341101c1445007400c513020348403101e0301980700002403c14003003009000c80c040d2001c101115802e050140d40022b03000e5514000503804141ca003003030140c09408885060380c1049042d014030300120680c441038401041619181e5003282194507034080d04c1c03940c804100041048e81d0100303060b81048035403410a2407943e0003181102c03c4036541c7c02e113819144025450f038201c40400b444003401e4040c40750b41e1910382817008950749106050412116030907c2456000c5618445040080000c0e00e1180d0040c0702e10307042560018110902074140342c0c900c030450b50700080c03260361914a49049a51585207444080c1410b00035041305020424003403024104e83d0708002d41c0e0351a10f102e03207410800484041400e9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 851115386 1250 851114136 851114141
    0x70f0516030e090a140604110a0f03090206072312090d021c050307170309070e0c160c05030c0f030c010c0c031a1608040203120a1419030c170118 64
    0x2c00401409448a0b880d001d44940c0084c034000032114020998100080d1440c9040d10591b4186008005481d042c800350f80b100301d0b02452014a1582450703924541e00008d6520180985a604d21805041c1050509084415203d5041d224401040d60100307150b400f08018107020340303100a00a0760035142c102290300010300d203881e594040600b290b0354000c2000900002200404845010300c0c01600502c1e24594020010f1000f22804995a0010070742801012888035801d40c07c041c0e1240c1136800c00c0581c2e400361b074840004880072560103044403800c00c440c3c24141302203030200ae0b080310030b001c4141c401d8000c00d84400b8010000ba0400080078860420041c240300c182002d160031140030004110306090741035000000b507a1319002d42c030000411190302845105131910440c1e018001e0803003402c2d0b0b03a110a481c0e0304480141410321a600100c2803500280002400e56160203c0a901070b0003200f000150031569494a041c04018500241e403240c5921000034504655100e0a20313041e4080c01200c4000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 851116636 1250 851115386 851115407
    0x3080601080c04090608010605150a0509130e060a060f0b040503070e070c14160b0c030d0c0e100201050103020a050d0b2404020408162c0402030a020a1805070f051603 73
    0x4544e458004080b441d1481544a203096400c1540c44400e41c501402c0b100b01d440c081d01000c8400900100700040701401c101c0c10616550444420100d072210700c5155250800400b15030407800299903840800c00042d002d07201d14010144000c609107000e0900b804030352294400c5c007441d03410f00a1a00801d491034810141c07400e030340c0d4005a003040411801d00f00e8980391405200c3c4042d1512000c0340214962a845c003c84060b84465001189000d41003448540a041d03e451100180149402d110b180c60311009131400d181d1080380c1c000582c560441c410030006070401d800060140f0103c100c208002080750300504d400c80e030560036212013004010324010b424503811010f00c0d00302d4008079000420000c0094401d21210185400303102040c0c641300440c9402c02e40e0039070880c140d541a0207440d103181000c09515001800503083c1d61411040d9004074041940c260f00814550003201e042c004441c425206140e0800304038509010510303003404004000d805481403650140c00b54002020825000720103d51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 851117886 1250 851116636 851116649
    0x1110c09090c1504060807090501090303270816080a0f140f1b040f11040915030c08030306010f020102030105090106050c0102070b01080c0307090e030d270f0c1203080601080c04 78
    0x3d6410b08250800c1c007540c0152046101082c0a040030074806030040c1c4108040d181c069554143e1240b80d500c007254203800f41f1040100740742e1144002c00c04400e002e04080e001e0f10520300107010000d4070031002e42d40c05c40680c2c440316990700012515000240e07811518403009801003000c6600340c440c85140e82c20400c0c14200d04100b40305009000c1d2000c0d9003480700b5100c015084a0401c40c988000307400c8001e56101d000d1456110000708002e005414850f800821022001c425808905840356a01d8055078040e82108209900c08010807826683c005c10070034826800b0310084d0300f15490b090200e0281c92047c040c29082c04000b05044065843c00d505451080350003004031038580d692103d002d5290306032080c46600a005058001c20600c901e4008d030403000c0c1601e001585020000c03158034006103070340011000000d00444002845640c00f102c0c036401903000d484695210522490001c0440c1b100380d0142e03201803250045500445d03000802a41d0040007804c003c440fa58603101d00c0582d522032600502d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 851119136 1250 851117886 851117899
    0x11118032109011b120f020d09031e0206160b010b040e0708041110030911010320090409080a020c090a0e0d0e1f02210309070902070302030412031d01110c09090c 71
    0x10b00101c0c0540c40c08a0440e501d60340c03800e1b116640c00326120902c000c00348020686203a010030010b02403461001500b0650048504a42a1580011556849040380c001c030404001d044d041401035202c03255004250210609180070324100c0741f400d0010f40140420706004d000000503050220809401808050007010b805802503003c1c4060300610148109890010714000003005a501a00c600c158445186880c120441d0200d54500c03007551025084ea07420039114152040001c00600290520b41ca0940103882c02154140c00c0c032003003450041c0302004442c00c0818140409034081801c180000c12854612211590f5001050b40b1320085034aa0344d02009103180380326030a038003090742203801001c901000e48091440f070750031105000540c0c000e580790708144000c0000c3c004135401070032180d100e40141e0f401c00d59a00407041c3d507440e0146040d000700b4411031041c2100010303009620181c11003401e1112050300751418480e40d5480152100340a2994000840c944180800a0010f5144d00800c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 851120386 1250 851119136 851119187
    0x1110050903070b0c0a0e010f021915090b0a0c030603030806211b150301051008100305030d05040516181e0e0a051005010b121801111803210901 63
    0x1a844e244e48034181c41c00004400c4000c48a13590322954120403880c5c9941d0007004c2e0151000d1950b5900f00e0320800846001a901000c202d100c0140e00405000368090b02c0200381600d050005401690a05500c040403d458403006100003038200342240d0700800151a045d4940d00e244040c649015008100042144141e543c484400d0a001000404200b415a03070081d0001d81107240c10079900083c0100c5a01c6a0a45518203300c0d02c5a007095a100160440c10805d5036600d459407800c650001d0407202036942c0720410001403010402102440d0074112104151140c50f10024546100e504840c030141e00b620b0b5441d0105148074408103000e130544401041050340a880306e11a600c2c006004215403e0103024403031581d060151040700c0c125614640710519080700030490110108006000e5030b050228051880039000c0c091042e812804100014030780e8414210846c01400c052110800d0311076405600c101441d0100703601070710030400c20400095155010000181d4100d045801c40781044c11a1806e0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 851121636 1250 851120386 851120401
    0x609060501081b0a0302040902181302010806030a0b160c0602030a051b0a0c080706091b030201090b0c030412020109120f17180904021f08090606011110050903070b 72
    0x14100c480280443e0150940403d00e041c50450780c62089074498400181000941002e40000d10130510042207000f0000c005002d15020800030349595449281c943c02d240115604402480d4008404400400404000d90f403075181c44500200103410714408031810100a5016800842010358094001c3d034403460068041d0004010481d40815440941d140c0181240f10401c11940380108035925a412100c090301c8805041e88000d008450895441d80391402055226031800c40d50f20101054401c41d61460000405504041c4c101011240080000b000724000000482d002c440307080342d1982c1c40658600041c0c407004403c2c1d0140842980c200261004c000100c40c00c00782462091800c00a0401602400c4005010b1041041d2100401000c1c2084900e0b0001005500601c0288030310704864141c2c45041160501d1100e00002ca1b00704003d01002d80c400340101e952200c000e01e80414082284100250b13240c00242000021076035400c0410b01980c4c081c0104ca58131604001108802d041010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 851122886 1250 851121636 851121641
    0xc040911030a080c0607050415030506190b0918060d022115040c0b040b1b010608010221130c150915050a020c040b151813150623030c07060906 63
    0x2042141a003d1744001a0b0030901413829101503510320b10030703450250050071040d00103086c00307018150303c041144554520501d2105044c2c014110f01e84a55441d8812407050011316621017100894419001c020040365480700e003042d00c0c040d0b404071007000078600f40b820520019245004000920f0203407550041c3c203060007035070b0203010718850705860304030035a29006184240128016200c0c0c035030381001503030007600f4800c40d81c00a40920a000241251351015014226400070503000307c42842d0480c00e401d884c00341b03130380140e1201e01101100c000c40c80c10750700c42442250310701411003003030b000303200c2d02a1a5114141d200040c1c01c00c2408410500340308500948075800c0400141700520541c140c0b00e002d41818000e50084550207005404200a105100d602c1078205841e45152031500c2c181814095458510580c0c2c42d00c04d01d640090131800f00303c0884035100c0b46400c40024045601c0f030200d111146049402604845203100e643c994407207069141440c49500006411a824040242c0501185a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 851124136 1250 851122886 851122897
    0x40b011d0f04020906041202090714040501030f0213060f2304060f021606092301020606040e03071704090c0c03021b120a20010c0f1506030c14010318050c040911030a08 74
    0x80350460825546d400703007110300c48542f0000c01ca845405200411181d4000d8000b040210f000c2c55000d804d24029041c5c46420300d506520400009840109400c01c045c0c0004046003c11341003051524044910b20a2403c0e81c8a18030030242000302003c1a1620746209200a08813210740ca10040c00c7c043e69900300400a82d041d0140188242404862481c1c0c20214071340804c0540f01030b005400280d44004c108402414500300400c00c50104111030000030380110803035592404026040342c0c0b6242403103480c10803682c104902605000b081c01520300070070340010310616950391b484034610485042c1d03000700c2c0d40003031a100900c05500c94056008108020b00c14002c0c0c810b40d00d542551804000c00c40110b5080c4840c41c0064a04908130368010080b8100007508102c3c12001040820b60550381ea4540720f114041d9400f01001d4410940102d100303691501030320070084007005c0d00070740036400c1d921516154020344030ba01c0d01c6180e481604804001a40d0043da603000001410755400c0d020320b041045095100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 851125386 1250 851124136 851124139
    0x303070c060f0c020c09070315090e0d080105150d0617030d241a0c06090f0105090106060503010b1c0c0309020108010e04050a03140d0c050702040b011d0f04020906041202 75
    0xb4445050103078681071082028004040d8000c1107003500c60020f0011409001d040a400c154980605240d8a102469044010f045c4d007440011902d00f00c800144c01d00104030645420092034000400899403408030003022030842140056a40c2255820b500040c10319500582008134200d0302481c00c2d00022002c2d0403c002d100d48103000c40c00a9043c015a56413003142e040000c00700348102130000b4050000d0040e84060116807031441c00c010f61202615000342124400307031560240084902c411820700503e030300842d0520007840030b1401c101015015002c14010380ca0b003800042aa0b159103012241201d11104030b20000300040000140001c3c09400c2d954416404504200000070341c40b003416012a00c41d98000c0060a031404150f541110300c6c1c0e2240c0d5061a44e01d9040c002d884443c2c3e620b100d03a03005603505c0d86859555000038818002030762900703596a414402120705504000c808100400b4819604481000318a4948030014000b8011414241d070000b0300854081503076455400c503500031500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 851126636 1250 851125386 851125391
    0x30f0c0305042a06110a06110301030302150f04030f02030d1e3918150906080402010f0813150b03010e0f1b15030403030c08150d12110303070c06 64
    0x11408150031000c0d100c111904607203c01582c10041540304425501944507494161041c20b0126107030703070050703480007099425050710000c010403c054040004100610004200702a980707040707030b90489400c50061001d01032000141c00070000601c02d104481c004094010104540304182003040c1c3d03030f0307040d02c82003184140c078114001c00d0841c15224110309400314001e0741081004000003005525401c9243d04050140001c1a032035003030001f507014809401910191070307002e51038120003021030346140e210f9002d0003141400e20016036031007140e6520720740c014142005103454500101000c41982c02000d05610081c101c41c1903066130303641141c5120740c0110005d00100c04800784030368a0320380c005000600307940000010781c417280d50320781c2484414034001d041d544c0407000d20114226641c0101c03011000266a130180c200401e4100d40341c41e4100d40c00c8440520240c1c802404120300400419020f01100800e032200c0e041d851203a0117003601080c40c2400c0c0d81e12820540006400c100c16000c04540c401e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 851127886 1250 851126636 851126663
    0x1a09010b040b0406051e0604052e110606010f12020c012f180f120f070f0503030d0f060504321509040219060f11120405060a030f0c030504 61
    0x94540161019100c1c001c0a40c141c01280c8001b0350705100505108980114090100007503591392824446490389000c071007d014548441d8040c0d4010444898442c1405000704c0240c100c080700040c401c2e80503e0a00f4010840180c071b00d400e403001804242444015800040e18000321581034108468244c0031440c0b44401e8074501d08211006101145e00810001c0103200f0103c4490b070190858403440b002a184e021540b1960b000300304030701c0a040e608462944581c99840104408100d040028011440c013560002e00340701c0000c3d100d100300d0340105100c5807249584c4880300510392201d40101030080040240b00e00c00702d55581011903c80c2c1500c1100c80b41407541c0083c0d0140290b2070702c80c100103c00c6d582001900d41c204040014054801d90700469401034010a4480c1280140050600c030388444105445141b4001c211058000a081d00358000583c210320030380c4100152000c0d908200e50340354139042c92207012001055a40e9100c0803040c00e0185031400302da0164001800786000f03449071040d18 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 851129136 1250 851127886 851127889
    0xb0301110702040f02030f190e0a06062301020303060f03010e190b010f030c06111006030503090f010c02030d030b121b0901092f091201050109150305060c03041a09010b040b 76
    0x3800102e82c8035901c1203078800018244840c04400d89801501000b0005a54400b01c9c40d02c2d103040a002011241596100b4060103c80150004002c05401c034108005008000500007900ca0202800710785c0180c41078440609030b550290054005035000c481203070088109800d40a0b0001c01d00802640c1e001588400440c00c031858158090075640c0200315400385c0c614003101211611850590480d250081101c1030b901c1490320301909006500907c000c544a0381c107a810054481c05010245041c03044c640c014000586000c0782001e0282c0715824001070006420011441c42c10016420010034090402031480381c2816a94244c1c844a0a80f02c0b90f01030b07a200c0f1102e408545248020728081c02101c1c080201c1c00a1414002089007070ac1c41105051140c0e5001103a07040503111607111840e5110385c0148180c011a205e5820301035068100050300794915190903032a51ba000d0f2071225250750001c0010b040c0000c2200d0f03144d00b0350800d032106e4514130304044054024213840101d00d01c91402e1503003003000c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 851130386 1250 851129136 851129141
    0x2071109090a080d0216051605010e09160c14060f16081b0c0102210615030403030b01210e070519050d06110307180503160303050d0b0301110702040f 66
    0x3264a44024442e90b2680e440e200000d81040380050700007038007001400e5004a5440f44801e919100354020b0012070742040c170f41c141d46601504400e04225082c07068029903520800542c4c0c02081d000c2c51501940640301040b80c1036510301c50003811894020072604c0c02203a0000b0300c00d108544440b2452610303180c00642c05402501c1c000d00200194513a00450303d1200c080e008440d044400803281d9182000700d0008509903086002d000300d03c0c403241000301021040211505a200204407119001010907601c4450b19010141c030241c10160f80d09801c03030060b402080e02c0c108480700b021040710070380c4080300400c0c045c10509810003103c0c02411800525403d01d101c0458042ca031844448800600b410b041c441d1004403c00162001c54031808042d0407055010002c6015581d0399840c0c0000005901d14180703820003d42c0300f14000c1d0302c000c812115107c00d0400700340075a40e161800300d40c0c441145020801415902c010385600d940303000f50711110702c0720042c0100700c018403e540600c980080c12040404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 851131636 1250 851130386 851130391
    0x6150f030b0a050c03040b060a150207030302060f010b07140c1c060b030115051002031209151f0317070203100e0c0a080c060903031308030405040e0c0109031103100f02071109 77
    0x4c5504040c00814000307009648071301c5d07011002034040c446a9680308110303001411040e02c56401b50704803000500034190705002840d8001e01c041c22643c40d0703514190705180503100d401009406d90011146202c1e10309403e00c400d0080b43d00082c252a07003a62010780110007449503450490b4100d10380754542d0b2080c201170050f0070480f07408018444801d854403050280280c20340e01010f0840c041081410040314070840d00a004031a0400141000e010458140e004102c002d48090016410006001c07009621190703900d0a0f280d011418103a8115a41e041111074080c1c040000e5060040e91600f60565100740d000e402d0107000c1c3c6041b540014900400c0c0515010607006102c80c07074014025404d03c500b00f12006209014016084034500134205100c80071f100031941000340b02d50400a810081c618090003070003069034400010301900504c6c100080c1c148843ca1000038003d41a4011407a0507a905000c04021064600303400e000c40f812070400800254081b00040b00c81c0d851301080d0410f0f0b410b00740b42a51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 851132886 1250 851131636 851131651
    0x803060d42090b190603020411090103052503020a0c02060a02010b0307060c15051b2d0406050a11030912060a050c040608220f03050a02120306060d0906150f030b0a05 73
    0x1040ea0f00c03049100400c3d0a244c071811604030b51a50740000058440d4441c891030310748102d43c260344620724040010103644019040b031448401c3c044d01e06c2c032803044501403800c01e00003d043c0140e03202c080d480b00b912140c60041e000380d800103020640840041d010f401600621204a00783c50307101d52110700035100d1094192026002081080101582441503403015070020070000d0001d48004040f908d82600b075002c10110052912507100c1c504040c2e0b460305040c4000500c100166080608146008100d4000d85c046d400400586e50080030301500107100329105400007402170824419524a002d99075801034400c0703502d903842d1400007aa4404082e0640b41980d950750303200390b26a102c0c2c40c004078404210400c41c461290740d02c3c0403100000e01031002d0f140001d2094491a4640001d041c002e8180000713045000c0200c3c41c02c1041044942c1d0f03072011107140490982002556070b05904025006152203049072128042e00e680105020302145450412a4450300505d2950303590b10014406035002070b180703070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 851134136 1250 851132886 851132903
    0x60503090d02071d09010b060705030d0b0d1e02010e0301150f05040b0315102303150108061605040906090b0a060201020a1b060b2e03090803060d4209 66
    0x800d00030148603c07550080101740c0041681140c50300015040c0c0d10610044030030380c1c4005017030600e171142402154034030517040300c00000d9041d182e00c03800a07100c0c45143c81000740282201050840e0f0042d030383e2402d1041c019000308404003c240502803030100c1c600842a5009158000050300e260500482480d58005405040d04500842c201003501d14060100ca4038071503500f001156013540c617008003583c0a20301c049040c0c3d1094003424036080081002c1c0300b240101c120001880081d01c00125560000840d4507480f40c10b03a40350900311064040ca400c0b040b45941404000616080349070040d140e410700c201c42403090359998150980c201e12850b461480864032102842c02c1a0681800402c1e40c00d00890780402d0704a14480000e002000104041188042042c01e6040d070b003100d210748001030f40c441e040810840c11582c444984600005140909c90311100e40ba41041050741c0104610325100d6040300e01a18042c4001040c88400801c5010b929498a070000060740406000340b056182c1c109110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 851135386 1250 851134136 851134169
    0x1e180901030c0b0c120711280317090d0506011a0a0f030213150906181802130e0c0c150114040b04062309012427060503090d0207 57
    0x120b515030010140c0620a01a212000d00312031401d0000301405841180d8608800441c40104080c00d071080c1420b04d84a0007204050070f8140b43d231044038007903903002205240c109010b100d100c0502d00ca2450b51940143d0440c0c442800c014000802c1810f0385d8038000903c00c0340085895984644c0a01010880042c1d080c0c4810b15150f40240d0042032480014140b40c081142c95202e042e251540c260004400146002810003100d60701c080100c40c460b0818402450003031908081030409000c608a441600b0740c009440340381d0038100d030400301c000d2150141c540424a0a1080c0001940008036040c40d00d001e4125a03461101e0407280e5181692082000d007291300c1c003008140300040402c050001d80260f036811000c200385e0001810b40c08219500006892142140c0d001e02031180c40c103034041e811680c14a2007000c1e104404406c2c4a02041583c40c0080b4100130150300703141484d002c45e212030f0003100c8580011907403542c060005c61088a080c0b04030703202038851040403a038500f5944141c110030b540c141070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 851136636 1250 851135386 851135399
    0x80105160c05030d0908031006090f1a0705061003050c0a0f170f0601080d090503030307050a3203040201030506030f120a03020405030105090a0b070806090f040501021e180901030c 79
    0x1030860900d4007801c216420702000318012005c031440380340180c0d10304178040100162150081070000180001c0d10380300d20001c0c9030031080008a038050040c0b001c0000102091512950b902080c3c07900980c00c02c085034130608245240c0350500f603090106440500a08404184030304010f00fa4008881e0800c2c400c2005d00d1400b44200c1001064160300e0034076010740d207030036915540100b16960192950b040070b0300c0c803142008005402c1c200306502080c0240c20500401a804e07070031105840385000365080031107050300c0e03408482c00b00a480d080c81701c26104041c120744d1b444030000805507101314401e072010407194480800305580c1e82e031201e44e1041ca90380b10b80030005514040c10040c0c862000c0a00f0b003d41801d880f500024207540089460550a03070004041c0410b01520340d0b103854002c4040d061000490501c00c000c5500100018142d0340d181e45004080303010454254101c5482d0200d0164005a4902141105250740c0c03001d4050405140b20000010035480c00c21111030403250b004601d00b1080c3c2c508036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 851137886 1250 851136636 851136647
    0xe0f010f05031e030c010903080106090602061b0a120c0503060f030102161104060812070327061407050d181403100b040908070602070c140f0d05010204050406081608010516 76
    0x12043c01240400d00508000100074003404a00381d00c40d0700e0300d031495810300800500c035240e41d911071005c40d404042484142d000000b912403030700080907901641c0e204200001c1d41d144685a8141e0340b000d15040b01000010fa00c000030b14001c9030101c2d03005000610070303010036091b4054503e998030124840120f450005241911911401c80d001e480030418940d1181218200103901d0894082d200000500380200340e40030302c014071015040440d03071a45039610302002082007a40d00800f01484602282500e000300343c2800e65070340701d510204441c2c20204050004081e680541c0000364441000301000c54800b03610062556004800703801450b070421b00540c80005005c01d05041c98201766551908400304501c1001440305a0061001680d9411185440602d0711001e520104a4040e02c500c00e01140c1c0c5d84900c0740460100841e0035410559080c10481d0092050ba4450b40c1d12030301d0311030b00050b00350300406c6207951002d0250740d0201181d81d0f071625500ba03c0c000c468409005000000c0402c070240143c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 851139136 1250 851137886 851137933
    0xf060c020f210706020f1603030804110406031e030f05030c161401050708091501050a0603050910020a0e0a1202060912030f34050709021b070e0f010f0503 68
    0x454440d5440c08511400303030b00f0180290000340042e04000c1072102d040d1010400e41c0b8144186400b400f140a15644005092410140000308130251000e00d42e049a40c0e030703410201c050758104200c00e141c3d1501b03051444c52900c01100807004200f10724102100d150040e010f9901c1696001486c0d450000c200c0340607940c821101c0411148002c40800d8042005024030a107031280d140d5489007038003030804480352494501d0001c002c9003011140c1c001802242c6483c1811421a4104d0078040303103944540e14490300f0114240c4400c08030030b00c0401c40d00030042d8404040e005400e03055070083d28058603100c16030010b00280c180603400c0f0130100800141e90030141400001c2c020700d0802e032800c00d650140100302c254002d4410344072840503d0890b5000a80f4030303850071104484182c6102c4e2030051981c8468a408144c80383c08803d0761301080c0c00b4110401c034816a40500c6a09040e903481c6510781402c591010f8050304c0c224481140480045040c07448050f12200340c0360018020200d101c02c0c182501c0040005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 851140386 1250 851139136 851139169
    0x90807050105091f02030406120e0a020f01030b09040c150203031302060c25050f011707080601030e070e040308180a0b130209190c02010c1707020304081203010f060c020f 75
    0x5a4070342e21410411051000c01081340c3d8081c1d40e0369803608000030020912002e442c0c5003075180001d00c0f450070100061a4000941c181c50b410350407400c0f03400590081141c1040c40ea0013210881c00c01040002402c103c400b40c1388842d41c4409071401070f00381280d80380001c48143d1040d504041890000d45842e50140207024451811030759840c444201c00c940310b45109504580060782100184100c1c6480080d25003000b00030303c1c0c241c1d00a040da0b0703a0b05002c0030010b070010051042140105003540d1082d0001a411441c5000b01c1d0241a5140710010308800e08032415000503015001184003084100c9074103a4460071080280700420b21234070340c3e04900001509042c80003030000c00000068813506986403086448a40706044100c40011110035a4808400c000440e4541404d2901c070b039421411992401c004124003480235a9643d02c143d2840c85540c020b141c062250178260204107105100540c16280001161205c00f41d03102d4064500c0322540e80c00a6210b00890044282d909001e0020346503203070b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 851141636 1250 851140386 851140399
    0x11010f051801140f0c0f0f0304022b03140d06030b190e071e05040f02070b0109020906040e1b12010303031b120c120612060b0a030b1909050115051009080705010509 72
    0xc58041203001c0c0d0344a034001f200c40000100410040d0b10b000c2034504400a20803001040e131070640d0039503e000010b201030003000d004010410320341c61030700c0704190717610104150010407006869042a2450302011114050041820f0440e41c0e40054207000e420080c410b032100920700c0300d04000008503003881015450b07020340c03550300c00003603582c3d26401580100d10b1205001a83c41102d030805985100e8140c102150316401040f0782840d44e201d21049800320ba04c00d0b410003a05c0e4840810401a0000607104c42c5610300c0d020418039603450b03a000140e41244e1080e101084410000e440306043d000140090001044a6406003030341c2107040d07080600c080e40f2611701a50300881c00003425080328901c0d00903d0b030420b00800080100069886a12319501c0112846800c580c515901d801100c1801800140000e1034507886c007804901035041358050960003c02480703811541c8244001c4501c2c644101840b407500520b070b4002190050140030182c8903100d01610754182414010b40d4240d2180020035008003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 851142886 1250 851141636 851141647
    0x210b09030a02120d0b0d0b16020c09070f140417160614090f030f0f0705060c0a110604030b04240504050601090b13090501020901031104060e1011010f051801140f0c 72
    0x1b5580301407000e04511551008400d810044424101c02104080c14020342d8481c80500580c0d130380300341ea059800031842c0340c24491031001c001c1c215a0350140500d03404402c0e070081008140311941a544040b0f0848001c1180c204032105021441002641d11613130000c6000c01c50358140d115600001451420409801c003d80e9802503008207141049071301c140031868202e41c0f81400c0d440ca00b03008100007050100c800a040040380c841e82c5031030b40140c500042c002280d1501c079401c25165801554000e41d0000d01101640c80d103400d10740f405012400d102c0c142d6840c82052500206100e1141c18065a00f0070001c0c6996030900401100510904140c56401100403034007460f040800c0c020041d030f00d48101c002503260301c0c5080c005016542c500101f070795055400d0000340b1189a1000c00c1e11054201200c0d001044140bc60082d0b450750740c41d40420740154209401c05102a01e1900498043c94602240390030214854108a0803513181d02e10040b0008030b404082400f0820207540250042010340b000342c03605 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 851144136 1250 851142886 851142889
    0x14151215130504140721140f010207120318020f0f040c0c12110a060c09050d14060105042009060c0703051609051b030907210b09030a02120d0b 63
    0x1808101d10071100300e80c50344104070401076020504508003442100400d591414020125180342101d41d0340542c14180c1e030900c0040c0400c07061109110700141d003d071030110b600c1d0500f16003c2d5021030360a56240c10b070723030320403100280c401d104026071742c1aa50364802c4802000c1c2d0030031821070508010300b9401000780d02155810380d110f11a0340300180b03994840610401d141c1c54100c8864542020b41c1c810b0041036007400800741c5c030210308007011380e500030400034984c00c2e154400e45183c4110f8210f950020802c407928001c0000100001d4645a5900c04440007681e8a20400c021307144141c0c8021034a002507283c00c0560141c00c0013802c0400d900406603400c210b034541020b07146c024150b00940ba03a60040302448111100b20400c5d03006085102c00c240722901c0c3c1803140034034503c00c490340b0182150001002a2a200d010b00c2141d010b81003018050070a80d00d5885101146a00e017101500c0e080704210116000c0d0000104803002114150082c00c54504010403240064000e140102001501c074104540a03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 851145386 1250 851144136 851144149
    0x7120602090102010e0d200a0f0210140a09181a0607050309041401061b021f0216060206100501090e0609060a0b030c1905070b010513020c1614151215 66
    0xf2172880d52040c0c201c147d9080c0f072001c80108904190040d420850140c03001c16828802c203000c00d901030f1105c1280c0c1845071000c50f842120352100500d1250040780040c495a80201c0784003c49424480600c600b400000341c50080f1f078030000290302d10152003600e40c074840c240300e4040c2203800d001c1d0007500d00305107803240070809440445c04202c0307e50b80464018048c0070380102d02d41d81c29000340280403000341c41076408564800a083c908500d0b91401c0c01205030030300d100300300018074a040286510912980c0300c0c0007075070b641c07405d58226003000318803e0040791b80d510400c03001c403c9070351644120100307031a100c06100c031600d0f01810540d0410107000380401d409844c0c030000d40c000c0c0cd0b0301440e1581d0b1260f0769102020301080107038101c20084200058400f00300484c440034151242103c1569048146e01c04a01c000e200c1c40242003c1c0d401410000c5040201203071083d4100e51189035100c2c2c8803a00642080402500c240c84164030308000d0040700c1252100d000300b55441150070b00c0d810450750004002415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 851146636 1250 851145386 851145403
    0x11107060f0e0406140a0f44060411060a080115020316032304050f12101a030c0d0b0c130504060b030703200a0e13060303080f010807120602090102010e 67
    0xc00d050003817883c2480e00f010490710b001002420404203400f0708140c1d418102c1d000c070b841c2d00042d0002d200e44000302594a070f100c55075044001d400303000140c003181d0007103500c401c021541038482e101244020030141c1443c3c400c60b200032920303940e00242d980c00c01007034014100700703441c1e6041140310501050f03c8680880c0315040c1e03254000e4841c1004040c01000b032071496802c003c1000134500c8140f00c10401501c0d00d008007800c0708030444000c008002e83c03c1110345031501d15029950f04604083d40c814004007e0a50445c05a40903000d4481115030340041c0091900a035a00400c44121200000c0312503141034003400034802500e1148102070760b940000303030a4a400e6049910281400404e101c03400350184900c51302c9464266503015100745c00e48009481e800b841c00c840041c4038102e0011031490762049040700104503922410800303561a81001801c83c40704071807903803210b0a850b0001c1a00100011050120342e40440c40032107079200c2e55641030203034004200d114195901c1d10a101e0100d68240040c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 851147886 1250 851146636 851146649
    0x30702070f06050f0d200d02070c0905070e010c17040b0a18060f0e0a08060c1207090305070605090d060e0f010b06040f060c02120303160905011107060f0e0406 70
    0x150903090503100740401c0556030002051101c2004081d8842e03d80d00192444400d0441000644801d40c0140c06141d04031000031003018040041ca840303a00140d54054442d882c050100e5402d41501c0714025030440d9002c1c1c4a50300861042403244078190f1280803101c010600c10205595418101d014482c90360304540c0005030608404a0420885c0d80c0c8034400c0b0803501c0d403e002c2d032146a8038014024091a52060b042420414881c41d583c0c1e25403074100700c4100420200048548a1800160310b032450f800000300e050b500c0140c000454a1203204e41000002d0704e4101c00506049441e00c0c00684031580b1a104058110351120700b1440880c01a1190700c60394014040a0040d1441030144242182c0007020905d00c0703104140000e0040da10780121100c01d98a280c2025411405540005000880255008801c03884000104110300d003501c2c0907240b01c1d60b569141c0c1d41000f0f48410056540d1403990305400f0f039550001c102081202d1152101102d000014204051680000710104054807411b40005c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 851149136 1250 851147886 851147893
    0xb090705121c12090512040807060c121d030a06200a0e0906010201021209072102011d040e07080a0c0e0c07110103180f020f15120a090503030702 64
    0x104441d0801d54201c201024642024252140c01005514506500a54140200964042500380c800516800640d80c1504242152801048543c0c1c0c122594024082c0c9009400345034030004802d4026500652050717401354000b494042d0b0100c0c110f40609180c4050340c8051040d405028954400b40008814180242c8020030308070700c510004141202000913000940c0000c10004101c55440b40c0b04502d01c00c0102c806040c5511110b0040340079000c0c4403440c104002202040c0801c050001407000100c502c1c610f180c440c2c524075031808501c40b00728200040d0201d12940b04c0d621300000c00d03d0305200307820382c001e1002802100c0429441c0c030b4010160401041d0340d0014612000344034890321448010003441d04184c10604d0844030070032140c001c200c0014206215100c440c201603019800603440c030722800080890800342410240c140c11709803001a4058001c80440c212241496501e0070254803440c1a0a440d01c4503444416030400d400a11916007580e80328078900020310280700450040000d43d004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 851150386 1250 851149136 851149139
    0x109050106050108090d0c02130606090801060506310902040f050111060907210b0a02040302180c0412020d0501020a02010207051c090501031d0703120e0303090a210b0907 75
    0x3800c560080e0480790610680c10100b0882080015400e8032107805450b25083d4134490788049042c0a03018032600c80c42e503052840202d62142d000c5002004c403401c0400034002191345100b8000c2d14890140c10301c1204601d5040304d03003c880410308285105840229201c42aa50745060384100e1304a504109140c3c084584100b0070b540c1d10030390a00307041d90200007400960800d810005c0c0d8171402807140310526144c00644554615500e6403101c06260407010003802807801a400c44029806400101d20800d012201004000b00460300588503032840900540f90038148840d80800c003505240c02c903800b40d420740c1d504c00002c00c280040c15030110315400140c0c60744100d183c02030400000c0d440c09032031022060300c10300da469448000d4004643c3c0a090002e0b801c203405c7c000c41c261601382c68480229110700030001007000340b00008070324441c4060351405280e050750420151284524140c840d0700c81d40e0041e061080d1603081c9181940d14a1044c4100500c0c01c041e40c6075009041c1c101c0303200c900d030b400a080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 851151636 1250 851150386 851150393
    0x360601060e04110316051b070501090b191103130801140c19120615090602010f0e25050312071109010302130b010306050a03061a031f09230109 63
    0x2107a081d95400726801e0002c40c5030081414031900000b00910001c0e450955403201450040c0d040320081b103059408044c1103c507e080f200c3c0c0d00da4840c801c00f800140c000740000352007854141030740c1408585c40b42c10844074410420813511103081d00641c2000c0e0104014070509401d208510100501d802c6001013800c40036a02103c500d03100007403030b0f041c05900401102c0420b00e03003e083c0e202c00d0611420000b00c8200c0b001580802801c0b60340258119100004003042c1c00743d00581101c00f1106168004c1c003240d0031a108503800d8840710110400e140d03010000c20605214540034182d4083c48943c10480f07410390f2040040e1810540e60101c1e840c8102c009102d801f07105091040510600d01641c510000f5459a40402d101102c13200b41010a90381e15120300205130700c2600401d000b00001815050f080d5100d04110006281c203064134400b40b484042503810505000c502c0c0403c00003802d1030840303800c0d00da2059a01401c0c030314000700c079210024a161071f04600740800144903940c4034000007441003607514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 851152886 1250 851151636 851151647
    0x190512010b04150503030f0f07020d0605180d0c0b0a020f03010e180c1305060d1712060a030308010e0916030c06030507031a130b06030403032f0336060106 68
    0x42803c0b43e050106014405a1000800c80762451012121385030b4550108070742c17180714006c00800135403011980e07103036500344041358200e903014081400c03610101016140910b6500ea01480c400008150031b1000710300400d810b065125401500707a0809803078615500c0c0e08241d10340c400d8000000c807810400c180210803134550392070b04000510000424a082e9054001a0030b00c0851149103a015120000580d06442e40242d81610030f6000c06000040741104a078421503410a09203662040900f10029402d840d25620100450350151640100703039080c4168000c10860007810179803035100b040400f50f8100cad05011100002c40c061002501c140341813407001803d43d08003078644000c01d8140f14145a00c101003084c0c1c08240d0346c04883c202002d9241e0300d0207101420b201c040499102c1b070040108024103801d604140390103081041001b60045001224502820385041c01c04108102070001880c0300a0905040b045940300d031032a5a1401007a4140f20900c2c02081e800b504940c0110004100040c1c02c41c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 851154136 1250 851152886 851152901
    0xf13031a01080619050c090a08060105270601030b010c0c1409160f030e160905040b010f0303024308012019030b1c0201080106050f09190512010b04 65
    0x200c00b51040742081e0310f0751010490341c0c030504060141e0b10404106c0318a2100300b00d490510740640300c0c07017901c0e84c0c4004d00d6840302c509100e0540210341e2200b100107800341b008444a640c41411001e0351840d03d5110044004000302021141885503100600c00410748480e003020007407105074840ca50001d200300038800d040001400c6200300400440c0d0304a01b8503040450391441c0c1c50325140c0019455000c1c4101440c02141c8000609103070307204400850301841075003046201e0303805941020740c01d990700c0c908601203030124030014005030095060030982c0700a1104e4084580080c0040c0340130410340f021131450b80e6005030500d055103103518504015010b0203008190000007112442002c0c680350440240441c410310700904c4084001229054410380a5400039540e800081c0031824010f0f0401e40205000d0b880c83c1d41030740480c2450000080b01446102254510180600d60038281b000c03603018003001500c400000da000309070302d80c004205030b1509030b26500d0280c01c4000100f00c4081c0c900c1030000321010b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 851155386 1250 851154136 851154149
    0x30c021302090103151d0a020d020f09150901170901020d06081516050d0207061104121a01210201020c10050d1a18090c0409080309161503020f13031a01 67
    0x24014108140c141b01503160342c0202d1400c03944040b40d80e5170b980241c002c3c803518030701e02c00f001d1000c50080011500d5101600c04005c06595412200e40e07880503101048c007441080c03a000405800c2d138417990303c0c45400120b4000d2101e070000b504201c0c41904a00513100e00d9005220b2640c0580f950843e142180e40c60f203500032520b0010407804c0714440000604c607100304080203401383e800050810800c82e0590010601449140340907850316100c2d290340c440d03c0388004058900b0350010003501404680144420b04941807800c50849550340c03031640c0c0311010340c1e49000743c0c1940564841050f250b1121051b545102600380d403a5603035014400701c1c200864086011078801034800001031001c0382c488400410341d0340c11410142c03030b065580d1000c0d10700e00450120459003190400c02402d0030010707600d02450140b01c40c003040c1c8440f070b0040900000d40d2030310351003100341c41e04101001c594140d000f503000340102100c02d80c21034136014049182c130728034451940c02141e290031020a000c03100c00344041464090081e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 851156636 1250 851155386 851155421
    0x7030b04090c051203091c1709060304022e03020c1002070f020f1207060504032310050c07020d08191809180210110706111207030c021302090103 64
    0x191551a1400b203a402054064403401c1110b840c2c1010420955034070303a40042a1122a45201841103000419403000302c8021840983c40050302c48004141c4a6074640905800d086070b45640800150f0080c0281040e428030a266080b94410159141e9981004103600e025a85411010300c00f86801118280413907060307c1413014a000403d07091205058580480b10a41086900400a801410071001e041854840c683c1c001426680140243c004c59004550014455407000703d141e039a91100640d0715429044070070107130f00c50748803588915001a400400742e42040e003242d0105140281281041d00c0d0980f0220340000d036682103c01105001d001d52a066100104141011485404900651240325101c0190028035a208021400d11940042c20a850aa14141c024004555a0003101a9406000030105440e40500002d030b9400131040014610503040c080c0c4044070390040d04080381004002000000513a641c024100d003442012000141e0b11100a40050304803070000490714507240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 851157886 1250 851156636 851156651
    0x1f15020d0219020904060e2a0108010e070206070c2307180c050412020102030904020711011403060612190c05030109141306180b1614040f0513020403060c03020307030b04 75
    0x1c813550303040754110740c0c40040070541c004032a03242c50901c05240d11800a20000c0c10611045034803c003d07200c2c0d50a001e0f22100290398848070704049280d0104d0710240946e1208004c5180144107459640456000e540882c91130301d10468490312032800ca80381c8020642c00700c5000d08c4071074400d60414100400c226001c1110441d11240507000f8012071107a1541d00300c10040350025640240100e4001c4240144210341d100002e14000800880c40a8150700007403420428110703440d000400c40c0d0240c10000c11590611228008201941ca801014070210b01c071428407100143c00d1a006030000303840c09494543c1c82c0d42c100150031040782c1a8002140c40004500c051010b50b8210001220200790043c00103c0c7d1084140003480894039507010040800000c0001c104081c40d882c15104031414159684002454450b012617607030340102d00800d1a1000408010001481d00303071a01d008800c0c8101e070250a103542c03500d4160841d14461016000709070000104011154148500c84480d40c04440401200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 851159136 1250 851157886 851157889
    0x301050a030201210507030504050c03060105030619060506040308071e150c05070219140102120a0e0d05030c1606030903080604020a090807080a0b0603030c061f15020d021902 77
    0x80440c0300182c140300c0e04a165840070b84e03400100105118500105101d58280600010014803049070140c1d01c6010310a41c0140500d80414014100ca10042c01403420f82c5070071142c0408000105849441c090f0b4544c400540c41c0c403024003820003103008910590b21001d2a00f000c00c4030644110b01d02c1d800d11004440c0390300050a04400b00020380b5010000242c18030000c400392401d101d5098013075480060b071143c040c080054505001e0599050060004088103550016642c0f4412001d85242580c010310810440e248503d0100c0345481c0c0040400c0c0310310a02d40c4903141141e0048046910a4000c02c1c00008103076504c103018401480b07035281c100442c20841c5c800400f20031003d015144a585c001440d60306442c40352001e20094071280040d111090740d038500103a916042c9410071600391407048000f44980c513000c026034807180b12100c00340c1081c5d03403a00d00248100188401d008988401501c003c600011800c2528000004c0f68000b009040e82e595000303490041100c4454428202320f06081c40103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 851160386 1250 851159136 851159149
    0x60f1f0e090103030c03121811040c141608070b090303040201080c210c0f04090501080c0a0b0d02090103090818090115020d11031917010f030f030e032109040e03030105 74
    0xc1e950585480769403003e034403000030003901c1200308d0f100e0714a920102d0030007071008200316041803030000c840820041a0140d0150340680c50a540d460030410144074000983c00ca030041d034000e06205100380c2d0710b07003442642c4030410b09000380e0f082c00c1c040c0d102000700411941c0150043e80c21810070340d619070511004848421440070064110390541003200007084040010000399040c9005041c0c0094484ea100d802c88801040700b44203000072442101000145070070407040c102d054440446000c2d1500c1c00e1522210041c2d84059400d40c1099a2288031704089013500e009441d80b00b006a10768034080c0450000c000a007241070700400d0750000c0742c0540740220368000a81d4600c003501401c05640009820280034194004e1405a1060303600c0500f50220240c1e00801c1c0c03250222400d01903202c80d90321041d0790750b01d00c000c80c0002000c080060510002003801003041515500c401412100c608042ca0a9141c000c28207030000896088003044250a0f4601401181c1128120000a60543d890800003c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 851161636 1250 851160386 851160407
    0x50f0106031e0302071710110705070506071515090b030c0901120f080c0726030d09060f0f0203060f06070507170f06090a020109050603040f0b060f1f0e09010303 71
    0x40d1100d003440b50008140c0207105800c0281003200681800340c0c0c0700740c811a01c60001000600c4690b10b80000e036803e101c0705ca001c2d9071000d0303005002010007a081c00c050043e2948903603010380710250107884c2c1e0422518030340280480d104014070880105490000001d040d81e0300c890001c3d00c01d8101000b130451648803118100e04640c09080d100700c0326455402e040f0480441000050428040000c40074400d0134000303822803c42d0603c242c07001c00d0461500141981d42144000807901340c01c100003018443d9115000359440d580510f000113070711068001c0d4041103031001000c0c40355494001c02001034510b031406004018603c161079407072400100b540c039a0744984041c05803070f91100c2e0100a00e1110641008281c810031b40c0360301210080c1c00c042c15a295200c00707002080340059803a1501103403a003864002c0da4003c0d6446204035143d07601c10340c1c5031100c0d404024982c0d034009182c00342d1006565a0302e50101e003411042510402c10220310000200b0b80c52940c041d02d40503103060401000082d52080c180007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 851162886 1250 851161636 851161673
    0x3200f0f0f0103020403050604140f0304030308040813080a060506040f18020405044202040303051204080d06030c03060506040c020a0b0a2306093601090b0f04050f010603 75
    0x1801c2011140058000740a103400c046d1030361068004100400444141c5100d20b041c0d041e04441041d20030306001a83c0388503a00005000030340321004907000522040280050142d400c2c00440040e0301c900c3c087c1d03c0c00c0e08651054942e181c460003032008608281c403400d412410340c600d043c481c3e901f5448a0032035203401c0b10b5002303010715a604000307000e000d2403040111051060394040c000d490703221588030f100300a10304420b548041c11056898018515817089804881d49900c50038107002c440c0040c41842c90340148242e90300364040101d060b40410f1442030b031000c0d601c00c0b18000d030007a0a5041c070000b116402072059000d036260040441c48281c000404407255030340014099416a1288442c502800840c050140c10300c020b49202c480c210b1220402512400c41600c401c892650740c1c524050600c06030228070340000f400e403249a03640c03080c0b4580c51003d4890700c070000701c0d02c0030071a40d0f10044250200c070080425141c0005001c03c0260034021a6240d00910000707001103810f40d00c940c01c1c103418006400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 851164136 1250 851162886 851162899
    0x4031e020316030e210303150301050f01030f0c150201060602010e0102070f020d14100203180703110f280302190f141f0503191509110f030103200f0f 66
    0x300035030354405504890340102417440b0380d22180350241880e40ca0b0030555401104409248444845c1d003814410f00f40314640d01c1d1500511079295848641d1900ca51502c02e4505031b5404401003a1500308040306c02000d81d40b0b9000091180c0741540003400c581c0d9034a84403250382d00402c0701b4000b107400480100c81050301216480082e13245407401a0b074103400c451110303056024802c075401c00401c0d1a80510b208071103a060082d000d060113042a522003d55000051403500f000d0b0125402c2e003010203443c440c1c558003400d90410190035404c0c0c419032078a504d100003a0340645038018000c5040500300c10800c100b00d07100e004400c60404022206030b5145d03000b1034a80c0714003407121048a50325a0303a88004284d290401c03c9101094100062042c2e0003200c02c078071000100034811000303049510030740d55403003d2002540507017420300c1c101402515000400c40b103070f0203081c040ca50810f400303803000314021481801c0d815034406035070703885c4c4003c0060030351654460305407403007245003c2e100c00000e4006454111060b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 851165386 1250 851164136 851164157
    0x406030b0604180c0f03091a060d060207050d090e0906070f05070605040609061d1c1701170601091e0b1c03170c030105010f050c011404031e02031603 66
    0x10400c02d01595200c800140304040c40b281c0144032a90241da40c0552650b2581581d41880d0000d6003601d0716040020650350400e8854480da8114400103500980010146603249600b070710792074140d07045140709681b150816280f044040d81c100c01e4100c0185001c0c01002d0703240c5441e0400750345800340100080f040c40b010614080e6401d10440841d481c0701c4d48070340c04210300d0505041000c003c200a4104455541c80c20003c0a1041d2408c40801c000c0344180c0300810034001c6115100c03d103e003070f0b401c05e0030a0080081a01203d00c0e210610b5070f0103010f25030f010025044c800682140b0344801070307100b00c09a0f4a020b40040407113a5803103509c0346451101c50003007262140d40300440c112030b44103096020708600e40429007040540c0f003c01c40c8580340c00800750344025103481c004207201d8807081c8100342c00b1900c400082150240180c0c05040100009000000d40c034540d60408002d00f641214110001408008441203920b0890540450b1000c140700a42c100307400c41460341503c2c00031040c06007c1c00521041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 851166636 1250 851165386 851165389
    0x2010203070804061d0609060f090a0302120d0f0504030b0426041403070f080a0209040c0503010c0e100305070f03092f010f05090105030a0b0105090405090c0f06030603030406030b 79
    0x329076145a001d01016981c50f6a00c400a0007407000c28036030f105001110b6815000d40c82d0907020381c0c0b40080b005141900e000010b032940e5030b1030360113030b1744164000d0240320000000d81da80140d60f50140442c5c40107018600200f041c028081e424040900040c400140001d1020a8040f1a215485035028460a002000180d004c904512031100d42003544d00b0000b40101c0c0445a40c950780c540e0034800e0b030841d8451500d4140907000c201f594000e102d1160701c0310740302a001d4a04120f506402c44d010382041d40c400c0b80c582c400300c1c1c2036a890b90507500206221b1244814a410104083c1081c0c3c00c035441c04004605007082c00600902c9080d0505041586800c9000240721038008602020400c000107814010008801a911106040a003501103040722000700703586030050b012102c0202059482c1451036983c465100d0003080300c0d4580c1810000180544055130b1602c0c41060302802d685001012520f541c3c10810191441658516014010610500200ea01c0000644054460506011070401c18140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 851167886 1250 851166636 851166643
    0xd020309011e06140307150e0d080c03030403080f06011227050609060c041406130e0406050109050603030f0f0c12030103060509060c07020d03080601090b0c0f0615010912020102 78
    0x100644075000c200e80e00d001c0a8802c0d940042e04861121104000710035480c0c0416440d070950b481a0fa034013034501188203a503148a04003c5400301170041280c00c0004641d1210348a942104180c91165400001404280b40d00405219841207403403006100601d01030000a11550541c902c091000e034540108811600270700c00b0005011344d020006e00700b807181a0505681d40c1c0001c0c2c640c03070058051030780414445600c200440381607440400420203074406c1c86040c820395603c1100030304404601c0680124554091091036030095020312800304165042c50381031012240c019005501c80e40c010072a50399500b050324180d0b603490f00c402201980b80c0d00c20420702420980c000300b151005c2c0c2c0300040080708000940e80402e000700c40003401c5400a83e00d1242c0c0390300e148603001010b0b6001e44149112070019204003d00c42d40b094040c500108000c0e502c03400b0305c00c00d81051001c002c0582050032004803c0702c0410005130b112802c40c0f4030140c071440120018008032414010410341824030b10981c2d0540e40200f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 851169136 1250 851167886 851167901
    0x9010f03061a0405040e03070201091e0b12150303041508040609020d0308040302070e060a0b2101090e10061a0f0c06070c0b33040b03070603020703080a0905030d02030901 75
    0x21042a20722200c103586010b16600600516110720b00c3c00c11410291880001600c0f1180d5041e1210300700d45040c050b8460103548418110f8481550f002008950703c54550080c110002c400300240d80310f4103054951620104881c81c007540a58010f100c2003000c888ae03c2c0c40d0a0416129013014840d03619a42003580c098202c9090294100780124036802c2015800404144154002d44c04d580f42d464550b9a103ea4071102952840d1b408601c002c418045803c9510080c01c2500105403490620b1200c55103009002c0d2003640861b110540e2401101e1111000340040b1109604c1c98104200c0c6600b40a00c11a014210b01102c104404010804c4241c0d028013000302d4806110b00401c50f911486c1c440720040c2041101ca000315001c00f2884040303448250340d100c0084903540e200f0403460318507400c1c0c031200240e60f100041c295441382d00c0b0340d61410503071010f20905014061945c0c016070703507114504001d801040003034005c240c45454201c00f440443c60110940e866000711140140e500c5d02c0e07551045001d00042c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 851170386 1250 851169136 851169149
    0x904060e090604021903030e0919050702031c2705030f1804230c031b12040501060b160b0712021305130b0105031f0f030c0503101109010f0306 63
    0x300e0510240c854001040ea00c59032085504114402c0514400b40c1c4d21101031000502103503082640346003519000308070a6000b44202c5105446100d04840e0074265281582c8400142c0c000003010341d20916815000d60000c45600f00911060301c8680e20601400b02c804002d8440c984200f180e0b40420005200b02c503054401a00065100c0b011081d10513102480f185026218924280c461640051004d031142d8180d0030350a1220865074850a4506841d400142144d01c1e848016040c0d003048079201000c2e0102c0801d66014030041d18192400d6400c69805e5002403101460911241c00e8031a0608158a6559403203402c050054a4040d402c2e100400c07000e86495020b4000701d9021100e0310300311902d0040b14400c40d050560250074071800e0b000c81e21003205150004408000040c0c1c4080c01120807401032002405d0381e021903a07148880d0040717000c41e42085400d840390031701c10061032404224040e4051480301c13040140704250188441b19108100f10603040c03103042d1414000c0603000754003810060a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 851171636 1250 851170386 851170409
    0xb0f040b040b030106091401020307021e0607050f010e06040f080a18060e0306010e010f030803101d04050127031b02041d060c0316080a0b0406090605010e10050f090406 74
    0x40710b040401c160f030000d00454001400c100d10001f18903442d00288140d010040c0c029500d425900e4090010014183c5980c4030380d090480004280e0782c54000040846601810281c030001402c072840300e084d00c076001900030495206200340300201c0c02c140240e147c0558000762240d1f40700e80c0800103941c103e10400450410641032a8002980754016890702540320301141910860382e04d410300c4c900481c0c82070003194400d1400e083c040c4000f0700440011a00903043d040c02c0340c0b09990f281014210520800b00d902e8500b100c1e0001d11041003003d00524982601c03010790006240c0003400301698550705804060304000d60f0000700141d444610104021a0f50058000d1100100c0c2e0b259003602e400c2094066506841801c00241400c0c1e101020703a4043e41c0741d5a1038610249802c00c1c01c85211201604034500345030396104641c0d151703655206900003056043c4011580074500f10000d482104d00d030780e519000d861101d2400b581940d00c8411101e002c22440c07001c0e0380300d070b0703040f0301007002051a600b11158254 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 851172886 1250 851171636 851171639
    0xf02070815010305060a110d0e0a05060c19081b0d090212060709060e10080910020c0109031101050f071b021302090f0a0b0324030615010f17010b0f040b04 68
    0x441c41c10419042e24090310032190980c80302c0140c3d508540030f007010000c0c1075806208007002e206464000500780c058040c00c0300d802d018181c50b1b0904080040d41c141c031110800090302282642091120791144005040c402854600354160304a8140405005061000e000030300001a04440d881a0200354001c0c0038500c1075102032100542d109402e03559900411100c07880001e0040c0300e41e00e16207000201600d44d00003407248103016035030100301170f04620081c001e6013903500b245003080c0b02411905450138004900e60300309080141500004007005072159041904010340080407040c516046101840c0c480704000500303002004543c140480250b112680a149821001154000d46082441100c8031412400c0e91801c0058502151081c410301a90610000325034030070160702c141220442490018808500c00700103401c0c403030100e4004294001003100a031880d46c0c0514a41d4083c0d8581c2440200c1084696242034211014490510803010000704510780c4110075064800910144101c1c68485 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 851174136 1250 851172886 851172913
    0x4110a12030c060f0612063305090a06030b13031116050f0f090403030b030703080403080a090e060a05060c010b0307030f05120708032215020a12020301050906010f020708 75
    0x300103200a40300141403144c07214140803144074070000c8031036032418580d41004503a200e01c050000360222200140d000e00a1f83c1c0c04c0b040e134420070003400a0f101c04000b225030801040000102c005080030340110b01d491003e20004889100d80d07a002400601e1201120030507107411103081046008480050040f00c62449000d051071380344e4000e458084800841807040319080c03004861040340d0a0390b005c25000007040100f4025800312400000c040d05440d85c0d0350702e0341c1744d82c5071540c0207900880c0c810700c00082c0140c45607402158040a8200c0f40071031882401d00c100040d9030302d407943c001c0300d205080006d2052240d0900351300c01036442c0005010368080542c1c2e42800d105810500d00300f603503640101400d040d1841c42c29001c4034000f903801310089041d600ea64a0b80030101e003180003204922401d0708818000f18058060025202a58000150340e880d9078034001403201a44000300000a401400148010361f20003030803a601c92800c2ca41b1030180380013081c08901d01031440e40890340764020002d07800c600 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 851175386 1250 851174136 851174147
    0x4110f060418050a11030f090c0d030809100e071a0904051e090d0801090c02030c060a050108120403021e01120c05040302040e0d0c0b07022503051606050304110a1203 73
    0x510290300b01004243d440702600703400c0e00c0c08004004000340c010000030703003204030207505140c00208500c2211240b80301680890000796460b002900815010f904000d10f10108010054030312030790b030500703002515000c1c00c1c3da5a10304480c0a066003100221035101d800f046a0402e031200304030b0091082c0100c0c05d008841f9031102041c0b10000280e45c002d44001365000c50000364040c2040e880f555120660380c03812641c000185040e401040131401308201600000604003c4240254801d410026165142200191806400e4200140210418003040001d070341e17680320045e56051680110400704241600480320343c490075054000c1c0500d07040301d032810a81d12401510969100751001c001d10700544001a60b40c150405105001a88201c007500c0058801800c8075003000003801211100300075080b0b110303450082c0000004180804550400c2444001c02550b101e1445000c42c88240ca401c0c5075004200b4840104041d0030440d1151200000d902c4803054040100300028071180510f480c1d1038000e04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 851176636 1250 851175386 851175419
    0x220911010e0102030414130605030a030e0a120302060c0d151d0c03040206163e0d03020d0c030903080a02030304060b060f041a07121e020c010804110f0604 68
    0x2941c08607090803030354000404c40c0e040c1c0c2e9106403002c0c0c0c800920010429070481c1e00c00c2d542449501e40c0000551501d0070000076815910039164410078880e00024040690400e510415000483c00780580200c0d801040d481e404c171000e0003134560f03070342e40d0408641d0180c02202809441c0d0010303268001900149004003500b4071598a5800246895400700b06405000a8801a5000c1010060385201076a81d21410700f11a01c05c00c21042e0880b030501c02d022000c0701d41102c0403039400e50045000e04804880340d40e107810800445003180c0c021425200203680d200d0042055040c80000d850407828140201030f401e000b113500980f903580e01c452111000b5100d030000d55007102c0081c2004007001c5903143c5802510240503c0712032160070075160007480e001501000100d10030142c0100540d1002c030341e581c04a501c5480740d0392278103031017105071036446030761061510350282c2190030032200c940c882c1c0c5c0e00956058105810080d07000b40544048000b603440b4030358040443e4401360000b000161590303070703000408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 851177886 1250 851176636 851176639
    0x20d021908121903020903010f06181b08071b06020409140a060501050a050a030605041523010f120e10061707080c0d0c09051f0602010e0c220911 64
    0x24403081c014074500c00b46000e00c0c41034140030030460742c1d2598100e10a902030440b8520050002c00e650200000134000c8600c0c42c3c00c880710403001040076000700c05080c01107148928254012800c90041c1200007080104041d10b190200000780c0c484550110158083c8822150021811585c3c1c0e581da40c41540206070085448155200640010383c514605100348011075030182c45186c58040c0d01241210503030f012040c840c0c01d15655140115654450740301e05000c615200703140240030703410550500102c02c2c595800901e01c04903070170030041070791340703e130344138080010a0408100c940507081050024010042d0107c461b44581c401e4040180f03407d4214004480d1035190807883c801140c5422905e8001130b02450350075034400c0c0e4180760303941400c04461119500802036042d18984400002c1e05407101520023030f514036032100d1500781c0c100004501070010b11050000f08004000f124195440d0480c403a1000c0c404c070494072246030310701c1c0d4034807a40a01205040c01004201d11a01d000188540d8448445 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 851179136 1250 851177886 851177893
    0x1020a1d030d02070312020a05070f0303140711101e3b090c1903050103031733040903111002030f041103030403080a05031906120b04020d021908 64
    0x1025060210b804140714000303502400c0308a080d61141000001c80a1120045119801c16080412402d104c194040d1480124290714107285040043c00c40c10030003020301d49080204901d80000315441c8214400c0704040d203240711810201e0340141c0d070040c40d02c1064121108504000d454144d402400c6030b009600c0a5a0741603020759034810010011120788058514915a00c260702741c92601d030360b200f42c0c0501c920711142e28112920a25001b0b10640201e2800400d80381c0300180200354200d090600c0030b505410208505143c4401c4c10440c8000640c200106c0358910001d40700046c2200f0301c03288820401800c01d100080b0940b600524448040c4e140180b02e01465400b103581d4803a900071603000b003c622800011540f150348614001c5150701c42080d5147c0b100b00300007c009159000075040041054513229100e01e0301000c600ca00f510280c0304444880d161902c24030000c050f1650411f800c58010021107000e944078404501c180c011480e0195111002c1c9215403170903082000c66800b91140d00060b03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 851180386 1250 851179136 851179187
    0x9050102090306090c01020304030f08070221010b010509100c030c020a0605070201171303050c0a170711040e030f0d06170d1701050105030f0a140c040801060b13210501020a 76
    0xd880364211740c80e50740141c008000030000701d0200e9901a5020b405142410324044c084e5001480d801d0010031480349041100c50002c1001500380305803105203400f802c1c034500d0130055200180241040c440d03180180705443c460042498892488440000d601500f081c401503110382c0090015081268201c2c0003840640b5110b40e003400106499014070025940d0304601080ca9406850360b4004281d201d402e0b10495410b040400c5005501100c1048040c4a2607038500641c244910001465116039011380e0071b200d250b100075400002112112100d9452481d210304a0b05203050240459501138811248604201c000010002c41c00802c01d40c6951960304042d02d02403032200c0039020912541c2d000c907109000003401e141403042e900b0350040c000c0200080003040c403102c1400c140e00554103032139045e0002c1410700440009204d51400303071425510729410410345010342c0d00728104502860031004813040c3c503405554241030103403110645c81402991242d83c2c0860051002c10980000103800000651 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 851181636 1250 851180386 851180401
    0x10509220c0e1b19050a0513030308181b040e100e01062d09150806040506060a08070503030301150e06040e0a0c0e01050d0c022112090601050a1205010f09050102090306 74
    0x100e4550800a8035030134a031085201c02654103400010b0102d0902c03504214115007403003110000d0713016601c80c1d1581401402c1c201c030010030001105a008103e0790010311040910302c10200c00804400c001c42e00420350729550791990f400c10310305036100303014582000115240060103420a90513510214050041c02d58640b88038010305250000302200c45034540000d108203a083d40060200501c000103200405030354003c00d52400c0401c81c2c01380c074540c012006000c014038183d100e00d4010000c1400520140b0704100001e5101c0c8410b22a000040e18004002c4a40714003588030703005201d50050445842d15a602d03808006400102c805110281c0f40050810000340030b405502001c0c40103130741d001d00341840d03100e04a000b071082500c00410340c03040300d500344202c0a1840d0031074100e1810340c0c0c6580d1a0030195046981c2a0343c00f07000c04803180c20a0005024980f1042c5088040300e030b2101910050402c00d00f496801401c05035081c107030480c01d203998807051100540003003984441c00d0341242e02d80d654241 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 851182886 1250 851181636 851181691
    0x1080c01030908041202180705120601020616200d020d09150e0d14060c09040612050a1b0803131d040b0a0b0f04091118010509220c0e 59
    0xa4004000720004d0009004007801e228690394030a101508000c80701903403061001d0600700480740000040c01c0001c45032001c3c03083d0310805410450a000030601c5051000b602e024000e440a0300e0001c10510700200e0880e000404150301035001c0c2c02d42929043d40d00140c000f9147e41760041d06034049001c0000010f046041c41d00584e085034106d94844504038031250810200e2400c8a50995150220004811040d0b105000346c80c0113044e84005640e42d07420000c10300c03040e82d1259210f00010703080014410003240c00402c84c480d5007940020880b02001c0d1240c0c00d00d1141f00d890300304600511012402180c8403400c080c0b0340703060310700340c520060086800400172583c810044078000d000604140200340400019000f000540c6802003111001d80c480a01150840740c80f414103980500104520440320305010b50100860100c03000e407507446604103004039403000340117490800c88100705500c0c030341e003000d100202141c2d442e440a4280000d9945610001c10100b058516a100e000862400c1c2d06403050b50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 851184136 1250 851182886 851182901
    0xd0b01081e06010c05011514040e01050103020307050402070305132705101e0b160606120b2a070f0b07050403050c0d0204110d06091103040f02150904020d0501080c0103 74
    0x400a07400715589000044a4440289408407120742d25042203d52100c2e80800c00009000c06039542c150102404040109070f030b140600402c96a4581401800580c5001c41d040040e207805813000743e0b031010306107002c69161041802001d140b894403840414040d2081e02480c6151800c2000c90101d0440b10b0004000c81c1c030700b1b603210250324440701810800c0c02e110140210b6a81e1100c0c09240e001c036a2841701d01070b00d038015041d0408510454000c00200f20891190a004d40500d06034500d500003155541001c1c810040c10404030311010902d034001d0000340604040d5020b04e901044c9031529240d1034072031420000d4070341c1203d45005000025541f1071142c016101144d800c0070050041c000124280400d2402c4a0030a80e002a16204140340c905c1c8030900030203809801c0c000c001101d92424800364210340e44090035a007042c4c02001400086084800350b2076003180c04a641044105daa901c14108070b01c52909815049800030031541d9060020754045812141040280c40502c00100c004404443c00b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 851185386 1250 851184136 851184181
    0x906090d0b0a142a04170a050106120f1e060c0e042004090905031605070e010801090c0e09070e0c070b0906010b220801090804031a010509061c02060d0b0108 69
    0x103101c4ea201030159404601c51a8807455091078a00f94880701290b11841d642c4481e0300080e440030598004214091280ca0000c01e0042d04400742c19910b03075942c0ba0820030a2202400c0808200956042440d4101000c0d4005510010421180741d0410004d4100c1d03000080340c52042d4617101e604000c0350200482c19000604005c0c3c041e01e4181440054801041310400689562105001541c4e0100f0f1101c401c5140500810040014500e4105507000303c500580140040340d04201c01880007805a686c82d406442e174003907180c4401e40c0d90030342c900d103030207125402250904680401d004c040070340070005099441c021800c1e8503046d510010226541d000a102e007018082e000c01010084503469040b03411414404403031b480c00c1310342d20210316003036a0150900751406800005c04008005100c86400c68420b5038014542c820341c98100002c460200003800d0b980641e2000c0c82002d01d400342d82c1002d283c0385a0080c07000b40c0791101e11301e1680041907a0060140401d40c40710100340c021030410b05d001080d52a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 851186636 1250 851185386 851185411
    0x30b0907021c050c0607020c19271b031e021e07020a080f06221a072303100608090a03140910030e07060c05060a020906090d0b0a14 58
    0x842591002610b620b0103440c41000418015541d0890b8180111070044045500400c0000c190104025201c1d07035200300242c40c660300c3c0034100700039820f0016010340e65840324040c0030340d800c2200178040074200c003030132548100080c245021015905540030032120181d02044c00c803201c2004031141d049101d40f10541030700c0a40b41000d816400110b00091110a101400403000e00e0794440764149031469800c240d4105070000c40c104484800c9604004140c00503100c0350300c40c51680303500c179940004845111307041c00c4142c4000050400d40100400810a9196820588808446000b6244681090b160f01090001e41c0c507000a40c28490b241c5207028071548005400104099a400d4500240f103400341d1410b10018810446e8a44d0f41c00c0e4505055610340d280490b8650442449605142d036942020081c008001f0076200802d034001415680036008042c0182d42c5d01350322000544500a422015038000c0107540c0920401c4904924180540031aa2041c003009000c0c0d82c0359100d00c00100c42c280110b0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 851187886 1250 851186636 851186653
    0x1b04110310090f06270207080403140105071412040302070b04060201090204050703060e0c18090a15080706200109020a0b0c1902060f0315030639091002030d020415030b090702 77
    0x2c2c45c0000d4800c0343d03078a09070052070b01a01d5540c80c04a07400c2503106550a04408011a03070800b800c0c0210342d4000268949038000708110f010302006405078600b60382c5191071610004040500800094018082c038000380c40e11907a440400078064078413464200d0003242044082242da9002c0c0c01303480305070f0f40c8071080c603c4c096941100403c440c1c1c021300300300c07494001490680d124503203801e0892406045451170110300c07054040786031a8500761591014145600c14407080008a1b4000c2030b00c4440c0c4444c404503c60030300d0005040c0e01401c401c010180d031102a001d03002450f055102e00502c144000c1794283e8448001c804150400b41c05000c030b002e5004042004024036a81103003008540c0309810a981c40141189540840c0c50550112100814560085501654003209440740205020421002d00c0c58180340450902a0f0041c101844c1c0640c003080c022200840c003c1c81581c648048201d0300715101d43c0e989000460030200e00f80e102001c2890300c02c1200150611407032861040f0465001480c2c07c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 851189136 1250 851187886 851187929
    0x70914071e0c08030a0b2d060a021f0c0f0302040b0a0e010c1401231608040c03081210080a031d06040905090f1c021b04110310090f06 59
    0x46140c14001c00c00c0080203140100002c582e4005140a5212408002001072544e02442456a0054004041130804e0701e04028207140c000071900c135142e800e07142c603600c0e1000c180e0203910b0000c003d00b00540000d1420031003811300641c0e9000d03070311107102036640900c14a41860300752304078030403402000000c6134100405800b090117101d40c0d01d44482c042c50810568500ba071a01041c003035070b0503662815a5120080c00c03801d0300c050b01c1a402c0c100c0c44884140468140700c0082024a0300315603445041c0000400040c040c02001c29600008540022207250b8070b0f0091004440c09240817207645c030011491000c045401403000540b28072560381a11030594425104582340da810305400f99469108200b0400859903031b0b501e001d40e40c02803415400401010400000700e6082001360105040244900c0300ca4040643d400161003101030b070080300080c0e0a800c08408280030b0b01192030342ea440e0003400814803c25803030440c1620101d4000100400045094400800c280c8030720340300d9283e400640c00c0c0f644024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 851190386 1250 851189136 851189177
    0x7090e07051615020a1d0406141017040b04022b14031605010608121603030e0111180a0603150b16020405040c060e0f0604030f03020f070807091407 65
    0xa42d80180d40b905403c0d551080950141d074040355281000810218081c0e45505560710b403400529003c0307a0910242d4100740c0f8003001d1a50740c0f61024458031a12018010150040080648000c142c5500c842c0074030302401c00310310441040d681240260612a80f5080340c03101c02d41041840303841c808120020111940f148241d030300e680c0341c00305c0300c501007000400d07201496205400d41781485140049074a40c0344c8080d9078200100c01c80d00240e045005c00600349030140540c8c015141d550f00d400c00041c10710400e94010b0040048070642d682c150400202520020340c02c1c00c004059071011600841c00b244c80c0d0700101e00b0b44001016203000e808101e402442150b801c0c00107884030748038a800c102014241034000bd400c3c0c580548007601c40545114003030007555031044900da4610b909944110041120a0100e68244030703d12024001c81c0c0003020340002c051081c48111500780160040380c07000c0b03844c1c02d801c5d40c84281901c2100310301890808184c0318262164200b0f031183d07007107071074042d040415070714440070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 851191636 1250 851190386 851190427
    0x60e01030f11090c0f0a020106080613051c020a030c03050708070b06030d0f08150d080708030619050a0b030705070b09010501090c0c0b06010f0908010c1806020c090402040b030f0604060507090e0705 87
    0x1f99501ca400c08500f02608124651041034400303076040e080445424204c2c07d003100304007035680e500030003994034000320b0f000031750020b48a5140c07a05111110840c142240c0304c1c000c4140050080d04005122030520075032020f1640144001ca041c1d81d035400c4048000da031074200c10002c0c0c07004984010700003449407800240a000711940542071010901c829601c500c0c182d4040d900c110703440c0b4800701c103010450504103230030117036064440340080c1c2e0b4605200c001804980320f03104801c1d084000100041516200e2803d03a01080d51040e00200d460806000341e030301a10007405091052403400107042e4090f0722807501d4401458008445180306c0c1c44160045903110b4184d121321003800841ea2000034260030034440d000e01c000c00341d99005003482030801c0000841700180c0c8901c045500000b00f8140c265280d420464001b58112000038006145401003810070480c103c403942c075800765008100600089400c21440794030b95542d4844d2164030340c694100c000006482d201d000401c00c1c4210401c0b071504022805 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 851192886 1250 851191636 851191657
    0x2130302060a050d0f02040305070b0c100f0e0a060b280e130507030f030e0d05030d090203190602040314070303050a030906090b041a090c010c15060e01030f11090c0f 73
    0x2d00c1c06168840d00d605942145d12804041a400a010806e02c0810301c904000340c03811403105031030118403050b410b85d603064103120f17402d005640c0e9000e55a40d9035540d10040c1003e03000130940304012034a081400c01054969403060041105e0900e04070307140c03090a6180341002914014800345414150f409149000003041c9441e02c003090060407000c20000c012504c021132240c0444618120607140083c22064020074a9000d400c41400c040e0000310b0200c20f81d04441514480020080c1180c00020305e4590510140407034040003503441d4082c0030158000300250f80c000c05202103c540702000b40c42d9101030700d22000d80012424070038a20103900c250400004180140c50201c0c8280031905c90a80b070890075030301102c01340031241c18810281010614240d020100300040d000d101410302c0041d08030303000c12000400140d40f103000d50402c170085a1112001d404007840c6181c540d0f07100d1420003450910f010007690345404e0206d000800f413800540c0c4c2d81c8101503040599003089210b26800340c140d008919240d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 851194136 1250 851192886 851192897
    0xf160c080f1b030a090b03040206190e101710050306041b03150c0e010201090c17030d021815090303070609050f060910061208162f100302130302060a 66
    0x12403501641c1144100b59010704051540d4566454020306060001e91084241010074401c000150740d0303240c2940c05e5400c5400d41040d05001880741280d11510300052203030310480c400c03201020030368000b0112304d01400d24112080d50307488109c00d05041d000340e44140390380760780184001400258043e91446201d40a511421030080e00c0c0d65650004060844680352445d0381c460402c250315038890111509590f00380020080c0441c80d0f01c2d9412040703103500901850720074412000081c05020012280c080d50301920031034448110945138205645015442803090007554180000d29078100100c80003000020025890140c00c3c0d6503503005002043c40c140d506e4000d00140c0c510f40201440000c5c4650004070280410344000c041c014111003890300300340c031280300b40307408480064801c2e0110360f02c1d055144001e80e8407103c40d291031450700d08542c0754881d080104680c84142541072461100c01c0ba4022103e100804a0700b0004800306c1c0034242d500e54281d07010399820030242c20302000400020407140f408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 851195386 1250 851194136 851194147
    0x21801110a1218092c06040809010512090a17030702031912090c0618030b0f090c0307080a050706080c07060c030e150105130209090c131505030f160c080f 68
    0x743c12090040d80f00c22184da40f5011420081445d0a84000450204001440380c4c101c2d45010240d43c0c10008100a200c1c2900007403501444c0e01a505841903a10116099092031034002e403ca070326021010011101150f49100ca480606581030541e4411501c690003181020740707607003460340c1c0308803060007040520412002e44000514a0b0003482c40f07490007607040426603450442c0040014002c1140201115800030062000480c04040c1c40d8003c44407091001c2c0c2c503291a800c95051043d060802645445403010000b0300900104641854a0050701501e803440c0c0d441105403040b0004441140c80c039101080b2220004c1c200340d0100c1409003140c03400241d41c01810420914280480240d0840da201c1d43c0f0041002d884d04040d0401c00b443c40800035401c041080c0041007001d08041c1c4200a8107501045100c044444800400001d0801000300d004160105201a00ca80e2007605c039481c00804c1800014140d211030b1040200c8120741e0341d142c201480700b80d2600a030039080300d101c0000c3c0402c100b20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 851196636 1250 851195386 851195417
    0x140a090c090c030e0c0102010b0604050420070b0f0c04050d02060c011e09020a091103070804060b04140a2306100905130b0907020606060d09050a0b0a021801110a12 72
    0x104001c690283e100080c1840700c0d0820149010010070702c0604582c148040c03c0c0081d100d01080c2c1d0100c1d041640e010405005100b009611400c09140107420315401007208001c2c0030780c46850a00401401c4640c844c1a10341c1e60b20f070300c05486107000e00d50700441c1445003c1b0050801d47c0080c00140d0741e050000030030090005030b603500460601484e0360550b41ba000d40301e05602d040304109009000040c0c080012012892788840f09010080209007402014800581448203580041540c40001841082919040f6101c40742d030900a40744240000e00e0f1551a290707100540070440c4240480303c58502c4265680803c00c40c00c480c074903001404106941e0710014003621200a0708034036018101d004a15403580c0e0342802400e01c0b0081220045501100030310071940c4800f82143c04015400a01081c0400d0604000e071500401000042c088030016042140d12215030307000d007041014005811180702c085100440d6600158021050a90400c40102d40010f14580323450b001603101e17052034503503110301d0103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 851197886 1250 851196636 851196641
    0x30b150c03090d05160506041410141215030625090e101a04150c0206040b03100f0902090306061c05030a020d0816020d0e0103110706060f05010201140a090c09 70
    0x1c40131141644103403900c0d035400604038460006840150703801c034186403402400070a8641c00c40d5000e03000d500250b6010f036900d8410b40c5006c090b07030b41c060805c03036841d00f0507a81038842c08011070f1201d41170103030b03120b00500d10b15010600c00c4c042c0040900141d10120500060308082246103d007809021280800048045800d600c50344500040e8a02e220b4880c81e01c03607455640c0380d00c00f040d0190b08100308824031030380414002c0307998480b020f45403c203141c0c000352021803ca4803958000038a4402c3c04410020a05c0e04911042d0569207a5200740b141d0713665039016242603001d0711000ba54550011400511142400b503541000c0300e0a41d550841d07400701c0c0b0340b02c82e030466009004c5000140c02c00b44200c014580c014200d1608031002452111000e14005d900070748440e00080c128041141e00000e01030960300c25003000d007826186c490341d103035141c2041c913044000b060705100d40424142003000006207036006103d0f500c1039508054940e41c056907400c0116005100c0518102e600805203040810355040c1032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 851199136 1250 851197886 851197909
    0x703020312220602041a0408070b090a031a07110c1509031518060f0c09040f0f0c020f28021c0609060b1f02120904020f12070f030b150c0309 62
    0x2c0f200141c5d0745003800d046200c04000d03070a040150722410001006540c20014051040321108a0754985840c0c848d0005140a00c1d82d50007d40442e83c0054100607010508660718040c90190301c540c102104014001d0b03071144400410982e101284010f0880306440640c01004005030060036618503903090b080ca10022003040d2460a02c4044c01010394910036000c012580d00203511991141c8640780100f8521242d10070440c00c1d5000e96110f800d034903151409600105d0209603400001d0000c45681a8004d54512446c813611005100340719202e030400002640060b40c441e480034445403641d4890702408122040d501066211851490304080401c11358840c01c200d09210345d10100712107904078200101c09588130400c15554400c5080c180e01c25400080c500101c3d81007600084e00c03400d4000c0050001d00580741851705a9100142e6030410f450010109403142c84a80c865103150300c00060200c0440f030112901c260031100710502441c4402400001d4658103210104030307850900f1071030110b040110038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 851200386 1250 851199136 851199143
    0xc091a0f0a08180105040b060402090607020301110d0f0203100303031d0102030a0b040e0d0206041e0803040f0c211704051207080f0a1e0206130b0d050c070302031222 73
    0x118424405107008060058590700ca00030f0082c412802c040e01c0d001401030014203500d01c01c580c000744201d510380701d11050305d104030b8004000b003241c0c4100c10000e074482c1d1300c50b0101c0c01034280781c09591030680410740b00748c0e80211800c1e0090381100d42503a9040e0f000b000c00c0c200d00003041444900e05007451000340000c51240740c4000001c01c50f0b001081c10310043d00c3c0b04607013441c00741e004511a080156400110268042e4101c82c0c4552507040d0b8000c640398046803028042c0c01c1007000000c0000744074400ea10050b41510510302013807881e40d181c10805594280e446c40520100031103040c1e60215a2072101c019462800701c94640c6882c1e5141e000400c110b40062440c0d400d5004003508021600c0e0a10400c100b124104c805007a881120340d41d20030000c2002d50b5010362080b006d06414041d91203103429510420702001082e44039030380752030708400c13140c100d04a104045424180056104140002950940c0394190015400d16262210b145200000180103503c500c014107481d9424256052140440742d01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 851201636 1250 851200386 851200397
    0xc0e01060c060b0d02060d0911060412021f020d182c07230d020903011508010501060f0801260111091c0b19020c07031a09010c091a0f0a 60
    0x55450514143d404540c070070ba10652032a2062000751300c9030307421200c0d81042c0c45000510303d941450b00a403221032482e0659040ba07404a40030565000100200c800d0034001c5910031001c240c41c14601880c1d030b00789a10a401a00011a8101428011200040f5451500303581e185025103d407036690f400c802c00c0750340003829480350101100340d0740b42010282d08044113290040900c1c852841200b1388100800c001d02a0542c0041c5da181c921000d030f41541d03503c0310000c00a01208006240a001c2d0107054001c100d6103510305400081c10b0750068410f09081c0c4e08586420203142e01c0c061540405c1601144a016180448111981c03514401e11448096408d00d0503e15203a0900c5401c2c807040d810001d442c02c04000200b0725120108102c3e00307055034001c8107a2503041020041c0d4040e500a0302403c401c202d0f01c0d10984601100300011040030740d910381ca002c500041290748181d0b82d142650303000f40b030b084042040710b203040c081011030310107410600c1d20f0728005a285c809046070b030004540c40f6501f8840000c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 851202886 1250 851201636 851201657
    0xc0501090308010320090c1305060304030302194404050303070f03052712130e0a140a050621030406030c0f050f03040f051f05070f09030b040c0e0106 66
    0x100740d600800b2071798140f807100c2d503108030100200b200100041c004c60b202c0798000c9442c4505803608a1500f02030440a05405c1c2c890034a403401038041d400900b4422108804e032519034000a21030030000780c01110109901c00c4036040610f00311450b02c00401c1c0307541030206807110b4980c2610008a01390003680300720010369507031800b108020200c2000c411070340205070800051011203003015282c000c1e6142c00304d806100d10801020214034141d200160100d90b1f080c0451581c5090035610108012140ca042140d1126500d0901c01c1e41121110000c10b481090044081b4104041030761000754490000780c407215052a0b83d45c5c4ca02e15224440d038203001c06910010741400401da260003102000d20b45401c00c1410101c0125020300f89009101d000000c0010100016013030000104034034004036004000d5131b0240070400006a049040040f050140b641003c001c580c1140c810076009a18120b20350710302014a0039540d860182c480040e00c01d60f1030f600c415801188482d131001341d09009140c070707445010314807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 851204136 1250 851202886 851202893
    0x403020d1505060f03031b1903030f0f020724020421020a0b090a0306020a030609020d0c1701080d12240602060604090305030609090106030510140105030703031e0c05010903080103 79
    0x842d002085a0b00640b0300c160034001c5034500005544801844c40a0069102d0b480380700c103840c10a1100c1a448400c000300c0090083c1601a404180102d00d601010f02c883c0b01e8045c600e2013a8400c0041c001e2030300e405080ca001c0314225508004054a45005015141c40d41e646146007c0188070b06c0508516440661400d0071464001e0400b0010840c1b01102410842d1100c0041c5440119100c080c22036500055071200705442540107001070040c20310210b403180350800f0b0041c01040201022008545003036814410f00300361508150480302100300620700b003c18024122020402d000301c1a56982c1c0790080e44034480701500c8109101c2d40010711401ca6140307000002803600c41d0203014140281c0c54820703c0c1010940c014116680f003241550b424405449040005006184941c0080d00c1ca014690500c1016805900280104800c58106c01c0c0540d0300c500406072141c0c0c0b90310000300400d012400480b41d00b68058000546584030342016846090907486d01c5080d51082c90040700094440b60051040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 851205386 1250 851204136 851204141
    0x60c03090324060f03050316110904140c090405030d02221203120209090a09030c050105010801050709050f03031602130e100c081006120905030c0303060307051c03030504080403020d15 81
    0x14031388002992003561444e02c4a0b51213100f0544003000c0e0380c5501c012901846160703000414020b4010345110424503050424255240d031100d62a0072900071040060018548070b40710a00854008000d50714149414103a80000d5220b201014101281d00004800307588a001403107000302a101214100e541040c64014620841c0c01250821588188140040c645848944030760064841d4400580c2e030b0200e0405560081d203902c4024507075805c09001184410064001ca40101d2050300c88040d21a221410071001d541c100501c660180c0c02031090100140704c050140780340c140082d0001d41101c81045018059440317500150b180c0c1e42c080c00d03110004104a1007800100c494030325202c0d40750304081c40d01c2e0783c08420300e220303490802c80b0000740c842c900d511541c8101d4405e030b0710500b00d82d9180b03c04908242c03030790400c842c024424064034a001650307050443d00d200103881204100800e09025940507002800083c10580356020f00307210200c01601d030a8441c51400f030080700c101c0d003000350000c000d205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 851206636 1250 851205386 851205389
    0x7150305090d051801090e04060b1009050d33020c0c01030905060613020f12090609010507090b0c01060b04030308060f0618040e030d060303080106080f010609060c0309032406 77
    0x1c15a20601d41c60007690b80c80401d454403407425054090300c03101d420004a44800c400c1d004141c2c500110420b010411a066010300d40c414400e865090f03911010a10a50307480b0003030710505030000b41080042d000208021440da10100203141c0300000c0e081c0301034030105900c04c00140384010950000307038043d6010081055488a40092078180705c03010039680d071a9240c200240c240780c080d000e0084564190b484640686d113544120380606030301d03040803500c80f544940c402d40e20b90210b0300400000c14480c000c180299071090300e2a0f01d03000e50740c5143c10300d5403140e54044c0006007425541d8074808a60030141000a00085010341d031003402c94184030040006440c0710071a5640b00d200704001129000d8100c440107a440c0314111000110456a0035400c0d0031485140500c09080b0f2608038040109608128051f050303c0c495500c03501a5641c094440c10414801c0c040c003804240c007958108415480782d5101510b02d442890000ca6040e0b50796a0303060030340c040031246111102001c4031481d0240301c51007400c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 851207886 1250 851206636 851206651
    0x5101b050f0303010f120f060e0111030c072a06080c1c0e010506030a0308060402130e0115020f030304050c060c011401290304020f01051b0628090c0e1807150305 71
    0x5040d1401c694a800042c400e4071002230082e629200030540101082d801031808400c0c05c003059540746050320000300f05501000e0225842c0450b01264000e2048408441c0700d19a04941c010804500340181039401c440020000d0101c04000c11401d8003188001d1610b0004540c0e030036000c079204105044c902e0944a009010314065841804111b001c06c0d0b0151059402043c10794005a03202038070046060340340a103400c4000086000c02c00094402031101d030201c02c100e40c0e40d0030740ea451008441500c1d22480181e030042c2650380010f150342e0452070200300034490090580000903050501c0551210b080409a0101001032a0310700360326010740c0ca5102c0054242034982c0004e2039440c05038000380d40c1c0b0a44100aa04208010440e504c101c0040e00440d0110511207046400f546041e1041251044c51202d00740700c030350314281c1032003d48a12402440c4003d5400116501d54a0500c58181e9240070000c04403c030341e001c12b1494840103a014011040038151700e60203800001050107020701034035800740049 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 851209136 1250 851207886 851207909
    0x807081b01020d050f0f010e0604090204020408030a020613170d09140f0c0406030317040c03020901141807050306010f05041d0412080c1b01140c130f05101b050f0303010f 75
    0x3c03000106c0d005500f81036500b0822080056141c0c507000c1802810301c0c600c02900f051001401054504001015190b85000c0398210b42c1541d448600e200b4080e81d400800411519041d070580035503d0420b8058440181c0c980d0b0300244811190325030810324880b20100402c550807400300d034620140284003e404d040401d4905201052843d0750040158040e84900503072001c891000c5405c2004111231070b80216001408000f04e56124002142422900c010082c818074403060704011a100410ba0944a0314040d15414115a00c550040d9105414400c010b0100a01044041041183c03451401c24030125070400121514041c580002c0d00282d4450031024040c000d0700b004045e0380e1050458070352a4180022100701003107424036a0140040c40d500ca0203030003d2104110b403409000b0041e0000c4102c943d1100207850f9a8540342003560014082c2c203810480f030510820b07910303000c2c0c1c810002c040308010303554400d44041c0e140d9506203050002c0403c04d81d00004010401280c246406502030841200c6e170 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 851210386 1250 851209136 851209141
    0x5041202071a070308090c1801060e1807030213080607090314010203060a0b070c240e010c02130e0f0304140306100620032703070914040807081b01020d050f 69
    0xd40c070341e5025043c8010304002c84100010065041130004841c80c1e2000313814130980b99503440d80000c42030000d01a070030000b41059050403003840d0060015041c0c4c406807401c204543c5401c001103029501c60107629128000b040e0b070008888500b0807049208101e5941c0c0c83d020740f401d500e4800d06122550200010503801802480840c1e641c4040c4a8100c805201e0040ea032401c9515004544038216403140f0310300b180c4118000e0701c0040c02a0030940388001e0741c0d074072001c00d003814005480d00618803c029401211a0608a240c6003196206000c40196038007280d10f4840c1501c501881d50748140c00c90402101d1301114a501070408000d016000588a543c8203e802d00b020720041c0565415071454220900d202260305200d130092045849907007684181c87d0200700198141d20611a03a411154040e10510b500014480403522030401e545900840081c1d5503141d644800781c09030011141600c9000c2304000041c0c16104103141000680c00d01c3d800941c68881200d036080c101c2d40e0081c000400708052408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851211636 1250 851210386 851210429
    0x617010e0a050402031c0c030801120b0f060103090b0115090b03243607050c030403110312041202040506012109050f1207110d0c150e040504120207 65
    0x18001e80c0201e10700d000003902d90740c9000003890070036650381c07010303080007440720b0300d40115405144413080d18001e817140141e42c0d0382c500c100c41c480c00044002400e040764a40c00f15182c1c1c56002502c0703800c04c81c140360200d4035000d1600c03114500b86007030307010f840142035805c229211a90080d110400501821380d006045150450000c3e4a022070a210300c40e00321f0f0304400040300d0b9900e404882c1d2440302c1208001c2061070120b200c145c800101c0080003010300d04624000344070907100308126000c0c425904041d504080c510f50315800d11340c000c4036480b41e050042c2903440104c40400c00c0035100030603ca0624000000d4540180400c54ac0050100c5041085d81071080485d40c40d8002404140c1c0138a440c0000c200b40541400e0742091021152021540280d040b0340b54180c040b034002d07159141c0906042c2925015003010000300d000003860007020600136079020040040505c1c0d013602418407901304010302d082150300203011500c080300c0403100c50344200203d151969041040c0340c0500214007600012401050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 851212886 1250 851211636 851211659
    0x1150f0603020a05040f030b09010f0c0f0809070e0903030a0c030c0c020d020f09090f0c03010614010c050304050307151d2407141e060103170a0225061701 68
    0x14040a0640005240c4522803058003101d00400346400f107446c001d0744915240042080c01c9c1c0f00b00c003056080080343c11f4580b16512a19a0821198507115000002180240c0700c0440c010300054041c01007580015000b021218454441c0300c00d5001f865491400e07c884400702d50484403010101840c08440e200166088010680d0998040742c60382c6d40d10200348001120790380a0213580341c001410600744103e450700060b541c8484007150065548603036041c03041c076003210070350700c50b428413814405084000365000d06041400d280c02001924070700341e00d69012902d041c1d0303140d018200c52441c0e04070013800359500c003028200409424081c2e8155104910000d8074050403546481070394040960514144160035080b245460350101180549a010082e22511041396215400d00700b18200144202e0840101c5c490b81038903805005610341c03022040307946105400c407010200640c46040c0614551020b1040804c4400205900049607941010781c02440f8104803030f94480044140c00c0140811940308 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 851214136 1250 851212886 851212889
    0xf0f031101030209031e060a060506120c0c160303080a29120c0d0804051008040f060b18090105040507080c01120b0103150b09030606100206060f1f05090301150f 71
    0x2460050b0702e582e1319400182c10140c070143c000c400d4600050040300244008903016124448603e0100421503a55003402003501c10003151003501c00080000424041c80000a480d515850804031000c0314006180501030407031540040c0c0104002108215151100b03000d884085684408080103021001c03000c00786421411401c14441e0301e00c440006a03002d0100814400c543c4000d099400d81d070307400d043c03420103a401406601e020301142d5800594050241c1a03c034011b9a002404d010220351710f8a072400180f461076245030b441844086200e0340c1d080e0f032441c040d001b5400e0100004490400d40b4165203052280ea00c21800c03900300030760090a503070304400b100f080403915000c04500341e114200100c004101031201d1000300d100802d00403070364004640c0503120801c010340844038252682010041c6000c164402140140c0c00b43d000252241050344e140003800c00e0240c14456218821030000f120100601007038800140d000c901c0601e1440c0c00d000f141c070300442007507800c6d00c074174102040b811906446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 851215386 1250 851214136 851214139
    0x4060b0a120210180905090c010c0308040b09030d0f0b0f011103120c04080109030c120215040f03112a060901141e2b060b0a0f120906060f0f0311 64
    0x21403811582d1402040c452501d01204c030f00d1481850b0300ca100c9000140419900c4170814803c2000081c1c40d54002c42c004840140c054440615641d80c030381d078480310004000c02122241c0000e000742e00d520070941c001c560125180d042c005c2581d0064009000d558294130f40101e0400c246154030003801ca502201f1140c9001e04641c444d141540c1e2440e40e4400d034466a07005404c4c3e586070550920030305500403034000c800c80c41100540702001c52420201c0c0d070f5003c140d60701c8442c0d2603820040303800100c00c00d40f46000c1a100742405041200540c84090400300d00d24100708010f141031540035400548540369010406040319014140801c0da00020864103283c0503426541d040012084148001d4044440000c100c481031242da5501c040456032110001a0701d0685500c0d2042d0428a565085e02030b1030305031800e11700a107050012140342101c4c6e2140d00c0400300e06002d01c041e1741800041d446d0041c14246401000013060043c83d100c206014894540d102c041134903a550b10500000e40341103500e90360b0310320 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 851216636 1250 851215386 851215399
    0x6020f120a0c09120c080d050c15010b0901270e061005070512031012061b05091f0c0602070602090109080a150c090e0717100e0f0a0b0a0b0304060b0a1202 68
    0xe03480d10f800040c459401c10300d44c5121f0414280041903024004140605201040d03890090440410300c101000a002d60028010240040401035100d41c5203040b400d210190300d02400c0c00d0003000754400300d1658029a451140150403c070103410880045003800040d8542240790104130340350280c6550110b2207407200305400201241e01c980042d82420003030038001a0f40c200418082c60404020a00d0038211014240d0214034022500e00500a85201c217402410008a00c40c03650030200000e280c0e802d205090261100b00c100200303807a0701c064070160344219001a5a00e441c2c01c009441c583c8103500100311640200841000a04540101c803100070231000c0c0818020000e040980c0c00041c1900484200c101e60300801040d10340c041a641c4032058402c014040d262910440d40e044e2080e140501000160017002141c1102018100c2d035601c41d1055030000340c4c00010500092079000154000a003070040407081c4400d000803071140e19010942260411003480ca00b030703500c5180c1080d04d48040c0c4210b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 851217886 1250 851216636 851216669
    0xd0e06040504021e0c1c0801050d020121230c1c020703050702060a050d24170c03120307020615151e04060309290f0c0706020f120a0c09 60
    0x24500030313032518410b007100c4130794840030f01c120019510280d0011076064032440726143c212041c01260428140c1d01e019042c1c2400c1c0710307a50010764044144500003881801d8000030783c408140e2900c44e000080c4c074603600b92500004440f860034000b41c0040c4c01010300f004c04110380c0e80300d800c84010111805442400c09604d6002078107007501c1c14005c225019402401c00030300440a1680140203000c01513540c10b0401005c14403469032581d91100c08614802000fc00700280440010001c800b0903040d21602120481c5503140301007070030590411311142d800b01d0f0220901484540510080d507010320f402485030460329200000500794400d00741106644000020000c410100a400c042c0d0150410000d487d030710f43d41d50300010003c04d1858815116140d685a180040060800003040440070414110507a500c8103541003110b002d01511090650608000141c002034141c00588a070707145401e501510303100b1001800e60f01540c004c1694091a2404002c2c21302a50031010038010744035400303005440705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 851219136 1250 851217886 851217907
    0x20d03020a020d0c0302120706140919090c0210090818040f0509101a0f0415120c06030c170a0b0109030503070b01150c030806060f070b0f06030d0e0604050402 70
    0x7011030180d00004801c0909060203d920300200403a807096443e401880c141405003520340505000705400502d60f44a03400048240e140500307550351b0f00030311310410480c40c0a200d4141855540c40318130650f85030ba04021250740c050005030082a040301c000e20518225a607103003141c2c8500c2a41021100655090700c107a6200e43d40312007808d082c028420007035814600c8085581c0d25403085003444240c20014110601c40e01c90f405240808000752050801ca110481000702170103524140480707201118000064180c441c580c03e0010358000e208040e0047d04001000b0180c130a80d07208070301401015070f04000c51801004071954003d004c2c0c00001603000c2c540004903081d45840c0d0024010f4840805c501d000d0201c25071456040f0340740c900d6290f074205925442030760b000e1715182018005c54410740000e0355a042c41d100400280000450640c82c2452b181d440354030ba210181c03001d64401c4000000c1240504042154a204a02508082000041410010740c0b10b1140e4050a4002e5401007010442c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 851220386 1250 851219136 851219143
    0x21030118020f0a0c050610060801090f1b051206310f0603060b0a0e0103021c0f140a021203031b1e0a1d04050105010f0302031f0b040801060b0313020d0302 68
    0x820031902c4000340c0c1d5056804009000202800003078880380984404a00003411030060f0b40d044600580f0303000e0280c0e281003541c00051081c0c0910501042c2c44181c00f03003c01c000d10b015000c14004c991152601c915030851140041da03030003003103640102c000c1001090781c841008050088459401e0741da152481e01000f46001528118048900c83c906248007c4200001608200510350090b2142103980780c3d265584229050203110103500314050050301020201c3c0384910f0400b0340d0044241e20299502036403840f01a4148080c1c40007582c0141e40440300310716043c01c50381c42d10070300c2d40c0c011400d604119206a409046800c814030b0820b00005d5007660501c0500c0525079510303401a03142c1e4890078450809040741030f111151104e4511000c1c28080e0a141c42e124090599006039191201c045100505900950016050b00e0307002e000400c40710181c10f500420403010b8203030510402d44031484d243c1e0315820341300b0b950414400c1c0c10051040003864021580d00766100c40d0121522802044541400d81c00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 851221636 1250 851220386 851220397
    0xc0c0b1005090709030302330705160b04060506090402090a0c180308040f0b16120c0c2714070c0804091a12210c0c0414092103011802 59
    0x800056440c00c108120b44c0000e0544101c074000c1e025034203880700e40c0d05c00b0444280803000e81d03e0310380c1f42c00c140140d0404c0681d1042c0c1d072000541c00d20a10b000030251105000340501c07a4100c43c50000f030001c002c200495405242e070440d90664074026181000d5000420701e10f40148440303045565a100c540b829841a603190010555806050324411f4a0f4240b00405074018060403440d50720100c00000c5198928040762074284440a40780c541d808103583c2d00c0c0c40c12a4140ca41c0c1c0422a116000102107200544020002e1141d03902c00d411003461208000642c4020078070814005281802ca440c049100600150b030055203490300420145051510350858000c1e50000700c007403481d100340d40f07120488802034464414012258194461340c4003000e03c1c1c1c1c4403609900001d0344080b100e4400340350b250060141c8100d00d01001038402010407080482c0c00c4a4040e8414040098580203202580100b1300c01105800c210000c11455107510030080d0b00244410700c10700070302c0c0411407142c4c00102200e41c140e84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 851222886 1250 851221636 851221639
    0x40b0f130e0c120d1119080a0c151b09030519020301090515011d16030902150d060e0a1b12090606061736030702061c050601030c0c0b1005 61
    0xa0040004800f90b90340310084942e06010440c6034039014110840000c0c0765000c03c15120034402040c2c49a51041d1842d00202205030a00c10901c0c003142c0000c0c605101c0c0c4084040d011800240d14510362002054094507496031824800386641c01c0c80070071004500c101004030b0303104e20601070600c14804a03005200600300685640558a40c191203601814541412500825500c030195121031021a50503a42501c80000e50780a9218402100e4080d421200106000600380c20310845400708c10129a40b0036002907a0b590307030316502031100550049001ea00001503400402c03101c0c0c1141e19103c01804040c12400500034034452040503003120760040c103a0282d1040090200640d1404090b00d10100154548152845080026400719060321104051407070312040d10004e10780806240310700d0941c222200640d003c20842c000c00340c2c5880b00100407000b94035501e2440303450104031030070880303002030181410541807114404031103601141c54012035400007039064070b0713450349581d082c0307180c0c45517002d103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 851224136 1250 851222886 851222899
    0x306150f07060b030c0927010501060e1318020120070306020d0b011106060105090a1a03072d050c0c152109071a12040809040b0f130e0c 60
    0x10980c0060000d0301c1d6452240340148022002c0b02c003019100c0300c1a100c2950801c4441e80051060424040c10701d4030401c2410004450b00741d5908040d003943d000741c00c00404a01038682c00d030494109100e140400104140d003c1240d501d45a24401c0c3c8003020560280c100003400100b56104101030f0307030700920b21101004650009540b4501940a0b402c900f40683c611403401c0700340440c0394010fa100c402210907800103081c4958521006650350340081c914941c2041c0344040100d288050040000c0000c101600c1c4561207240c0828020210881d642c05094555040c0044003260b1052004a481c09121414001c0e01c1b20b44d1125228940781e65640841e92103c2c1028050a4140b8a070009182c0310b8601c1000440714482141340740c21030f4100703441080301c540c015242001205c0c848040203040700c4544180e54680302c01020403071048042594182c4203002e00252808041c03030644950071520500760b5601d099203060000080c030b0045000105440292140046580345005200501c28003034014120b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 851225386 1250 851224136 851224147
    0x50f0a0207050f040b130e03160b0103140f0309060a03110a0324050307030f0302010905243103052502030c0a0e0403030209010215070206040515060a0308030615 71
    0xd60720452403003024000c5599203c64119030030640290000500080c203c9414012401000d40041511101030302d054082404a1442200c5200d040c43e911400740d0038801c1a9415070403d404c030404001340303449165019201a2101c10300c003000356460420101c582c50344500701000e050b13000e04001e440c00700350034200107a0240b415425a0001c6c0c080c6503e5500703407400b69020070b41c06003018064091154140d000b22000c00021310411a20141a486880003185521095561914141181142005100407400349410600c0c24601c0190700c01408580101c04214a05018004042c283e050140001d6464444028503003e0000c80d5035510070102480c4c0103900141c1d081e00400c00801080740b1900030725240714183c2c50702202c00801e807004106e242d01c40f41c460b560290029400b444025040d03000b00903400f42c560481c2d240043c442d40098001c0d003070030300e0540750403030910200c0700e81270f034030b454521041c020580c59800304034007034a501401c2c1d0350380d0303446400000709c21007500c005445401c90001903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 851226636 1250 851225386 851225407
    0x3060109030611070b0a1d24100e070915031416110316020f0d03050f1e03180d09081903050c0109050c1201180b0c0903061017070e0a020901050f 64
    0x8a504106010f2001f824101480c001071600c0e00300c851801e01c1402440d0a140440710481c0c410300d6040060034000c1c5455903030703c0c445440074020850b907000106861300410000e03046c190030101c1040031540740400c00b24103110303006840d00c20060200c1080c004290f0505480034056031048690b120820200d03502c40c20401c4403c00310324950302089008da0b07a0f0342c1c0784030340c80c2c00c2c1500145259945500d541d400c00082e849180c0d450b412500c84034403900c220012130600900110002c40c0070b031404000401500407400c403003030f14007100d5440c804104070316a58100113404c0302017504018040e000f02c20800f854847c3c28211858090706134500500e510b0101030394104400010702c50080350301034070740000b01403031050645c1c00c03508003520050071101c3e104100030006804140503a0712100f100391081c101180b210129103010030851b080500c0e0350400740184450184202c052035545904001130112508181c844514a10b000d0100b0850503004a4800b000b0b0b80260240c40c1c80041e004003aa4035501d001c0f6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 851227886 1250 851226636 851226641
    0xe040e07140a0305060606130e0c0711060c0703060203060a09050906010303020d110c1c120305010f09110906032502150f0c0901081f0905060907030203060109030611070b0a 76
    0x1007108022034855558040e0350400d0303000d450480b50480003410050341c0b400d00340086540700c000340d000a450164000300c0d0140c8a100e5a600401710760121f03a8445a0b03c0c40c0a07102c00881c207010310312030f21047c40a40300401d0000b4001d406d0703950014003da12a01d55001190180f41c0135000b03114264105010401182400686c1d40d048900036404ca60006075000004da6540d51007030541c10321740d08003518610650811110704000d128181c0f40e180c040c0f1030b15880c8c201c418140100d0100010752114010003110180400b00b01c09443c2c0001e041100c0c0904031000c5190340310310308104c1c1c001c4038040001100b80c4c0e0584440002c3c480d18440d0080282050380000f916a04503594000005034060040f6512035480c1c035072a44111118011a0b142030124001511480320040c0001c810b1003503404001c1600c1b0100031000b0080400340008600c2d81000740c00c00070310080040840c005c052040c02009020b0ba80011480100c03500710200160320a039050300c4401c6c40c4a0070001401c0f02d03903600c043c000043c2865 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 851229136 1250 851227886 851227889
    0xd02040e0f0c15030f040f1a070804120813150b030703230d050d020d060503120909150904020d0521030105030609060412030f0e010e0a020a06030e0613030e040e07 72
    0x80f00c00510890342071800021502040e640030115a030340034002000540030100200e640d50140c401c20050f45102c2441d0308074804201d91007400201c81005001c2044003511068814010a06100c2c0302440c10600d079451800d460385000e00403030800e24101601c00c810707502072004a40040c0c1070380c60642d10fa00b00000840011400d080500150031000f40b402c140200744861062a266191490401401d000c030029400000907040300c01da460000186039942003244d40104440f0140a545a2501208002c0750781c500a00a50308104c4450381d002540c0d660000070350b0312a5048800c0c0145c01401d00f81149088031851600000b45c1c012481400526030840146048a9040b0100c1c0c01640d070301d1449540b100b400365401405100d00442039081103000c0e030800001600c0a2030006848040100304600303403074180b0342140c56038011030480805d600300a0b800b48040c2c00c040c10103110351105e884000e503445000900d04a04201c0104400007054070a003942185000c0c010801d000d080c1070301c0601920b80401e03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 851230386 1250 851229136 851229139
    0x9020307030318090213030b04030e090415200a0311161506050d0b0412020c06071a061c0618080d06090b0f090406050411060307030b0a0f08030304020d02040e0f0c 72
    0x50f6080060311411030700071691200542d80038000c120345582c0c1c440c0d04d0101c02a00c11014845000c0c44000c1e152a1000700d00d1007140110a6405200c000f01031210071150585111880000e510560420120040d001c030781c0341002d00e14001a08400d000300043c12400307a155000ca110301180c01c020188802a01c2814180789618410401c095443c4100041c0d400e0500c802003c1d140014005400300c0c9080520707006d900101c0c01500c030b09008200c0050602d912000c02116000f500c0000e50701416607010a1941c000400e030355400c401224414a030000d0404154020542e9440c0e08030540c4240c0303240c42080340c1c60352001c40340341c031003100c404060301500140c0204002d10746001c11214062030040c0b800010040e0141401045454030746443c006040d00a106542040d41350310b4280c9a130312045d0096214a8440c0e070000b95503072403a010881041401e03480b081045281c80400e01007020701100300ca41055044503913103041c55403440841d002e04006c9440c00224011044000800c071000300c0c581000c040b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 851231636 1250 851230386 851230427
    0x30b1305070b0d06270902120106090905061506030f0a0612080909092a06120f180a08180409060606171b07020603040305070203060709151719090203070303 69
    0x481e412172074a40515110035540103030701d558084200e004598003514105d80040c103e0807085001106240c2503460030f5000e0001c0c0da54604413002030003810301006404c00b04e1421440c414016200c0028150300014040f401d102080e03001003403490a55038841001040044040f14001449007000c0046d0340107a89154011010302c400604107a9010510f5508002c80b0b42108028641f1501d04c0c042c90a03400780700340e4003c0010003c3d030075418042180c10740305070501d0f01e924070300e0302d090700d00c1400c518511000468a81c2c0048100313400500b0394000e030b8032046550b13410205208010360020f0060482d46801030300d442d240500204441d6800280c4481200e4908410a20b9403142012200c24152100400c101510706000c10001490032500035030300280246045801e04a0780c3d0006400c00c0d00c01e48501c2c01280602008004e004905c400341e00c3d1005250800304580703c040031450409020051106528181921100d520381d0101c0d806045150780141c101d540c116104d2802410041c40c00c2c003420020b54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 851232886 1250 851231636 851231639
    0x515010513050c0a0e03010f06030f2616060b0a03030f0f0c0f0b0702211201050906100e031e0d02010518190602070203012c0106030309030b1305070b0d06 68
    0x20340740d0050601401d015445945004070111007100d200000354403060b1702d0354031442d45103c17107041030040c00f0141d07018214201d603050292600043c1c112281e4007a500c11141400310a412224180c160303008806040350403041d11402d440c0c40b400070101480c040382d11940c08080441490f82c40f00c00303c03681c20240e440b4281c0c600c01c204070945005000c410300521080c41c1051250001d40714a05241d00070009004440b4003410070301c0c4c0301c1d2410030940f400d1b0221690103e0012007201826104a0041c00f082e2100d0541d03081c44400300b5481041044100244800690100400d0324100a00c411141004242141c80791100c950682c440d101d12005000660800d801300e141041044220b4107000b0600c0000c000c011091903190070141c1021000382d64a81c0c3c24001d61015031002c0c0034400c20b1801103400d01848611848c8461200116101c454009078504481400081c0c0c119011400b43e98001c1200f030401d648204468040c8103c19800904502034980c001410b00300010161843c1e440e90081401a00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 851234136 1250 851232886 851232919
    0xd0b13091b1a2d0406022505011b02010504090c0203030901060f052b02060f0c060f090a03110c0303160b0123040209030f0313030b01050409020906010f0c05150105 72
    0x5030745142c1c0b5a25441030800640c0c01c80105245a8070b84101c0a002510480200d0291080c00d6041396100e4005a00448203501001c0d0400394085280c41e00151010061410040003c05007203052901888400c4036a00c41d000356800303003050320300a0440108c00d0008003c0031100035142c0d00709455404081d82417450200c0d4015080800c2400e80384041c003440c0343c2c1d884080b0713950300795003d0002200340d00d4140171409015841e034000401034080d03001c041e95580c0c160301140c1c52500348010800036081b00d05a0500c41001804501c02300242d4162820320002003c42885900300012280d9072507141c4400100281c3c1194a900246c140600901081203e07a0340c0d643c03400000c1c007910107246651703e84911400001d00c3d16502600c0d00d21405000c5500c0502420343c400d03c7c2d6448100f90801c0c954910303034100200203107601103a024190560301030000d483d86a01044540e02c0c041c001c0d43c1400394000c003484105201c2c006050030182c000e400c0310240243c2d400b00e00740070301c07080c010309005030130411410303240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 851235386 1250 851234136 851234159
    0x2011110020c0c03211e0a03020304120926031c05010815040c0501140d092003070f2105030a03090b0f1302090907030c0f091d030d0b13091b 62
    0x90b48150200d240c40c14026400c10030171540503480c4021084c201e00750b030101c480e00c8040501042411031710016607908090800c103400c421038517021020081d42000c180016090107041c6099140305505441d0130402240b101e90450142c03002400f551600c000c0700c10070405460700710354100d03200c0c2000c0c0c44610b00c87c00d110b060140300841d000351400e03258400c1004254480c03182100681d00101c8028141107030f4007017104c140c400509007a100002052003120041001c406054910707802100142019485d050301c3c088080c041e44110001040f5a6030740d007112491802664150540c084240da13962404404058000d01d8014800d03a11040c0c4040082d94008610260703070f02456800b0741501d64146035508210036850002c00c05c0703203140941e000000014031410300a0000d4900500c0d680b012504ac006818103c42d0540c0c01c281c0c04000e0903040129002d404012100020400c5002041da143c164001c90091418114fc81049a141100c40c201388945000300400c5041c43d000349140840d0b607008030903072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 851236636 1250 851235386 851235403
    0xf0c12071412040e06012c010e240d02040b0720060421080c03040f0302030f121605150109150b0a020c0105030907050a06020d020111041404020702011110020c0c03 72
    0x600b02c200001c0c00707100c1c1c081c5442544408145404c03062040203403900100103a2003001254689031011403016190b030001c0700f41a40d1001681c00d1906584042c0050050551105030032000c0b400000d4201c0c15102c941c0c0499001c0d1034125044c50350342010345803140c0803100300c6101c40c48031003800105030340340e240030421281190708a017988905040d41043c414021321b04040112a42c070401c1150440c0210706001520080500413440004240795005141c00c00700d402d008401c890f0400c40000c2c9440c004142507072000d00401030003181103542894281e00d880804004501d800422100005151040707030448103a0340144620742c10340c951f69000d01d0322203000c0c21010401607005115081190b511070b0000e994024001800c961a0540c0d4401203140040c0c1c9c2d030004001a046030b00202a01a02405690410105a401545402e1500d00d041062440d107112031845690009501d400f5684510a1400320220007000e50b00c1103370417801301000a5110030803610003402404103403e0300b40b401145290 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 851237886 1250 851236636 851236663
    0x90204030c150c060f02091e01020706200a140d0c030210020f1908041b140105072108010914040b0a02091915110604030f03020f0c120714 61
    0x4281c0c0c200200451030824215020041198104142c030200b03103d4041c0c032403000e8406200580d0b40c01c1c54000d00904406003450740c0d000c0b00504a2240752640d000548001301e070317810300d49803001072801c208400b1140d14001164086202c0d220f007910038000081c0500640854000448030081c40b003000a5440c40c091640150250b00328854a50148440e50014214064003054040c0b80085900c8650848403500c031506c40010009401c000c100301c3d04010310810044440c4012455910f4a800341000341c000c8641a0304000b070125441d07041010140d520083c2018501a4000b1101c0070007005280d24004d220b8001080d0a0000d845e9106980340866801140c00c00c580008a40d210341c0440b0195215507800350300007450103044d40c440282205200c024141d40203541c0c110001840000302082c00c1a19103032600c0e040300b41400000382d005003103160101380038140541c6429650310002e419008020748003000340a0020b6013070010209400030b140c2544205040d800050032900da0303643e140e0b8912481c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 851239136 1250 851237886 851237903
    0x50f031603110f0a0b0c06060a0f1503090807050a02010f0c0b010b03180a0c061d010c0b190606051308030903030703231b1c1215080d050304060609020403 68
    0x510104040e210a00310010780030340b90f04400c1003010042100e4002c42d0340105030110f008500e461601c041401800e802c51006c403284034103281429518207080e59103105801441a58001b456242802034201c2224141c00030805034541c2544d0034420345a0300b82c0712040380020606100d82e0681c60040300c505540e0384d00700b41c841940f60f00303250051100d9800904025090000541c456547d1002003004074011031082c060000e61606e41100503148030303080c031070351641a001d95400ca0740d07a90b8081400300000750094043c003010740303034920445101d0031500c41950170700307042c80e001180c0907070880001d0405a034091500c03070307202c0d50f5007103500c2d00ca00074882c900342c4c1038108200580101c0e101e03004040ca4104811412003941003180c0301070401c0d5100c0d103000d441e40c00c05041100d02c0360300305020b4500715080442d058030000c03a44000042031107007140c080c40c803455500d21148840410014400e006003214200300ca0341300b0700e5180040e105030000c8804854103403d10790003142d0641d19000391809c07030307034004030300d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 851240386 1250 851239136 851239139
    0x213060c08040305060c2502010c0f020d061b0206060402030421110102181806090c0d0204080726010e0c04020336210f03040503041806050f0316 64
    0x3210610316000c41030300c25107010302002c40410400d200182c003411081600c2691500e4115411102c0c2941490800004e20f0303480d0701c000541d0b084a45a180107500840036044d03c509071000546002c6403070000380a9170710340218400380c1107418002c400c01030310726000c0f20060782d10303841040280c0c072081320000c015020103803010741d5008812040411400e0380782407609000c1203185600f422078100c48071490500b028004101150300b403240c0408401d110404d03040c0740d180f0b0801d01203a000007025081841c0013070009440091000b656060300d02802c1c90000fa43e4500380d44910b44030783c5901e11034040d04801c00640c403025061405105a2000142c0040a01842d240306010070000b500010010290780a407004007100054045014948107002c03185044060000c1d0504589440441c9500e120101010305140040d0801001a83c0d02c14050b800ca4940d07940d5985420750550040394403003075089254510f480b00f4244650030443c1903403420b40314004005070346c50170182d0300c024150091038207284c0b8410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 851241636 1250 851240386 851240399
    0x42616090c0909151a1c05101d1614040e011e0f0b0a0e09130311010b01020c0d0201050c0604030c1a06132c070e06150a03051e0c0a120213 61
    0x160b6807825105d0a0940e8100035080400d1404525082d84110115a49908100c1c1c2c401902c00034201403d04080800f04d004410701404100a070054030910101405100135024030703209094420008192280050b1220ba072121a801900c07400c2c0149081c80124054a50001e504441403604452241c5240708000d45404481c800c190301004041c03017000440102508645c4490310014024503181400c40100c130768506000700031140341b1035110880d0341040a0629560380c00030300d1200e0880c04072400140580e041c40141d6551103110808840c40c05002e04020905401c0f0021500050003a01a0f0001408c0d42a002c01403002c22111b1907440480c030666140c2c0100c0650014950080014110b42c11560790a004041c50300001c49001c0c559104510034005036a010343c010741c10920558007444502608442c0c602c10b405500d80d11020555180001074541c581801d91403c1a104902100304a080180040302d590784902c0090f00440c401408038848000d41d4422030b44000b0702c9550720008641000d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 851242886 1250 851241636 851241659
    0x40e01142e030b040e0c12030a1403060423010f0503030403081209100609150e0c040506031012060207031d090112051e21042616090c090915 62
    0x1074058080550380c034508240354032248212400c1a40070401070500718200400c001142024000e901040d800511a0060958100e0a01e104000300051207684958818010600505094440304c80c02800f0038010b104c440c804005040c10382e10406040d000e41a1120181076a070f116a1100a014070801c1103c0c080f2a4101c0b10501e4118210605460350b06070b441c0070f00c030151415908440c0030165940d1004035801c0d45070421000500c070308844e40c0a04d282030310000b80c0f1402503204d118082c0100100203a0b4402a03a91303e0380240049040100e50030307109007022802504605d100710080340c54602200425080f8007200a80f2000041080d0410b030700704450714815115661040f1498890030382d2340317001140e042c0289111111007000403c0f6000c0703c4000320406115407402c14880420801050021484074011070380da280080e0520b00c20300030100c003840e1400d8140034036024900c1c1c0c101c20118101c02c1d02d03040001210007956601000701e4803140303c80c044401202c00c81c04109245101040750740c0c3c0b5034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 851244136 1250 851242886 851242969
    0x80c130207050109150b03060c040306180606080a0c091406011b020312120f0f07081005100215010f06120902010504120b0106230307140f040e0114 65
    0xa10094109000c6a440ea429a1000302c001c85000741003c1100303a00030304910407000070300011001000d560074440c3d2010349520031800050b2101d80c94617416050350411154100200e030344a90308000d240c0e41c48a045842e00c40c4044112401091080000303842ca8641c040d5044038880380143c0009910b4040040d80c20302d41c2a8000c200300076000e403244000d6601401740d401800072102813555100300c00010030846c0e80000b0200d214080244040c043d600f82c0042e8201d51001c2c00382040c500d1a140c1da000312404100c590b0120743e00248000301c51520301d030701007600e021001841c05400900d0343c0b02c00040382c40b5a03090003041e00144078146000c103e1405030300581c000c2c0e030040c148146000d403912400c440b03144c44110241c90302c0803400e00411580d0391040702501d0310305452140000c850000e900340c243c54400681103004018800c041006849210340840301d4215818050075560361ba21012400d40c01e034244182c0100345c8881a2075030241c1440094030394500d01030b44e018030b20303051107008024049041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 851245386 1250 851244136 851244169
    0x305150702120f090f150d09080f0a030e0d0f0c24110c210403080d0608060a0b01020f030702031510080706120b0d08030601120b0d210207080c 63
    0x1a5400c924080d015800100500403540054680d1850850107000320304441703000c9180600c4101c20265200c000450640d040701d6900303078001c00c144203075080075469401041e904111070711001900d0b40b203450b01a03000b500d010040e00d050303544802c02082d041e81c0b0f900108500d000072910b00d40c1c01390001806442007002c107803205800340c40c0345e2961a8032441110720f9043c13425907032100090284008001046400d05c0100b0784501801d401da100004c036481401207120042084c0c8021550b01122441070b0401000350865804880301858004001e6000c2c0131582c89090141c0102c4c020100000302c00303c22100119000f90041c11650041c60000000e41e00c000c2155058100c000710114810740e060240c0002440d00c2d40d511000301c49140b01d0403040b2440648070a11504d48030000b44001400b0400b543e134030440074201013180340e03400a081c074090030054000c0c50740400c00c10400703801c01044140c10343c820943d4505e802012064a101130740d84034400d0180f039415a1104484403014a04402003c1004c0c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 851246636 1250 851245386 851245393
    0xc060d02120408031f1a0c0c09040803060a230d02010c120537050904090c120512031003020405040309030609050f0d020123100f060302030702160305150702 69
    0x8840303000c07580d0318800c0d1400c98141c00000244001e1440070200c620600a820340041341040c5040c0c04603441c2e40380c001121964420110311a0300c00041031200d40d11900b0050411003403464540307000030540d841141c48511507111413038049441445410512180d00301c8507040500c41c0c0016007001091500340500302e0401983c9820b50b00001c8040113410a102060744603182c86014407a5200a8600410381030b040d0500d040e03c079050b00d4040c01c20720085e00700381410300380d03560742e04a80420054490054040e14000d000071000401c0c20100d140300410a000d801a2105480034030800010303407000f559103000e00d5178861001d001500c1c160780816042031003070401070300700b966a6030740c40140d40d2442810780d5942c0241c02402c00b4144e090251441d00c84c094030080000b214101d81001c42040640c0150003c07400500000300442402c4104001030000107092022140d0358410040c0a94000c8415038014000c030340b02d15420000900040703041e1f0303034400e0181c82030041c9106406516500141148210711 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 851247886 1250 851246636 851246647
    0x1b0a05102c240a0f0b030c091005061c05060415090b040912030504030908060903070311030409020c0a150216020105091801080c09011a1b0106050913060e060402030c060d02 76
    0x359a111500031031449500042c003d00d44034154030304440d41d50700710f0a02a07091801055969402003021104407400b110203241549611050245038400d582046401c03140000314072003080d0560307449a0b070f0610807810520060361907030188070641e4802c0c040312090150101c02480ba030701c5260400c0903882c1003d000050404015150a030a40c2d0a401003600865900c905000c1070541c06103072000a840604001e00311400d041c141c2c03541e00d228041c0e02400b0001066200c1c4249502842202d00828100c0810b6417100481b03201c440d00c810141c02c044991810614840c1c1e00c84031540242c80c40110782034002e400504454006484c154010382e0074179031114142444503e0366008030f110384e010746410340080a2b003854000174031054a2041c0c1142800090300c070015460280c0c07600c100d410794001a580604956401c400d0b95015141940200307601403418010455080590342c0e01d002c6550040c8000c1c04400035501460b6196402a81e02030b4242e000b40c02004003509040c40100300c0c08120302001031801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 851249136 1250 851247886 851247913
    0x50102120721050423030d05090d15270503090d0f0605240607110d05150705090901060e100530071103130e0604021b0a05102c 56
    0x20b0045100c580045000858244a10011107641400c034002481c00c010b903c04048000030b03a140845280c88040001c0003883e2022030700c455000100050303100c40f1503810341d0024003420000c1c0645180c0c007814650000c1c50820100100c000b889140e6403c00007540c130745050074061160005807040c050b40c0c841c5032056204001015403150900c605174104180c010385042010310900002c80d0350526200784c1e0188020300c08a058a882c80c0030701c00d07040f42d441310310030854904103041020705130038820b2140d8a40c08000b06950024002c05107210b0441d44080543c0c3c98800669181098207003450700300000019000289001d00024178440c4115003012419616091018100c505001144a1031668500c140318000d500b1080d204400b44586025604201c0c0140c51859403460078400e51000c0c0c8400e8010600030386072503048452201c01c0d101c001e528086401e83c2c066943c00340788021a001d105a15110304600814880c03c0c1240305072a40d00c0261401501882111a551180340348290240043d08041c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 851250386 1250 851249136 851249183
    0x1806030412030608030f030c070f05030a08041106030c0a080a0608030a0e1017040f02130c030b0910060f080a060f230301050c12040309090e100f060501021207 70
    0x580e20600078000300c1c1c2514000203064400d640d0240b8940d51091101c02c490140382c00131341f503220000c440d00b80d8aa061904054604480c0d0003400303059400000344000c9007a40c49414184100d0090785561181050700c018401c261004441c2e00120044c144003031700c04144541203e80e0824414a000300300ba6403100031044c11680310294000c007103040d81c94818110306100800000d00c42141c1030aa200751850100070104400041000742600d10144107401156100011700c40d0207a00c5031801c000c1c1942409001e4000c0085012007441030200b400022410400c800c1301d0710980b40640d071030b84100d02c1d03030800595181c0005420400200c0d100d42c0040f03801000ba814480080030559007030601030414404260500310b441848074002c1e4106820440c0c8140118109e640d0342d80501016401607886003012034078030005070496900b96050001400300c0c0c281c0060b101000e0420150708005603d028814601110040e104007401b60308484000065950103c024241082c054600c44261445c04040c0264 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 851251636 1250 851250386 851250391
    0x301090f0b2709011415030c0409110415030204090501021b0a030801050f0d05161502160302090603070b13030314070c090218030709023705180603 65
    0x5440da11a522100340d0900d0085500e016400e6450180840b10314161500e00d0114000b0040044661408120003040c2584203070305240140304903031094205032540c440309004071502103109104d1445103400501c0c1c40d20038200895403004042d20554002400e00024020208500c030403008000d01c00030160b2501d006000c1082d1240c000180e40c1d0301c0d1808507031200d0407404034042460303001d603a1030000a90001e01c20b174103540301103030080003010100300066850180e015000b04140a40560149605403240204c030a441c003201c0c100595451020701280d03500300c0c42c100c0b84d84110f8800420000740c180440c96a40045020301078826594654804001d5a48504181d103117031541e5060801c00d040e84803005920010141c5e100c41d20380107983d11160500d101134001c2c6818507034002040700b50102c00c1100a02c04843c05412741d0307070f1131743c0d0781810000035042100461135041d00301240c20314640d40750341c0c0d10109913003400c0d61050301c0c01000c00484643d001592001c0d110714481d6459101941c803280a1031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 851252886 1250 851251636 851251649
    0xe0f10050906120f060f070507030503010e0a0b04020d05060f010c0b060f0d0b07020c010f0305070e010e01210204031a0105030d0e06040f0305160902040501050427021c0506060a1e090b0301 83
    0x26003070a1105001d071006c074005081408000061107101c1c0003c1e480001c80e070454a0089031403081d5142c0c01010802421080c03200c1c0d5006100180c0c0d1005540349801c032512415048610b1a4a00840801940c441100794401016042d5120004615250241583c465a0710103484105000501c1e074070035a01c41c800361015405603000c40a101c1c0c040d0b9020204843d40e2000b0b01d4140601c3c145034030044c010164200c0d04034107001d004042d080c2503034417404410f40303042c1c8104100d100300e141c442c104500a6005000c140c0302030130481c901005001450000074102d03400a8000c00ba49114404100c0d0503804403141c042d80030004120001e401110642d00034041c600801c050000050401c0e81028481865807048460b03074011f100420ac541e8000e016202120700420310b181000d1001c4460f001950040356880b94003d10200b4002c0c500007501c81c1e40010040c01140030012030300d4103010404103000d48031607500040d04681e4070455003101a020400c8400c020700380b00c0100c54450030000701c2e030303082604010b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 851254136 1250 851252886 851252893
    0xc0c0d0f0501050a0b01050301030303380306060409050319050c0706170f0108070b130905130c0608010e011422020c010b2b0302100c03060e0f10050906120f 69
    0x10103001e000c0c401c490b0449012001000781c00e00303d00000c1d00c1804144005810315a48030807000c007502080a14040b41c0b07805c80910003c50540302c241c0d11030808032000d1107020f0b104034800108103003854482c140300701d50000e0046080004402541107450030000200081000600c0342000c8101d08001810180030f0903184d4445910138040140380b0900d004180c080840744280040001131800b00d4254140e444600c0b020741d40c3c0c0104803811088180c41c0e800b40f8080d902d8001040868082c5a0011004621903010550155690703041112181f80c28001d180c0d00c10075020041003c4c041e40860b803110030b500540000110f07401070b80102052403440348102d00f03081d000908040c082d9402e10660350305034801c0398000100484044244401e04c60100381d840c00303084041e5504245070080101c8125002c12500330302c43c2c07088080c8000c015144a1041c0e19080390400c0108800820030806940310380441940401440e01e80420014001d20103040b842d0410094602e245800b84140301000c1c0c1041c240d4010b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 851255386 1250 851254136 851254163
    0xc06152d13050f0a02090f120c0a0608010803090d500307080a030212100519080604030c08041a041a0922060509070804050d080610050c0c0d 62
    0x14810501094141d100d41e20340340070200300c8121a1206075580000d1403c0e40161602d201c08003145038048034240980e0b000c0218821490300316000a0201d020030420384007200c3c8180d5490084e59031a100780942d040a40041c4002013450500400321f8000a00840d4034180c0c41c00403135010104082d0700d600d518842c0d00108026120134241220b1000b850341c800d05004100b010004507103403030303014044000384034043c0020201040c512a0301540c0c1c113110102d00200c240d0402c03041400720801207200307440c003e0030100c1c4c0202c04200c4040500c0c0855900c034025154075a02d40d44c0031140c103e001c00f070440304060107007c041500d40b030016091584182e50018641d4035820400407500d40c3e50745105000802000f084950566240e291084d12006c1c0c0c130001820510300c1d4120010090155078100170341000b01d4600b0420300c00d60101030742d400380d80900291003070079070424001c54009004a862130780010006a40d046c03824803510003800d020040d241911680c074005000681108444e0a0644034030812028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 851256636 1250 851255386 851255389
    0x130c080c03070510090b031503060f04030e0109060c030813081b101b08100320100207270f0f06150504050a03060e0309090711070b0c06152d 62
    0x10030005444120f0b0040c21341c03c01381e6001003005200d4011071040e0300010000c1400320b0f000303594071528504020b00355140b515005144000b000411074040d00040e42408007086203500030703981101991166039400c050402d55480a0f01c008030f02074903110070b11a00c0300d40030b004030300c0070800b0b0a03045030a8a80c101e2454141007800b8030b04040100c02408070351810500b9144100380024a175540e481e00d042811056440c04c94200e10203134030380c0c000780503400350584500900b00c40048031070f4100e40c211410f0307100114040049a03142024000e08003955070380b41032010304000202c85408803c480b04404141184c60318410015503030341041040304c0685419050010b0341c0010302280000f082c44c0303401070a152070300c030021303044569920010701825681c2c818054a04e409104644400310090030044003402c0c03214005040c101800c0718503001e07008116020406003804c0048540c6081c102e0300502d010b4580d030076030910030000303480f0465201d10085d548401c01c085403101011248030001101105106030030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 851257886 1250 851256636 851256643
    0xd1401060e0301060e01171c030b010801080c030d1404120f06050f161d041d120703050d0c030e0f030304050105010e1603050403030b0a0b0913140f130c080c03 70
    0x14106200c1c3c0d04014090200d40b180c82e000504407000c41d5003080110503052001070606500c0701a13101480030100d00514083d406412031102c076042a41e8010582e03a13901c030380390740385d0000c0011558107401c0781800e00d52643c0700e207000003010b00e501c2c0d207002c2c074180d030350000c4082070354040c0000c8070744010b05040a0305108952040c55445a42014800d68510304003c0d24080085410101414452951107400071001e48000050f8084005881040540c0f2008045149810202160003461107010b50011001c00d038042038805941e4035403a150304203821000018040d0080725104400c0660701ca0581140c1d1a04100340e048a0324668003966407810107007020b500351041600018114603401c0107120040c3c241e15410706030f02a89140004d15038a4a1400f10040d11610350480c0d4010300020010901402c018010118aa4100e4104800d007019503d0601559400f00c0518051100c80b0005100da501c007100d401c0e03001c265041000f00c00c020666801e402150981c100d0070381644501500311080c2004c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 851258992 1106 851257886 851257907
    0x30702011508100b040b0303040515090402042d0308160c0e16031a0d02130906020706020403031805130218031221060a09110d140106 59
    0xb22400c65840780d10700d80c020340c09031030080d00305404c2c68140320f40d0702c050401501443c10035103858104294075240980c4140010b0080000f4813803640c9030f200030806400d805000000c00d14400211502c4081003c0300c0c44c42c2c03102500d00a001040000c010744155051803540340505078050324001230001215401402003201140602214240810207050450382c169400c04c5040c00002c0d843d8815114642495000ba0b030030515100541000c44045440012518002c151a0700b5540c034201203900850058862603400b01e003d10826501c03404041200a120452000c02801d19000800c00309101072078091041e40050401c08034240c040003035170300c000018180c031461654106030000541c00b20854105040301c120b13640200c018004440c0340030318005010342e0441030a00c2090401896076860481382d80b441400414803d903098002c401880061941e403a0665240243c090700b00c11f0741 = true := by decide +kernel

theorem cover : BRFrame.Cov 851079136 851258992 := by
  have h0 := BRFrame.cov_init 851079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 851079136 ≤ n) (h2 : n < 851258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
