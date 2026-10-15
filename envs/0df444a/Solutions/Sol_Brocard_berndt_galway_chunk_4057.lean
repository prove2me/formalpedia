-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:45.443087+00:00
-- url     : https://prove2.me/submissions/b124f2a3-5d39-4aa0-93a0-cee33a0f2fc9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 729496402 ≤ n < 729676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 729497652 1250 729496402 729496441
    0x1140d0f030315080616080604020c0a0506010503150c04031e080711090709030c051c051c1202090f0904290603010f0e070b07050309060a17180a0b 65
    0x2003041203031019003400307401002c0c0b20510303480191070320001181c9108000b0302c0a0080c0e501c0790079049000c40507141154182e42c080c00c010b511503001c00082c00030034020019030714000d0003803001d00107039403620b0f0800d03292400c00c42c00e0491490070031080084181d07240c8181d80071240c02c10b4440c0d00802101c0030519980f040c041e4014030f1150003140643c103100808214841142058500c401541c07a0302405480a00705d07440b00409401a4000500003401c020b00c801480d0b280480507142400c2443d82e815042800c1c5c0c01c4407a1420301080c0080c2e01455004011440c04910102c04510b0900c04102040c0120070311500f0701e002c0c2e14003c000c44c4c10401c0c0003030b080103688120000c00e2001041941644a82c99050710010701c20b608001450307222000500c42c0c001c101120600800320311385440495403058105a0707090350580410301551a654840070018103400041d650340c4c2d40200c1c100203584101b030f00040d103121100428415100d10302c0304001b69605919030840c95205065440c0c140398110140b007405e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 729498902 1250 729497652 729497663
    0xe15090603030409020706290f03160621060e07080c0a1418030607090303030b1c02010f09080d0905030d080403050a0302070c0510030e150f010e04260c12040e01140d 73
    0xd0352803c058100c1c0e201e10980c4e6409c840707682005242c1d004040d40c0f08140d0b2014890090480760401c03030070b0301440c03c500425209590110400c41840d0603401110300c9c0e0390003044011704800402201c20390040703e05501041e9002e10500340443c854009018500320012288204c60000d581d18803d124650b4840c03100034000d040715418a40102d0041c84c903c000c0c03004a0200e41001d0a402d02898800a48402045111a080140b03695500111120040803000c641880402c01e0041001c0340e040c050003415486e1501c3c1d0724410361800c01414580700002446800300550b02041c8000241c0c0f0504507101c401aa20f0013507280c50041c107298404008550169a1102c040000351740c9158050300000e00741c0d02010151203220741c000380520240c0c00f0482c1c40801061202c030061029051203540c464105000b03201c090310340116031103800c0b1001c1190001507080503000c034200307418410803c03d4181440412943c00c1c2420315002141d01c0001c0d0600550040002c1800300c440980c42d072030050002c668202 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 729500152 1250 729498902 729498941
    0x809120705120d1b0905040f05010302030d030c050d0203161103070c14010e030601080604060510080c010c2307090e011a1e0d08090a0902040819030201060f0e15090603030409020706 80
    0x10030040d20340b0141b03200b014000c0f0704249407907441e0103403403040c18126070300a4045c140164442100b20014045611400144101804207450400440c80a1445010380d2640d42d06020182d01001c2d01c0c488030003c0e0712981c1c0e841040071a00041c9840c45582c01c80f060301070340c04420900312006842d000030354004a40c1601c10f18000040c0c490002510300e0145000701c03803c2086407690045410700d090301d4015031641d07500c01ca40710b0030b644d480b911240d04042c4c00313078001c141c0c42d80c07102031518000c4600300700c111220341c09030400f484004514480c915904801d00020084235a813003c120701d0140d0101c5140d44194610b50300000d00300d02503101d0800c0c0d480700070541840341265207456200f1360440c11070680140b402d0a000310f160340e918800c541c25501d03020000c00110300620b50300d03810001a001e0850440d520f54800140b04c1d0240313440381c4050030f60500060050b2031b15421495044884a02c9a445820288107201603078801004a40954203c0c3c0707c09070717440400782070071000b9000100051300500c50302c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 729501402 1250 729500152 729500201
    0x40902130902033a020a020102030f090414010303210c020c1201140907030c05010c11061602030615090f0f1f05130903030509011a040b150a0809120705120d 69
    0x31884c5107041e800304052005a03c5648503812680d42d16203050090140e442007081444d91042c102c044d22030a42c0060002c25803c0c807020723000d01c002000b030344101c0c080740d00d0150f498441c01060140b084045203680d0108003404180790000c1d950250314a04034002c2c64040e440d002015000e401a0480c04a03074189080385090101e5040d980700110310003034030480341e003410116496200e210507072103d039042814081368003500030800406a00407040c640903450801000d0006840900010340b00f007160080e0010100c4403442842880040100003501400480040050f00004140c072260801003405004d02c044001e2a0709094a88098110350360041c0c501d80c4201c1c03c1103c640207030103ea442650188041d0f165450828282d0b6440904003051003200d100242c01410a0780c0511030040c030040c422082d0006c40c030300700c3c100c1e5444044030400040c0054208a01c07441c080000104003001040303400d14004440e20351588648180c41071a01c004000110307606501c00300e80100105864007064008450072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 729502652 1250 729501402 729501463
    0x1d2b0c03110907020114010e090f011a0111011e090201200307062306011209080301030b09060c250309051801140102070602030409020c0a15051504090213090203 71
    0x215201c468826501e8600040780c252042c052aa10701c0400c2100341d500340d08140d081009038a0080207903401e44241d04041d10030b50070034044c44081061002490615075481301c0010402c6c1c0403403601d110a0380c18540d00841c100200da0254401052070f181c0000c89101c107200403104140c45500300c0005d1031000292038500328001c07005006241c4140020800103d00d071440410803801d204505c0d16030048040007400c1c2d1350180001013503511500380c00080b0f03400d4543e40d0644503002a00141c039950384e03540401081c42c0c401c20003181c010424000041c14084000a001c40748481d00c18040c1080c8203c409500415000320300450141c24020500300700d9030108036220b004a0424812444510650002c50b081340d400440c0600a989059004c0e600d401c5c00c056400c0c01942c001c0394141414070a003c0d6900200d65114403601589480361004622800c200d0703041100d000e4482c092030312691a0958400040e5185503007410403100008002c1090301807800000d09001840a0071141d440d034000005043d00d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 729503902 1250 729502652 729502673
    0x702031e010b04090b07080c0c030f03010f050603041205070c051f0e1009050111070e070f0801090614090a09081c0e07050604031509020618011d2b0c03 67
    0x90414020040c0c2c005a8080005442c0c003290050480e0700b201700800c2602d441000708680c8454401402840c105003005001d14650140c040544100e40102c0103000944403002054014403040302c4583c210300740341d02c0701170304c0c000d00d80381480901c00f002855104200d0703805002d40051000a100211000c43c00005050320208403114800058800c041c02446141101c0540014661036940d40e40e11400d200054a4008200e515450383d0312508000084040341120703401e118802507078074050200103000000d010880d0680102c2421414150240b003c000e00d001d241c4242c2c0c40484216400e510340494100080c1040c8034090100900014448103205004469001e003140d5201c04000100d801003c45454107079501500380d00900c100b000700081901000381ca4130080c800320b0f0008400180303500050319035000d0282c0314104001d68681801d55030300040070b8441c0c120000f8a42c004558a02c000511501c0350300541411b00c4010441100103410390111141c00f160b1000840b052103480c2c1c202171541c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 729505152 1250 729503902 729503953
    0x6011202040b09010303081b22051906050304032d080114030106030f02040b15040602070321022509050a0615021603030818100f0f0905030d02030c070203 68
    0x2181000707442c00d0142010106503048940660f01c006960319958034403900d041d228148c14030b091209100e0102240380c0c50340010003003e1088018000280b90506000d46c80024034041c84188418030030401042d034000b401c43e035000f070303262904507640c00f00124692101c1a1880059504840740a10b014043c7d030811800b078180c0b4a01d1648940d08050441018281c0d07005000090044202c001031f0001403d0540103409414002081464000c5110414080036046035001c1001648407500c1001806440f0140702c00394400300c0d0058a403018006000703940c2d131915032a030003d102d0b10354546100c10ba0364048140054510000c0c180a642840105000500b4581c001c540104d80c034169030148860001a2590140c801c10410400c024995102601c6e48080203005001d41c4140c0051b001619409016484422202d21400214004d241031b801044440f45014501c5d083e241104102c08104000141c40c178440d03c45002580d00c2c1e43d2000e040342940907940d0001d426200d001c002854042c0d0100c40f00881 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 729506402 1250 729505152 729505159
    0x10e060a1707080f120d0b060910020606010e1206041b0f090e0d020105250201021209010e0d050c072d06050703021002040506030402010f030902130b0f0a0f0b0705070806011202 78
    0x8011000161780c031900700500b8441c46010030000c84071041c91a030410b401a910041c0400c0c24141598003203455800900c032080016042081000410340e000180d4402c1028151040d150300c6055141c240d075240d43c060006011900207240c122141c880201314000074005440d91113100e280da560400014001b060342d6005180a030070461102ca0384144035182c411480820850004041001103000b0307034020745002400c40d5000c1090380c091085140d1164000d400900c00081d0010546600724205498591003108000040242c08094100002d1a80690702c000240080825500384081490b405000800e0710756070f40030304002043c58101000d000301c24066000e6860044801032820128841c5000b82e0790f000f44180046009035209462200302c0300d469040000e4104142c0c2c0020b8101130340c8502c00744141c2e032520000601400c0c44902c602010b807080c1c40100203541004101800030f10b0500445820050100300c0700d05201c02007201c0d40081100c1800c0d5a003d5031100c1200300e007001c0c03ca500740e02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 729507652 1250 729506402 729506413
    0x1b0d0f11030901022d01020301061e02061510020c030a080310120203030717120115030609050405060402040c0507080c2d10050c0408030f190512010e060a170708 71
    0x40080110858484250503805000141110840400c030160904c00c0b17050307201546140305005100034402903010304030a40302d00c90511000340b04000524417440d22581190040350a024200310794001000003004201c0d4201c41b0011001012881d02e102480c540d0b0b854420110410140001d000c01035000c1d600d4903416069898039422045040045440000d406610800004011507c12061a0001007510f440c803031821417868106684c0d11070030b802039540e640000010000c0c50f9054450103004290b5081d080c48240f805440d039076141d4600400c040e020307a40361050406d0981c890740c100c0e819aa0300c2450541c81e0300304400201d40da07560030800c1010054006003807503101003082c010881d11001c1003004241812100c003001c00600000382c030303d0030601c609000210318580180060f05094160503002da031261000c4041240c0d9450300e00f020410300c00d04002c03000c00e01e07c01d0f04100303041d0790a07601c2d4403a040d1240004600f44000e02e80c8090031107140d91815200b94580851154204d0343d20038100d41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 729508902 1250 729507652 729507677
    0x2012a02040912091d0402042c1509010b1e0321090405010512100c12090f0c06090e0c0a021905060f0f270115031a1006090b1b0d0f 58
    0x5207100d60810f51005d080c0f560303002500510303050700072060f032a00c40700700d0030114071080c0c2c48201d84074011091201030390800c02807242451040c0c00380584c0038552038000c0c0030303140356080441d101560b2040c45102c81154484201d01d1034804204202c0b41c03440c1d00505a042a01d50000d0b03e1640c0c10100c1414410f0742014000030345450a0041d108000244002501c55400b400d02880b009110300c040c00e505101c2e00003040c1e0b0551441b40b013103001040c02a00c020118031010f180261172800c85400c4202407145c9040c0c107000345800c0341e1001f60300c52140103c5035a1861007420582c5080e6036034520003401c140d0004200104500401c01a0244401c040541c1391a103e20b0f0000c080340300212860110180c682c04030b60425181038201d034403904800c000000e072060340d00000e010150015001603402e402021003844101c0c603003008446d07009420900c1c5518082c2040401800d44020340710340f001c4808049a094a411000c5030030b18200f08030f44c0203e0f040008060400740c03220b000d540d040b40206080c01e9814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 729510152 1250 729508902 729508919
    0x415050c2b030f1103070909150b1909050d1212110d230103060e0d02010b0f01080a140103050105010501140705060c0f190201091e02012a0204091209 66
    0x4001c200940c0c05403446081c0021400c900814440d1060300440740c0b00c1d00b031030032207010100c000d40c082c0080d030366501d6040c0c1c1440d2041040d02c254400003400070a064008200b0020f229054800c140c0502080e10070700921100c089454030305a800c60ba40c0402c84030075100421101c1800b00c078003412151a010140d120003400102298480d140400c3d65079010440170702440d00c59840b00e00300075905410f08018000400c0303d000c640c107090300121480360380e80321010174030142000080350043c550710080c0a220b0098000c134099100441d40b241c10b0180500100f412560603400031210480507240d49034003580d581c100940602800c0c8507050106400015500080c400d070400c03150225000b030300400c860b45900c15510307000e42c4401410408c1c030b80c00b84100c00f00f5526031035048498400e161300202e155403190400310780100c030444011444100312090900141d0f041602d14003a2202c81d40d0700703400c050614080110f080c03c080c1d802540301c1e00d001d50720303410407900d1440340b419070550341d0381c6801207905c60001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 729511402 1250 729510152 729510193
    0x409022802010b010905330a1b1a1312020616030204031a13051e06010501111c0203090a0b040f05030613080c03070204050c0309010e0309010918020415050c 69
    0x701c1c1e00017800b018061241d401c010a0302d80c4440211803c140c0810840201c60745c950807642c0d00d03a0661000050713503081041e8400e410075004c1d540c00c4c200f40000241c44da521290642c6044940340c1030b5a080d40040c490003d820f40c014005034125148403902e040d4050f00a40341c600441d82d00a203d507038040e80f103401e0752080c42540c1c2038a0380242080d4807249810400045114010304001c0f00318110840c0400158080c805071002090800047ca50124617020507070901c10160011410010114440c24150000054072101e00800a1481d1051400d4080403405c0d8840c0104490300315511000005101135900c0c005c00489154444071541ca44c0c0314401c040e2a140c0c140e58040e12001e90f0840100428415002009030340e001c0011249854003941c0421305843d01150b0543e100100402005401d203001e0160610240030000a1443e107c0f00d0000a44058024012122036080800d802d4200707194590456025040a41c0702880c10b13507903e00c0041c003941c48001d014006010b1400c4a00c038050b1090314 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 729512652 1250 729511402 729511421
    0x80310091a01120f110a09050411071416081b15041e030b0a0603021e1005090a0e01091b02120a03020d150e10050f0a09020f040902280201 61
    0x210502802001d4011500d22882c45002540349035600d01c13030308504c4101e00c034174000340b084000a9a1546074080d80a802c0c10441da0107640501c4c01e201410f031000c4480c00441d071403564408241025151070500c9145000780020b2400c08920403224080754060340090060901503a5a0142c0f8007031601130288000644010400520508244014030200500720101c0c081e40495407104030109640392240e102046080d1800c9030070303075922641482582412100710f14049c501e00c43d130083c3c02c0c00050110300301c000c6100c004401c0140104110940340e80e002604002071882216044441d40c503140c10304020308040345403404418000c801400c00b1800441c000c0c000c81c1006001d03c7c03e00e4540c000503406036201202407110f055135100004180840d00d4003002c0a0701131186103000d6440d20044018004036150441791096090324400c85080e5900d2140c482034030210000580c07640019450104503010300d4104004060004c21014030f0150700c14100c00b032420141c2d802c2111071061003000e80c00c9800852 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 729513902 1250 729512652 729512681
    0xa060f03081801230904050705070203060c0d0f09060c080619140109080d032f040315060e07050a0206072a08091c02040b0a050d0b1506030408031009 66
    0x1000b2200e1140c040d0380601c44006040c001490610050b0000030381c958600341c00800003002c1480d5030305080500c03803160710504d1420b00b185081046c4d00081da0700d0300e004180c000c84100c00101406a014036400004050700342503400c1c881e0380e22518104000d4500d20780c944000030050000940c0320303c0e09100c100c201f004d4600704801c01c1e5003010035103198506400d41030381c103200303030341100180030380042151a4503115155800030380a01039100e60072005681504440301c2c0c14841c0c8260158451100481f41101d030703c08924844000000c164401030326940d40140c0b0903200003800c0140094110000341442002a404d8a21030f5592160946880c00040010314045441116201c10460050754000c1e540d13000303002c1e65040004c0302001542c10440060381e154401c50210b0980308500f01401f80c3c15015038100c5503218100e041c40c0c040365a1001c102005014903074080d001c00c007145130024000c8003900000d0480e40c4d80b450141400c1e0103540c816181e1403c840c1d20582c0004250340a0312400c141d01c039000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 729515152 1250 729513902 729513907
    0x13020418092604030b01081f0b010203160f0206040e0a050609150d0219060908010e010203061507170406080f06030c15130f0306090b090109021c081209060a060f0308 73
    0x4207501c0e42d240301160391800c00d40e03a0410000c00802d500965480c020729507840100f5580f003145000c150350400320303036225403058103002d070400c4240e0300401540c076011806d00e09404110014102000100f00c820350207034101500140c00f007034141e03061401500c103100c907207014003440e1500030502001080c211b40c1303014480041401e4004518042c0c0ea0301c0ca41d14001030140c105c03003140040500c01034000340c0c041030105000c0c0301d00700705403482800745400c100c909100850640c603061000c01c00d40300f0412500007000030001854010031140414034450400b40643c00c0340c0320354545030043e0402c04107503415440c0d51540000600035150000300c64041500203030008640a000303204071045900809020045c401100c030f40460945031100400e40118001e0102046a5502d4108010134140c0074008002c0790341001c85190158640440300c070008482042d04158140803401e121845000340e04d520b22030b10b103000080c8600c60000007000c038024006000200324056179101195003054861000030207000c000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 729516402 1250 729515152 729515183
    0x1060f090e07030506010c12180504110a0e0310060801020409060909031202030c09031605040c02030406090b0d02070209040b0109060f03050a11010c0f21030506030309041a1302041809 81
    0x20380000703030030410604101f20b02c2d2a5170303a104441741c900b002c090300015001510707200620414100000051005076020404c000d04600c00c0800c504c13a000c00202400702c120900d12841d14100404a848a402902000100e4450840f14080c4d030161041c400c0c4103040102c00b180c96030840c0301e41c85090b81c1c0343d12640e9031881e007100014040d4100801c0044058024010303a03040c0d80381441041c442e44018007104441e2420002000210341e4041401421036205110500400e904040304400317444a041006842d05010104078001c1e10440100030b41142c501c03028032007045170402c4024141d6100704411f11000e42c56440710020600603201c0a00a54880644040407805240c50f00300c0451043c9000e5644410640740e290160b640350f80c0481d001840d03a115004100c0c00802c3d1103540c200b01d881c0901683c00e107400088c1d0b590040d01000751145130f0384c611807100c1040c1c810b03c045034500080c011189a03500e810400c0000c0d00300307206207020940c106400f0b15041101c0e205401e0007550041c01307070100070742 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 729517652 1250 729516402 729516407
    0x8060a140d061506021f14073504020a0b0c0703020609040204080303040f060b0312121e0703060504060828050a0516090c02060103152c030301060f090e07 68
    0xc00410595145960701c80000001043c00c141c6030241001e07400a041601c50028040c101c00000059810118036089540050103290300350a41c100380c40d49030540c1111342c05449002c0d00103000020f03000e21200b0b8508041920009100c451140d40201c5251600c160b459144140c0c500c02d58200c0e0082d900300180502c010304c0c0281c0036050f4074401400040c2015203548000d4507660007503801799650340d01c081c03150382006500c0c02800078000c02070740a00300501c3d00e01c03002001401007458070025102d03000000b41d80e100d88042d4124460030415141403d80c1440d0402400500503406143d01460400700c003c5645100090040c203605100501c0b4000c94004007000d182404d100d0104071000c0c09104d02120100e007003002011a818803980c40500300301e02c1c10b000700c0f00f110b102080c00c90079504840010004960307107000c440301d001c40482000c2080c1258403441440c40810031460913046014800301c0704405000000341d0b060390840d03100c3d8000450070000542c0c84454038070545201000c843c000400c60751 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 729518902 1250 729517652 729517669
    0x150108060a0903051e120c040501020d050a260702150108120a1809021305040b1e04110304140c09160507030c0602211810090525050108060a14 63
    0x42c061300c2c0450030a01c0106103e00316000e6040c591544003000310f4600180c80208800c1600401d214030405d14040c41d00300082c0d12035044100c0c40c0144a4041509003403a8000c144010b003940000411a00c000a100d40309031b414034068681c800181325800d810091079039035000c01416620b005e0024040a5185221800c2644c032442c03d50701000320061070f030b020b400740e41d9605034081c24806030b0158507610038072006001109554402c40c8244e0800a6801e01515840009200581004100d81822090901207000b52103112440c1031032103800002c01090000300142d040c5600c50141c150b6140000c0c15082120349642961240c034541805030344510f050740668001d00c041c612a04151510031025100e607000c81e040020a8800c0300d11654443c29011030414070703c2d6100c2180501c090801805086042c1c0d14150103d002280540e02d40191082c00f000b04a00c10a1080440902c1301451408403d1075945981d032003018042401c88012401da850400d0070641564007410010440d640c100e001c2001c01c0c1e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 729520152 1250 729518902 729518921
    0x50a0c050c0c0d02031f020315101d04020f04080c1201060f062f010c0807051309020313050f030c010b01020c060d1e0f0c0206060d050c2218020102150108060a 70
    0x14030a00091784a00340c0c41c100076010782c1081590040e12450f0101601c1c60109c005030405104864118820f080541c02450b007000382608680c10014000000012400a204604883c00c1c40d490100300010f03603120000320748080090640d0400c1e9034054049803a800d0300c8182c0607072a5016010f50060000303a01c9111a842e840004000300554600745c00c00c6007510401c41981905565150248018400d801103c4150448854540750b4946082911540208051030060203403440c0c001002c148845d54035941304802940110960f2101075011030b5103a074a52180c02024104d508121003507405600200d8900307980314001d402c846c80e2041201488004080c10310002211282c60900c0102c81d005521461001c82400d1600080b4484142006842d202c40204190301c55144090008001240400d0f4404030400940b05c0f880ca14800100e040c000c1710403441120002454284050396610201c3d080c1d1020354002e07000d50f00381070310300240844480024016050160301a5010400901180e4011000b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 729521402 1250 729520152 729520159
    0x912030708070f064713020706020c061f080c0f0d020d0b0a020406110307121107030f0f0303110310140114030f0f220303020702130906050a0c050c0c0d02 68
    0x3030403841e44d111560421840100d140007034028500c408510805e1284480078050031101613460700c41d010004000000a2041d100c2c3c0540200d88082044901e806845000171000190340c80c610300310ba420507100390100384d0f402a0740000c980014242401280030108213001400800407a4144018004401101074040340c01c00a032040c0394010500e96803505005031f40e5400003603070712403a0042c01480d114055018250b150010005080083c00d0541100d0b40500141400f000b59440c800c441c0c0e00340f01c0700c1c3e44041c11401c50156501c003000341e203050500120344030b51010043c080b0300d1204903405d0300044864001c11400200700780070581760b00311210301e00c0701c1c14900741002c100315180a40321604180d428000303802d212001d2100f86140e00c00440d80c0221038201c60005a40d1000f00c0a402010181c0c024050541c0000c015040d9110033541d0300300c0c211040810b01491046181a000811003156403400081c5482c00120361107200c2c100703c4002442084c01481ca4401130010408210214103049070b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 729522652 1250 729521402 729521411
    0x3080c0d05040308060918151b0c100635010f0e0303061507121b020d0b0601020714030a023d021204030c0b030a0b0a0b0912030708070f06 61
    0x803480c00d50040501ca10f11a0382c64007003a00b440c1d010f2281c002c034003405003036184818000200c000c1c803000810070f007440c803c02d407100d17000d4841800450425500c0c0d41e5241c1c4450002032050304e00e02c000101c0180c46000240704020050303699010f8002c00c0e1061f0140d10480c1d0190300e0040c031540f52960710703c0c031000e0703690b00004641c014860020300301e401507030142403281c10200402101c0e01c0e1680042c0703c041980c1140074541581d5a913100ca000041d24216000d20500301c0d956903440100303040303000b02d01d41d0140c0744e10f0400007181062600d40004440d482d0051045c1403020401c80c80081003950140c5000d402440c0b014065403c001c1c800d03041c9095543c02a81d2040718003410000b14145162080c110402c2c0805518841c00c001c0c2001381e078060050b482c0d0f004200401c0000c4c00700c1c920b001120550076101e501e07031701c0c3c80310070801814801d25815800400d40c04041143c1030f030800140115141102d0286c220200607550584030300170200007810300982030100c000414801c0f001c1941d602d101d00170014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 729523902 1250 729522652 729522667
    0x90b0a02070f06090e09031602010f0315060c0506071d01121e021b030f040e061f0201050a06051207030f14010c080f0a05042607080f0a09050a030c0303080c 69
    0x22142c64855202000281d0722000411890200701103054001ca42c80000c1c41c90000820101d404401d01c241000341000311011070403030410300ca6071050400c041480300f210400c6070340d080f0040101c1c4030318006455901814010500c0a4040c410346040c00000c0301d00e581d0078100c5940150f4a44413201900f4024644580c090621540c100d1f441010700c0c2d5140c200141c545041140c809060001c0150344401d9138801c10481441c4148030055078101e602349448103880d40e1354100032a040504219401414110001c00090100d4064125600c2825146420001c050351542085070320f14020b40e8101464000c51000d1000c60031103403c5641c80382c018a0201901d4045541c1c690858200c01c2031480020245401d00000d04954205150412070040d014003190420351500c54408010942d00b402050402d10001c0e8501211002c0e1004903811000c22030300c50520b18841c5a866000540c120002812050042181d142510f60704040d2a00580706907009800c1d6901510380020180080200070814043d01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 729525152 1250 729523902 729523919
    0xe010e0303090f0105010b04030b2815060815010507140c06040f0f05090402061902241602010501180509010209090c1803011808090604050d0c0305070603020a090b0a0207 75
    0x110b024000710001040c40d440300ea03a12a086400c10781061440c5241004100301003502620326640005481800d50007050980e80c110b5803501ca19046402d00e2401c0c041d28100c3c0e0204892008200c0d0f00d00c1d22048556900c854145070740c10f05d111905804500207201c0303c40803c0860324070360041b6010704200d40e0071070684800501950001da01c00d0b0316852414605000900105d01e050001740b9003a0303160a4541010747c0020882c1c041d01140c140603a42501c7c00e02c1000c1d20030801c1c0303c0811102010f10282007880b244c0c01e50342c00412145040102040780790025030500c1441958100c42224031600045440e004821010f404083e05144582d0340902001c0e1071a0b6945400c240030300da145100c25516159140c440011042c3c043c5040c0c4282d2511a40041c0b10502c0041d14607215480540d00b503462045000081349030140c1c0c1c21080e0080c1d0034601000c00c0010307042405080d00d005c0e200b202d0315542d031150128141e1041c1241000041c000c04d00400c041e100c110302400c0078480d0743c015601880d85a0010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 729526402 1250 729525152 729525157
    0x21207050705060f0c01150f030201032c01090506090a03080f04030c0c060512160807031104170c09090d0f0804140f061e04020f0f0a0b04030506061008190e010e03 72
    0x19044e04080014494000050074811828a514074074480035205103415040b6000c0b0040744000703418186c03204201e01c00d0514401200b002d505010030b401c600c4104100e4194003d0265072411600d911809003ca2801c0d4800102c4048145e40340c0d9840900780e5604039404101300010300308405015250018400240401450401030b01c15982c5d803e482c0c505034504c00350881400b810b94440e007000c10340502241c1c1c3d4000a000e83c48042d504022690000050480c940c0e48526800b20441002489042c03003003240200f5160402032088802440d60341340c0007105030f119500304990700041a803991b640020030703010307a0000b50712a000c1da20681c609403043c05024100318181d8070102c0d10b90040d00410440144442585402c3d1564400e6109a45400c0e0701203140022855403540c45081030007007482907981c030000040003408803020803903121603407803400f80d980b0102519901e2244030b0340b90a1384c202078441c0515501c10800d07906180031070254030110100502d075a000068030f039501d0300403116108404200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 729527652 1250 729526402 729526417
    0x250f0b0a091517060d02101107120602030a060b0408100515030303070c0b011707090203042303030a0b0603040b0402121908030f010b0c0604080c1011070203060903040602120705070506 81
    0x45003c288401018800340209004110700c1c4201d00d9400420003684580e22a0510300440d420300c0c80006d0001110070345070180340d038801500048402003580810401e60003840c00f80e40b8081061054581320303100d004075401540948401d56115a281c00b08800751500080c0d0002d400008040024841c4000f04c0d00390360040300c805000c9880c1070310405c100001c1c601e525006202000c920109003641d10056030711040315100d640030640e00400803a00380901d00e451200c1c4041c0381001c120710343d851002d030107869030800c503503240d8481e00d000c000c200f080c01d1034403c49109981c8068560907a6070f07203601704402c282541030400d59a1180e0f2801e0706005509007120708020380208403140d101d14154444406050341604a0002d0001c28030403061120000161107410561021a240d111464600e000303181003602040d000030306052a000c2c0c413076200b01030700401d90107000354240c803400e540d0300a801e6904e104070301c10900103078404c4803a0080e01c900080500301183c800c3e025103101ca9900d800040143c6c02014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 729528902 1250 729527652 729527657
    0x10b1e130b0a090b0a1b140601031b061713032c12012c0a08040924060503130203010b0d03030b031018140309040e250f0b0a0915 57
    0x42c00c884041d4009203820002c10210800705d103000c1d8406401010f41103d0183d040702c940e107000c8020204690303401101030030b40c1e40500700ca465696070b09100103480c1c44000d241068216101d008070f4201d00c1104040c1c407584041c40090010384411740358a0032081002002e404001c0d65500800c5044800601098016810545000045080402c000d41914080100c0300183e15000035400c000200d021600b03c80e03203085601c61400980400d00c41d050541e21000140410070000f40486c03503410541c051040c1d00140340865010306403150f14900d1100c2580204030115070240005150380c00c00440b600d00041c4060004600038020350701003050445007650840106c4d03100c0c2040401c40c20704000ea0358000d0344103281800042201500d8404201d0249806000024503100700d01541d10700704101e4050380f0000e03004001404a0061883d11680302d0110501c100e6125031030000c3c480541845941a075a400021410161910404400e19444282d8180510001784000600580104103102403100c0c40d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 729530152 1250 729528902 729528907
    0xb09190b09040f0e10021c0c0c1401020a080c03090a060e010203180703110906041d1020160201020115030b060a0b19081b0406020f010c0503010b1e130b 67
    0x44200010380344a52502043c051030301602201d00ba2000594001c40e05a80c500140d0b1a00803807006141869401c4c1401c3c1804d0400c90128a20760340a40d507203803500d00a00c1c08a004401c1d030f4100b40d00781d1280a07a40c41c0000c0192010400b030340e40500041d07400c480d81c082100c02904050303540c01c041e075030200c002404503503010003005542d8517602040c00c000152400076282842c210360b1000344004909075010302501d1040c4c00a201601c0e9a4400c5403800d00c3c0c8844450000002d034400d981d5080b24403020401c0034240f007200b88241500600c00812501e04d4103d5a0900c410089510714001c0c820100303a045640380c0d500404070b040c003c142c0c080614000c144409081c9000c60501c88502c19951021650507020000801c1802071000c00902620891800000d10381724a03041c01c1d4145142075a158020343c0c0050001401900090740e01c03010b2101000038440359031808010750b90303070000b44590b15100318100402c0c0350035041542a000000d0040e44881d05042c01101c0319401500d187d004407002c0d9400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 729531402 1250 729530152 729530167
    0x204080706020106050a0e0402010c0206032a0307090b09150a0804031803031706040b040c0e090f01030320010e060c21060a1e030501021602190608010b09190b 70
    0x500c84040a4941400244a43d901c0c001c08903c9081b020310450402d10310400101d01160705c2005501c86c416002810702c2d8030303814101504540d00c90f5001102c5100f011031124810a1004031051ba440b40115031504004185400d080b40340340e901c08600998080d204440c190340c260405c002030f1400464998400000749000e25020300304d1000e4a40d141c4500000150800000e40c0c88041511051558006015192212004140a0001465030369880744c14401205035442d40b1034044244820304450540d69512003943d040c6c01890b0a000240c001452640000c21030f9440e010034010000e684000010041c0c3c2130031065040c210240c0b030b1a04071745c2c40062200b180c07107149070b0f081c8010101c0741c001c01814104a000a404504140303c3c040b480120b00050f80c4040341917920380001141c2042c02990f80d060075209041e405200385008910a610011000515940581c00700c01590007a499031407803070b42401401103036178211402c020f5001d0000300c402045011040300040090025107000c603145e450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 729532652 1250 729531402 729531419
    0xc010e030406022d060a0c03020903120d150b0f030403050d05190534170a0501030606080d020a032d0801060f0216050405070c0803040510050105150a27090204 70
    0x21900344200d045000440d010444e000701040703140d0403620100c00050002141c1906802034020800702d0360785400360500303481c08000504010601c50100110411010141c2c1c102d00901e86c4480c001e441e0b02020902503802d00d1043d500080d500320340281882814903400b44030070820398008442004026801c1403400060600030b000301908032145000d0b4180344a005d0810406010822a000035010b80710340c29441d4060041a0158040810400300030385440e02c03891a4010748420f21044410354680384000403406030110300c212007103241d94043c1058110303c0e00c3c200d50308000b6485c40c0c0c00102c0812002203201900725161401e41000343c440a403a580f4049000c0c0c10140340301485001c0d50084a81114007500310552001500d40803100003039152245102240c2d51044d0030002031020400000b84828810000b40b1003074000c92080081c08580e80700c0c001d0110a0504881103000e8a1051121001c22401348111500c190140200c900c0c40c0c1e000840351540d2003129a01c80241554009800e029851 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 729533902 1250 729532652 729532693
    0x30c0201140703020604241107021003060308030f220506040506220201081e0c070c0f061706030c030d0c060b06030106051209030702060a050a120b090c0c010e03040602 74
    0x74840364500305105614060344490000308000c04101c2a4650014502550b401c102030014101c042044102e04180c61404c1d43e40c1305081c1a0f03c946800c0911244040c03090194806890740002c43c2030860322100c05510340c56030003070030300812810800f0001d12031042443c035045d4518000c50041200c1d00700b60410324100b00d8094090303450304a603403c290004a0f00700e80c208040541c21300c0c0c40181684c80d102c070f0401da000181c80d0030340100e81440030f00124154500c040c01006024100043c038080e5248105007100c1950f12a801c080b82d135000000c15600c00d400010350340400d018040c2e8510741c01d01d01c0064207050700d10440c20042528141200280300d070500c5400ca80090546410f4599414060041c03c00d014807401e80040b5540c550001d41445002d1003500c52840e03010b45500d4035200b015401030a00e4102020300703070010340712000540341c0c500c5901070420b022801510040300c07900c418100d03004a42c403c0d4004c4c04a50740700e013901c0307940d200c08000900051100d58080c01c2102040d038030804091 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 729535152 1250 729533902 729533927
    0x902010e04060503190f0b04050705011427010302160c140f031009030908100203150d0215130506040306020c0105090a032f06091e0d09030b040c0f03030c0201 70
    0x1103242003414080f54400041d003c4410005180c408010700750717841c0c003450841c450701e1b00408444400040c003080207070008090f015200300740c0b11140e0307031552405000c05078000c40301c3c503010071424014603510501400b007501021101c10b26002d45490011081c1d17100a1903030810407541001111810449008056482615240110b8081014100d104006545d03035000340c050711501c40d03940251070105405070218800900304101030740c201304141c103031100082d0030441c0c2014403000b40300c04410652030210f070400481075000b40b11400c0302032003045005a0b6040b80c5403415400d9885400401c4a585800107440158410300300541d6613016003520314203440015001380c809501400210000a80261040d0b484c070154200103d1400010003551600311100c0d10380001500501d002d200c03c460000c104130551003d0044241c108074400c440c0b841d510002d1600000c00280c51400a00c0040c00300f074806a0000d014000c7e2406003034540000010182e0036a00450101d001c6865180455030480d000300304c607 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 729536402 1250 729535152 729535159
    0x2151801020f0c0f06130f08030c060703091e03030b0a0b04030c090b0109090e01060902190f1115090f0f100606051305010e01030e010f151707150201060b0d0902010e 73
    0x183e11009000c581d600c0702e040740940c032800001ca541c20700c007003802ca10000107241250a00070f115982d61065500d86e4007030021082e40c2e00030310000405090103402440149640310740810b0006407044641d02d000c0c140b82c0011000c0507201d400c00c0c403107640c9602228001c0d103400044282da031441d61415030518a0343e60302101400d801c1a2520b12070b60780142415048a060010201d65210304006090041035241c01c500f44843c8080350811900d0402d00c4950712911550711010402c00300c2d8142031740d13031440c0c3d40500c285503032040c40c0603009868010703980c41e04080441b0807203041c104101d801509050110141001550040f01026003410a900079100100302c00d041491a1a9106170004801c02442c003c150502441c85601d89459100340d014800c1042c1c880c00070442c8011310900350002d0320550355456008180d4107400b241540c09070501c0302400360140001d281880c070b0201901184881140c03402e065540e510070000d074403c110001802550084000080e01540c0d82c800904441c0103030504d54003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 729537652 1250 729536402 729536413
    0xf101d010509070201140903040602100b091b0403151d011e0c02070509070c1b0b070206030402031005280e0a02010e030a05030a02070f080c09060918030c0102070501180c05010c02151801020f 84
    0x40dd5121280d480e60000c0c1460f1568072000c40000700300190344556803000b803001c40d49880000c59202d040c5d100102660903906810405c8880b00a41402e8445900c42d48172100c2681c2d22214000005600901c3e0040c050b00503107550380e55501c001a4040021520403010806028107441001290916a00d116840081a0751010304150031080c07540540c240c02409080c00202160540d9400c002501003240980400d0015142074014081107000540646450444000601e026070f00c99002d80b049960481c030081c0b07d00b07a0305c0e400442d56070351500f80d940d4042c0201d81c800001f1540c18401807008e03008a8005241261402640075444060f903800b04031141c102c102500c009590f4070042e0350700070340205d8481684d529001aa800444d108003c0d62569103c00a000d10340054190040c040c070340c1c060f600811110413030480c014001c030b420560085c580e07070b04800284800e40c000da85040030340b400a03040c03e085002c2c4d02103403010340e8800c1040100491998103040b01d00c0d03904101945214510501070035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 729538902 1250 729537652 729537671
    0x40b090a03050301030b07090b071406011d130206071e031409030a0b070207050d0b0f0105150a030c0e0a060305102304050417030f101d01050907020114090304060210 73
    0x2c1481c0018080144007500400100340310602c0340040101414010042640d1008246410b1080e10246d001900303c0380180800062400300360407160410841c20500ba41307032a6540000340c15101d201503001c03a80a101440880f0220b1018048440c86800982c5518014105424040c0091781619000040a0001c2040d01981e880201e5214051540301c440c0c600907468904059041c0700194110540080103055568103101d00748000501a207503503200c40b1035030790700c0c4c4040c00f0014843d589109110b01c003c020088685200c3d61285002c000289455a461010300c00040d0130b4010650005c2c00284d01c0c3d4040c05000c14015000d200100182e1500e00007407180e20b41301e405039000d0504a940700b80e9840300014107100c0c000c440b000c0362041c2c10325956074914007005114040e071419558251031064001021039140000507200b4840012100d003405280e01e00410007000c1c0500400c92005c42d52512900d504842c00100200d00440004015540f0340b42410402445d0001c169903030600542003041e0007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 729540152 1250 729538902 729538907
    0xa0903110402031b0711030322080a110909010902040504060f0c0e032512051e0d090905131208150427140f010b01030c113012040b090a03 61
    0x102c072494507030320701d95841702c1e81c1c0d050098104419110710307a098000016501c848129841300000550003030600000c0241d00c0e0841c4030341c2e425112000400342c40000d50420781500d4020f003241d9002c1442c4e00041601d8482d54045420f0341c000741c40840303486444145100402902c2e006102103081145098a01461081d0000303030345119100b414140b041c40000810ba191002e10f210001038908400c07040291412882c02c540e9410f481c034404694500c50940f170100c004000b00d00d1484a072083c2d91100861828214800d0080001402d883d000940c203030720311400100e90142d684141c0c1c1464441009914040d100300c00444842460345204504c0c03d14000149000407001032051440e0740d5440c1c03100601c601e80f00c00124142c0d41d44903524841c03940c02c100a00c9054011401c10a8281e0301840071601c0000c0583d840c08003411411002e400c855000107040d202c40110a40780049101d0f29110280f010a8403551580121114640041014200418050041c4106d03410034220801840c01101c00c1e10700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 729541402 1250 729540152 729540181
    0x1e0614130b0114012303040b09060c0703050f0d0e150a060e041e20011709102a0201020d050919030e0301021308031b0d02030d1509020a090311040203 66
    0x103e0342641c1c0540120581644600340101009400030006061560b08120f6044035030400c880843d400d1400d07800190503100081081809000001d8480e0304010315035406481e1078020060304180031205020301c0c1000e244034040c3d0020b1a4111000d4094100084c0c0551050300e002411014a50b0800c0c80404c0807800d400305003580160461002a04240b0207500c2202000c41a80041c101d04000d80c0d51400c41401c44800c280e142900340c1701e482c00f0320308880751401102c004542046094000301c0101010380c0c440c0e00481c0c0780c00a54540c028500030350802828803850b0400713407400141e43c04182c0b010315255901c1502e402050304001424009007500840000300e017520b130000c08201c0c0e0300340b60703610b5a182501503c0303859440e038442091310342e00d48800583c3d9401c4454942001003004c68850b4039000f01041107a11095a64051742c5440d40c0701d40f01c10042d01442d4140c2c44000c240e03034400a81595070b480130f031000c200c013543c3d54640c082c614200041e006c4106842c80b0310a510420030b01c541c0d2514001d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 729542652 1250 729541402 729541409
    0x1a190b0a030312060509100e09010c090306090f06020c10061211060d0b0306041406070f2a080406020606210303010e0406090c0e060a08281e0614130b01 67
    0x2841d003c1039411060040181c121075212542140483c0300380654124000801c5080d02c0c207043e14210301d5130b80c1d010a1400e81b002c20f03270400081240c1c480c0c1030001c9041c4d5008502e489008031003000d689040d603030314201280e220b181101e5040d00240b0200c9902c40d40c07800303448014142620308861104103511000118000107071110f00c02c1e940050b0800300c82d183c0c0e40040c4c41450005003038461619150810300840710b640d83c000200740c0107490004813403c0c003d80040d11824815681c41007650081d45d25142c00c0c0341140e1a540e02a2441c028050000c0c107120001d00203084180d000d8070941c00d103401480558200060004442900a0700c040d41402000040e2411246c010a05881981701d50500d00000e103644003025100c0b89492101044041e21500518010038040d03500212603507803a10200d8840c0088400003500c080881c0d800e02d9036070a00c0d144106c805000d444a401500d8000b4540134441c04204000c4803007a48a0b105065004030209070345601c00000381c0e425449240c41c6e030b00d41603884414003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 729543902 1250 729542652 729542657
    0x1a0901081b2205161110021b01050438130c03020907020a0c05100c0f1406090d031103060f1201021306110606040b09040b040303091a190b0a0303 64
    0x5040d002650b0348200c1c458030b03141a07031640d91a9140410815001d80b01c12510414200b0100b03200e05145807180f80c500a04000d800041c10304080c4202610f0042d500050001000100c1c06e0b4031010400310a21610740078603c156000c4100f030381c0110b41030303031100d01c015a0102c958003102100c40c90444055043c1e42d1100c0c0040d8680e0406034075142c89040c0414a40001c0c2d00700c0031030001c01c0780c4e1940008132240d58038058888082030551702c40800c00b086424400b1840001c1140080f00d00003151101004a02da02c6165080907141300190034501e8a8802c4803004901c0d40500d56804107035805100d0040c22000380c0f90883e01c1c614000c40031451000e80382d4042c50084040d1000e03000040b1f400e5065418a41c9420500701555a071054000d11200714007040c00d010340141400300c0c40a2074244942e00301a5009031000459988035140e200c4002c0f0018070036001d05807a09031a00009401c26403507101c031036184203025a58188190b0024948951542d10b1729644e2401da400302480c0d8544074150101c0b41e151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 729545152 1250 729543902 729543943
    0x26060601030506061b12030705181c0204090807050105070503010608060603060f01080703200702010e030106030c05090c09091303020c01030908030604200a050406110109030504171509011a090108 86
    0x2c1c00032454038039409241446c5820204c140240030368084002c0c11420b01d00f17040e04803131900010030072284401e018440902c49070500a51001030405400c00b10036507005001c620304001003600c550382910021240b02c0000340c400401800200d40100003140c001c41e09590050170f501d0304002084507001888034085c14000d546000800a500ca43c02c05200d401540145070708140d0105242d44094001d20012404544010b4004070b00d0b080504c14181103a82007102038000354985010f0080c6400054440000302c04100315148981d140c00340158001d800c074001281d503184c010304009050280301030784941054101070100d00842c5071141074030f0700080210b074002402d0030305284910551200083c83e100c2c1c0e07140030038028202e0b9040000b61040710000d454841c0c00d000490b10040c2210f1102c40b00a022442c288024040019080d022142200b08507089070102041c8130b80141000104903921001d581d1070742101c415620100f0f0b81c00b00122000c1d5a016104d504141d88903403100c907000090032405a50303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 729546402 1250 729545152 729545197
    0x9021804050c2d09040506010902090112060e10080f1c03230402150c072102032b030b031c02150f04050c01210903092606060103050606 60
    0x61041d07031420a001000d40f000b422980c1c00d010441202000714184080894550840b2030402080c62445203602034040e0040380e08024040000f0342024400c070303040003480b4010510039022445600003500f400d48544110b850721203000801d1141e1038001c92420b8000207400c07030301304a000942100f00544030f0807500044c26103400403001009281d0a010903110b0044211709000443c00645c0e00550007502d074103220704e8403050360080c944982e41e912071413a8050601080348914034041308281011105044450250a0700000d14054040f5488081d219030f2105100028501c0a4100401d0240d8102801410b8a500000c1e1701c2d02102c0251440c00f2030050048407c0602c2800303c2241800c03a41210341032400c040e08d001c1944d000885007220f451242c0e81c41c551140d801141903111001c1c2750078100c4030340c01640110002801000800f01c0070b11403050400310b40c03000c45194044074962100c00c0d055000d00c2e2a0441441c1100c003070041418940b404040c0315264442c80d00702ca650060325420106240e20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 729547652 1250 729546402 729546413
    0x604200d1d0307030314160c0b07020a060608010209040b010f0c0303020c0c0904032a1110020f011b0207090903051204030504030203030a050c0f060105210309030106030c06021009021804 82
    0x1c110203810350900000500c28105605588414600340c1e005450103c956180035901100c01604a8060041180070102c2c100007069075034650f52180880c4107a90160b41e8941c0c034002520105c0e00500f10303994000c00c101c102c6040a01c50b100d40c4440900e0561001128101c0c068101035a104003c1c00300358002410701030102e41082040d1204002400c2501a8078142c01c00030560281d4914020170f1541c0e4569900c0403541030b00c001b0300a80d030006401d4004540d44402c1045920884025038154040d112003040c00303000a10541c0210140c0403040d4900310009a0000d06110743c0303421000794a03281c00711800c080307a40003094501d155002143e0210a864078101503820f40140d51000354140b0000940c0c00a5603400406002c1000041e0212600f800108241a80b038902c24064140c11402c0700c10741c42d0000c504460200c001c02001c0341624644814840401c0c02d5551b07541043d1880b1180703003010450242d040014104c0e080c040c00c800c1100c1607051b030014040800b8120240003620000c00814240035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 729548902 1250 729547652 729547691
    0x2091b03190e0a111203070302030405092e06020d08100524040b0702090115080a0c18090c0f0801080d0807050417060402040c02030901271701050604200d 68
    0x120030003c48440307210519241c885000c04150300e40c022120003201038410301001050301c0c0c2c441d626070003440c105030802c07062000c800d000502103054413111003910040f6030000e8688100c0750003032500c0302c203209083c91006450304e40d40200a4080100d410100140020045043c0e402da52044804c7c3c1c42c5182124003034a04000340c3c482001c2d25071310004d400211842640c0080c000f451007503400389010381c1da6004c1040e031310f20f4202110000c1040e0b20001000160309500214103000c00341045508500065507908042481740c005001c40c0d65102030070003600340c001070348411240e49840c0055043d030520000c41c1d180c02e0b10b040703010700b4800402d02003401c1c10b0045040c3e40241c80390600100300d2005010075155611002d407400d0b03010b05d28024500d5451440030048074000e02c0184c40c1c0c402c0e01140c0c0c030840000c0c0745400004e08aa40ca11281c013180ca5590544064071845c5140004140c0e41041d0b01080102c602c000b0300447c0709520784a0142c000301d03521003a074503141140000080c403850498410b0002c172 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 729550152 1250 729548902 729548921
    0x60c0d110c06090d0e011b1718040e010507051c0f0e1b27090106050d0323031303270902071104020408121e070f02091b0319 55
    0x1110301141900c212140060328510440306402100c8075070306216000e83c4d95032051046940010100c0020020108201c400950240d1103855003601d0700c21380000c120044d0f0010b00c40758801101c10360a16517140b50900443c940d102c40000208a175050031000174286115400560308032590560500d01c521340d45600100c2c0e4101095000d1000c500d49006440d1a0300030b403801c0301da5151144402e01c40c941401105c0e0f449050410000d10b8610b02107000410200000410f88410342d901d4241c00302c0c40703843c1e50180ca01c079140709455110408121039278076007001074031308142103044a00744204142140f600c03100586290301400c00d8500e1018200d5146001003803001410003110616400141741022b6134001e00da1503005000300d001c0070000508100903441a4400c0c5400396002a103448415a401c800401e00402c5a44d00078074924040041c895580c1c00500050303031503c0100d1004415424076010300ca41c4400d52004040b2481d5910040030f942e4003003d000001c4a1480981d6454181210b038448a5007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 729551402 1250 729550152 729550181
    0x200901022509090f050f07080d1b081602030709090506060402030a140103050601081005130204150f0e0a0e0f2a060d05100f03080d02250b04030e060408060c0d 70
    0xa00c43d2070504e0142c0001410080312540b0407104410107004020842c3c1c1c064900780401780c00d00c00e2904400701c400c041020500f21200c2680d15114001442400043c80b02d82c0480c561f40001681e90300403d407c114056000c038400d1814041e075a000035034082402607015404407801a20703601d80092990062002c20004d022400c000e1002005005000504034125180002158000e0b16400003080a41e0b10a943c4103c0140c00140d82e100186425000000d802407030309203000b4210b0340d0f041012a041003e03841440c070418980248000d100e403d00a4030000d21510008204041124681a07038447d82000701d07040900c9000200528481c00c0c144010003044018006074440308290040c000400099440460400e00c4039000a10a2080025001200c0d045130016081c161050044406584049820403080340d0306109080d89084550000041724010003290507985803526010b030161440d1603c1034402e80040c0020000301400050003a4450301584d1190703151041410b820016102c10603040b81c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 729552652 1250 729551402 729551411
    0x3050c07051509010501120503090d1403030c0c10090816080d020d14070f0903032a03020a0506060a180e030c15070806011805120a05010609200901022509 68
    0xa02c0201c200030758000c449101c000c02039a640ca12500f0090444440d00820350b400c140a0070344140703024840c40c00814002c44000740c0011100420780d0456008940200c070662002c01c0540805000b005035000e80c0d01781d500d003088078546a07111500b29005004040c40c1c07100a4680e01810019090103540340d10705508019902e4000c548608006400412580454642c10400203080c040c41107140e440540c1d42501c64151540c1107032801c6594408110707142c0440c1182c2480707550710408000207598020300a501600d5681450301c0c05134108030010301030034801c840d4010248054141a80c0c100e0b2034401c885000184d034250f1a00040c21409003120440303030b901450044000310490620303400c0c450542a51800c03d6030703498500550b4500c020040d03901203400845000e00060501e006115032144001040341c9458142c1e0b9501401e58141c0e07005001403a40b5000786d80302e01902d00e40103017043c0400c003050034209421400001e50318411440450758414401280c0d520b5003104900c02d4010f400640c40920 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 729553902 1250 729552652 729552673
    0xa110301030206071a10081501050105091c020a17010c0914010f020709050a021b1605012607030c020f0c03060615070605040507031a040b04122a0201090f0605070303050c0705 77
    0x90380c42d015200f1108203004142400c0300234030904581034181c6405854850074101504140104024007a8240c0b8040b600c0e49004400b6030303102c801c3c0138000e00c0021483e040c2071800c00015401e4030207001511007400030a48050054044940c0c04491440c0280307407940c032480040104a03d41581e6074040010140b4101c28040005100d40041c003403a514842e07518010860042e645940f1014003010b0f5080040b0030702c0500c641c2d8407502c0006c4142180788141030032014440c101d0700300c0742c0060f686240400e5660340806a2030b9018415444210f4428010b01424a518804251070b41e030014059840b4000b841c01c000c40001004081d00c040c01d030044404c2000e86054600f081d0340e140070340010740c2c2072030000e4040c0050b007011012003445690b02451607801a1226695402548103035030852007489040003e0300c8212140b112482c0169030b100880d0b07007258241d8000540548515000802000080c420a0003201d41050840d0b00155040c6800541c070354500b1104515802402d070010000d01075181801c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 729555152 1250 729553902 729553921
    0xe120706030b060304110628020a121815031b02061e01050f04090201050c01090c030c12030203040e040305160b06040e060105100c05160e0703050a110301030206071a 73
    0x8420348895880400a00036003404101050000300d4005080700e09256002016042510181401100c1065000715007283c0c00d01c000904503410348901c0050b03122040c2013050060b810500410b100c2d0f981000380002080203004d02d03100c60140504915500942c01581c8010301c00c0d44002c1403800e02144000d10040200c038003e40310740d004d98280040307140245061300307400807462005049500060151400141140510001d40a200ea0507411b00c0070501000d10741a0b801c4c099462500e03c01d01074011503a0540c50216040c501c1c94120305000c030340c01c80b0303150700080c1c0001c111020344228000d013140c2603669103001c030f80c18460b4008000810121245801c10440f80c402650f0150004480600079200804c030401d540c0c038403d1180daa84011508444032105020300c040340c501e0303402842941c0c0c1c00705000111200c4000c1035809002006441801c00900e560326209580e040035200ba014407a4450041041c0558001800041e10507400001c4500800120014085080c00c01c201c1040303161410340c2d0b07030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 729556402 1250 729555152 729555163
    0xc0a0c0c0f0f090506090610080a060302060c0a1401020a02030a080c160b0609070e100302090a080105010303020606122418011b02150f0f13060204030b07030b030123070e12 76
    0x9002d074550900c40030a9171450000c14003846540d014080c498002d0402c0070850f61100082c00506c02e0303039a0f541001c005078a66200038054070203040c00500c000940d5142008195005107000412a441030007080703041e560100c1151801003039440e19035240c0e01c86801c003500920480c1c1003039410303a64034030141c1c08001d4020741e5035124040032036505a4564844c101911119010f010480d800800d81e080310310203d02031b9000c0c1c00d1000004d030212548988603441c0c1803c586082e0000d40160b0b00c564200503852a180301d540c042c02c01444003902c104000c86007100d59a04103d0440500c5283c4080011a0503019a1412101e0380d0014001e04c0800155104120110300c1506000f0050043c0c540f10314103521410310f450f0141214031080c0081e07654103040c041e4038040142003c64125001c0041001107003184c0060310285008400c002c04505002e0005412110f1078404a40a80d040184a0300f804010000040c4100b400103155249565100c1007101d00300010100e0780d6003c460f0410713500c00303030200242 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 729557652 1250 729556402 729556409
    0x14010e0a1106070b160309021e03070605040e0f04141e070b18040906021b01020a120c05070210050c010c020a0b0a020c07060309050304050d140c01080c0a0c0c0f0f 72
    0x414605007074848080c081d0720b00c10fa50025100701c00540214006000914080200003120300d400190041d140e030000d0500083c0140c842c140c4002c1215a0285142c207101440003004a410b000e845c05150400d600c0d50300800820f041c00c8100200e00050600804c0d0ad101f42251821605440903003041400702c500300c0f50760075a89450b600c1000300118200d070000d0300b114101c03129140100c0c1010300742c1007040040d003011401200c140c1d40902c9131145048400c40708450000305c503000903807286200c0701c00815000007030000059203800c15160000700c0303802c5812986004d030142c4154580720310b08141070f500d42c4560040c8440070f61a2214402c40d060b40410000c025902ca80e44031882e546400b5440341c00d0f40608072503140c194100c1201044441c0c000d43c8400360b4140b045050b641001d980300300142805000000c107807178421b81580118056031051100824080d42400e00528a0618500071801030103040911001d2203228a0014140485112448010320700f02c40c005101644034400403801888510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 729558902 1250 729557652 729557663
    0x52215050603030a0203120c07060c2d121a060a031e06050a0608101503090524011403190f23060a0903050d09051c050306090c030414010e0a 62
    0x404240c0314035000c02103c52803004d9034011400d01c00b81e40c15100344100d001c1c040a400040402001001602900440f88941513944915814070800611600d41113a0b96a4018004000c1031841001d2074011000d41607840c605a00014481c640289051420500c400615840840842e070340c9144e13540f5812496030b1200b5440c280c000f1b5810002644c050b240c0c9405001c0d40041a10406d21619100f0070209074400c0c1110090140750341d0b91503080780401740c40000d841c00281c446c1082c00034450100104420541006d00046c01c03054922072a04201406002d41504142d10241102d003541d402c210084805014504038008040c95140040e810040d42c001200c0350b01c1070600307043c0151422210001c54103820009003031140d450114100c01800910310440c10f00c98240b04000303459070544a64040c69100e24001d0030f812140c40f200d244520038101402041180402c10443c56840c1d01d40a00d411503580c0080a0712a1210328118070007094810303e090040d0328103661400034000005084000b1400740 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 729560152 1250 729558902 729558911
    0xc071b090b0901080a0308250215071107090b010201110c0601050f0d050309060304082206080108120708180306130606061704110f031212060402040315052215 70
    0x8410700c180c82c0e40034030035031010381c006400603400300b80110066540052144400c2c40c03421484045250504090540c5500690020041440b0012002020b0741c01c04158103100d44ea903402607605d156244030781e000701e5107415116680c482031a4000d40040c0302446182c038134144c076040d102810590341d4800740319052080103072000100c21070800420610a580d0000c000c0e42c0390508500600c406644098000c172441041004442d42c08012248690340d0021440c0d41d41142c40e03d0101c004184001c186c2110721150000c0000a52452000e021100d10320360222200361140d4100c0d81240180c1ca80200d06a05406404200710344110070314245001107104603001c1000c10749402084461121415107000f0402c1d0f03200c0841c0102e00345501c2c520b64060010b006102c0120350b1401b0900382048c0d514003e0007201c01003035140103601110000c1394000020b99045003018603607128500c04103c41c205141119583c0c83c0440d031001d041c045c4140f180c000c9109418001c409610b8003100c1c41c001c1c03040000f80c56150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 729561402 1250 729560152 729560171
    0xa03050c070b090d110a050604090b0f060408150a02070b07110706020d0807030e01090c1409090c0d02010804030504050613151d1e130204030506010e07170c071b09 72
    0x700e2003034602640020b4944400d10045a0704c482922090b0b15a03290b10650901c6e000403940e07a903400030005050031102c0480c07441d0a1038240840c1c51500c0405504c9028148824008801d00242a41100c1a5000003400e0f0b52107416070000240b29054000e80449400c1c03081101081c1c00c80c202429090b9060203d030b540a41d5008100c1c2c5400440c401d40c1c0014502101040c1c00b18800c2c0c1194840d4800400009903042c2d1665412801030101c2c0d200d0024000340745422101032520540259120161801600134908034600041020400c1200241800245408030f010b05100d0b8090b14046c01c006440b8990f10341c1000d0304910340308034a02c00e80420a10410a405400703100b103117409402c101c0e012000e44401c100108026a40030b141094031402c51701031895510360f0381d80390b106862200c2c14510060b030f5107040d4242281003040c146c2000c003026250505010100ba44a040309000321208e0100c4851500c590382e0b0042103110f001c0f00a80400000711401c108114502c850301c0455070640d4041200001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 729562652 1250 729561402 729561419
    0xf060a0c080d38010c020102010219180f0810020f0705070602030d050c0a301a030105180a03030c032a0f0e030a2a080705030106051e210a03050c07 65
    0xf284060340d520110b00141d01c2c2c4035500644524010720320500000d424240c1c2c0007a00b980070b06d04540194000341318071010f070742c0f00708034034000101800382c3c0070045032003a041c259241e039102c801c0300700c10900c0c0e0743c009602801c500304602642c86d580d5001d0103941c1c2113035480100940d00e400904a08848601c1d010128080380b2001c401c50305000750544507001420b00240011200c680301488281c00305c20b120144a104da1980d1040e5450300485108000150003140280b500711440103088030601c4c0801c1070610350440b00014102c0c00c850345460041040d0700040001c4000c0c000f40050114440a040440429080301c449034280c2109540e80d18511045152801c8602c044031201c400d425812011140340403d80181d1078503c036215070f13061060403120b0f041503001e1041140d80703c02d00d42c0d08400310502c041d00c4c080c00f070300700206000c80d00c869690603d5002c84110101c40d80200b8412000c403d80c242c6504014000c028900c2c02a10607580f4425403810702811541c40b44801c40101e000350900400c9504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 729563902 1250 729562652 729562721
    0x210307020d0e031018060b0f061b030f0703031d12040909080408060421020d050f03090f030a0c05060124050307030f0c09030203010b0f0f060a0c080d 66
    0x24254024000401c0d51002030300d9440601c081c2c41d400d4058044402140510781c0079131541090700c0900301c95030b0151802c1c0075040f1003002010070311071035404514542e2942c6981c103560b103c94000c01001041d642041c240c41c81d43c4900c034600003036044089001000e044d01984104030010100c56080b008040d4500310a0700c0300d081c65402851100180810f0000180d2503010041e114410007040745815150041545801c0d006c0364112508212503120f00340a407000684403034440c01c180020100e151404101401a0081c261161032464000c000605812400c00c40d4200d8a402c440075656a00c24034240201110f00300d41c0155180c3c07140b5070000842c07000301c2e90015078140d49462350641140c5140380c1102c590344080c02c40c0e0301701901c40280000b086109e104041e01007402d40c807111541032840c030600d42980c0845102c1072041555a5404c081601c1e40442c62003050b4049415a5a5482986050302c240c0510322015007684800b150030a81c810071580500b004500c131010656aa1250703a82004445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 729565152 1250 729563902 729563911
    0x150301050a061809021318210207140d201302360d0c0314010c09090b0310020c101401090b03120729090606010305010f0b030105060706110c2103 64
    0x340c0b8071b1000f451040c130903501c044d000017044ca6225014800f180c880461074200e8203068180500c00002c1102c0e9076070100510402401c03007036003a04054600f4800140e06c02940072000d001f0484218000003007900018980c1040100100000070030442c000b4000c0c0290400000301c51040105904241c00940201d41041c070b004800389460b8448070070900380181c0c01881e042c1142d91200900020002803441c0c10151600c94010000140c140f207d4080107059422a0344014041c03031501c0d0395900309803000318003032840342181c18015a07100561841640303400e81055100125074070b41515120f010f000054082e04a44502c0010700190986e081015100d207000400d2a40c003080802c0080c0c002002e00c181c1215054244854551520310800d258034407280461b0b800c010b982202082061541e01032142c01d000d010303400c0310301116505200d1300c04998401800b5a600c02c4801043c103404200942d000b085441c54245103d9445140d40c08640e90340d004d0104400d00f0811078000c0145040c02e680c3c0a40e40b05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 729566402 1250 729565152 729565159
    0x40204022203021e030618030f040b030601030b0904032c030d0507110303030c07060b1f031d030301180b0d020a0e10050f06030105120a060501060c05150f0c03150301050a06180902 79
    0xa5440c7c21b914854180446a15030011340014406800c0e5030030358034080c3c0000d240030700000707170b4a107851300006048551000c0e0040c441e8144c0c00a00021982c012400030341070341c0000710000d075064000115130f0310203c25241e0540c0b621800313500f01e504c190b112003e0011588186031080100890008154490001b00d58480c0d03005414003d81e804070303545412040c005107000c2c204000c41010070f12300302d034014403d080b41400b00e40c440342d401c1b00c801003402800d1610000f01d4051400c5505000300e8468040b40308034804c3c1d13450f4036805140819541c0c1c01504d03014507401491949904d641d07206040304020100c0c0d10b058a50701340540000d45080054510000400041c80ca40c03540e800c0130100039074115000c811005611402500000060032481210b02070441c0e0b46500c000c00200e8a052031902c2403012106101c0f001c0c1d50f007800000b110462915420000050000d9100ea480502070b20320b210321580e00560544c2480300b801001c070f400398010016034040749145c1c1d40d42d4088065040941e1f4a44100030742 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 729567652 1250 729566402 729566413
    0xb01050306100e0604061d010903050c040e010e0a031e03020415260a060f14130507022a09060301090b040209130503182107030b040204022203021e03 66
    0x32031600c0da00110260000d8103103001203e00c4100402c00680003600030202195200403400d140b1a000d40f80700c2d201550902c1c20540450859070780d40e031034140046d207840c0100d4803180c2c1114111000e401401750b0a445208944400e074041c200109610040c3c1c040da0100b1000c52114050140700e4001c80e0b007560f00490300d6003041d41c0342d20000c07075011100d84400342400500e00c082c049220030b1000843d009441801e000314400303081c8101d00807218940da001520790000d00502c0282e903191030100300108501c3c0c1d407000489554405080e410403c500801283c0480c3c19602505884400040200018400c1d174034004d280d5500c009041c00c9a0700104060800402c807800a001450829881c9900131100b00340c01c070011001e955a01d1440e08811100b140d10398205a22400a080902001c0341a1811565296010303850195940d101c2d1641c0c007014028007201030004040d5292501142d103c407101140b4066020404625031080038110301040384a035204401c240d10b110488400f240c0500801805010b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 729568902 1250 729567652 729567661
    0x1022104051c140a02010f29090a0e0a030f0f050309152a0c0c01090320041404030c0c05040e071806050a0b0d05010b1c05070201060e0910050a0b010503 67
    0x1503541c5410140c1820054040103880c0e000d540200602503e03a482d40011580c88842c1e04c1c1e0905549040d00d90362130043d622607035400780311060203002030317100402e48406440350ae9243c1000e000c1c0c1064171800207240300b07843c028000c040e84107483c003074100d0065030742d950b04038450002180c0c2da00c0241c0d07058403503a000d01c080c00d20700d00341e049096400107a19800c040030314441c1c14481c0208070752a180614100804602e41600f410f05120115904509203800c0a40c24116911141c100001408207200001c41540c407502688850384194880441d4030040081468245001890b480d1685400c40302500e000b400000d050401c0d014448040810401501c005030805240619400741c00c40c003030140c5900c0320b0f030010700c3d5141c10144601070020b1101f8a640d50403070550365421b8600c103a0021490501c20459100c0041c0c040440d040805000000804c107500c81c404107d01604a071f0704071721046050356040c05034101c4005640400c0392040c0e50103010660b42e4040100495a402c0081400f1420400025 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 729570152 1250 729568902 729568933
    0x40603020d120314130c080a1e1106040311040e16050f130e0705090c0a050a0f0c05060f0711010204030b01050603060d1e110301021603110703050f0102210405 70
    0xb00c2e5031039661400003606442c000842040c910141c4040c200c007003c959090302807101d00400c40c0c015017a0b090091404070034030f5580341c5009604a06500a41c040840f0030810041850015040144001d00458640e43c1740c3c2019a81c0142c01d40025220303d1418540d8a0035200201f4440c075040c90314031000d25910701c0e202c00e0040e040d5140b051183d212200a8550324603ca03548102004c240b840740c0240503160816050141e40c000140080c41c8000c401d00402c0603041c0e00500312646a4081c2c03034405c00c0c00b00c00c18004d0300c00c00342c0b12000501d40d01644003001842c48000c20800d110b5101a41c402c0300000520110030300301c1c4903034000a4002d24986005002c1820f091000f517401c083e010b42555880440e82c0c030344081030350781d1100d94481c4070780501014040c400c03061494a40c01c1c030101d0007145400d06200c00c4040742c03070941c0c000409100d0a8441c500c410340301404003000541d08030050320000c1c0400f01040e4004d601c06510030b80310000c050b1b030b011110004c042d80e45208503803000c024003118a044504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 729571402 1250 729570152 729570173
    0x30f190f0804420204030620040320041d10020702090417070f201210050c04050d05011d060112030c11100807090b030c0a0c050a02041805010605040603020d 69
    0x340d0065034100e1440d4107005001c041c1d8002420743e140d0040c0c80301c0c210715010094038104400c0364012440d0a2288482c8442d42040b00e0071668000208010200d0307841e000941c03614201ca0a0707601c5440c02800c400e1038240c0700c00044402d040ea900350303a013070381c01010904d08a0203600f90180d003000f078602c001340001d50412000015071300744104c2d06003051180e5544200e0000f11510841e5002e0230020001410700000c4101c4044101c1112000c81c80c00d0718580c43c83d903d00304580404405a03c0d10041024060004116070103000082c10781c0c500f00c41c045c140507011704090202c0d00001d8600420300305d280300000c90054180d50807080384c4c2c076201d44c003070320708480240900100303860903608510320300300c40d5442480c5929544d56a89848899140544020740303003948030f501072400003008008000501c1030402c2100c084000d01c4c20f00c4910380c441da0801626100c0d6030400250050715100d8408204011564400d280d01d200e0f40007400242e4692041c070090b29814400250094960381010340040c404118 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 729572652 1250 729571402 729571463
    0x807020d090b0c1504050d110604020f040b0d021005090901050d030c0b0411100801090e16060507031403090604050706050406050702090c070c14180103080409020c030f190f0804 78
    0x1113490030014401c02e09006001038404a460340c2c4007000f90010316400c02038802501c000c010242c002440c050b004640000381e4405440c0c49199250410402030395a65225500140c010300304258030341e18414054140e92005c00a588104090000001c8070302d020007448081c541d0554808590040c9a40c4e107540c1c009001c3c00c1128120301d10700c0c0705080e58840080c01e4200440c181e484003040e5140030414804c4510b003030980051a0482c0c0509030039070102d00c1d014011202a850040e95644050404482c2c0e0b40b0500c4c1c5003108154000207001070340328006580f43c0924080d800b41e41055942d504260703682e22a43c482d02010072001d005c41009803506039859540000003504030340c580721040d43c170884c0561f21908803074610301c0f500b45212042d0824642e0b07440289100740c0c0c6414194115110030160303004907c9001c12640c1c00003046a104001801512803031401070710100c2e2241c4d1140707221504444840c03010000109000410900d00d440f85001034001c5800c000582c09160380c540e21305000780310655 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 729573902 1250 729572652 729572677
    0xf0507120801031a1501050903010f020c0105012610020a0512040605071202070201050708030403050403121128020127090b12070b030a05131406070807020d090b 71
    0x10422010501589115031046100c0d51901e00660444c940304001100741070325040c948000741c0400c0340d068403a80320510f4142090070b04685444074031000a01500302002d0701000d003400425418008081504030301c1c1070341c3c0b0280d0180103120410301c12184001c200003110710264031011040c60030461fa5401003100010a00d031580c07500003507883c085240c81d400d40d0215030680d5580104000294400d5030b94072601401c001c03d626050744ea400013422400380d5003010348000d0001003c5030400d8091001c840041d80d021105900c04c8900050140c000c04880c4c3c5a250349005034200380010066a0303150546d408038070a1046240c009603001111074030301102071540b0b90f0007900d006101c04043c8901c0c25004151000002c20041d841c3e206000b000754140c400e00351958000c51040c0f0980c031754081541ea026466200000d656a15510f440000c3c0e482180c000e00300174203510ba81245240302140141c880c6055440d20a00ea4035048001c907940c507000711102c40016180340c1c0c00d12100d00b441300100040e80449 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 729575152 1250 729573902 729573907
    0x160f09050603070503090d0504150e040f0e07030b07081003110415081006051c14071809291f090204080102070b1e0c0a2606010e031603030f05 63
    0x2400400c00c00d62055652502044c400300400c041c0d80340400c01e60801210600c2c05500302464207800110040120b4610000c2c00440b15018035a03840b65404644841c444d924140f01e60414000003e807103d0700b0340004c0c1c80c41c01103600003c00d0103015080403801248031341c103800d00003859038903000c56543c0307452813013548140c85808507405410f4000615024182e00c5010b00000c41e0911521000c0301c481d42d0006001d0144003031102560404c02e044030801035042051070190000000b20f17a4207022054220b022150302d1020710008012a42c0c2c8640340d594460008a640d201a0310000340890740107449001b944014100090900c1c820038048a00d122009011144030540341c40c81102640c01c076401c91200f0340e6000c030300c03081440302c3c9501060300000580555100107500c445d1800d0751440051010035038507000100303440124400c0340341c48044011000500000c4d4500c440030001403800b929454006010500400714502d00440e10114600c5c0c03c04e0540c0c96a031030b55030160341001d103070074400c01445402d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 729576402 1250 729575152 729575159
    0x5180f060d02130e0610051e06160c1d1e0403180320031e07090c0e10090e090f0303060904030207080d030203100e1e2a04050414160f09 60
    0x38068850320062210181c52a444d000c01210031b1000d49507c55482941100d0118585545071292101038000c1524043e50f01c000b9200f24683c10100c0c3c5500511008030f50340000f50000343c21568076044005010701080e0307078a0300d42c1c0c944400313501c08180e1040340701c0c2e100100d0006801a90791841000104011803030450360f030380724105842c00116210980d040700141a05603480c040c00040742c5180e804000a010003202c0360826500c0c3c4084c003a480c5403030354454160307220501401010120580080129803081600c0341d0003017100040d442103114060004020880c125004604d002035990701600a50455846408102d400352003d4825001e600482e000031652600074010701258810540740581c0d00d00b0220680002e04640e540310420b00011101400300080c0764032070a00c0405a8900c0d40c079002c0d21800504040c51503013481181c0344000c110364107003940084401501c00c50300111341c01c200d00301108100d045006001c6943d2040c0e01e0703102a0f030003c194041d48100d2a004071a142941c81c03d0344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 729577652 1250 729576402 729576439
    0x61207031e0b0f060c2107210e030d0c0206091201060803131202010c0f210e13020f0715180305040510090e0a0c0c120905180f060d02 59
    0x200956141c40e5107803260882c01c030354242600014140d260030385a403071414400208280d00e40300a4194103690480e5403548071801481c1d0740c16a9802a0044120000303010040c01c007518184403202d4440200d0f80c0d0140ea00300314076001c14441c1500c00c0c1e0f07444009000030940e08102550b884800d032658000404448002600d10074440c40c0050301c40e4400450781c038100751140040d4000698051075242c2e1060000a0050740d00c420200342040d4402d410b2007116519142050b020200903001ca5555000140b0700c0002c15441400070414031002d848510100c65a0314290040e0710602c01c0c94081070008008240000b55a0202c10994820401c000110050000510a0341482c12081600054000b04050000c2d1a1159044602c07a08500f40a206140391210580a10343d0003440511202d0b51500f4440e07400e0b00402680701601e40c00f424821803040880c1c1d0142211460b0300849010703030b0b81c101c842085541c265030124002c4140715242061581c6180400881ca188080100e17005240492803140114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 729578902 1250 729577652 729577691
    0x16050303131406040507091e11091905091807081504060c0c0b1501090e0901090c15051c0f05042001031a041802100905010807030b06120703 62
    0x8119580c003501080d0a0800c2651207908010b000000c1c0c01002c288800200005602c1c01214800c040c00300380e1910302c010044100074203000f0401907038205003103000c0c2c2110301c0c2c008010144007102c5502101c1c101c0c04110301302c00c03010b01400d03802c10341d824089015075010810748440712014604840380700340c80e81d2403181081c03890358420740660100c00c24001001000d005030062402d641c03801d02d0000200c1d031221b40d001800a003c444581545807068002640700320713060409005044004221400c03c80e40e01c500a041c001015940d401c0c1c240004541ca23008000c10000305601c0e43e465071f00b080c421518031900c032040b40c524511110382d100c551203000709803801800c4c8610702070821104181305410b54a91511036000d0b609042614107800640e02da04500000882060141d81c0014a04001c0c01c80f0340303038840740b00320195103d03001206080549a0104020051342e40c280d81e501c010342c0303500009030706885002e4a600e0740300d013041c0030891503042d440101c2c1d83d100c095442c001c22190103401d0f04010030b1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 729580152 1250 729578902 729578911
    0x507021513230c01120207050c01081f17010f060501170c040e090a0b0601090501090e0c04090e07090b010e010f080a09020a090b180105030c090a090218150409110616050303 76
    0x80c0c103c5881c5030102e6070030001c030078030000c00100c042d494031440c1d41e54243c0b0782d00c01100b014144159080818401c01d84006481200c503601c22031000601d8031b400d40800390141007a9420303155800c0c46a803920f00045805a40100c840c113031200050031001d1940c0b920603140c000c0c800070145600b0b0000003035140240e20440d02643d994000b8144054003400c0c0039040440040400d4103001b108182004039903031142e84802261004811030b80d0301d440700c5254140a100ba40d2000313142c41c1c00c0252400c6032540108a040417103407011010007900360701d1401920751900e01205c15000c0340c11104540011030090051507401070200d43e00041104096001801c0d8086a400254066035140020b0115040c00b079820001c0c00e01880c000c01c1700392314100000b5981c041c00c20031503010301807000100303401c0031198115100340b640c01071005526591049080241c6042104c0103041002c01010340391148c2018428810090f80101032011a0f01c110000d000866100c085100320b84880ca11040002c611f0070300285018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 729581402 1250 729580152 729580223
    0x60721050d110910031b05070602070506040b06030f060601050a0302033d0801050903310810060b030f18031209010e070803180d0305040b0d0f0507021513 68
    0x701c1030380d5400e10500a03520003036907091510304500d81c01e0220480c03801444080c01447d04503600c900f2407500b40e01030b00404000400c1131103082c060104110101808911800c001c0d01103071680168041c95641d6148240e03220303404500100400c4980c548aa001140d1119240c2000002d04202e0744005141e00120410222840c040d48910610407407548140d00041c20b0b06002889a4140328050b00e84034030645000a1180340c1c3d0300d0040c8080d01c10240c030070142c0a40882030041c01a992240c043e11029080c6044901030b2804102144103020401640d0260b000f0000300d0308103030342c1c01c804a0311110403005160841c0c070007800308418a421214400e81309180e18400428010031000351645001d2150308060880c0e0024444007103030281c908050f500c405003c44580302810f000d81001d491620503900301702c1a1003000500c18242004a40020041c103103a0f090422180e03617003890480c2c483c0b85007800803141d0f2000e00041100c40350055840e500c03440c002e600c0480b1015031007801502c112504000003e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 729582652 1250 729581402 729581407
    0xc18070e0d0c05220b0d020a0506031f030309060e0427150c020703050705030a0b1906050a08031309020c070b22170609070b0d0531060605060721050d11 67
    0x1c900c3c600d170041d42000b550944442810410550000b403400200d8000c0900905000c4002044001106110502400041401403060361030381401400d004090007481c010801d03168070340446060030701c10a80703007001c016038901103860310030b0780c07800641d80c014030544c0c03080c407a200c100f1141e00c0c641c03259080d540c03040d80003410003901e94946a4142038030381e032000307100390031105446001c2401e12480e10ba2000e12803400002000882000ea001809641c21194115021120100e666100007004012542c860b915140d481039554010900fa48141c120100782d607007054008000103601440a440903007010051504580c44180b0302060360702c035031f038440da0a914004804502e00b50080c800240c1100c2980060441d9504003401044144203e010360402250741e1400108048801c249603283d400e0321002c8180000641c04e0744c4d4a001080030310994003a0b00d4484001030a1400000700d401c04c5901c03407405241d6448a01e90002d29130614048042800002c010202068000348940e8444d2010880039a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 729583902 1250 729582652 729582709
    0x15030c03030d02094905060a0c030f051005060d06090906021e1809220c062601090c12090b0f0c0705060114030f010203090c18070e0d0c05 61
    0x214a246540c0c00b229511082c20000000400e04060840d070008a041c03510011745552485041e6446a8016140c0c0c0a00d038103205009130107070040f14402201d40c2c2d0a100300c8000f101018100c0d2070075582601d07000020701d01003102d418001c0151206400c0b00b90001000c0e650b802c0403d0035902d403c03508540c003c0d40066560350b2003c00000c442c6c2404000c1000382c0c140b48440000c4c1312041504404a4841c1a0b018005030740002090301010074958141c201c00c80440140c503086990803481d000300f0001c030b5102c0c05000d03101014582e44686104003110481c52507481e08038500010000520090704009d5000031840300c4584a000d0701440030301c01e480024152903d20f1410118440c060490044000100001008184005041c0341592442000012102c489100083c9016281000031403a540003004005400401091180c0454404c1c1c4200d014502d40221281011500b15500b0001c28a101d1024140d8100380c034101c107801c0d120b01841c088203900c0e80d000400410014210480040d074038140f0300b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 729585152 1250 729583902 729583909
    0x5091f0204050a0b1e07020406080a0510110a120c2a0b071b03031a13150b030c0d020903120409050403090e07020d0c05010b370e15030c03030d0209 65
    0x11001800d1041c544c3c2d082c01c0c03842c209500c50009031606508100c9022071640c0941d82d131648400020712007141181c2c2ea89109103800c0c1c3d02c0b24006c103290180103203031101401091191000311400040d0a548402008491809080081110140c2e0004100780d600c00440242c000021305c408082a010403a0103140851800001c8060700030080c0c4204214210364103c2c0b04103510440000035070500b408152800000c6004c0c40101c1c812000960020703044200c0c0105552980c821031388920645a40c40c0025102c841d480d14a1009550710954a80e0400800f890303814035501500e0300b1007000b0181c410204030035840d07210a130080d401459100350f0b681c09010070140c003d40d0100c0100340c202c004c080d113840c08010281d1600da4081c400014400080410010800207500c0180c0f52000204011000703422840703510301141c028107000044d10303888035690140407417504140c000c0b50304141d400082c2c1c5c4d549809502044003031059064151107580101115a9800c3c805084414405040182c4818964080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 729586402 1250 729585152 729585169
    0x31803070b01081b011e0215010b070203010605100e10050f030103240b090a0c050d0e030a020f010605030c270c0d0c090e0c070203030706180308070e09040605091f020405 75
    0xc4d50f1030100b401003002640d9802818607010424910841ca05c1c41800840507420030b40c015030310583c0ca40700c1000100741820302c0c1e400b07090001d0094000300005622042401115821600b900d0041404070012040e0f500d000055180c0d4180b140c5080c6041c0101d100b4240d14641080e00225600310702614940300c0491240046c40d00c080180d1014030403e11990b003c5069508060303d0b0b00446921040590303c514003540849001e451221b004002d2804881c0c08980c03240c228009010060003039800301d030440c00050165030250790b030090280c020140c40000b000744411104104002d50160444548003d400b940c00480c8a5180d682000c0d550304107081c04241120300780050270041c44041c1c081442000c2c6901000c0703a204036408400707039454a582c000649140100f034801840d05060640042d05540c00c5250820610301c25112651103454400d8161500d41040c65510b4202d40c0803000030300030030100c2e040300350810100020384046a20b100081104001043d548964940c3c0004080040d400c00544 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 729587652 1250 729586402 729586423
    0x51203190e040b030309090406020a03060f12060501060503100e180a030c120504080304051306180c12060302010c0303052505220503030d0b040204180f060605030106021002031803070b0108 83
    0x1d1840c0c19446e400103510030b840034001800e03940c1c1c0031a030411500e00a500503800340c200c0e40010100c0d10f0742c5484048801c0841e800464166040100014065000304152802a000c01c8444000329040071424000d0b03000042250400c3c48450b403220285140520880c264580660740c0c10503188100d0030b1410003041049104000c0100801042282d968040240d40c2583c8046901c0d001380702d403420510380035000542018400400b0001002440c407000da22000c41e4100300e4031502c1411191200000403540d452201a01051300c000a15002030711a41c07029910000040e08080c81c05030341000c00e00d503201e41c08800b40c081003001030a40b2a0796a140720071410200100600341c1918102004203440c2d015481903c03121a84410040b481079841d42c05540240030302c02c06442c0b103140903030640c0c005484451030310038207a0b107041300100700300d8402c50882e8161146034006200032100052018002d5000608620034845a41010003020700e0910040585074000c0e480359400d5414040e2103400d0200d01034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 729588902 1250 729587652 729587659
    0x603060203270d0f0c0809060a021506190b0a09030b010f080105090c100804080403080d0902120607020303150f0a1410020d020d0815040c0302130e060a051203190e040b 74
    0x3c0c0301545842c3e11070500303a00d09030507140400a600741e03890203081c00c1c0159040c01d0b0f0322900215a48001070f0f400030b00c01d800d000810307155508079181c0600340006405034100c03207140d04122000c01d00c111076030500100301d041c1c4c2030f01e40142041da403a10b0f2a11f50000030307000982e014003005030822540e03100f402403d4000c058036014000b60342d40000000d140c081182e030303040b00380048500054240b0441000f52070086070854490f51303035400143e40620040021880c224030900d0500d01680300704d9000500380d8805c0c6d020303800840c6542c4820580300c2d1101010507045a01c0810f200d0309004507161122079000511400141040302034481c0100445421181b503032800f158420454800030503030010f01840745c0d141900340001c883d151110a0713403010b040f00480381e03041030400a07a01c85c090f0745540100080b90b40440d04182c8103403145d404c849207884c00c1c0c0340643c0c4a445c0c100148034910301291801c54007068001201d103096080d6a19400e01d5440440d000003168038030804003043c3c01c0601030384040c4034048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 729590152 1250 729588902 729588913
    0x100c02161a0414130f06050a06030903020d1b17120c18040f02220302041113053a0c0b0703080a05220c1e1a0d060306020327 55
    0x60034940301c18041e51189064044604514001e1034071620340c80015500f02100600c0030309515800300c005010244a050300070b02c6d103c4800106203101e8840c0c0000940d05a0180040c10700100d0100c801c4000950442e4010b0701840071940090f0a03050140404080c40e21040c1e2a0003400f40407046016004000c4600e02c0002c104803440041c1040c0302c101c14520880e400104a010601c1160090096029600c880d41d0a0308505818500413082841100c0c0300b11070504c00441c5203080f8400c00d0040a62440c4494001903080c4a2440c08240e420b4034584958080206034543c40c001801c07400c1d40030b010000c02002203005505105503c6500006082a54109460021550b400412500004048020490b6243c021410001d006002d400d120a41540c1c541c0510000381002c49961426109010102c0e6009400c00e00300c003c0d000d00c0c07808455506102d00342c4002d59001169840d480306200f40c04140d551100480016030a00c09513016124031485816085004846120142c403a009006480c0c0d005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 729591402 1250 729590152 729590189
    0x102041d060609011b030c06060801330e04290103050114130311102306040608190503041a09040c0201093201020d020306030d080c1902100c0216 64
    0x1d144a1045003050b0608982d0070345c40c2400c441c1304c00d5030040140940e00300f010010f01d04105412515122241124420b481006004024040e0700c004004107107212030540e08000340e03504c00758442c0d40140034500454844c40d0807460401c24484a014040c1070b26540d00060007400024415140004400d40b00201356042a07040f2003040300e40040000d0400041c0d2904200000f0240810303d480040da40c0c081c019071341540c02c0345501c03500310400500909201c100040251405003d030b07408440d000f10240562410b1880800c0400c401c512041d00c0900c002c0000044011100761841090190308561b9900d410078082000152030b60b00340400308680c180000b1001089041d11350340b140c2c040d6a14031180a1040d8410510b11600800a140d4254804182c000d200b105a400130742c801c44040341035906126030001c0c05d689070b1400340c1d41c1d140c202c50144030070043c04041149410350b43c01d10740101c0d480740078000c4445080d10101144040180c00c5001d00840e1900e1000c11000500031049040c480c8944 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 729592652 1250 729591402 729591407
    0xf070b0f09070f1203050c0f100e0c211c080115031406060a03060905041a06060c03030c090406051903140a050a120509090a05070f08090a0b060f030102041d06060901 73
    0x1641c004c2c9880e41c0c0c14040c8000c02c050096040b1840d41403030300c00341d505d03081d03007070b02c80d21744800303410a03904c009078101420814200d80219204000f85c0b402018810203402c50f0b05485950f0030110308000d018403030030710091049400500740301c0d613003051503840e06005e40c11b0954404c2800d002840c20703010f03d400e0507000d01550040d02481540a481510003d46410242c1c004401a00643e4800e55015180006000070b2080c4040b02c0040701c0d0003a001d54a1a0311020305200701e0b441492041070301c5030024001300d18400d442e00010700b11100d00410108034180c8940000d02d14404102030041c011001c040200104a4138035800c240d8181a200035101d03d01c441d48840d03031074101c0c0040c020300e43e208020420301001c0c010020386001c070f10003401040b070a01d04550060300506d4165001c0c0d0115164180320321080744030f0801e1503c18045080900250b10700740d614070910080291145504c808804e10304906610248080c0c0010601e01c039080060051303600c045003043c030300505000e011344000c004818450743c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 729593902 1250 729592652 729592679
    0x309020117061914280e0604110c0105090f010c020d18090e1b1c1b0b030c041d2a040302060f0702210615060f070b0f0907 54
    0x1040110724040340e55032500012040b209000241d8689401c0b03c03004079020b11800c01c0050300c014103544000e50241841000429560324541e01e008181040e6810300680707a12413503031504800060b10109280b40c40c0d0b10900c04980002250034480c0c0e540d041082880b640c20007401c541c4800403030007000100b188a5000b900c074081841820b00303001c1000d174001000c14088040d18004c05254004025034580c1e050403a0303c402007817000500201ca0541101c42c540f6010b034400503640c5c03182c0c4482c101e640d5503540d0483d0401c01100140482c0c1441c41d0002000104035000358403460700300039010b60b506d080c400120340440c5120004c82404c2a1401003000340714160210801c001825051405001e0344020715030541d1181d1380009410010105580034442098406400441c0c400c8400320803503404202c085d01040314807142c110320341d4080d00c023041a058800e8031030072848801a02d0f6911380200320b201c210b019031000e1800c41d00c0310300d00d00402c40490001c0f41c2c41307500002540e000d800105c0ca40b918001101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 729595152 1250 729593902 729593927
    0x1e010504060f170c03041a090c0f04020c070f090f0207020d0b250210060b28050d050c030105100807050d320601030b0301061a0a030216051c03090201 66
    0xc014000880401c1e40610321050b0050710350940e007001844c1440b103140700c54005450494808200807403100a2416409010703100f00e041500034034110341841d0402c04400c0b41c05a00c941c02a908005040306071005103e1031004e0078004d4800703440d5610b06900e1508403079000403401c032003a205000000040e1303100d130400d020254000090311880c1e02d80304801440380a0081a01d000e8610305a12400000c0e0003003002440f00042d0f4008100d504d6a84083c21070341c0c4250321403031400300110610a1800d030420f000a2051700d5103803401d282004503240f9001e04444c0b06685a091300c2d500440100071a2410980d11480b2052604e00f1501c07504008101402901405ca12030030004d0300c4101b11102030701800ca2088410f4100c4080c210120f818005502c200d180980784180020705240d0307890406e0805000c0c48045542d0f6030101c80c010f0003a45c16401064000940840806408101100e003580881251000c2e2034041d401034400d0312079004140e0140400c0e281d0b8407060500b8010b245004d40c0c0c01c21101d4509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 729596402 1250 729595152 729595157
    0x180c1c0809041d011a0a030b061003060902130807150c0f05030904181205031314030403020a1d0f0c070b060111070f0620061305100603060b1e01050406 67
    0x41e003000d64005070180a0418407100200d410000d0184040415044803041c0c11000310600380c0300f8400b0b801d204502610340000b810608080c000b0880ba401c00e5000c6030f518494524002449644581c3c1d044242d84c0030000c01c0143c07030300320368050010b8602440701000500c6121020710034581b00341c83c05440c0294018000e804001c01c11014800d000091040321524440100304000f4210118210034900e80780c80c2e004d846413071140707140703680c0c40d401602100c3c080c01584000030140f540d10f507242d2003105e0240c0b0700417010340814080000140c444006000150105c08003140c420218411260b64405006040341840342140c000d11117188040800c0b00c54a940003412501c0c0350340d62a0050351050340101007014580720315100011301100d040c440909440c5155100c800750b40c9008441c01d03550301a04401c8c24a44c010b400400c0200380303001c0d5014545803061068039659040c030f00d0094200e8080c0c0e031052707c096445652550492904142c10031280044004000b0b5664100000900a0103140140c005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 729597652 1250 729596402 729596407
    0x114160c05030d060e0709051c050c09131b050d03050304030513090c0f110303060111150a0b0a05181b090a03050705010311040e070521180c1c08 64
    0x4180d1080d2480004180c0000c1141ea850f000080504020314030381c070413181d00104030740118998511891030542241c038001e103a22407005c08045102440d5015202c01c03200f0741714942101c00b10b5110780c0041407040711100120310700780d00d003810030310a00058021484074410b01c0d100309100c03640d2112134400880781c05207406500d80e41c440c6400e545030b00c503000500788500c40151002410681c1034000e44910452aa1038000c1124040b5058540000010141c0c08a40050000800c1548117032541c0240c82000000c4442c40022603a0451a854003583d4900b0065203a41061803c0e04114010600801d41501e80c558004404c3d0480004094040d100095195452211582c1c605031001900c3c2c400348000d0a000304140e4a191081c0c0e0b030300349031203824080b90a180d804500205201e06540848225000f0844c150b614100225800c3d48064200d105004502100740a22507061b0b038854803d03441c00c041001459041d01c2d94ad45070603800c9005900c180848200301101450320300c480c0d619a58030029154 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 729598902 1250 729597652 729597691
    0x1e040f02010e010c080708130e040f060c030207110d020604050d0303060905010e2401030b03160801151a030603100603030c03080a05010602100b0604081504030e04021206010513030c14010305090114 87
    0x11081ca42c2e54081c030f540c440064240000e00059040b13442f0414400c18003000f85200c41482a4140e001c3e240c0c01811090b02008110b40c42c0c00c04012850040348018211443d1a0710341d400a461510b900c081540000d07541c40341031003080c1e010700c5050f01500c40700000000c140b03483d024039a0020040343d600700e1a00c01d42d0841101c1c99001c0c0e004550440c60080c10b42e079468502001203d040009803089200f0f43d03013081000c81d07030210000a140142d52100e1440080b489602999880760b80c070241c0b1080c0c15103d1f00307500c0c88107002a886200040d5100e5a80c1c0d6420b10580d090081281070301408100c2d4084c500300041199035000036441409040d115400304031043c1355400541c4034050b82d4031011260168484422074038200200755881a0312a440d819507a07054007060008078016501c0c3c94241042d240080b8500c0d42c00b48000e0b182c00500421448152a102c3d42c1e205c85940300e6030311100f0750000c5295098019a01805a15480071001008001810f1410a07a01103000081c01e010a40503043c6c0c206d0303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 729600152 1250 729598902 729598927
    0x6030605150d0912020a050105010905010b09010f051c09150e1e07080601060206010e09120405040f020d0e07080c01020604050d050a05040b03010b07060b0f0a06081e040f02010e010c080708 83
    0x803c4000e4010312100715080d02100c0c041c0d00d032200381c107049900b54a0140041403480007489600c5c103170380340b1042c1203080142c2c00006590303003490020302d00309111042c0114204040510486d0600e181c0c0c9281c0480c45c41050314007d00b0010800e1016180030b800c146001c2e01d520000650715440b03c6200e040c1a02c041d10a00399035051860580100039103000c0d550000c5502030700040d0090403103004020355001651082441601e466060125188014040108005a103001c2d04000420048020f0043c641f2209480b40002c581c082020b41042e40c20403d030421140c00244043c0381c46c0e10080c00a01b440d842c0c84e540d55a1a41308400850090103808111220110312541c1543e000d08411200140d417075848100904a90f08071890403034240381040c5510b441070400207a0408242009046061018280718054412001c01032000e880c002c4900c041c07031050306640d00d01c0c1d0702460041075510342c0d0180781d00006000030315000c0d00a040c4000003c038003001521203400c0303540342d58000801c0703030f01e600009024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 729601402 1250 729600152 729600161
    0x111031e09041d011b1404090209010302212a04030f060b03031b0c010f0f080402280f1703030f090115060224010b041211031504060606030605150d 65
    0x301c0e074030380c0701e2400c00f0100030542c000342c07100f0810754400c2000c14081c01c04403114490400404841602448100003c0040350003601d000141410058104042c0c010680321407890005250750340d03401da800703010800c102d000c17010104c01051050035404a4030351144c42030610981c48018910b41c80f8900e21018400036511480c0c1c40d01c07005040e20b03070350b03058110716031a40784040c603845200c1d00401040740400d41c02441360ba80c01d00c400d43c84030500004099400d03a16031400034030917a08a11100c010410030400d016141c80c40900c0049001e0b50743d400c0c17500c01c0c3c0700c0700401e03040780d0740c101c44541010410312000002c2d02e9101030f040c07403030550a90b0340303807040340c09403800490142070b03000c030320501280540c2c000c2404a41d5903103000c440e8088044032030302070b449401c0a114002c8131800421087c40804c51510030b00c6440c5010341000841c0840c03241c042894148000a440110b5260006100c104801ca0103600c005124a02d000c3c402c083c00e24001565080700d605020312289000103003e120f03603a45400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 729602652 1250 729601402 729601421
    0x191b08010204382703030901120504030e0301050106050c0c03010905072c01060e04051003020a151e02010608070e0c0906031f090b0a0e19230a0603020111031e0904 72
    0x103080e0385903000190a0707049145807034544c00c95481e6925960a007424000b05880c40c2060580d10032010046500d910402002c020b0810b0b01005290038102c510780e1070900580740200460340d0740d5941c41803607018060030301213160b0410748130fa410006514082800040d00b01e0a0b00e0142c03c1c2e42d1819030020703000c4420003c1c902041d1003d004220300000d882500680344441e40801580c091006558084450403800c0b2a0700000307600290740c00003070100166031041c00030b000510b4140030740200f4100c61150f92000610303440c500180c4d1200b2040c00b02d50300070b00650006140c0000040c2080c108100c001c4d0b1f0341d00072030b0f03500c034011400400099800303522280303501c80c0e203200c3c554007001c3d075038403800c1c264043d0900030b082c18002c070044400010f0b03100101c580144100455168102c0b980400003240c0d020f4030720f0203200e0b444d60501804024002e205400c0207405103040b240d001542520f584000740a0804203282c0c001c45170000d000c0d01d049051202d00c002d05903208401c08070340e14035401c40014010400e801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 729603902 1250 729602652 729602759
    0x110a08030c090a0812030433110909090703110904030806040b010302040321080c09010509040f062105070905010608041410020d05040203160b0a080702191b08010204 73
    0x42080340c401005400440c002c3c1e00425071148c894490004014501d803840c00c0c540c4140341624903400c0e0000413039101c0002c01880d03604852600c440080001c03000c1005a034560050340000c102001000540143d202d04da05054645070a0f501c1c150710060010403006007030070f0195483e078a43e003032940c0c440c1d03045401139503001c0c2c654051a08941c0c80c0e400304903200010440803860407c0801d07030104022040c0d403410701050390307814607100301030045c44045c1c8400300c14007c3e00c5860701808150021175803000c0d050b13050201e00c260130450032810070900d4030605d0391041c1080303403400c40140b1002c1c0e4812482d9070f000341c120300c1d89030448a45c3d0240310315011104070b103403041e2803000c1155002d50146802a501840c000c504903290210003001f06404001c5501c103d00c1604401c100700450a8000d02c20590f2050540c01541d03002d4041e0b6801045403010780004442e900c00b003100b035144c114420095a000707401030300000c504003410700c1c5c0c0d00b103115410742005044081c421844d01c3c440542800b04503440e490020b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 729605152 1250 729603902 729603913
    0x190903051204030f0e06090604120602090a120506131110120f0b011205060604122d02031b030c060705010f060b0c15040f110120030307110a08030c090a08 68
    0x50400401c0f55000e05135100004684680e90b8402d854540152000280c0042c0a140703094542002e00880b2402c819085541580a011069180c0e46094001e4020321104100800d2104246005424007800030442504240041480320200c0d8080e1039048104100fa180e41043d80c41151b029540030501c19580c0b4000e6003800c0c3e6003140016950010383c0001020b0321203400d90041c280640f4241d8504803034030350b00002c0a110030401000c44074440c0e44482e025078000402c450001e0741704510207c00100060078a0451410407003141010003803114401d034005802c83c80c859540313001a80f2a1400408180700b0310700130800d08107000d070039440541582e041c0e804c1080581c4d174600d80800160484055005503006280c010000401d401540d04d11544d032000e4a600742046640d075a41d05110511030711410402c0c042c08015400d200702c5486400c04400b8402140c8a00c1c02c941c004040b00e07454008401e564201d504050001b401d40c80940742c204000e484e040f52551321400201d040004254445940752290 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 729606402 1250 729605152 729605161
    0x30c0203011e0b01020d02070e070e010c05030415080a02120c0c030c071212050309030d0f020c1005061f020c0603130206070b040b0c04140904080412050c040c081909030512 76
    0xd507200400000083c2c0954400682043c6c00340e031528100e12400c000d04114000103800984103030110180035105040190034100c3c180c40e054515001030b003010040030340e04100d60b44607580100b022540541e2070001545000b001c0c011606e80610041c064000031440490f17400010501031056640c0d0000e40000c5803011aa100e15046070311880c070000380c4860f44036141c08103000340b050703045a00ca251110011460700d2000703540100100940303900744800c2c640c20b1260380c200c030800b03001c400c0402d0b40e03416000c07c1c141060410492802040d019002e04821040c10120f42c254002c0344500e0054400c940da90b032a039030303031100c0b42444000030400258800800245601000307403403400c0a001e075010b6000031840faa11f00c40e0a05062190303000340c0050074142d006031070603071400c0c1e002c6c2170340207104916182c1069514000180c20001e00b0b44126000d0b004141d24900600f000d1042c0d4603a201d60386854400340c1404102c21a480520401c1490780a40718101c0400380350107541204e4a909040700c00d180e080c5070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 729607652 1250 729606402 729606461
    0x60320010909020a02254208150a050a0504020705010b04052d0f06040e0106091a150a0c02060d020f03072f07091505060c0601060f03050112030c020301 67
    0x3c15034007000c01c482ea2881c5000c503411644004002c3e5031400c525007114100301100d070040c03035034288070f1f100d0340074125900c0b618030a05100c1d0701100745d142500c456541e03081008001500380c0c54001c00d1805617040000810940da0f580c149031041b01d500781c0340141d07100c10a0824601601d0141c0e12590441c1c1080244604403000070800700104c1596008045a40c03540d10000c4640300c8165440c84540b26028085180380c80d1a80c403000c1c0315107c0b0f500004015944150940030743d0814170701e0f181390051000000d042e030300382040700700301e1043c424031014507120090f0000303400440d10b200064050800801e6050380010f40b54100c8a10311028000d032522803410523401000c1c0105040150402988102c062100380c6840082c0014940030074007402e40d050070610304070018080c0040f12a0701800d8820000351b0798841400819001400720084e010725070402070064034840300c1e10403801c10146440010031958408102944009078141b27480d05032040b4a00020f8050201e03009031907001500c40c0c40d03d030007044c1e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 729608902 1250 729607652 729607663
    0xf060c09041d190b0108030a09031416030302070504140603061f0e0112020a080f1e07030b0112030e010807050702040b150c100506040e19020105220801050a060320010909020a02 78
    0x503c80c1c6202d211036031b261500320b92640110203030080460f00c1800284006003401c2d0402c000c4030034079811a103a110441c42c0e000140c801c40d40c015005070700000014040382c1001d01800030021890040c0c8800307800d00c60701023603403910004d0016070b4400302d1540c0200c40c60241c072503640c01081e04002543c46940c68401c81c0e0325501c4564012445007110040c0000d00c0c1d8404900e44081e451000098410014403114410b50000d55524189080c0103a040100c000340d00d81656238042d0408105600c440b0f2114074028050b4200003084505016011040150305940721045551255041d03034003040c01c05c6450041800c440160301310301c200380c0011035080c0303503214000f034000381c1092202d40611158a40405100071142c00c480340041035000020f0a40803401078011a030059807040c941140360070610108c0500082440346140741010100350b00b0000b17490f090103259046800345108100f200d185590301c5144104502505650300d611040c9468660b000e814510014420070f6410340d039030103401c00000c0d01d0b070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 729610152 1250 729608902 729608953
    0xa0317040612090807020f03070504020706090b0a05190c0e0604120201081617060312070f120906050a0e01090819030215010f03022407030e01020f060c09041d 70
    0x50890b600c42d1031a0400d40c020001500e4001d0304040c03424010380c0900419115501d13030309801d032140345000121074840b0b1004081c507138025680080c560700301c1d1030807120180300501021042801e040a0007801d4a00405204034460014000580d0f40039040e000c0d90b13100494040c41d40e1045010a0000c0c004c1d003543c0141c00854800d036590f000303035520002080459080c070040c200005184400480c11814000c0e01160070104c010b04460360380459a08201c0700303a0006404840642c000340e082070811030070512031141c42c0748600704000c1c41d60030540c0c0203016015170700201c0308002000c1c01c1ca08041c0d0285601030080c01710300701992030504e500540200e20901e5807004070014810342f1094400c1060345c00407141a14088282c26000600e540c00700305481c0000310703e103000c02d40c100030002541e4080e0f40c01022840d1182d02c3e840130600401001900f051041d1011484079040842088004582c00c42111407042d4211030004171882c1182d06401080c5a01c0250801441089082208051000c1c031044c5038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 729611402 1250 729610152 729610157
    0x270f02090103141c050a0e010309020a03030c021504060e0d020f090a020a0e0607110108101d15060c061807030204060b03010906050307030c2108031014010f1d0a03170406 75
    0xf1240200d02c0410040c240510301000a40c00b40009a1698854203401040300c40502d00429644401e03000100c40344c424dc2e0046002c6000b0400f00720071410404103e40000e00d24a4105081034580a00036140404041d192803042c1c020511070811503075602c480306030303002d8050702c421110f141c40c68482c402540103074a04408031b8140041e01c8820316040c011907010990048610f04410359010055030303101c20290810082941e41400411b000f2245581600d40f18a07944045920341850300c1500c003501d91920710300d409000c0412040031b04e100001011900a00c1019550114252a5421038200b00254100030740c858200900001d000d0840e6002d5410380b201c04108020056981040641d038074000c0c03000601d00060884c080003412a04500410400c20301d0507900400740c00c694030110140d204841c000711010f02d641003401a0741c80d4076590801454282003400c0f0001150202500541c50030303517010100008001070307140540313a0002d090b00855002264007000e10500c00320080c150010b0140000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 729612652 1250 729611402 729611413
    0x1f0c1703240409020a1502030f07051b04060b162414070c0506070513051c0501050106030608070e06120307051e0d050d02030601110706031a04270f0209010314 70
    0x1c0d150038810650300c598020700d109442c0d403a014054101a1441120f0b000354001803003420140c4215400501c04075215102511290500a906401a00c482024070b03000da440d044081c0710000d02c0390100c50904952075103140600443c0e00e4200c80711000c007407980c8002e8020050035040d503101a0031428210750ba40942022941c0d400b00119800c0003c04000741c074550040380410b4895008500501c04078440036805107809469a003c20000a420703c02c0c1148240358100000500000b8450640500303030500c0c080c080c0503e030004031a61420603000d50305a6080c6400400c0456540c0e03000e810004203010156501e40116061194440705d6240410352820340c6074100d103000e41ca01040c0c0e214049015202c4904259000750b50350700030340000f003d941c1031290f0703e5101039200f04108400c100814940d580403910640c0348610841d0028048440c80c003a6090011f01c1185511240d101c03d8543c01004c1d040c082c009090500340ea1851104d080690811301c084004001c1c00a805068190404224122079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 729613902 1250 729612652 729612721
    0x5010b060306011b11190e0f0907150903020d120206090c0303030a090f0b040b0a23060919090309060f0c03020a080d02040902040f050f1f0c1703 64
    0x10303052100301c90007400038400f030040601d41c580403a44420702c2e6002c0c450044038002c1d8500071640030389403203564850801c42e00b001005844180310066078030500b001050b19060030b1901c4610380e0390f540c074007036603115004002e00c1c1d0002c5845906101300841d002040c44100754140d09010441003480b511090044c003c88000071841c3c000040d40140340d2901030011481e603a10004020000c001d1ba100490b001d102c58020300380401e1480c250240298002c0310304d5880c50130b25844507802c4072a5110042e00416000a00100301800d01031080d501900c2a214044140c0e5900c04d2003100d181e96032280701005291065401c2407590007800c801c20340304503480c0c071010542404010b5a0100c5041d00040042e03103c1042800000c50501c0941210a2402005410a903e4092400680e08240c00c400030450340e08000704501d1401d403038450145242558550a80190350b140c820400d202c42500405205d0000d4030801000200c4034000814401000800c1d120300782220b298376062044900c00e0f003c000c07907041c2c2c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 729615152 1250 729613902 729613909
    0x1e050c01201b0a060912020603061201150503160503060f071803080a080112020d021302090406030516050108041e05070e0f1005060a020d031a0d0503040f0e060a12060b0a06090305010b 81
    0x2c8054443c440c03210003808111f5420466250300040c407094019403d100e850900381c2c0c09000c0c0d00f0002500d5114103004a040c2401c2c13514186003402d80008036560b0b90400c10003524085141d5421400c1e0303070502102c0d41c2d100035046e070702d00103014036038901850320b0800001804040380117005885102e0352041210399864012140700c0c09401d070080c1d4040c2c0d00414060051820003118250130303c850340c0250510300040d00240c1103074216413090383c464114111030600340302518969000b4080c242880e40083c10319860f484610364400000c50700c025010030683c42840740030424a002041402d040e0348051400300702e90440c2040550301207013080d141c95004155858001d0964503042510b81c000c01421b101c61034100e02810707032100c416a070030300000076805139910b503000002d43c03582c0030380011a680c91402140c007600c20f0581d030055000c40c506005000d07103070f96602401c0089071a803100d445c1c1c007044036003040d00042699024080d4011f085180011b09550001142c00807280901d0003040a5101f13602071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 729616402 1250 729615152 729615167
    0x10e0a1401060b190e010c21030f0908030711100c0518030d021c17090606031605010c030e060d0507020705280308030c041802071e050c01201b0a06 65
    0xd480b40900040240500184031704071210401c24149012580c40c003103030f281c1c45545412400082c441c25000088c19943c160140a090006035a5400c1003101c5480344d150207080c0e010103440c1c90100010356002041d00e05080200c0d00c00448410820020700140322009452070b0700c14010500c00b900858200403e40c50041031000244d0001c1e000f41c40b41203a007070002881c05040104050074859071041c07805140d22040345040c81081100014907060601c6420107160580741e02ea41002e2030742c144001c2c440c41e40e100801c200440c0d85814640c2c0d8804076540006c1d00c901a0f50b1207074031003620f42070030096440e030b00095100c21100c09940c01011a61000d00d103100095492000170100030603142c007040020708030401540d0082d00c101d005820140c441180c031240c01c09541140c0609038002c42e440342031101c4070202c200b0003002e10b0810084150a50b440f552030341450a6600e05004031140c0c0b021500450f100c0043c84c0d00d103040c0035640c848a030311039254941440e81c00024042d110f800c4002c44e1450003000b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 729617652 1250 729616402 729616417
    0x1205090309150a0c1218180b0d050309100c0218070e27060f0909150606034311071a1603050f03070819061511010e0a1401060b 56
    0xb0341e00c0300740c50135440304d04c50b8541007100f038420050640d0000719030407104d220603030240613440d07005240c402c80c1440702c4095480001c20540b080300008201000944000202d0b500e0b95400e036080c000301c102244080d034518125010280d004901007102501021b83c10740424498170158441507104100e500c01e1102c01c81141510102e54180015400c00c0720002002081e4042001800b00c0313043d00074480400c00c6407000340c4080e045584103081010b0800070502e6086e40c00103080d101030f405c0d4a0a50780c050160700101000c032945002c0380c4400c0c90146c0d030000601c80390300000111403002c4a1214002051811000400d0000707000e4600003041e14209401050344c1d40503494006800c20042c40b000c010142000581181408030800005010b148243d02a500c141e00075120008a40303401d461500440d4000d0000c00c0e0381c245040340a120100141a6002d456130b05440d2031140d4040e03144001e0b006007040043c0300030b030341b1400d0300c07071030030800444502416151640c000740000e42d81d5061051a03801540d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 729618902 1250 729617652 729617657
    0x10b01120b0d021c0c03081e070b011e05030106060e0108090d0e06030709030501050f07021b1c020a030812180c030309280b0c0f0c0d0f02011205090309150a 69
    0x11042c002600d400100c69010003200030503040070135070f250380d0142c02d09200e038411102c0c03031f201056840e0215441c1041a5902c0c501c0119036103031078032036614088042014000c0c900004074400074071807212110040400648400380007084400e40b80c040180851240c4091a4005115030340018044113011590165004180d1105000808403104104094200400980030000c001200001203402405498060442d062440c19242442e032030082c02d00b01240d14a5100d8414a81003504944030788041030400e132030183d05003d400da12480090400c1420703034005058024081042c8415440f0031002e03a004015a40e90003908a0084540c0f60f1500324002e41c0c285c3c59001800100ca0f83d051100c4200c454290107112107a5084440703008284d480e4481c0c02c40304806c40d01044a18074940204a034401d0440b0850003000b0810000d00002e1111800620060045419001d088110f902030405500b50310001d02080c0400d16081c10a41c2e6a508549026071244800c040c15008105048045440c04521365 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 729620152 1250 729618902 729618919
    0xb03070906031101030b28030309080a1a15060705030306040501050d0c1806051e01022104050f010228170903030306010305040c12141b01020d120f0e010b01120b 71
    0xc0300151700801e42d04049980002e0940c40c103401030b12030b80b0707400417802046100401c0c0e09801e6040003409480e442d04003020540c007607101c48000c00d501070550b282c440604141e80c0240da4407211003158400c1c50419003030b0000c0300418944c2c108200070001d98850030301601c040010781c0e62001005a01105c488014206081031a0240300100c0d4819540449401092001c2001c40c0d132140884d0404009404103020080c4490b0303200107035a414040c0d009002090040030702c401001e0720100c03916205d58491244035110010307851040d41d009010326201000d812261400341215234803d00d000d08050b00088a1b00c01c3d1039076040c10581044d1040d60201c03000500111b00b941c2e1074800540007410302178410b5448141031b0740001501d0a140d000050014441c0d80030555003100b02e40090310300051303003002c0e01070480c41c60700700c0c69035903400290071810710503a20705141c1108042d402c1e0001031048502e4083c0c10b50801011508240e0150070139104c040342070380d03a43c800c0160707a0341100490784c4d0314100c1a4084441c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 729621402 1250 729620152 729620183
    0x10050907050702041d03180f151303060219090806040b0a0518030c011401080a3801030f020f03120301090f06050319051b0d03140702130b0307090603 66
    0x58000740c0038181c40a0000604460f883e1241174154502079016141070303000040c01e882c0c02814881514100c0020340f002c01d02003602200041e0b401c3c0c0c5450a0306012a404200d512240e0840c1c44400c00543c1c01c40811542d60807641042400720320a50100000300386240d00010740f000e40000e541b4032443d00074041d44038985031b8101407406064080c204107408e5401d92102521141c060000303044e504000400041c8248100c3c03a001d20981e8142e02c2002e10350016501300c0d001c102d0b41218010400c6c40721031010401c40290b13000c050301a56910506907901c113800004001c200244280f0800c0500032108254009900300425035984030b8425a00d00b0000700b0700042069091a4001c10040c1c012804003040258507900403901d0404079150100b0004004d6082e80140002800401101280714452200e04480d010100e0440300e0102ca00904002d4002140c240c0350000c10196003009034001d02c3c0052031804561420064905618140d2013805069000038000c1c900d80304201c106c80d8003042c2000101007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 729622652 1250 729621402 729621407
    0x80f07090209040f0c0801050a05180402040c0210050c070c09021603031a04050c030109180f021009080a03031a060c250b03040f03140901051605071211030610050907 73
    0x282d0312003604140c4074801e0b034010240c14010740103214903540c0d440d2010340c58142000025981c541c002c038001d8403140c1d4545100f2814048559100d038068030b02044040e9000000c0303103040032803000910500d1800d01404100c0003600000c0c42258022800070780300a840d015141d04030300c600c240305401420108a50b4001030b000380c00c0150300a103003800040c080d58918010600380c171030440b0682e070841000070041c8411280c81c8230f012001409981a041c2400042d9900c50550b0b0407003202a106000d0101c0d00f8010301e1080c207000c4c01030480d901c25184025400d24010303010700109840c1c06291141c40410000c1400c08a09440c9098840f400a180f0112141c11508001c0c0d03420211642407480001301140e810403c40065000d00d228140502045a06041c020402c0d400051603030402c6000300500506030781e0290a50300c0c416000000d000c00c4581394a04146030800310b40c400508000c10407004000c2c00305c0c035090111444803d6041d5005540c2c1c00c06820402c5e209030080356480351325080070980071031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 729623902 1250 729622652 729622657
    0x10c331a12210d0e03040303270906030f03020d0f090b0304080c0706091409010e37020406030e03031e151c11012a06090606060810080f070902 63
    0x402541c203445800141501c000c5158454864602d0400c0700010203001c0600c1074464211030484010245040905607680180802c0c60344031514181e0b100700001d900380e82003070700190b0b00030301d000304042040c65940d2a20708002c98030310b5800e42c0540502d0114000c21801040c00300d0303038000a9504c801c90142001d5450b00036410140c0142c410407000c1c40000391719a030030001c0390050102c1380c451202540c41c01302d1010000c5607030018107015080c44001040002000c81240750800303038281204048051060700c0a201503201003a220007000446030790041402c40381c2c02801512800c0c3e6041c405154003103041c565920064810744690400c0c401c00d4003400b035100c03055603001a41e842e2040c0284422400044c0e00d02507104081418200044140c41040404410a00b1504007030a14194080c951020414450755103210240045074040590081040c56804120b402d944001c0030011151240d8001703003086030072a180010b0311040000882d1301c0704005003101418865030010003410341403407031140c084e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 729625152 1250 729623902 729623929
    0x901060513090c0c0507090209092202090109021803060114010c0311070e070813020d1502041e0305010b011b030c11030d030e010c0306060c06050402010c331a 70
    0x10400000b1941c4a0b080c02008250381c0c4940c0c0b0503600a4482c02e01c5410b205907907006441c4a44100308039002512003405d4960302c134482060381d091945a1044103031800601c2c3c40029408010780e00042603001c0b80e40d014002c01e0025500b42c5904460200034959500e0081c011601608002480c2046a40c40703884585007240c8a85000a840f9598040142c5032000c1600308626590080c1d040040702135000c1503136a44546500c034484020a0703076801094410070117540140010400880c0d05041c5045901200e009000d00030919038800000c100c1384801c0100c50000310760b15400c1c0302c00302e81c16601c144240b0210100300d03440d80440c0381c4075036415590317226007140032503002c80540c0700043c980e41c06120000b42030352980c0b0701252079249005164210b4010103029828140303400c0c428404e0b03690042c2012078640d400200001c490305e0743d000507a108403401c0e1004068110544100000e00d0100902c0140d054400ca41400d20307180800300b14095810129082121a2000104440c5880c084c445c3c80140c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 729626402 1250 729625152 729625177
    0x6020f07020a12030806040c1707090f03060608150f0112060f3b030a030f060b0c160605070b06100c050615011e02061b040f06270509010605 62
    0x8021050780032a0007654990700180c03942240d040032000b8190071481c1c1560003c0b00715020801c00c0410714000e45100782d07190380b10f19400c2060001590f010b0082081c1c001410000d10300c070703841594914040c805891103000d641c1c440c0c010b0502c1003444103610305007940507643c41c90081c60b4030303804e0402c1c06034940303101001610303000e44442000c06014064824070105540c00d030404c410b040402101b940c0806a080740946907418030b4540441b4214000c81900c544110914011461344042807582e4060849500949010306c4002170a0307462050004520301d90510409070b00160540d907404c1600e16000c7d01e10040c1c061000305000410a20388800310082281075820480300b00e00641e1916460410101c82e0245001d03008000300c0001c1da0401c07501d04000040d40c409100c44036a20788000e446882c080c0150050742001040c0800306007024040e50003a0010b10081818142d0784d03440104007116010042ca14210414008070705c150000711460265440603209010607442d080c012112035006801c150701 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 729627652 1250 729626402 729626407
    0x230a060513030b010306050103060c0c020303030a1d2d0d09050105031f0e0106111614010c12050405041a100e060705070e041103150402090c0c100e0f0a030c06020f 72
    0x41d01d0b40f00140c1c080e40c007610700010258118600300d011504c08103202c1040c081d41e03a0410006030740000440707512028044021480e030307114140340c03410007800503d019454000c11008d000b00c0c1000841002d442011b20303a12075004903100214503100c2d0046d141b244000740b45c1d0391f020301c1554002c000071500052210048583c806030302000815803016a00700500c203000c0e0400420103642e0000e0040d05500c00940541100c140382c2c00c000400e8031462085804d0081403103070108850780a4030764041459003000700341c90a50318a0700000d00a5216001d03a905c5503290071110703a181800c018512448981c01390841c0b0301281a01e03400c0d01d811120412290344034030204060000900b05112000040402d00350800040c01c0502d046a081d904107003c041c000e40c810350070b01180700c2e5507106454226805449900494a0f907841041c0c0d148070304120400c02c0d124021001c1005440340d4081e441c8d140c80740d016148070b0b120000b2603584400c440d550242c00950700c45007903000724805500414243e5114280c003403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 729628902 1250 729627652 729627659
    0xa0512060c07140a03120c02010212060d0809030d0e04140f071409060403051518060a0e0102071416051e1903060c0203130803040e1906030516230a060513 68
    0x1460104c034482e0860002e151002501800b2040d400b440003044101d000035824410f0315400c3c829804001030100d44105044111181440740250407540040c1c8090103491010203001e078003400e070821240c00c403406145000c4810010160f514001801100001c5c0c2c41d01484d11034150841d01c0107495140442036040410502a1503515a0001c6c070065108601030076100c1e9034400c0300c00c102c00d00140360075070038030a000d0404415100850000d07808003541c4400501440007142e440c1c0240161b00c001800c41c4a2205081443c0c540021008468201054240b400f6a19042442000511700301c0c0864510810345401066140c00900e8440012100400c0303080c00b82c1e2038555405581e0b4101c0040c000d6040060b6040000314440b6520010307180c154021031600c0e00d08101c4c8121440003c16001080c1d1150282c00d6a0070019000140110b030818202d4803040520103c40c9032540843c4035811500f107843d508000101a032411a940c202c8008280c08445807401e001903455902c1218141c0c2c18544484010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 729630152 1250 729628902 729628943
    0x7260d15080f0706030509011a191a070506090d0f0e060f131503060803030f07030e0f0304142403130b09030a0314040b07050d09020603010b07020a0512060c07 70
    0xc406094402003c2d1586801000b5040360341c00f45c0a008243d0401c01c4009050000751404404e242d41518101c81c03040d02c041e1504003800464100107000d8440c00504000c060344013000d0714079103000f4401d0365865103450211076587d03d6480403040c0480c1106c152400d149000d035101d11814440a015103107010701d0309000310012b0703101e40c44800610034183d20a010f50785409103e89041c0c0c4550504126241c200220030f40e507800000c164101031820000085c01c41c030301c41e0f00400b040b02b01002c00c40c4c0d400841c054034203071690007070f0107814031490480841c2041c07072034500e001a000e0006031040b8a038000d90707002d16001660005010310702007034a81b201c58001442d41c202091042c0c4a5074007540e26503003d2040282500c4200303410341c1c0400013007401e12005c141c3c00d0031040d03001075050811640d10720306156000090481204081d51158000c07000050014844004102032482103407038030501a1120208041c8070740c04020b0881c00d0740590300103603103071201100a040700d5015551280c070031000a11207 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 729631402 1250 729630152 729630163
    0x1141602130f02030a0e010b0a061d510301050d051507030c14040315050402010207090612110a030c14010509041a09010b031b090f0406060507260d1508 67
    0x5c103041559200400380c2012420b100d1080c0142c000c91b03080104c0340ca004030041149031420141e5412104203911003002d5074440010110307550340702441c0f840c12704008804000c14050b490f0b151801300400103203c140c08001110750600c2011340c1c5c07400c42c290703420102400f0710076204100403101442100003000862071000704051003a240c503500481c03030929049000b000103485c4042410f501509000900001d4420000c0c2d140b090014400040c05640f2130004078078040e6194043d2220030725203400402d0f03d50403074011a04060041c450386000403104403c0c0f020707a480c1c80c4409024070420305001d001e060003000f50100714881c14135100b82440410000941140c9205100003043c1c3c0541c1c03080c0d401e0303007000d04499004100c5250f61509601e0000c01ca0001c1510152244404043c0054083c502ea84c45544018010b0701c0680f04000c02515908041d041c0da101403010766401500119107500350203c80c896080300c80450408600f045840403080703010b80107001105c0c80e9040c2d401004a40e18404002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 729632652 1250 729631402 729631411
    0xb0402030a0209190b100c0b041b08010c18030203070b0f0705011a0103140708070f03090c121b21050f0d08190501050f10120c090501141602130f0203 66
    0x413650046000103400c20481e191008614000e100030b500b451583d0341c004071030402064000c2903446840d079451520340348441d002c00e00300c8000e011809012402e000f0540c40140c07210f0843c0c544400c0910304c0c58003610069032610002b58150b010213803e000164032200030705520781014503042d040c9800782d03440609448d003030482c1c5100512000281c1c2191b6902d4080d203001010850021203030341c02c000c0707402404444014403000901c90500e80d00300d02c541c40303540030422280e04144010803454880451a812500e01c6001f568a50a048580b050105501c03845c80c04540a0525141400901c0e41c806540c0154a070416603a034000c51483c4055080e0501a41d2f082a070f443e680e615003460100440f80e00f9a40411117240000d1800c4014051a00c0740030100316510801c444100001d4049107084600c0403030020400f030543c5c01d044104188030b0300300c0040700560b00240c03100c1e8043e0a015094035800e00030084038864800d901104180581041d00814600517203240b800700348601404000d07030a13640140c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 729633902 1250 729632652 729632671
    0xa020c0f091b0f0c01060f061403010e0f0c1c0914030403020310180f030512070816120e031305210a0b06031c2105130b0402030a0209 59
    0x916100091030803084040d05918100e03410016810212015901005014159026560700142940116660400740d444503541d0310020310505449890b04500300c0118402c01f400301c0c20f04c032103010f40c802c004015a410f95038010710044169588011f4407401001c090041e060800041181e14a0407144204d1000740e8104c3c1440811f42c0080c0f40781021700c080e401c003120110b9800c1070005000596012400b2030036100030000200350703000340341c440c5a44007011107402420b841041d042d2404040d000f0015103461504044a056195100786040e00c40780001c940b10360b960b203411080901494010190a61000341c1c0c80d0700040c0f100040c1c15080d2941d801040d4030840403905000c200303e20300d0401581d084044000c40d1100111220510203555900b90303841c000e1a02e030364030000881a44081102c000d000500b003540c003007118154500a0718440c00740c840080b00641c0c601140707801e800c1070b0082d140a01162050714010710540d07200e900500002a20480e414041c0765074480150387d845889a0290341243e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 729635152 1250 729633902 729633913
    0x82a0f0a09060212040311040b0603040c08060a060e04291008100c020a021509040f0203091b010f051c02030a0b0a080a15020a0c05010905070504060f050904110a0b0a02 74
    0x80c0c401624111036070748071800310f600899841100c0500101a10203c0b50301c410500708407100440090040c01c00155015000703240030041100b03000f000c500f42c0c2c0c102c54002040d911140c07a000200c1c001e0b21401c1c00313040c200366000d00208000079030040c0400c1e554509030b86080c002c3c00702e101e942c0010490588401c031540d0380d441000c0c00b0449042c054106601500d05080180502015006e501d07205483c0c8003a12600b4901d2078114500c1c0d13400200c0303d90310700062040001c4c000c8004c0d01030080d00305881403e0140302d491407246110300a81c0011341200016110740030000c01c210700c11102c80c3c4c4000c912024040c8100c8500c81c18245c18006540070720549070010520701d0000f001e020040403070f40e1040c14542d003d508202c01098254034044c04070540d09001683e01e000405040d9141c88ae40303a00109990b20f0701198070b0a2000103d00c9005807882183c1c01d0000b10743e0b031008044134141d1805010344c01070400700828001107502e0400f408556000d40303000d50681e83c502d10a10325401005450700076030000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 729636402 1250 729635152 729635167
    0x605030706020106080613020307090606080403030f0b0306060910030b0112020301150b040506070303110714010b0a0302280e0a14070908030702130b0a0906081c082a0f 74
    0x92000d1030252800b0301c02042110718142071140e8804001c0e103080031408469050318295203051004801420b0302c40414080269191001814003108503016800203141800c01a202c5e1003c0c0140060000001c1c0100040e0f05e5480401420709000340400d500d0b4a81404000300041100327240714000d1801e003c0940341842c007801031500b92060307080784088a0140b028103001c52041c2e2400da4050360340548041e42c4805161500f600149204580d20216030390210f5014104001e00326140c0d0b800320340301c0090008142480c00d0101e24076560100962241000107445000d0481c1089955160340145e42e00401d03560f10403048030161000d440034400907491344018000a50801c0241d6006000d40c0343c0500000c2c0340c101035039224028144001e204540341000c0e000305040c40c6d000303201403031401801445071541d81c02c030030002401917128408440c000c0d90000c0f0102000f0f40c05c11600314809441d51b07201e540d140780c220141010028070b024003070f0440087e500b2480b941940600070411507880556603c014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 729637652 1250 729636402 729636409
    0x1b01020c0f19080705030d02041203032f07050309090708090d0c0f0209041104051501140405091801271e150f0e030c01050417030103081603020309130605 68
    0x10300ca1441c0751203038020500365003180e5050031118101500b00084035180c0d0494940141180304000d0040611400810f01041a203903100405950030321a0710300b00203e000007020714618000820440810321042280e24084100d140002e02e1080d00c03401c252480e103000e1400050511070161818070004424500308003a4840402240d000c0094904022000c04007587d503c1c4100102d8110007070040a070781000c28204180085000b0042c00300510901c050300d446c1d500d20f00366404400d443d1340000c4000c48000000b40004044409561010305804003030346d40c2581c1c004120101c80d100d11459940c403c0302c0d071660211507914840070686410071001e50340060070a603000041c8455400c45c00b00b03000e1600d1001403070002c800048034840030004030300f612003458100020000010030b0324803070000243e15881d200065004078410340c4101e941046008803030359600032501090000804022040280c041a1040b0b030320407000440c0301c0d104886c5440c0702c603008030f401d50200d103180c4003e890710790505009519 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 729638902 1250 729637652 729637663
    0xe010b03150415050f01030201031d01050c03070f030e120c030c01091b090b010c06240909030f051c0b0d020d06050402010206180307170c060403020f0105012403111b01020c 76
    0xf80c111505020b0750810f4202d03144205410300c030090526a80b644c1d00d560303854507403c04854075807501d0020012407620042d1380c1e880794000c0340c3c41d07400640d4441000c0f8845000c0d06c24948111440c41c001e0610000300f006008840d8040c90703051149120911200403a00401d000740c15807a0310902e01e9000740b2440342c031480d00030f0b1815000400c865040444080190b60702010694545400080104407904180002c80303d042202102d248039550030500411410180d80052403035610035580d021100d00258012070b07442c0154803450312200d4118651525420341138100410b5800018184034610b01c081c3c1c0004c05800d807455003151165110410030040d50b0701408400c1d4890510040342801c00100c010351610391041c100010000c006141c540400e101c0c0d0032080d644002a030404507151030419040c082e640c0e0880200315405507090030000318407070f03e51001d0718818564848180701407001400d02036014041070018682581d2003030044c5518250503980c1c2c21008401c0000043e92400c04201c00780c14031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 729640152 1250 729638902 729638933
    0x30e070b07110a14010e130903110d090b070308090c041d06150604030209180f0f160308030a0e010902040c050403110a051503070311070b070e011707030e010b031504 73
    0x880d03e0940030000e040084080c50480d0801340780c103044140380600025001602e08500810035494614100205a049803105044c0008030040321b64084211600700c0d01c0c42c0aa000d1802d08040901c0024000380c09040b20356080313500b48003500d00100c404d0004c101145d040c0411f1420102040481c0f150318881031282e81e4002c0008106544070f00d0302100480d407580714a1100038007070140340c000551284991519803142d0b812040c281d8803041104842e0366551070510450071814061464005003041440c48503a048a070f0051aa40c113503602c000c009030083c8811403040159549071004500140d5172442942c001003d80e4407080d0700e0714194100159003041c200030460160884120501036944c42c03640110116010781c0410381d49545400088018082c10180e40784900d0011a03040300b001380ca085450b10441031565007155420110340115227000300c074040c1405a440400100d60b52078840c1d0000c1c503a40700c500d400850803810b2000400c0c45c24039280322072450640c0d402c091000b00130070080d1a4090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 729641402 1250 729640152 729640159
    0x3070807020f0c01050d0b090103082502010e1c050d081008031e0c0a0605010b07110f0906042d021317060c1e0d0b030606010c1a0601030e070b0711 65
    0x51a40601c0059940c3c0d800b551440c180f010102c1c00c09881e82054120b0380010002520359410365a5a181c600c1c000c0e048005000104d51201c00350381c01544070300d10a140a40d405030345030401843c116091005681065000020012001234001c011030710800280c0804103003980c80444500e03021f1110705640c132064001c45847d400810588004003020160303482541e03024900c0d25907c1c030043c050b2030310741403048400800d02d90416000003045400034020345080f600582d800406008180b04008408003201d070b0f281d41c03140d031390030110310f590078a580b212900145d07400b020310f00c0850186442e0201700714a9407400300c89800089010110b48814085c0700203015030208030209807000030761581c54900c000c02540c400c04001c90700000211007800d58842d03482c00012605e5940681411003406000c2a604060081c0f0806002c1000c551248503210300480c3c1003010707429410504041c0c0202c01c0d4001c2c00382410140c540b1941d00f0700c0001881101c0040141100d480d83d02c105038075008018841a40d0719620 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 729642652 1250 729641402 729641413
    0x602070b0304080a1e03020a0311160b07110a08040f1415031909030f17010f09022101060c0b0601022b0314071205010e01050a1e08120307080702 64
    0x2100289020340c2c0c1c01c1580000f80355120b0085001c100e4403a0142030741070701146040040001d083e50182d000f401c40d50450741d0248204180a00e6003102440341d44198020055580188008034880c10f4280e900000146032035580c188111000341e2030411100f405407544140001c0420400b4407140d0b42c01d00620403040f07400400c020050018054a0070080818200c000000004489045903c2106400307485050104402220307421f00401c0c800568030020040340308029900340e2050074800d418101c9008204000229003058040e8002e90000515502000c05500b455481034559513980d6020301520783d2004181601402c111390f40e03241c040c00b4181035400205e041c40c6d4a080c00d0038a100c81c1d07411040341851580e04014201e0041c2221080d6075a400c00140901c90300560045561405c0581c8203414055662581400c00018600f8411a684400c1810080119942c0300020101c5c50380340b00003072902d007540d403901c4e1410040a5254040f84600000401c00e10a1700281d20f540c124049100909 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 729643902 1250 729642652 729642659
    0x315031c0e011d1801090c0903210e060309010c08070f05030105010e010c060e010507030b060c070306180803040303050403030c03140c0c211822020f07140a020a060207 74
    0x8181c01c041c0640c6a04000040b0760a004080e224030410490100c040d18032480d88003070507000b0f02804403c0c0a01a203070303801d0064540c455440f514034041501d4028505030683e00085c0c0c204004034550784141c4040c0030030450800403d940d09405103104014000010a1200451400400c1c0d00300040403881404074a50000300c5903603218003500d065810030708204100b081d01d00c0c011fa40b541301e40f0354000c0515040c40d201c1141d030407040d048580170345015281840f03581c01c0d0310708005660142003000784040d80b00500c01c01c0441c1c95500085a440002440c0201d5090b1544a07043c0d2507108079070550104c0d4640050008142d0705d842000d802a003a4a8200014543d076403036808400c0c409001c0c0c00c106607011030150030030304040c040880040e90300e02080000340d012601e48021034101d00b110004184800c0c15070203017410607001d1044100040e1004103800e045030b030300c040000c0d0403452503944842030610058000902e0760810f5041840c0000003070414090703038410003150300141e40080045400224040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 729645152 1250 729643902 729643907
    0x50a050d0c03180501061401020f0a0b06040e0d020c031005041115091201090b0c040e0109090c030b0a0b09060312090112090c060c03030e15041b0b0315031c 69
    0xc88811003400008207010301d200004a02800b183d030300404454a000f2810350801c001503000c601280e281d941d014040c0c841c08001681c8440c0303d01c450290303641011103e14005460360052942c000d070700410004014001030241c0b490000740d00c9941c0056072001d0f43c2c0030001e180c208001e0484015200083c44145410340c0c0d07280a40b80f0402c2560300500c03049031b4414154560b035042c6d5980a80281911000d02d85070102c140c00781420441c03c1d14034036540c40c04244903a030044200c074190303a20110a81190b918156186008001c0500e0030744034080440e0000c03000a10581c410f501030000c481002c52540640d008002c001e035800f420251080d070141c40401202c011035000d44400600034280b0414403041d580b032610203845e40c1d1000500c4c245403204046442ca030040700c207500440c040c0d41e0420a182c14401c1700ca540f110000040d400b0907614a0001d4000b821368440707981c000030582d209440b510b540e142040c41075041642d5030b08805280a011290310304040003108290344c0c000c0e01b11901501c010b60003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 729646402 1250 729645152 729645157
    0x9050303041401030e100f0f06050d02010f11120f0301060810050109230415030308090105090a080f0d0c030b031b06040b07020a080f060f13030f030203070e0d120f050a05 75
    0xb02c60515454148000c04004103110700c12460a42d9501070044411034030f9204000c040284070785a401e4540b02c030205031428075200074104140d0607185c506c4403034040b0805580e0300340b13909642c40d541d114101040780003c41010107841c0c2c58043c1c8081c180c42e541021006010320200500c0a502ea444058041180d47c0e4004040c40072143c1c0780c14400706000907a00140400c811000515400030704003025940f0885080754440102c9009545401494440c80e54190a8950030740d542141e0340d001e00c507180c010640b60310007080c25001c085079181c90810314a242c0025600070300c0041d00801e80c1d030b07000c410003030605001d1710141030003004424031415019000500396000354000c0580320768000c10814110f441e030800c001c02804c82d1000303e80312314810031320441d036500007203455440c1c1445240208a180300524011000d2552546945c80103086141d000c80003904002d08403000c001c0d09013288560340d2101003c0000c51409a00c0000c0b01a0b078a02d0050704070801601401c4c1003240c2048003003004c2d5403007401d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 729647652 1250 729646402 729646439
    0x3080c06100b0a141c02040806061014030f06061c060e0c0a09120203010b03060405210406020a0b040201030f0e06040215090d06022206050c0c03070605120901090c0e01060905030304 80
    0x501340d4442040c04a41c0304a1255000c11418041c80010081415940015401e202c0c2c00c084400c51588801701408540d9280d8000340c00d1600300080c40801c800d0100c0141e0b241c0c1c4024080c1c00c4038180400108426015048030b0762540e441a60346009201100c1487c1c5066403200e43d00310701a14085060100500070f44003032050301200c0c00450b1200c0115a800e4200546505008045034854107060600c941c542c550845104074004141451100c20411030007034078100c0d140d0781c000c0d0007007070800e88614403e043e000b0801c034101035403000e91034488403151196024181c07140e4020080c924252040c0300d4039080e14811040f084074240b00440103592a4415003840f181c0c0310b07401507120b00c2c007070100e54402c4004040170810001c0030500412b10701d50000141202e04001c3e006c07907003c030130f0400a050f01c40c541d0b40030380000070300100001c84500f0440c0248541128030399000003906440303a1210060b81003645c2001035030504d444010840306c1d074040c1400015000880141d45030501c5c24000104c10350b003200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 729648902 1250 729647652 729647687
    0x22b090801180f020a030602130801150609050d110a060c1a27150c0903010b09010b040603092d030f02011112070e040606030605010f0c0c0509040c03080c06100b0a 72
    0x3500f0219250200b0070402154803941c1551a40002c1c0c40d0040c030080344e8011003006618001e082d2640c504508003ea04445042e2500d2060906190034000c030292480c2040c0d491350100680700a1545908007003000400032541c61401c0c4c0200c2e40b41142504041540040d221a010310030311a5010f078a105102140e564030101440c074092003450341d404c0090740c1c3d415541c80d82180041041c0107000c6401003100e820308800800980d1845000c01c48028001e006030800c0903070a01092144034000c4e0b100d00d202034040c4255818040015130100315405481a4100380c40d404000c43d04d0030503030895100310320141980000c0c800c0c002400810301081c00740300c80302600001c86202249815008051200c3c0d9a58084c00c1440070a032a00c0001e0003a02ca00c1c8503590029002c1c0741c1004500e03111384000c06030b050384242010030703440c500010061031280140040d152200c0d01100000051040c0d00200000c0c60b031280035245601d40340340d4020b58603001c0d5100701910901007100d0b001896101882c03d92142111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 729650152 1250 729648902 729648923
    0xe0f060a030c0c0503070b070905100f11070911040603060e071b020a0801050f04050607020d050910020321060405070e0f010c0507080a03051309020910050a022b09080118 75
    0xc5100301c03445000d4880103440c40c080086c0e81c00611800004283c070840f40ea483c0c2e071040d950385005001c1c05d10300c15007411000628241d0008076941c81102d01c030312503011a20071144880c0c0c455244404843c0420031640e20103170700160802002c3d07014040e09000341501b0441c1a01440c0903107015198020581c1c1d040440d01c5445030f00400c541e59005000702501c07031000204203514064000314141d0340b065400b030b203561103800000f03407083e8800281c032800031246a0b210760400034040140400b55038924000c8040d0b01080c00359608201d11116409040d40d44414011032505101052000715030024080d0010043c221800304030b2038641a1a0100fa0300f020729206034104564141715042541035044a03c40303000e245441001d059003d000b030202000c101c7c215010150351085941c040f0b210745a04190040500421f522541e4007440c060440ca00c298010b50300c05601d83c1c0c24000007210300104c02141a01000182401d9aa1091205001e000710300c0013000101d402c501198803144100f100100b121010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 729651402 1250 729650152 729650171
    0x307051002090a0b0c030c060c16020f030102071b0f091505061b1b0a0f0302090609071e200115180e15070f08281b0905010e0f060a03 59
    0xc090100f00202101c9544075102c0714085651900ca07403060522007018850f40c00840c1790351001004540388004000702207030900d8440d03400e000e01c0440355200301e6811355080c4404004619009221440c0c0040304800703904c0f40d824030001591000c213907002107461602d48420310340c070304162002603800e0352000c0b107195031107503030241050300d03654842e03d916002c0e0300640034400c010501c00c001007440c02c80200c0c0c226035529214035454000d420b440c440690700c00016000300c0d21301d00f000d456141d0003140d40c0c54916a00300f8408c0329419522080c480a600140b48820420500700007031400180036044840280003881d4014200300c86045a409040400e404400000d8941445680301512010512080e6550390168450788a4045422a080c1011403c80404610000c0c42100864465071400003041201000c0484081c2c018150300242d9101581d5a0ba00c0500c42c016a0040d40c041075240d0341d1000011308000c00100110703c0085218002d082440c04540c1036601e0205a41001b02d051500007a0180c0c0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 729652652 1250 729651402 729651409
    0xa09060e0303160309091d0a060c1e05040513151403160906051215040b2806030311010c140c0c0d0c0504050601110a030f022d010e030705100209 64
    0xf01100a14020382c803040c0030f0308143e0404104001c40d02d007201d0400081040100c14100b0204900300f048054205d500d5031400640c039076100314203900d26440c00e1018607402100c2041c031170149120280100704041401c216501c6d00c00072280d8403449a417014404010a00380003d440031072402031300017050000181102c0394804020601d296500c0d544001c461603503c9120000501ea2402118024010302c414250110000101a840044010b520003d55955510b4021030351801505410302543c1841c500c180d07002d40440c4403510b092051300c00280781f500d5494058004410f01c0c4200000e87d050604e9001c01030740158680c040e08031805200750b56081061842402c080d00203041691060b8884003000501281b0554101920000d440401440c1c40d0741c8011b6928102d41e0348840060707407003540c0d80400a80309540f003616045490046820078844c03070800351500c00c0c8200c56500325140d10401022958401d00411a0022104024510b0810540c40e003548605201712010031054000805050700e88 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 729653902 1250 729652652 729652657
    0x20306210a0231020904060e0402010909050c040f0303170114030309060c070e010f090606031a040b0d140a1a010f15140f0306010e0109150e12030301060207060809030a09060e0303 79
    0x481d400168414445143c00c850003d401210768180110b140c40030200e4010091241140030356016102c542d0150314041c640030240030000d00d0100d01485c00d010015001c02d200d02a031f000f0b103201c3d0302c48011380784171076001c000c041d8070503803001c000c00d41c030419100c600d51004403c83e0701c21038050320030356981c040b084d0b02d503441d10381036601480307a400c05000001030f8034080c6160b80d8155007560b04144031240c0e5a10b0201c0039100c0b904062000a1707811104a9490700d820386c400c0c4801c0c880a400e0112950b2161900002278402d602c642c00c043e0004560f140411440c840414030455100070326110550400e000305101c0b4160f802180c10309140100c00301d0003a4006c00002000310444d6038516941e134000d400d80940c94100740c1d0024042081c42d1b00800207517001e002c6a40a41d0810b14036000380c1440c9072400c0307465000301c03204d45800040c11044a01340350000d00056002c1e19181d001840000c0c6405401404001d000307107030201c9a0024003418014a90010b01d02c0308a0700c580c644405070300c0a4a00090551 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 729655152 1250 729653902 729653959
    0x10311041a0c100b03030306120c0d241107020103270f1401090201021c1b26030702060106080c040905100608101d100315020306210a02 60
    0xd1007892a40140102803000070225144180d05440081c504005800c00fa03030b500c0076489034550030510000d0703d42c2c180044a040511f070881c0c2101c00840b2980b010407a007100210081d51211040daa07003002109010032408001c0d011110104844100105c548019008041c3c0007410551548040402a680120f0040b10030401817aa0b0810317151911b0b101e5112001c428080741e00011801100303241c0d01044c07140c13402854041c2c0181c0a680403401d802503201c0441d00c548014000c0e5690411403c4400004136a249840b914085180041c505c0700e038500e400b841c690b806c0150f9810000c1100035a804541903044410a0900340b11644414005104500854100c051401d140000b0041c0248403220050111202502e900c1c4454890b21400b14442c43c1030f005a5142c0400c03c0116188401c40310f00c4940d001382c0490001d2105a200d81e521100f00c94902c0a99070025004018000c003480c040c178202101503080030140000f210092540f50310713588180c102a03c070344c54001c800b01407a06200155010f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 729656402 1250 729655152 729655169
    0x50c090a060315050a0b0a03050a0e1b030c04051b0a020c0d061b020d090b0903030903010603050f1203060d030503151201140618010b070c050a060507140d0e01031104 73
    0x941c4420000b0000c0242d03401884414030900800142c2d0f041c10b4064405030b0f00d16601c440c2c41c00d03925000680146c607000c3d180401701ea54901e80c54030000800e0103804404180205031407407980c02002018500310501c2042d91196180101740f05041e911035006a5400e0300b500c2c00ba64484800d40410b80c10304800d00e00342504041109001c000f0403505901489000c0300107124807160b403103004403c9a94000c01c011180101c3e4000000740042038142c009011919002402c5920f8510000c000c6420745646503c12942684080c41c0c500c00800140441c1c0d40c1c134030b442d505c910b0940c900880010405d5260140141c144080000070400340c803014025010300b0000982414902c2c28000e138024020401d9965034150603c8210200c3c60510b04011840d8200c1c1d4001d01d01c044ca81d08020612110380d1203c1c608450801c3c0040000626886040c8444001c2c1225181c0a4840c800b03800c01016500d424401d0f210190003210059642c1d5401030704e480800320085c030f030006110b041580c80c0c0403180301d80d030080e0f1078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 729657652 1250 729656402 729656419
    0x9050d140d0305090d0e030c2103192705010809151f050103180201030506010207091b0e060a020604080f0702090a020d23061c1202011b02070e0109050c09 68
    0x100300e8043d0000c41c0100148022550807400c4600c08468591800c00e24039410780001503015820324207400750030f210000030040c00e000e403c1c8040040d4610f074445030f8a000089a0190003804060f04110010159605041d0b40652895500311075061b165160180b541884820800726042d001c0801005107081e504945806071420469450552412002c9507151300210020011416521a008401d00340d583c0c1011110f04510942c0190043d040080c0041e04501c40c000700080e000e08140200d064800200012008034440700c1c000802144c402245140501e400f0802c2e40f01865001814640c402d81049885447d034100a03444820b601c240d4502940c040d0202c2c0030711540c00403540c0100711f100000752007005003a40300b8070000103510303901042ca8a01c907510000140d0a050440301d80580d00441146241c40c000503985031540c0c1000742c032000340141e55500154946501d070340c4c01b000600030b01b0300013001c8e190300d8084894000c8005000f103401c41c64036207011503010320740b020641d501e800c1e00422004c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 729658902 1250 729657652 729657673
    0x510d0b030321100608010902030c21010504050c072003100207051023010905070203191e08010f09021608210c0306090403031505030d050406080a02030709050d14 71
    0x1000c141c10b14050103280e103120040f421443d828260300d000c541c032540f1004800d070718000483c2c0013034000422941c250941000b14544841300c4102c860b006000645004504c2e5052009000489200030170210b0080400c0040d06c000c42c60720f0030042080c2c01d0005041122000c400046400e2a501c45105050240082600c404014000c5600054410348600c2048044404602c5404510441d400150031485c00b00c014003803641c0f181c1045038481c1c25401100c1c54045c205001aa18080061002000a06082c08a41c2c1c180c5480d8a51013901010300e002c0c0400d50610040d41c0d64040b1521801c0e00b100e5000490009402c0950032052000307812018558a5034030002607008a0132500060f1400609010001800343d080c1000303807400390401404842181c0d640380e070181d0003008144801e44c0c0141080d2070008441e6010004003500d01013542e20a5105c0b03103401c80103880781e8400b80105280300d0044c41000203259100c50300c0001c41d0011240a00780c00841d052001c015081c3c64601e92540c09140d9090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 729660152 1250 729658902 729658927
    0x1e211d0d030905010506030715080406060b04030f020405180d0c17040806010806090a1101030c05270f01020625140301150e09100302120309510d0b0303 67
    0x22140d490241000b0710060380c0e80740405864252602860080c81e89c0c02007042e120034802c002c140d82c090310540000640548030510201c8540150f0f1048480c45802c0b01120114242406855003015a84c01d01c01140721024604584441e4181d0620b03040100c449103e80c2445a442540c481c51613020a40c10348c0d45480c0c4a071030741c403440d013405203800d2803260300c1c04a00c07091030006602110b560403900c8003511860315801140030300031892112080003070a200008a60500402d0591001c8000703030f90079001541c520034403620a040800b0350b411354005201300011103a200c441020a203c96400030301d00562f1044042c4c9100a10000d004405900400085040c00c403030205c69080310241d44491443c61006010001c0d664021660340b213455005460400c01030401d401e01004161008080d0f034104240341c0041030805201c0140d26406141441000c500303900c0100c021540030760348460060440c5a080044211112920003020001c08009071103000c144042d40048040c000c0107041c3d998408524104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 729661402 1250 729660152 729660161
    0x90a0f0b091c1e120e0f010b0105040b0d02030402210a051908220522050a050606030f060117130b071b15060e071e211d0d03 55
    0xa025182c030600d1031440c81e511403840c00061040143e500c0c02024280a629035541500d07a01c3d00c01c0c00d01001c41000440860303a030040c1d041010246004041c0410020549400d458441c1c0300ca50501c503040006000d440d0703030307203007100d803030302469074026070b8a45480c80030688191540d8140c0c84411000b181c680441d40c000301d91205210701030400c8942c032000d944c8a051a003c60060000e1a000c0c0811074030040180c5a184c0728110740340315490b51140d0f9900c078080788410f8085040902ca100000404010a616074413400da0070803078004040010740381c0350000c0703105440090000c03e0f0085654001a01607803081c42e544009082d0302c5200d0f030340b50421220318001d941140707070100c031052100000151290722809003032100b000490b20820764020242c580c2000121a41c40d1001e502d6180d0328041550b105c400d02003070180c0080ea940018403103d448450710342c5a0305008883c01c21030449800204595288003600807412100400079000ca00940400309040901304141024041d2004008003140c26502 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 729662652 1250 729661402 729661411
    0x15090706081f031a091906050709030203030406020c0301050112051203040c050310021903050f0711151005150a080612031603030b031513030f140705010204300b090a0f0b 75
    0x15200c45035103a05110030b484a0603d0718840303d0303c81b014183c80106640703400141d0090381c00d00305282e1094482c0c0109056a1241c0c00420160b4080100030110382001d02c0307a0340c0140715030034102e01d02400b00d070b59058503840300d4250900022404030100d030511859801c403000400300102110819280c042400000e034020f00c034019042ca5031100302d00000d60290150602c1081c9044010040380e840420965a84580324918050b510810000f4400032400c3c1c41ca0038000d0b02080700d1000700502d4035017085201008020302e02e8070031006000034191640c0162149400c00c3c01103400c919030741140503800345107000f400d8852262a609846900038140c02d64000d820f041010360030789902036280445802c92030402d99440601d052605c05140c042403059070080a080024a4522407800c1d480345107807102d8010031020b503402d941c0054100b043c1e580d500100d42c80d40521058401c011160120401306d06902428094044411b0000242c00214103100c00c40c490703580a561115000100c0c182040306100856 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 729663902 1250 729662652 729662693
    0xa2111150d05160816110316140d090312030c1b0c030b090304060909090f0f0311150f0a0b0303040504020a0507020a0b0f071511160515090706081f03 66
    0x43c440c96900b803003500400c1c41403402d9458100c0b020f0075000110b80202c040d141144a5020a20104600ca03041c030701180742c140d004103e00d42c00c809120250310f0508014860401c01d01c890501c003003002540030a0350407240805c9007000109040c040e1070a640503a80c400c0c0509841075400081d0702042418100801580d0241c041f03907500e582c4081c0c205035240b00c1d50040c0c102203019050704201142d100e03044000e80c1c502c030714140a00070303035160307201040310034490011008100c16000800d40806c04014401010401d08090861070070005070381a841e000c05010101c0564543c42185a00d44040045400500c0c005c0d00c215501d07048000d0003000c0341c02c5680100d00c11030740c000340000d48000c800142d9020341840c0700380ca4500440d81d81d9242c00d03080d40e1000140c0c0c640d12403909114040d2a0030240415003100d00c003905030900c1d189003890034020742200c2000d403603611000303002c0c5545000400d00181c50382c0c0c0c10215065200d030908007152944608048030442c0422101000b0001c2d54154000451202c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 729665152 1250 729663902 729663931
    0x708040203100509060f070f140d0902040204060f110106050d0b250210060803090303121902120a0c0212030a0c021608030705070f12060c0521060a2111150d05 70
    0x44011180c804c0281d0802c000509d03540042883c035080e0000410900660010000f901360107580030a082e60025401080404c016980200d002900300194610103040c48000300081810b1000007070180d502c400c0c021744a2845440040c5c0d0307982c0303440021003c0f8613115001c89403608851200950311021070790081c2089082000000b122000041952a02000200a9030415000d0001444400d10040500680a4400150038070b000c0d82031000304000c5189000e541078a00e002c802c035109640c80305142c0303411540548400502c003503803401a40d80150801001044443ca901d10491422144031361461a0020842e40003401c400d0000c001c045507840340e02525202541c41402c071404603401d1181d591290000d0500c4000155668050301600d425401c00c5410268000d00100d07803207052030140400010843c0503c42c09291404100c0d0090000c010300c00d9200062154406600d003104100500301c16900d06001c1d81075030392205007a000c244c0303030300c40039211400310f0080c00250100f60b40c3e040541300c51 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 729666402 1250 729665152 729665161
    0x1002040f032d2a08070e190c120e0c09041416080d111911061903090b060303270a0512030406090b0a05071205130909020a0603090b0708040203100509060f 68
    0x20081481c221307035400c0080c00640c0d15049003840900e070000c040409009042c64051019403030303441603e48441c030981d03940c0f141c5080e900283c801c45203481140491a40400c01080c83ea5840040a0383d120360300095190410342950a80780c0307481c68006900c070081c0340c2800d000c01c15030400a0096038441199641140b84e04a42110644034002d24441000c40340d105918207000c03400e41140e5030b03420303034014003017910781040182170020492121030740c200009c1e1105444400d0202141c2c120350024821405540b91000103400302c04c520001c40e0b20b004100c104038841c0302059850030b0b1514010800500707588005c444482440e40c03a6071050081c140490b92035400801c046602c007040c3c44882e089a11410701c2d0298913116244040311448100d03007040320400c03070aa01c1c0d4548200a1004060544020071001c2c01c0d4810011540c99030340040c0c08141c0f82c01e11881c082442980f1250f0090114200070f0441c3e03d43c0c2c0082411301410580c2c0450141c18441403202d46100010303141c0c407a1881244c0345036a40ca8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 729667652 1250 729666402 729666473
    0x20c0a110a2c07080405071a0d021204030e01090609140604080102030403020d0801060c1109040516090606030f050717180a030c0209070f02071509030f08040303021002040f032d 78
    0xa003605c020f001d03036001d000103019092070315410804a01c0c0c0620841d040150106c01c03002a86c0c05000003003541d0303004900380802c240d045407200e002d843c02400c00e660340c070b414045c3c0146205d20500c03a414034005500901c1c80103449000c1110040c112110007507590b89003606019603103041031908000054040400011000c2c8660f0344130105543c0003034400c0c0020801c1c000c02c140b0400141080c2c03030030b029043c80355682c1c1d0b030081c0c8945c00605542c82c002c01c003145484070140c12643c211102802c41400c20b0100552907521209a2180240c1344046224a464101c840c101032a03124201d07903483d01c2400c003600c0625800c2a50300d08010320232540442c0b6543c403c01c3c2110802484050400540e0040005109000b0b150000d4205203520380782503035100f981c90321240c00c514000035003034588040015080c028144d060101c241c582414050541c9403d1400c08410b4600c0032902c0042c0028100c090981d81c1001000308000c00b0640b1200010303c51489801c141c0c04c00400c03064202245840540c010a40c0f01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 729668902 1250 729667652 729667667
    0xd0b1609090e0304031403090301050405250510230301060504091a09071d0306190617070b09150c06090709091109090a0b01030b011404020c0a110a2c07 67
    0x9402e0070180d4100b034555030700c04501c2504505000480c1c0000d219a004d903440900c40c044c484c6010340014400c00815044840101800c4c0e050062410314680c0c050216440d5960304028180c0f40385004c40100d507000c1ca481440500307039141503140850001c00003840326442006082940c0800d00100011040b03d00803442c0304803008240354011030f00400013241c040c010840401c00c49541d000340c43c810030065001138240348086445810300f02d9a01001c2410340054449d44015150441c111074610509121644d504c003210700c10b1460201c2e0009021a10b601c0d80c42c218140300b8012411240c5622001801503100e0400701e4140c0407510644000003540f01c081c0c001d102007503401c40304485140941c4000c1c07100500004085007014880c0d80400d9002a6194920324000c50103146408451b504041c014501281001704582c880ca00500c40103002d13a60124002e012150b200410318084290900415095009607214960b1114180001d031706070005041c90b19404640480130b804240d440302020f0b40c040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 729670152 1250 729668902 729668921
    0x60c1e0111072f0301020a08090f060708181606020a0611030c040e0a060815100806040309090c11100b091e0c0705030d0606030c0e0d080a05090d0b160909 68
    0x500b601039143c0c01d08101140c8015107561a0020030035080e0001c0400e0a9901c414100d40025207400d041004891003402030708941030003900608014148503900400b610400750243d40300340c40c040d5140b030690342c0c10825445030212000700f81814566901c4041e44030012000d09561041c00d0020300a203803164402264460252440305a0905013401425414400b00415442229079a4540811076940401003603148141c1d040190170a0f04c2c1c22000140c1e0b121040c0d00a2115070f0003403052100194000a42c881915030101c400100f02e440d0003412034481038245c1e48410715000b281c141800300e2103c2c0d04a512601d03400e983d40b0300d481c3c960340f8a00351540d4200c070008400747c00c0e070004a0071664041d0003c2292034000e07812281840b90b40c010705ca0444000c0d034000300100f655200c80c414802d4001c21040f03148641103c804c14007079000c0d1030300da006218506031179003000700004146502c0c1d030f2152002c400441d0807000c0d001051400c201c00909a0001414100c0800c0c01c400c80081c007101140102d00c0745 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 729671402 1250 729670152 729670163
    0xf01090309231f02030708070c2102010c3f020d05130e270a030306090504050d030b060f13060e06040b07060b060f07030e15120f06060c1e011107 64
    0x15001c40a40f02c01d01e101000310980c0c21404208458000314104a01909240e405600b03203c0010345000101c91481d04c114110051800079016100090703a00181c2c0c1842054100000301040080c2c0300103d4101d26030118116260800340b054081d0310480700c6254054503a060f001c855910884400031307640c3d801018003036a000d5810740300a0183c0c5040a2905401c007486101da030340141745014815101803000240101250320002965040c150704d40501c0000f45540342041115052580f51551503101003044030007410380b20b100c2140c49031034120841e00166a11800c00d038640c20b03602c0002400c0754007881080c2c00542c0202c40f007049403802a0032241200d0100420341d1420009030790340b00291020781e10040c0d00c24410300c54800e00200e038200030454244240e94020110a034030080110828055540000c4818207101000c026526086810740003104008416503540d030f51400104c3c90b1103420311110f424080c48001c800b0076000307400404090580100241702c110340030b03e5900110300034010080e00303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 729672652 1250 729671402 729671419
    0x1e02030c010306080619021605011a040501030f0209180f03030105100e091b090a06031e05330d0f03080a2a09030206031005040608010911060c0f0109030923 69
    0x20501c3c2c58504451100180031b001606120006401102501c460340301520541d44607041901403c40a1510102c1400212410022541151900c210641d2000710007800781e00c11001091095207210100d5078a03550140484554000a01c00d1907103036003007842124041ca0311a0303060301c040c40c0102a100302c2c5140282c9480314503a6000c400c1929100000d4000342820b0042200c0e4145854040c84003002c0d0041e0f8402081000c6840f034504001003200540d4001149010300707000c0ca442040c141c000b200d01a940c032103418404003925041c4409500d095041e4001031a00d00e0104010480d030966a81c54002d48450082d03646015964081d103009103141c0042c0146019600d07031040101c9100d80202405203000d01c40d01d81c899021a400d54029141c880f01c0d419102d80c1041a4502805054007419030500203020113481035550101c65100d20402a00c600400720300b80311895000c004c000d82044100000348021556418043c006e003115010700044c030754034402e0310808004003403101000b051001c2c08024 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 729673902 1250 729672652 729672661
    0x60702031c060509041208060108060f060d180c032310110c0703061e112a07090c0e04090c0608101d01080c011404031e1e02030c0103060806 62
    0x8003040c5048101ca582d681c00071030291900c00a00b48035500c21031407600000250980076040480c0100b10a0400c03148408209240c0c5a680190490f504141c4107551294000b511060181000d03002e00311010800c3c0c0035101c1800307800c48080b81200c1c051594241503810410003580c807129090703031032807141e0b21090341c44050340100d0780403020130105104040c1c20480701d80f141c1400e100055100340da400761201641500c41d20002c281c4184900c20003000c02c07076280c0c2526050f405005007030700000800448410299103480c60302c030511080c505102520426621080900d00801c0101e64180000343d1001844d090b03420704e441030200071038002d51200e4140b4a00403044429080003400c04598012000c03000580b1441d42c042885812072450460501d0340c1030030b000a20b0702c20031103545410060080401c2c2c1c0717044880d00c21501a00d4100140211745800303040c05a051680080009140c070007100c1061710002d001001035100b440c401c4060340c0d5030f80d410900440c1511481d0050306070340c3c0c00c85000b04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 729675152 1250 729673902 729673927
    0xd0e06090307170301030b0c1c090f020a0f05010c06020c012004030c050f031b01050d1418281e050c040f0204050f0105070c030b1008070602030406120e0c09012606070203 75
    0x80c5001d803041740400049d000ca045a14060351044c40045a05210f01c200900851030700d418900d000d4086c89844800c03140c90540001c000003014900a000c241d8005581e40081c242034000c01030481811400ca42c0042210001c0e841d41d50040c0b009895070000c0d0740021074a441c3c0740f0f4041e842c6440080c010048000c0610006000540c0d920240e81070200420229401403014000c4500800525403c1e1206280c5000078203070142111080e035105800c1051840c0b000008540c1066481d01b80c0f50152000c04101e281c140c1c82506151401c1030318004c183c0c440d00400c440050300c900c0c0ca000645040c0044d007003009401050780124018680d102407660600c80b0694420b070054114103014004102c0127580e2074907800d90030402620030944088402d00300b0b001c1c0a0301048150024255403008503d05882c10900a0001d0400a890200541c90b045070040c080401c010410b00d000c001080f0701c8865a480b900041001c1c00001d00c400e0340c60f000d0f508107aa516000c2000d43c841e0b03d990700610315050348a00034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 729676258 1106 729675152 729675157
    0x1090b07081e041a0a021006050306070f05091306081510170a060509010f11040308040b0c0f100b040b040903090b0d0e06090307170301030b0c 63
    0x40384041120300c003900e80ea042d55000d1507862000c8203184250782c070640140c0c41d07036054001070310f0041c0c0042880030b18580032902500f00301d20010043d1861361040366456008140060801400b03040c903480701c1d40c0240341c22441c000814000800a0100d03013007e554084e59800103003c400340801a08003d2100521502d00b1032801600e01c00703502c03907140218155000040002ea449410070055200e0650784040d0038419464003601f82c03402442001e00e0258202d04100300008000821000c0368240c0750442c0500345028203080980480fa8804101800b9610546065550603881800f14001e5074032817030b4000c103c0c0f001160800017555a6103020b18450380c40e00110b240000e40051040c411200c01d4100036032506003030a21700d07000b851003104070604c07801901d08015244030044003c3c080c051182c0c8031105110310746002070500d4002404001d10440b0504041820032014101 = true := by decide +kernel

theorem cover : BRFrame.Cov 729496402 729676258 := by
  have h0 := BRFrame.cov_init 729496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 729496402 ≤ n) (h2 : n < 729676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
