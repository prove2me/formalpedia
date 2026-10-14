-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1460
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:05:43.755154+00:00
-- url     : https://prove2.me/submissions/2c850bb8-07ad-419c-a34f-170f1a29428f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 262410071 ≤ n < 262589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 262411321 1250 262410071 262410073
    0x170325020a140d0206070819030209040b010918090f0b100608090f1c020304030c0b030a0c180501120e060a0515030a0506010504020306010311040306150e1314030c010c0203070606090608 82
    0x30b103503d0740800c8103a400030402161280820040000302010742c010f95190100305440c01340c2c03920301d900100020398911505003810899524420091400310021a13515a80825000500d440041c2407591100030a080090321401740c4100380040070704070242410460340d460360340502c80d44070034450a459506070101e218480d84880e1204070b00c0314034181e120040e0403d900460340f61941e80d03910007803011081e600980001c8000300810a13005101d0040a4880c0c7e81c0d860600101801010401942911805150304100001e02042c030103a241d5480300040480f10000c48085103040c080c284080e01b8101c1c0c03903031040c151804540b1701c03904000506a1487e81d102c4041d1613140e09181c00c0c0710003500000e280c24109522424218001c0710f01034010030103035001e409d0203d4600000c2c0450689801980e001264510310380f0704010008503180c00b40c0710480e5105045507401040b101c14540346004842d0300c503001e0b520b0300300010411500000245182481004240406907a0f1865039003119102c0c400d010309 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 262412571 1250 262411321 262411339
    0xb15031c0c020f010e180a060503010e070b2208010902040b01020319030e03070b010b03071404150e0409050318010e04020405030606010c03050c0d030603060f0e07170325020a14 78
    0x145429020b8020f4400185410394860649100198008440842d058001c403c03110038081541e115005050180ca420f800a210300c1520100c3c0540e030300140e2240e8441d070003010131990360000e1780201c100b4148800c0c1200d9040c4a4582540034000c040405040740316a1604d89140103070750001c070650300300382402d04000300580d6899000364058000e24a114030280010090724001030308090803240138020895045403285410307100607000394901d5454007501101400104500300b0f0145c00301c170700d2907024a09410604081d10204014101101c0c00034803500010031010300400e40c040422295200c01d1341d8000d400303522078090100301d20442c090190160007000000c0c0170303035007d00c10610501e072091501c10f10304011000350b542030040202070400003e031078000070420311441d4010ba403819245a4401c000001d000407810346d0380d200921444400fa440f41c0541200742800780306a41c0f0301d0140307044940c00c10010b130070300c00c0103590180b100301e108200404001c40c0d4640741510001c490140a402004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 262413821 1250 262412571 262412573
    0x80f010e1303050d09050706020607080c0301231002030a030f050402030a060207080d02040608010f17071401020a060e010c091707030807020a0504150302031b010e0402090a030b15031c0c 82
    0x21400c070009506909024040222030601076440c0320f0514100c0c010405403038100d041140c02818204c020b040c2c2000c00c40402c050141540c0e4400c00c980c11242040420806a034000c0b030760518200844e41000d0348025450741c0c5030003c507004402040c9056040e582000700b043d0314155a000c035541074038080c1d01940200e4034540001c0e03165008105840c0a0101c09080000040c034003c181c3e0300c59045400090115001001005030110100015040c942d02c41010b200740b90060a50b90955440781200007640280e008145900a2005291303881e0442c1c01070000d9109030400502070310030302e403525000032111000010b0121010160b8180d09142d076018100b0b55245468614058101140a80e40170060880000e200d41e10740c490115000c1011054a0103181386004060404100c010b0301401d000c00c040c640c5c81ea503a03121401d100074040407030740140c5a50201c40400d100f210b907504020710203166901070080700d14000078071410b6000100d040b034019102c1182c104603084a0340b024240401c206800c180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 262415071 1250 262413821 262413841
    0x23070602060109290f1f0f260601050d0c0905030f0309132a030b01111606050706060308120907080a0c06080417030112020a0e070f2003031006080f010e 67
    0x1c9514800824121170703d080c42c400110110300e440c0b45920007204811600000c543c0000711203601b980282809062079090300071500144070018110a580046000006d015a0003141540d07003540d0855270070008a0080c14018005090601415200744116400f8040045000085810900010349444545000c10b0405000b506080385405c1d480d2070104031070703501c400341000b15640140c803d54000c00d08403101c00024200c41c10340a4560280d80101c07050300001290920840125111880d10030780d5071035141070410003001c0760341008068240004030480041c2d0b20805950145d010b050694951a50fa02c84e500e80d1480c41f003100800000500000308000c1d40a01005079200f4061310301443c03150706600b10012035074026040042824001c1841c0710941c01c0055031500038000102407001107091a500160403841c0d40704080c0100701c64004082c1e10780003050783d8011310604180c202ca80320305014500305000d0445020704c03c00503035003800040140302d041e05040e048031071502d801c20360b5840c0ca6400c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 262416321 1250 262415071 262415141
    0xf0f0f1d1f0216060f050a0605090c1b060403020f070603020a02100203040f02040603081806210c120411011e0c120e03030f070b070507150923070602060109 69
    0x70a4245034284903007081880c10b8101190481d115500000b4040603a0394460b00701d60014103018505480c010040c00580c85074504a03070804e80660659072982070039100c031a24201c80c1c42ca4004d4070b004910a000030950001101c00d1006140000c0d502000e13200c0000320b049004501d141030059000031045441c1500d240e0065070018000c036030080034804582c010409540c01603004980e040350001e50440b40310f005001030007103000d003100c100f0b25100601c110108580703212816400c64404130804140401c180300b00300c070041403a021000c0e10fa0f181c05d081c003032180044150b0f142e010510703910300010700d011351020310009200141c5074050294001c2d241c5918281d801041c0e032043c089914040080f40d54100058140d40d5450041c803a40c806507490442d062403400f500e42c3c4240401130110100058559030400340301a00140d0004d200c902d1820801440301c0d1940c4a1401403242c003241d5200d00b50702044103000d984442d001c841541e43e03640300e003074116105c91806610f107440c100034020070300c00c000c115 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 262417571 1250 262416321 262416373
    0x1d160c0c1203050c0102070b0105010201050a060f230307060905040b0901060215041b0803090f0405070503010303030e0114010e061e030a060f11160b01080a03051602040f0f0f1d 78
    0x300138206a911116517007243d01181040d40c080070740400403c42580e0900419034400ea03c2e25062052070b15281459503c00b090b40542130001d101c2d844104414064007224411703d45006045074404c1b9622240038081c100e6a0040381e01607070a108112000d820320642540c103c0f98a40d00034012600c06103118050240003274800c0311a880c10f104000d015401044000c2c0c00760001c017001c0c0d03a507110303003004001c10405c45248082c003c1e03041804000505402000b5681101c0e0103082c0491298501d81040d801000c4520804e8955048080046040740e000300d0700607c1010141d50175103a01040c1e1000100d0b00100614160749948103004040020791540c2008180b030004050100d02035202c80c440e203031250000d52410b285040158158018800b010604a005002c554040c0c00002000c0d1030040c00c40c49249090700c001c0b0580126030341151119401104900d100311800c0142c001c825580e10003903c9110b6000800d01c0c1080006940f078068001900c001001200091442c0c006001e2104440111010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 262418821 1250 262417571 262417577
    0xa0f0506091503010603060f1e0e1005040c0903030e040e0607200a0311060c12070c02061317010b011b0308040f0b040b07030c050901020a02040b03071d160c0c1203 72
    0x10031588002d05810185004e1300300ba45011071f08900300b444007100d411031640001c6404d103a0308584070344050703450f445400744c1d52240025083d55440e0b0b0710b00c9110840c258003242d00b05182004559220382d00c09403d01c140c034840c3e40c4101108034010100804d440d00010150019001000400c10840c018080110609061003121003250340000c0b090341007090340d98040d004204c000411a0b00100c09014031503005440c41c00c0c1c0b509006000c5030111000320010202d00030710030003040300030035940e03114140c40d00c800030b8002200040c0d807103490f0285100e2003850000e581c0d60804003d00d580d50301174464061000040141c0840032843c03510200d0b400307100640195040da0703e00440b0004a021005154032450040c035031040c0a0611240050448483c030b8001010880140410105a030b8081045940e842e01110045007a008104c0003a080c01215403021141c00d0864501e80b80d1102e042c92120701c120312043d460004410482026035152041c8440240703010354010f1305200c1044580704243c01103001c0c2ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 262420071 1250 262418821 262418839
    0x60b0901080a12031802030f03040824040f06020705010c0f1206080c0d02120d03020a180518040804050a060306211e0f17030a0b10021e0c0d080403110a0f050609 71
    0xd0046400e1940c0d8210131b03e238a401c0060180603000c0700f0060622031840c010100351f40008074850f0100070304006000104602c038521900d6003841000e805075a01c59410000070401802c1c800000b804003403203800c1102c04501140c80d08010410903204810450b003444c3c0103031010510310010090165255103040382e20041080862540c0c0c1d501304202002008603480043e52580341c10000b0703000e8280000034010589100c0d0003849540c441c4e84041d07910b43d40200000704151264941502c00e03016a80005400201c8110700149450345030b002202103d1480c15101c0c2806030b00c544280c070540c01040d002d0400d42c14400409401308d8800158000203002d03d032104c141c4800c2e681e440400d8400074130450602600882408119050344c418050a100301303c076908520845d844029494012030081c0360245042401003072040b9400707101d4003229910040c403848000e003003841c0c817044c81d40145c081680d040b618200000d18500304500c120054801075600185194600010030519910100c10f55810180c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 262421321 1250 262420071 262420073
    0x6030b060c03030c0703080903040f060804020120030d1b09030f0c2c06121902210303040b0a151701140901020a030c020a020f0f0604030b04060b0901080a120318 71
    0x10b001860150480c650380598561840c01c004010303200103085110203800400041100952941ca070408852043c01c0c0401c89a58600040e142c00c0c11488104140c054078401100001c02d000c0010500000042c0c400c00ca00d20340c90208080b088a650303030110204031720345001e201141c24003a846100074031860484203400c0d00e541001c4081c90403c1c402d008000f80540d80070301001082240075038001402da440000c50510400d04695901e502d0407148039001c1e034170840900b552140319420708101100488000c03c1264240c05654a50080310b0a443d03a03502c00001c40d03240140b9000d001404450b100b131164000381840f01c410500c03402e142000b0f955668501507400030070f00c01c0384030301d1280300410001a2586001800542550205c8a101c004c5404c0030254400513564075031a07a44440003540c0e007021504002020800760700c6a40c001510110000081000300700c400d0700510b034a04401c0d41d101d05640d82e2420030070b94482c0306203001041003081c027001c180e03418882e500032001910800d001104c40412 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 262422571 1250 262421321 262421323
    0x50c100f0c030c020606010905040e0c09090303040b091902091519031b0e0c0309010b061c06060906020a0303052706010305060106211e02040e07020c0103020301080706030b060c 78
    0x14040380304020a86070145010000d80520482e403145034940041c008614201c00000c00200842c00f07404d03c130355601c81c0022460344080203030302c41d40080030700349031582e0808008095894004803402c80700dc00960001900c80c080114845c039034100300865011074003403540d007002a80c64005040440c000103040340361045950300810304541e10207006000d0080c17811801d10a8114584400250400020300030402542c000b003001c940d0310142044065459858030f01c400c81c054914036000550004001c121800a10f10b10030945030303003074102041080760b80e03038854042d119002d19208900158200c00410808680690012680140907a08100c02800b114403003216150011007030996a500403001030040040c2000030a014001d241403c2940e4400800c0950014000d0b19202442544035200010200c4452b42014841d01d151070042d52101e40315002c990718064210343c00c00044c4500208500254064400c4078107903042e800240a0032130400300194081d1904903050f6401801c20441a040ca0318 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 262423821 1250 262422571 262422581
    0x1060b07060b1309030c03080906070e040b0411070c180c120c091503021b06010f03020d0c030c120605070e010206150607120305010f06020f0601061b02150316030501031101050c10 79
    0x12086c0c840740c0304a642800e004084546c000c0c840d10242c0d004d4000c6c804c105402140c50520f030241101d01040722206c0101060141004807001002c0020200350f420400100004800599000000001300c110740010341c081542c142010340000f04007071001007149400c0c42c0e00902a8a0501c2c28109282591680e0142090a1072840440001d90200d2041c260052000002c035401309044014401541031603104580001c440c1b20007071140c2c038200b06c0f0b28208a00c40040d80300954026032941445a61486842142048104c044400c24909000a5016030140034100548071040e03005201581d100e01100541c0c00030340c2d102a921210074414200000c8021913030034181041350b60046225450107550300307030055440d0045000d542084400c20001440010442e0449286140501c40d03c1481d11141340070700d44080300a034100c54840404805c04444400950107130107000c19010702d0000642c811000c589080c08001e040001e4014000c02035031041c405450141c41e504c054481010340c490442c2c080b11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 262425071 1250 262423821 262423823
    0xd080a090f050a0809040b040e0c210a0f0b0c030f0402060306010c06092306040b1b04080f0c01140f0409020304210804022d0405100906030b010302090901060b07060b1309 75
    0x10f04e0000301040103080a0140780000a025030741440304d8601c0070141916200c0300d146c914010340c804541c004510f000411402c0d55492080f007921000690350510b60126050100705840082c10131000c1100a20a6000ca9205600c86980000c00c0c3e2916400c009041d0700191165041080b220745c0040071541c41d1080e0304080d449902c02d52680d07590f82d034554802c4203d0b8400c840c0e950300414200320201d4185603045074089c0c080ca0000070502d2455050305118050b58100d200180300d407508081d8001070008101159010980f03034405180140e5440703440c1403054045101c0440024001006a14003e4001d542c005108000401180f4040c0d0049d00c1c2a601030f0b541d000016030300c01c041c0700541c00c00c08090700010300c1250013200003841010414004003c400308090141da13968001441d1302d56000400c00103400d00040500540e507407070920b8031b05882c2c280002c0c0e124005203000304240c600144a45000c40d00c0c2414190f0801115450344401403e00e01079440d04598042005600f070581841101e46075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 262426321 1250 262425071 262425083
    0x6040905010b06040b280c0303020915190306090219030902031510150311040608091e0309010315080606060a0905130e15060a0b07030323090f0d080a090f050a 70
    0x8180c03020401303418105030100f5298020086d0082228140d015a091451640609015a0f80e40010000c211840c1440a50901e440d00c04108820780c50319922aa1141e282950303024803046899103103032000c912903a100149244080e0054030403441c00707908440c00890004003a100d507851208650458071500702e0700c004112405100901ca40b02100c640760252078028039007040703c400c0f10881003600e445980550000d0007600c00000d00e01c18402c000c1a0b0000d50b2044400300d90301c007407442c11a541d402c0035a8060100b4108505841c0784881d6075410802c4403081d00003410700751190010b00000e80c0c00700c403070340003080391050002c12030742c0f214142c2d07134039103100114005a01a50140d810303041c0140d10794074010700380244003800607542d20540c2c2c02c01a9040680701941d0b4074400c1c6401d5000b002c800c10007024095201900c03c00039101c607120305120f841000d0907540100c451030401900ea81295070300c1e0001c01c46a201007006d002056110702000340c845c0720000040401030325a1443e043c8000710440e04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 262427571 1250 262426321 262426327
    0x10b04060906030204030c0317071403180d021e030a050f030304020a06030b1518090a05011e0609151214060f12070308130f030b0106141206040905010b06040b 70
    0xe415400786000000b010149811030410b070443d5154400780c000c174800035010384684c5c481803c04913107800454a21551019020260078aa002c0d026125040400d081460240c030f124010702c0c1e0304220580c510801e5000700300622180783c1241d84616006000d80e8107406102d4921110001101080615281c06036400255228a824030411070130440c20780010040608081007010700b600c85000500c0d0482c80e4141e0662903154420442c0001c030007007031250b60301505c05c90a10101344910303404203043c1c1c0c4000d003004c0041e0b1103443c4184840c1c240c6100d250005404002c04202d40b22021051000747c0d20280303801000f45029040c03800644005600b90f08178080d0180901010346010080c10305a8078065400222840c4080401a02c07141d5522018007403920000b1403140c602c090420500250220054443c3e54584a041a4010038424010b60000c1282c3c046101360100c0b5445c140c13040401d800d20034602c0b958600050001034070f05141c00320f0b00c41d034035a0300c2c02c4016600c0201034800b5084d07802d01152 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 262428821 1250 262427571 262427579
    0x50a0e100902090f011224031202010c1e090e01030809030601080c130b0d060c050703020105151f0309080a110c0405040b01050613030b0103060f050f1501031e05010b04 74
    0x41600d040d548564002881005038400d141c5461440344c034490401d0800c02c64040f040042030010b01000503100c1c5426040300c200f51442c03104091a03078296030041d00d00402d1640b44080580c03c80d0040740141c00800c10b40d00b02c082c2990504a10b1070354030840792520940050340e80b14140700b210420b070022070b929040481d0100580c1010002d042c01011180001d20a83c89404041041c000f421400d951b44180c0f20707904110310740c440e20010b54034150b10500401240c7c0c41040700401a42010800f10019400d19001c11418018140204c80c921001442059000d40a54040c01a911210300b1a8240754441741c880010406020240101401e90707181c0c3c5840344008500345003084001c4607241e1041e440d080600001c5107281100506448003642d03a03030703910700c0c60945c4031030003076120b07840100028259000401004078603002107112605070354040c4540d88070002c03481c68046084828001480741c00d43d60781e45540c440e4206051081d0300408011081d43c03426058404c2e25000d81020f8001400054100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 262430071 1250 262428821 262428841
    0x2d04020304060f0b01080601091e03080a0c03020607030504020312030402010c0614071106010b1b0f100c03050a0207020d02130207230d080108070b0721120e12030c070c050a0e 77
    0x115042030241b030040f203d4075244002900e1008603028802c100341c0c2a80c0d05522a48490103030b80051074021036045c0e03c0340400340340104000d14201e02200103004800224011038001d00400f03004503402409003880710404503418501c2e4000038001da042002e101909004078101b84584900340c800c42c000340140d8540110b000d04110366540c88010290304c0080104034841518065030a0041903150b200c82210305855214580012000507079041e000d8210708295801c2d032a4090b00040c0107a84040c0070b142d4581d04644100d00405d0400380d005000402c1c64801440e180410241182400030014200a82c45c0c031080c50300d101c0c0d0740d41c0c0ae83c101214040055051010002c0d501d90308014a80b42000d50b046c240c00c4d944608041c45416440c08c408600c400401480400c1450344211104101c4840043c00070000c101314070000d000c554882c03030b052902128880100340807000039103202440b861074541031315450440c2d10030407003034a06502c8280e01081c0e0f656018901c4000300b00d401c48101f07160501c61040f03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 262431321 1250 262430071 262430081
    0x90314010501140117061917031810050702040b1f02060f0a0c02150c040b0c160e100e130204090b0916030221070503030301060c060e03092d04020304060f 68
    0x81c0c140110608000b02507411517400e540e011400f80c810301c1200c15800800310549100d50007040140d00c00000384410004000094442c1d40040c1c24038064403801d070301c18001001400c3e614440015020044040941815000224880c0f006000d0f80c1c22600c2980301001203124107200d078001a0450300178000e00000c1c0949554001d225040d08101404882d01b0180d0703500c042da502207114034010000503402c0c4265205071401810b440319010f40c0d03100250555030b110f4500800200541780c0103107000c00d00d240ca0304400f0b4407407180002100c4050b41000320030b403061080284542c060034903100289006031298018060418450030b845002c40c1030041c01581064104505c45400740300d46401007015030b42d081c4100c2600307030302e4841124840714090510f03414008141c000c1034040c40b0000000070b09aa101152912560250004009084594211903240d20030505080d620251a00401e0700b525100075991107080714045030703000684100000310b4141e030401c980c1603a820356180a8030078100c119001b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 262432571 1250 262431321 262431359
    0x1309020307120e070f1e180207081602031903021f0b0307121707020a140f040e0c0a06080603060c211302090c19081b0409050a14010602030403080a090314010501 71
    0xc503210300c20200c112503400006e52150300318450201c040c4907400099503040380d05987d00300000d141e81e290340c1d04111062880c10541203010748515070001c445100c14540c0d4110f200e6055018104614880c4120f40c0c45002c1030600120b1540d0b26450700c081303554100603000c0140009040018280c0c0c25003498098410324044090035800f0800035040145c0e90101c0c040245c0751414006100440302e18046500f0880d010101d079001847d1200714008001b0000b841c05d00d0300b400702d0f9840ca03140e44541c021100e8a100392103c540641c88500460298641d40c00a080e0211550108114104400b0130180b0f5944060318259120a000c01d0544151705154840d550305c441c081c6991880c0601c0c2c41b0b06407070500704c542c00190400c0840004944040c80200000b80d051a00d8203c00d40c440780c640030201c0040034140c4068422500d801c0c801046c80d114825568100e03015500030b90700f05851038507031407580e90004180c6420040d5080d00400010300c452b1907820041e0315880001159030401942e01503104801c0c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 262433821 1250 262432571 262432589
    0x1002070b0901050c040b091c050610050f010c1e0f051b010f030903080402040b060405030102040315050702010506030d110c0402030106020a0312020313060f0e1203090c061309020307120e070f 84
    0x18001c10010408680c425a402e4400d4012084508c144100f60b06804900400030300402050002c031900490024003540c0d404c6441540120305500159000c03440e0410041805203000308110025044029050314280903070001408030b281d650b034240c1001c114407602e0703540030943c0c001d1b1718055074889021070040d01a428104400c4842c0d4030b0180401c0750040c402072107a92910a480c43c9529007009540041201500954940da268079120300038400000c40b5000b06031500303001905040c41401224000c2002801600c6602103081c411100300480f66070319819441210010a40c548a40c8011802400a0f03030113001c1070300e42c1d840d004125842c5040d20400840c014400e000260340d15503000d420169110000140b051030405140c405460a6140300d40640102100030f00119413a5005512130081c58041d61090310070340c0304010b1203000b10341d512107009031044010322020310b550380107540207103d45c10502d411a11040200d0240c4200c18925445034100c0381d4108a0703451a00458409803e91b01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 262435071 1250 262433821 262433827
    0x902030d020610092003090c041b0e0301020a0f05030a0b0913020405070f0203090f010201060807090e0d0c050c010e190b0c070e0103170a05040e0f01060f2f1002070b0901050c 77
    0x42d0000d026605e0817454035580940080440c6c1c01041c104000b085980d030140c41031100410307160044500c03807240c070401c4002c5141240340300d40350324061007100ca1041d80c94468512010401e241280c00b40c20050001020b180d99800642540d0381e0200b00c3c5120342c4e44403a40e10701440c5188144016901c000d41343c0010f10607219610709505070007205980e0b4680040d201241c08221140040340981942e034490082d5028101021400d150207412075440105041c045030300c0a044548206c0c0d12900d071450151443c1c00c40c40e510700141d886890140c645800c010100880030000c41c07889003085a00f580b00c41e0640c2000a0098070411051103994020a580c0100400035850340e00c0e88400d07290201c50f15600c0c104c0000c0e0005a481c050000daa020785241c1300c4125061424150401401c5d03000e000f40c10100700d1111080500034800c0303c40c4a8260480c0215401c40c3c60a00c2c0110700011850b130031a80140101c2c1c0c3d0b0490b1200c45840503102850080003440014200400380b1821148003410701e0520301410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 262436321 1250 262435071 262435091
    0x50606040f1a06090301060e010b090f01050a1211070218090c010f0804020d06061e0302010e22050405031c06050906030303011d0901091505102301120902030d02061009 74
    0x819210a2200b1054405542e103041100009004104980000381518560400428481d004a0280c10302d0081a504c0c4126035000703030015602d174018060b422002070041c000a440c03000d029044282d504e080e22059a0404500350f00140861481c401d1508a5402400070050410020414456841401c0c2405150340d04981d2000f00302c90f500500c064020700841d240b07101080840e0f44110b00810822840c81c1c008000d06000406540740d1344070607400500300007450351451900003107880104404e014248502010341211801170140100700307035031030700081c400d0f550180d03145e90600d250510f01510028040303041c101080345ca01d05c041c103070ba40a944144018010100000d01a13040e040c041e200d0741100b6994050003e0142851310001803103aa050360402d038200348c1903046103004903280042d80305102c0d00d07441c10404031100091180c0c110740c4048450030702540150740c00340c8a001c102c2c1c0003040f40c00264012900d403110000c07034403006038441c0c0c00b00183c2c0d4100a0140340600310141d002d011503105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 262437571 1250 262436321 262436351
    0x80c0307090e0402190612150e0a091505180106300f1b0602060603011b140f030408030414011a04180606060504150212070b07050d09050606040f 64
    0x45070240c1c501d8400d40c20301280c25035541c40c60311040c483c8000c45c40303404280c5408005141001802c80c10361040c1c100032030800c031408480144415541c64002c00742055803115040409003191440c19a01c8030303503040c6c50050040b800d01841c0d224400f5200c2c2c0d020343e04810170103623007195080d520803003040d403030408c0c0d45900340403024140c01c2c1e040c070003002c401d43e4050343d0400d600764141c0b0341340c02010079155a0200545038070422403001100c01c2c0f5001e907801030740c44c0402e0500742e50781000c1c40480500b80c0030440c04058044d280c5800c16004480105081040d2480c1c1401302d544240c034140d420030070201c01c0208003d00c401d4140304180d0680005e002a40c210050305284c01013010000d88215210b0245006030355920301180d403041d800c50b45c1441440c2c4e60f01405405540700b4001c4800200c10460f50401040c0006558402e0b03007020003100d032030220340d6104d5052485c0094011410001c0400c0000d245101078055003003403900610182c8103500b000ca00300409c54207281031420302103042c10340b90301075550 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 262438821 1250 262437571 262437587
    0x90506040f0b031f031a1f05120f0f010f23040b15060d05010807050102070b03010314120f0a020c0117060d050f0d090f05010801080706050a03060b041401080c0307 72
    0x3000d20b40340d1251035521412203000d9406280c0405040094000024816613126500204440c40841c030a541c40715141d50036034410021240e95100b0240c2001c001505140b90890700c4c101160042d1140f48440d500b102d4200300ba42445440541c0d10303950203e41590b8144030354040c03881480d4902014130000e0000074138410008102800c090a51000203c10307a650080b8204203800c01800a0707655404110004004c220a0284588034819850080b1300c4d07500000d001c80c1920207540d001c43c196032031503455444208044c800480540200700c0d135596a6105007001c0c00e4002c1406008503191038000d01d0081c030744031003104d14034100b0a0b40d5a44404100008203c50382203141030b1030b8001010018282140b80428810515a1030700c10344d54420300b03095000c050f40c010f0301d000c0f00160340065076407401100c4136602030281c0c00e0940c208843c00c005c0e09010368010001c00081c0d01b0007244255844829004a0300140e00010380c0f1840c01c10526450369105501540c0b201c000c440b16425424202c400400c010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 262440071 1250 262438821 262438829
    0x1401050901090e10021b0c0906060f03060a030b0907030605070905060d091b090c0905030d0813050f0303010e07020d0216090b0105090316030b0f0609041113060b0307090506040f 78
    0x2540c0e8095000e040340f400c2c4030040c00d030300281c0f40a540d00c55070707100c02904140d51002408124051030442d03100500d0590724640c06800c00400242c18940f034501c0920040d40040e00255000d40342140020000744908007292181c40e1200c0a84000c038503605140d4156040103040d9000c020864105103c60303036601003520740b0300b4401400081e061007a0304e860120f10419800200c000a0b81400018028080e41c02002c0b9098440e0707036107039000c0d943d40280341d507030801c1482840c042145140007030f191380100c5442c4013406005070201d80f1502c1d800082181180d0080c2c002c4c00b4090070b014200304003580c0410800709818030394401440c145c0c1115060390f1681c2c41500800b0703251500d40a0b0545568400c2c400c0e03804164009050b141c203070038880b04c0403410440c5071008441c80314865001699030707650001c846224200240405444d55299030b5095002e149000e15182c0c480031030118891154030a11a940c0170748100740c2d0040d9030b402c2c400e07000343c0002641da20084c450a4100414480c20280004030000c603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 262441321 1250 262440071 262440089
    0x9180a080309030c061017030928032a0b12160e04110702180f07050a110d020c01120608120d180803060a0504020a050a11010209100809011401050901 66
    0x303480b0100c00d241140310300b508200841c800c5a0a00100082c1c0340b00e2901206d0608003080d50030007825429a8032800760a20283e4401e129132800c0001d500a18214017455400310b0700c100c2c03a65165a119400c5619100c0300410200c1d0021641340743c200090030007000703000c08841c4942050360a082d440b00c080002441203071811170020644090502501011528200040052000a202c00c4c440c203107680041e8400c1c0d00c500c00070742206003004200300c0d01c85c1c05095200000f0b619982ca180d401d80701c690240394454201301101202d4030451100340700101d800c1c005507014161209600c2c0005018801542c3c890a1440c41c1000400002c6000a55503100d416040701541e01e03081d071102e000005000c4800040030158a0414540801c40000e00861140408035041550b07151240300b8013003240a00d0526801294041080c0900b00c0c1c010720400b030001c43c4103400980b61000301c2000c64000b41102043c4c40229102c0414800342c3c4030300303015000b241c2e54400e000204030761501000070910801840b0300000b0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 262442571 1250 262441321 262441327
    0x301051e01110a03120f020405150a12020403060c032007061802090423070b0304080d0f15093b39030a020a09020f13080c09180a08 58
    0x1441e400384800045540540c001e451041c8418100035004001021008804902c1c050040e4442445031082da015110090b040340c210001c40c128008260340013002070014042c1880e5081e00140f410700040c009113110b0540441c0c0c0da01d01c00c1028050311a4240c131040803140e582e5600c803440d80c1d144183c480d095004140401d50388281d22050f00c40d40f124000c040c0d004000760041005001c510340000726048400d1340c4440c06140782e0017106031205a180118404c804040010401281c4994040c0101e000382050000d09522803440c0e4900321142d00306a1807241100032010401001d0700d11812520300060041c040010005001e05000c48171420403100c40e64001180d80301081c441044207200811a01000500040d00701014070352039040e8440e0101c000301c20703000c69010b6080100316295510381c050580b41d501c5041c034400d800030390410520b0500e01c04040c840c2a45482e0031540d50000ac090400191040c9442201070124905006040030480311812280d2451060001084200c0540000132161 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 262443821 1250 262442571 262442629
    0x10807080c031f08013306080103030311090415060f0503060a03030309080f0c071701150b03060402090a0f030303061203020303070f0e2101060801111903150e010f0605030105 77
    0x30f01018160421034140d8a005410090002400038811801920090002020713080040c524072600c418040c0c10001a802c80040000134026048040d81a0034040e280d4204500345020500710b9000c0c072030019800560810030010b031504031100b0b84240c1510314181c2e16500d01200840c9440380b00c0d1100804155407800c3c03030018002d6000641700300b805d8a1851a9445044200c1150756240a0103503c4d1500c1e69100750107085c40d0705200c1c5034000d21094002c0c2e681c0301e180c0144c803250340c0c100070400c030b40258003000008400d070b5510b00340e04080c0c1121101c1086050860074010101d66071904151a2030001d9601c5c000400e8000003034a501a000c0d1400d0fa0b1421483c00d41185c00413110b003142c40d000001500b0300d180c291421038007403060f2150940208411956250341c0c43c02e07104008030a000c00702e01044965001010b09840403084002800c01090000c0c2550a4803150b030105c2c1d01070b80350380441c4001407082844580d5903070010a11442c0c99030540d414100002d11000344004d1050005031443c4c01c8070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 262445071 1250 262443821 262443871
    0x70f051e0105150402070201020a030f1202220b1611040b06040603020316050307140904090c1205010b010203040e0708040f0c1205011407050901050304030e03100209010807080c03 79
    0x1400d5451003800015060002100e581c00781000f52039241c1d540042d40710034540b6041c10310079103041e103405900800103801d00c0c0d2002c2da1460580c2c1405000c100160390a400c84d5202800100b007110b840000c1800141d45605d0280d80800940d0440c040450007041703c44028010007080e909056001400b03c0f9507809201c000800405041d0981504440080b600140341034143d405144140e040040c4091913a200d040210760310700c4115044000325840c655498110003034080504000b00001d000014115056180c02c0c0750850144c3c464611840c040c4600c00030058280603c2d04d440b0310a00040d030404e8141023804600316001440304041044000c0007030140240c01c40369108250b000b0b02184800f5854001448161640d00c1c1d0681e81582840259908480c6040c60180703c6c1906956590404591000440b2140c3c13010340141e041004103d030344641950240310061140a80d1400140d42c1c03c000300000d01440d0006008505000001d810032802001080031203a0281001d820301c0260440715420b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 262446321 1250 262445071 262445083
    0xa0807020c0406030606090c090305060a1122050a1505030a02030402031e0331090902060706060602070e0a021303080d020f040902121614030a11210a11070f05 70
    0x5a940b0904140f400011302c41140d119a0130340d002c0480a01c010009170350281c40f51001480002d0180d4404000113100300c140303902405020080320341170b5180480d450360b894141600301c0007601210351003000800051401100c0600140048605003916100ca400090002c0c000100610b03c100d800100203411558240403403103d0142c00688890300100928515a6036001014404140310074452103142076118100d40809840c568500c800807d800d291000d00607000203401240c004400740102c6e40016254020080600065801089035510f0024521010f407405032410149a1042041d0f00e000c0c0802c42145003074980000c140d5036564075455040707000381726414a6250800d408603021a460b0119001843d0310382188400340d00b0751312a542c21a081306d0038071600700049408442c91200915103000950340c0015800e800040381d117180544c19003d9030020071810541916488014600404007611503004800300404020407d82010000c400e84551940a0410b46601040c0700c2005010004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 262447571 1250 262446321 262446343
    0x100b010e040e0114070903020d06020d06030c0e1509060906310509010b0108010e0a0b0a090c0c0b0901110f0c0c030d0c2a031203060305031603080f0c0a080702 70
    0x8200002e1050b64081402098035182d03080610b80802d010580c01403098400740e00b40c0390010850144c84003d030352242c0c000d44c412103030840807a846030780000108018058480080c1142c95004070759160034030005180304000340080e4421084281400701c2e039264804078603400344003644e0240d03900c0e0320760342070600007800c40d44074840502009280f90b040c0491070b0401806040008002e006020300c50b0010f4407420405d00407240d40c01c1071040040c4031089541c01504540002a003122111500c801501041d9031980381540c010030b2a61111508001140d50380c0c1e6070102c5994000c114601804440c0c0d203191240c00c0041c00302d0708011864a08800d07051080603400c0748000e04a0b0b804090b405006030170144000002e440c0c0c100b80409450050560040b480d07a4200030b144140c0c445401c1d6a5503218800d0000208010555951004000218100010104484034050804800106241c002c1420030020020a54500703482c090200c83d200b20016a4070180d030354100000a81d550340c10807072901d008c1040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 262448821 1250 262447571 262447579
    0x2040c0311131701090302190804090204030602091306030803181e0715030b0913031b110f18040b0615040906060f0201200c07051e09061002100b010e 66
    0x36500301610b80040e449400c59002040d40b0003002000c00b0030303500300c1c0c0c02d43e00081d015070042200b0906c18041100400f540a01c41c4143c90b0810341c403000501c0898001e41c0044900729400120484145426102171040101280080c40b071141185d076401c0c410f000180110500ba0030300305d21000301460602c5860b120803098505a0501001c1030049955000d0a02c03464071560380010707100c82481c1c420f002c0d840d030407403010b402d641542d1924207000c15210b075516400d80401004a9078021010080b401c06000e09010b00c0c2c0310941d003281401000340000c65920344901c160285181e19245071020b02807154400d41110003040c05a07158400f06c6c901501c00070b442d442c22500054081004031507a40100c05550382d82c0c2d81d50010244c9600d05900301d409043c0705050301c0c3c168002410310190340d0b00003404425080c4050311006075445011039003c94a0741076101d0725443e02c00707a01015080c030041e400d90140080750062074680340c10001070348803900c06080c20007003a10794540c1401640900d10310515030700b01078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 262450071 1250 262448821 262448827
    0x8060c030402010f02070602070302010e0a1d01050109120302070905041a01060503312d050715020312010b0724051e010b22090213030c0b120402040c0311 68
    0x200816959481280c00300d0200d0419072840020520006010040e61f013070307800a14819045d03070015503c00c1080c42c407440d03108140d1807000c43c10500400d8441c0109000d04180780095042c100054103140d45a0040c201c03941c00140108003283d0300003101c0c1308490410314001100d407280d04242540607604c12240032502c41107000015065400001144038162202844401c46184140b04101090b54004460020b684600c004085011001d2031360548084c40134001016030041c0c800110498251300135501604561410044040700f48600c4444021910145d03103051811459040c095406010f001941240803841804100501d161406000c00103161510100101202080070f0b200481c2ca400c0007440c510307904200c54810420050598590400c071608011002c901c40203000403081d071400c1404a00980080da08206100500c102004c005000040b5030071401c1941c1102030075408500800c004000c0c580c0380d0456900c2c900c2d0040e5045a0200c0c2e101c1240c242140640381140002d1801c10b400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 262451321 1250 262450071 262450081
    0x8040506040609060806180f09250306060e0606031f0e1312090b0a0e010903021003090b0c0708040902180406090617032502030a0c081006050607050d050901090806 72
    0x10700b800440c2d4a944c1c1c1c44617603946400500c4090443c000d0b404c0209103010002c035043d420140034031075001d2240401c560702030008801c1c01c5038001d05a003109005c11090207090051080d10702401c000f40075918000d100b107042079804543c1d144402468040751102e00d03021410503042130f440ca41c000b00280900d0005078180400388460f2034210480807911808600d1044003440d0158401101f200d280310007080c141141c3ca1400c0c4c5002413508171843c108403002e00017000503036800c044840148010355000a0917400380c03a001c2c0b903046026114641205081c0650300c00280c0b0641102c0603540c8888025803500083c0c100406035900008146074020f041060100708074100d603108204a880007007407580460720700d1284039240d120340d0303204890454136002c80c4150401e00040140421b4805001c4580c600201d4031030043e480816000605690065401048150b0541c02040c1c00351004440c190300d03107a4075690715559080140107071414004003180d1080c1e581e0103950444020b1651100f40d480354905 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 262452571 1250 262451321 262451327
    0x1a01210c0206010f150806090a020408030c16080f070506130e070201140a02070809040209010512070801060206010b0306010507140c0d0503130b040e0a090f150903110303160804080405060406 84
    0x42402104060b4014484c001a40c50200441a183c05126200c69189440c0d1000340213107001c0017001201e030580c0801000070b0300042003000340340b2003e40b0700140000c03619481d012410b203c002c0d400200c5941c84200c024040c40008030740c01080780c0c03048400310ba03105404402c156130360701a940300c40c90791000c0e1410045500d4040d00301d0b02985404070b8610301d4035131300e401c4410100d008180d800f90024409002e2701003079091550040034880414100359007001e0500c545036507400412200310000075a20f500406c82540c04004260140c40d0750540380342540b81034000202a40280e0902400e08030381181c9404144409002c440180c0d040a0403400c1980aa070030200d03aaa400149048500b1a821400041c080d0f140c8080c0c40039258282c0380c04845441d06441c500260012400513110420301b0740443e00000c1070027030814956011503001280d1038a00d4240034211454814140d90281c00c10002c01c140e0021751241d150110429041c03414039a05e482c01e0082c0075020b00e8000740e4007e0400a00802c40d603030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 262453821 1250 262452571 262452583
    0x1418070e01021c021207140106180c1b0204020d0e101d0a0c0303110c060310030201020f060f0a0c05070203071e0816060c14060f0a0c031a01210c02 65
    0x1800ba000c0350003080124a103110784500507031031540141c0081e4225840c030441d60006080c1c0381c0c0074060b2413030030304041c408180c02c6455030b40c0084d503003207007040d2903208060300d500500a0351409824014031040c0807405020003451440070080c462035000445001e07c1d18580e210060100301d000c101c0e440b2005140c0318000414400d0070303075000c40c40840c0d0018810000000c85c4000c155010b00080b0000e803542d5002da60184046a20100c54000d10701403154a450307000207541304850290000100301d1440c000a401c1c1030034040e20403156040b0380f00b0400011015002617030800230720100001e04100c03690044615002d10070000f541070080f2000040c401400020042121920782244040c0e560383c3c4294564a01d0541d00ca10b020440f0188200015400b442640c031400380201140b04000751010320140c1401030807101401642c203414203100031100188141001c0003218201080700354211900070b04106409a0314030704200145107003c001c14030899605004408a207801d00c207000000e64040c1d1126 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 262455071 1250 262453821 262453847
    0x302090c1911101b0f1205150108010e04210306080a050a0c0b07050a03030f06050619020d09030804170a02030d030c0f080103110904031112071a010b0301141807 71
    0x4452044803c0c4590700030b01c148098010030624018119502d00416210710011401d24002d211221004410b4400d00f8011144181002e40b42d08040c070003620005030141c072040e004103641c0c0302403404001c0001e40b414944291802010340741410580151000ca014142c1600811000d005081411040000028036111528031031450100c019488424410080c060082c02801c1680110740644c082030007136205a51070000c65030f010503200e07290030100e0782c41d500450394034524070303030744d15102c3c00740340e4144064540d4628030300c1c000c1d0030f0720f00d95207540790f41d800366001c4c8000d1414003081141c00e41500300000c0c0030b410303400f0b002c0e65084a103440c800350062000c41c481d0804240707407903203c2c0d4031140700b031701000e040e00d5100042c8408401403106103c0304001c020002c405222400c0c00341c45501c00100301b010501440e1000c02942c803680c0b450940c1c0e0b0603805003070041080040800500c03400c0300c0207003603d05440141e043d443c3e1503141c00c4002014801025640080b00040030144130040d40c0c0001c00202030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 262456321 1250 262455071 262455073
    0x903010b010302091305040f0b0103080c06010b040b040e0604090c0f1809020607110d0b240d020102060f0406090204140711060403090501050a032a0215060303040302090c1911 77
    0x1a103000005406a1168110156020241903003502d0900c01036071246410901607403050706540384640e80c40308000e07002c2c1c000740d0b003140b80841c209110b83c004008450140144400003070521b85406010301d041e004a0040c1080902e0031000241e894480e030744041400c2d03400542d009a103a0f40c8101204d13448425026501144c44041d448604013405400340303205082d4040c00b030500e0500c60740c50360001c0e1b240624050f6407080702d19040700080703405a140b85010b191241d1980c8200c0c2d4120200214282c0110680c500070740b9082c002002503a00410196400540c03000d0810341c560303e03031030810700802070210025130091078040955804c5040c80c100301d00c01c0c6a40d0716202c4002d0304076455503954000842d0018001850f000d030a02c640e5208402501143d00036003000318070b801c100580e9004100c40c41007096a44404c8025a07142c0036410440204000c2c0100c0c900240b170308264020a850713224078000a4090417407240460445040482200e007090300f40305414508440141000701441000c0c004c030001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 262457571 1250 262456321 262456331
    0x206010905010b041203110f0c030114040c0e0c04080d0903020906010c0c172a030c0604080c150c010207030210050c0f07061107021807020610081908160602090301 72
    0xe0562a10a40307042c2c0e082c00c0921410585031401251880b90702c0c08084041010000e4070b840d00340001c000085d0309041c20380180095200c0070091501312100c1010a8100c401c02d1028800442e403903040704802d54003001d208081654813000307902034134456640021140c1c4980318650040540c424440010b40f442120b02c0c89458407007500454055209400240014003403440800403043da0b903150780941358403841a50804941400d14204007955034001241e800d560100c3c21443d85002d0010208007a8102c1e0410704241c18402080e03681e84c8408652401505049116485400f81c00180d41880c2112002555114078a160081d03c44140c002d804007481e042402007205070303a0120645010203101c04009052501c540c440034007a1160020400104404000000140c0c03035420b040220444401c55044042c204848000e01d007400040c00c0c40c1d2800d805030384c28054064003080c100c2c1c0c00490800c0d8052a12204c0c1414581c5104800c9c000d070103d00d413a0072440c20000c1c03580241400000440003000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 262458821 1250 262457571 262457579
    0x307020307111e0f01030621060f0203190c140a021506030705130209040f060f03140606010c240509071a0f0a200d081f030809240301030f0201020601 66
    0x1c0b2403c2101e0301e05862820950015516080c0110300382074010701450081211a076030b42581820f074950380880d03400398512035415020303c6075a0203840c1481411080131032442c030b0000300d20401d0302c800c060001003c03a106e0b05072018030742c42411000e040085110020390f8502e1a068080d42d07496902060b00c0551010f040042c009181c08111002128000340c407509075846041d8010300294401070000350b0141c0e54840e030080c0000e2501c41c0c000136100e10b9010f015102d0a5040681581001035440340f1164041c4040080a0f40d001c0f0401031070303507440b440c040c900c0c41c2c10172007078008032040003a0480c2e0540380104000c0d0101c03001500400300d41014050744d1200c610300342040c40a220b010800343c6401010040c421b0513501c1540300c401640c007041325010300c4e41292240541000041c0321424001540c400078044016a8450000c1001c0501c0c42543d0103240b0f550707101c14aa00070340c5111445805030156000c002c680d0250007180b071004080303290350b8030342c0c49160140b50721203c03240690040c423800d00042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 262460071 1250 262458821 262458829
    0xe04030903150c030c092301051603030203061903020d0f0501021207020106060e01020a0506072f03090906030a0213021b060108070e1b19030b040f0605030118170a0c08030702030711 80
    0x3e054071020709a034034940c0d9540d1a61f0010b1607140d070840341044410410215011a800007240840d40300307a40141e035904025040005890424800e4a040300c0640d50400040e5620904000050780c489481080003e00c2d042c202c1c024021001040890003002d0200f00340f065041d8043c40a641050704c1c4d00301240e101c00300490740e40b8042c2300c00810350350185011a1015004800b524041182d0117281c4d4582d10302e010025031811b00600c40c100c0f2540c0f01152188103482c10034220b0f80e0091003500100900c00300d640000c1d8003448812032000426500082500380d43c40701341100e099520043d011501c50796503e8005507554079151107820302888065000c161000041032810307500d8046c0d2a003d5060808507400b000800d211491804d06143d40e58092582c0c0d91103074002c041101c0452100010300600d81004d0500b0764040d1000c07030144909a00c0c0d107400240d01c61000340c08a50001501d10f40b940030425007624042e444002c064580070000c0f04200e00245d0002c0100810351003034404440310b44c0c500040c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 262461321 1250 262460071 262460087
    0x207030605040809190f0602010b0f09150607030e0109060528140c0a0203060a0b0915010918020306030106080c03030a0309020a08150406180c0306020c10150807050f06040e04030903150c030c 84
    0x2c2079005404100384d02f118540a040346801c103120082c1d0b806071a0000340001d02d83d50001c2c400700c0110300c4420100d035056810403003490041044e4100f0314580f02a600b007254101103d16481c400200030800c0d908013442c4a19507062a440c4018402c580e02c060035101c00d9a01c6854010407442840b030400000d1050126015070b90400d080a00900c2c841c0e21007040c0003c040001d4038142d030400100400024030315034030041c0711803000900200103989040c65411305003907a5494014010381c0d4014038100201c1c1e10004201c81c0002404c0c43c0c001994411807002801c4002d03a5480f456561080751000004009010b081c1806280701d581c08000c0c1100070242144c080074107580140059950505c1000800c1143d0014000e1000788800d880480c2d4640d82c0d018125250003210590904001900340a402801c00140002d408201c1c0ca001614510100188040c465800b070303a100c80c146d60001c07070704042c00f65040c82d0103035521215260115444080d54001015400404030003e030078564600c1030f244c000c20b01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 262462571 1250 262461321 262461341
    0x200405210304030209180102041212080403050d15030b07020321190c0309051f0e0102030906040303090201120f050f0a05040201123c060609060207030605040809190f060201 76
    0x40e60070b0600e5502013005048004140f0032104418441110600c0d000707100400260800800401c9801100c0c200b2118400c41d00c0030410500000b0014032000c0317a04030302501d0704d0101d802c8010034001c40b1840c0c40d40000607580d1000b02007240701e406014509401101800c16009542c4645800c544210b40304460b8800640d0340202e5100521170450b01c004441c0c210320410300480c203001c01c0048855130380c246014010800754042130b040320320727441751070740c40340207801d4080c5208009600b0b41c10240c444035200c00c0c0c041c1c0000d007456581d1201004590080a40014200d840601000f00c2c5045641d2503000c4c05084031031a85c0e401300b103000202103c4880c4201401250180e64448044c00010618402130ad000c4000c3c4407090050505403040030148800034000e100034014000c0204a0b031400c7c8c005680c0660400c40c20302001d80000d12490b60f00080300c1c03007182e401000101d81c5480300d060080d1284250181c10f07402a10140345100700e804060484411102c400441e09400c5640c1c440807403ca41c10019 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 262463821 1250 262462571 262462573
    0x306060d0f0818060d060e070c03020c101e020105060112020304030804030305040c0f140f031c05030703060b0315010905090c09090910020a08011514040b0d20040521 73
    0x8205000c07400c0b4502801c10340d200302e1080890900d2140c005205500140f0310003c0d019140d81080c0304c05154080801c0e0001000e041c4007a80000c00d58000e0344501024852500401c0c2c6d29181c0d2440a2142c60503144044562014280f0001c1c0c14100034040c102c2100e00700e0210784070921403440c8403050720882c0d01c00d6801d0f541e46c2d903851f2544c0c2d604801406c40a0b0054541030307000b28000c12103810b030301c0e5414001c0200d58214002074241c0010701040c1d410100d1b070184a500000310070a003e0854080b40c05030b002940c0b41c00c91f0740c2c1d951600250014046c5400041440c0004020800d142025000e00390541c0d07001d88030440319940e070380d04020300b60004a03034000d072411060155003004c0c100f28140982182884050b600c0d4007440f1400708080760406200c05c0700052405c1d004120b94103202c400314555030401e141c210360b04404c0b98660303040d6104903ca0502e0042d070005202c005040594020a501502c6469420b0008000c00d031004143c0c1150082c0c0c0e00c2080010141c600e00a0801e98040000070020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 262465071 1250 262463821 262463843
    0x6110c030303040c120c0504020d0902130603170c0f12040306200d0b01030b0904030306320f040e07030605070f0201020712110709091506051c1119090501050306060d 73
    0x224921741200d44000840f40c14105c0360020034190b4541c006010035900e1200b002660000d20700400450344902010306d040689000c0040c0049500f00d261f452299410125090762015030b615842c0ca044182c180c2e4840e6405104140c0001015200003482140d00401c0140407800034500b07907042e883c802d03580c0e40d61003101c200408510310f100c03908806010003050500103104001c0e403020032000e103030032582140003d0f6260828003207450b61a0280301680b606481c01162049a054103010300c00000d003101c1c0c840e0700c6040482c010b030b07511030b000a400b0f02d0f6541d050310042941e9103071160141c042990a0030100d045c0d441c40d080c04600c14400e8a490b141c00400c08140a8003002c415160070426219985460007640808a02c3c000e240c0031b0071403520301c02c485046590031aa81a04211511034004d24454140640307400803a010f4808004056038115080e03074980c40400d000118100702c5814035044c2c1c000c41903000551450746034045030480c4c406038295082640e0319000c0115040442e100285680307400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 262466321 1250 262465071 262465079
    0x50612061801110408010203012402150a06030210030506010201200430150b090f0f09031b0304050f01050405090f130804030602130f15260106110c030303040c 70
    0x1c2146880344001240000a10210034030082c08554031681268031107a40020040202d031071441506081b01010b0642d03121101c1c0324020094550104c00300d2141c009076110041400da106a0340804001c590048c40c50520007081d00c0007030081e08040ba480c0d80954070704080600381c01c803100d25140350080c001030b01074903080c10008615a914000c00c0940b00f5100b4000a40140c1d030b2918003a444654080d1402c1e2038400800580300703091303942030380c0150300034440300c42031004041400801a410554802403190681c0d00da284952a5003e07030b01d1041280d08860032201035202011006005a40095540b010f054035500f006441c03520907885110340003120040001c080d0184241c50640255140e481d8460b1807900b501c2e49580c2c1d0304079070810b85110b0341c006442c1003807200360000c040c010b005812101950390700c2c007031070405e4400300e400c0c83c0403c0c42004644502101500c1280104102051003503104950312004018402c800710b8100030300310311481c2140a201e150000650344610b91001000c20080c0c20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 262467571 1250 262466321 262466341
    0xb0405030a0f0501140907090e011104030210022a03150f060613030203150114031b0402070510060308030609090f06161e1d0d0510020a0c081c05061206 67
    0x282e08400c0d51903545e280328500d402c030403100b41e081c001c014480c01480341134100801c0358121405442a50b030a607152242408022880340d007600d044035011150080741515485080e410030192000b5400d200c401c00000e04030107072090601d032210003001d074105c6403900d14150310307440760440030341d8407041241d28400010310900d0940010845806030140d0615001d990f94086032406c005184010203c549003801403199400e8441e0705103260b0b40850041046180b0900240c6400b050301030003038001c0c1d400107084010300c1000c01440f51651041c0e4020842c4070340e01d083c80512904255102c40c1b05440840c045101031000281c61000c1c161700030080c00240c0ca50015550fa01c1c10070503d04030500404100b9402881d64001c0c840d48000d2054803594a0682950010b85001035a00c2480f03101e403030b1605408003c500000744803540200003072070069503034030851820303541140c104e8001401003074002032014400c039101040417181440480144044c1d1542c43c100302c030141c0a400061855488500010a1148 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 262468821 1250 262467571 262467593
    0x10f060b0324060c060c07060c0c02101218140609060c2502120703030305070f090b0d0e0a050f070e0c0a0c060b0a0920040305070e27010f060b0405030a 67
    0xb401000c040c58955169861400c210301202d07407602160001c81c9002c148402802800c44401d054a8400e07542c04a40e40024140012451200c08128000640f101403c5565004e900728100c00c054100c0030314201d1604201e00704501600c400c050140700c011504660000841d40d0060002c45c0859060032903001e1000111400850107112080e2180401000360f2541035495060940840c0600619421400d002d0140c0c0c101411060800403091030390318206600410150541e110448199a21410010700344040d00c0402d00c0c05c0038501170041507100300030340081d1a41d41900c103d0160345401d81d0f104d00020b402c4200b200c110300003039002c100f040107040c80b40c0082941c0e01d2081d4000980c10404c000416841c090b19000580c4503541c1c0c413401d02c19455244261901c040703001005910301401c5a542c03645036800781c031456a10b4500400402e00d0050b078610080384c9181c0c0392880024540d00d4983c40b41c00303001c40d9601444040e140c90700c08500e0030510801c50301981d0b006401800501c22075607400401c45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 262470071 1250 262468821 262468891
    0x30c170d03181e1a0c070f020a03080f0301081209060405060706060e150306060409081213150605011d010923030106030308010501020d0e090f0705120108010f060b03 73
    0x618400340603000200107252021241e03480f000001010f180c1d41c41c01e41e000d80e160340030810481c0751000400503202c441c041111501588108082c2e00800c881c4082039100c5031640000f8101600071030484001081500550f0483d20104100c0307048680c04115440c071441044070079904140104000d01680c03c3c4403000b482443e110b084000780281d5510950350800d0000e40d6000300440c00c403040c0b81d0003440c040050b144c0142044404102c01103050303440c41054492411114010030040002480c60f64040e101040b105410110762042518000302c00d2001f82998050740b404600050b140c83c1c4100700d07107140744404140684459a22608004a03c0e078900898030b03807030001510502d04005151401c2c0151802184640c0b10403002d541040006030503e00034041d41c0080008000c0c1040341a545c80540a8200b6507101c41000d060b00c0e41c510407a00c62060005000060700078600005084905521224400f5045001044800e0321411410182e100a4801b0704000e810b82404503644010340c00102e0f071701 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 262471321 1250 262470071 262470101
    0x30a0503091501170f0c1f020a080a0206040308150907050906040b0c030304020102072c04021c030908120c030909090a0b070c03031107030f080c0408070807030c170d03 74
    0x3030950aa0b25007880c8209820414001d0982080c00c440a00c0801c040c2d07040303202410140035000c200d0380c0800e070b000307900c820010400d003240310071007001900900a00046540200242d65542c50a400c047e5071781d5820755045000807000c0380029019803605e040c040d20500300400c030b4038a584900c03800b100c154100061542d840300b002c1100003410001c030340007040d00314901c401850312858240006030a0031403591000440c20741009030f40c5014240311000c510a49002540c0d118039407541d001090400015a0070045003168141c495400e05401c4031234401100c0c0c00d00102c541400c07854004840601550681c1c0c030090b441802141aa45801600c1c150301a111744220b4100048a841f19400c5007426035020007c1400c08003003405050f414011200d50801701c2045500d01607007560028003018407a60715904101b1000080340d0a27400c08400c640041103e001141c1c2541c0d00c803503003035884050a2100700c503203501001001590040070205040c01c20403083c0988003840010318182c014144461501d051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 262472571 1250 262471321 262471333
    0x50d0b011103130f090501030f140709020c01021c0b01020309120a020306180d020304120204021c0e33180f030307030606030f0b030309010e0609060a051c050603030a050309 76
    0x61100400c09000388000c5000941c0b0614613081c5101c44514068000200300703810540144042030500c82c40418150344031807115542c1d040c2c507540302d04104140d0404014140005202804c01d24150060103001007024032868801c4081c152120458074580c246c0c9000d83c02c140b00c40b515900e0b1266040840c01214000d403050108154001703400c05d40110b1320800c0a00d0200b0071041414003c0142404241c5203000031443c0c14104102d1005580d2a04002846160001020030301072400642201c1c003014141c83c1032201021080b2016183c400341d110040351750343e182103d064855070340144103050100c861400c0344192110710205240c1e42c2c20442c200300c2403064015400003903000f04011441100c044e9000a100360405030020140c44a800000c2d80761810a40c2c5941159004411034510003401d080204425004e00d02084590040b882d80c6680700e10702081056a25030014014143c240c000c4030a00400900c420485044031401d40340150554000e100c00e60740103008000554000e6640c10403610 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 262473821 1250 262472571 262472597
    0xf0906080c09150309240108060121050a050f010b09010e010b03043f1e11010f050f040303050c03010303140703091211120d270b03150a06050a050d0b01 67
    0x2907109940080c05c0703501581c80580d0886c482001c0501c0c10040002c02c11165162004140e60b410060084440303c1c4410002c54282c00e001c18400e00354a5800010b4400840450412503110441501116669403c0401111061500310b130050f040c1c80e45001e03030001d03d03402c180e00b00d0722a8000520460300d42e40143e0074002d04113041c14080802285032400c1c0c01043c40050480700da52103d00085405002031980c0241c1d54440da81c4c90152448410b1400c040c40040c014030f4070340034048840c0c00241c2c1a02d040b0034400400300e0450400d102d280651014019620742d42000600b5120900c00074001610041c0801d08020f03100000b407940d1802407034250440b5441e044c080b480c0400128044a40034014001c00b0300c141421072030035440109a9000d0710135420145000340506403584403040904001700300400c02c90341504030000191100859860306c2e40b505a00e00e0492011080103c1c0c412000c0681c00100c0510071011105d40c1e03201c030755900303060401000c1c1c200040c284c152809414043c024031b400c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 262475071 1250 262473821 262473859
    0x1311071a0402030c01110c0d050715020106080f0a05071211090703020912010209010e0111010207140f0c0d0c1214060703020a03050906010303081b09041505010f0906080c09 76
    0x4603a5480c94240300889050a204152070005005007443c14001824000c540902000c0340c04000c82506544103c81da80c107525200d420100b00d40c00620100c10020300001007240e0540c840000c1d1060b030740032540f0360140703580c481e540ca0203060001041e903030100740c080c80000c10000c00b4401242c0708a108071003000c42e41c4005800134400f1600000041e6000c00c101a1520b402500b00f5080f0304404000c500d04520311000902d1312064118032810303c0704001409140c1c5000354111019507401c00035140104004603001502c94201040c034401910650ae1400c0e05c62500052691565a1001806180c1841e02204a506d00c00849040d5031340490302c0840c441c01441801560b00c00e0780e551b500103946403a048005401c0310006801c10b50941c0c4244018030010340c004090b250030400b0b115066040c040180b8041d9014440c0006aa4210b0300f4080c090b0401080c8003030107016580244c807268111084168210b0707021220344540c02c0010000c0000c584c40e150888014001024007910424001421510306 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 262476321 1250 262475071 262475093
    0x6030804030f05010b1f1b05060f06010f0203030f060f0103090614011d011409180a03050a0801080f0604110102010e070f0306050106021207060c0309050a0309030b1302131107 77
    0x2a10600301c0c01030742c1e4040140038031503290306000c11079140d0b40c030f100c2c17840c40311000c41e013051200070078040c480300c0804d05074245902960403036912030704480305850909460300002e4401e031150b80c045481c0d043c4072403109001205483c400da00000660b9402e9541f4800c20140e0800780b0091030608d5950380055003c9000f600a00034205102409209594075100c54202d403440c0c068040b040300015000140100c4c5092600820303008801c40704024a0b44404c0e140b0b0000101280e010b140d28440c05c1100000c240d00100a00507034003460704c0e100b60b960b0380c803200c1e9522201c00356250079291b00b1080006d00015428082d450441d001072000107000d0584003a118138004607904030403002a92181c0400030040b1501401d13014241500c042c107a4000e504500c0605030082c80d400410aa88591424000c0c51182d030102600320b411004440c00000c8a040240c40c1c2c1085000585541a440340050080b01d4004a0b000c40c90b03501401c50381920781c07034040c1e16009080382d0500307601c2e80804202d0100400e40201103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 262477571 1250 262476321 262476323
    0x910140d0323040b03070e030d051e0901091d0601020c0d03081b0d1401031203060509010b16020d0809010228080d0b06030702030a03060602060402061c0605030d030207030201140115120603080403 86
    0x300d207c5035202000305031914010036501d40400004000c0a01d0b01c16088070100b21802140d40d882c0d131644280c41c01a41c0402c2c2c1c0760000e4074420141380f078035000304009030405409801d0a8082d01c0c8070745444000d01031810003208000c2c1c040340741c403c0401c58680071789065000850340c1030483c81c02c004074082407005880b6054105840c0b900a83c005000788034100110109036800f038281000301c0c900e084003145030705905204107009203130040761350301303610030f644404541c1d0356402018294608078600c1d085113660030241c1c0c101e006108680030016003d620040e010780b2054940c4103410761805607503650751640c0c440c41082c3d48035070304d402c01c1c0a020344035a40991300502c015000346880d020b880200034102c9545902a004640c420418400580ca400040380c9050380c40c9001a48021500c00200001d044c0c0c5a02c590f4041c46400306c00701d8510b6065025028540c4a98000c0c40510009600280c46080a0041003d04100921503403400e0f07006420703400b80c2d0b01c80c9000101e07041da03513503c030034400b5001540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 262478821 1250 262477571 262477577
    0x60c07060207090c090501050309030909010609090e010c2709150e0f0709060c111305010801110304110402130b0d0207140d0c0605150910140d0323040b0307 69
    0xc0c401a5010300050b0040c00e15494200036800007007000401c0300c8864810b25041c0540003002c62148501841281c2c0c4490001d441040310b542c6d2401e004064501c0c81c41081100342c600700d21803001e8030040c01113a6000b140b5988580881c00031034034034407084402c01c54150805a08103000500b80041d4020303486c4000a40641c49491440c000c040209c02030000c5c000c54a04601c1020081031a4115014506551701803070711401e502c6043c41e0007c081404444a030f136110304003500f10524076003e904010306a038987c3d8020300400c0403464000c10640400e5900608006481001d00c030981802c0e0301500022060310034681000b80d464140c01c416500440d4400d00140d00003030740005100002011401180b020303001002c0e144051500241014107d500042a06440b8404110344442801c040040040b005100c2541c0d41085403000c01817020b540b02e900800101d41e4008201842c206110340340180e01901da100c00d851020440c094480000c404a054040051201103403044080300554807401c07007a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 262480071 1250 262478821 262478833
    0x2130b04200a020f0304031212060308030f040c0b0f070f0507180903031a030c01210c031b080c030a05040503040308270a051012090210120b0a050d0b070e060c 70
    0xb002030030074400312036032100742d4001c000800006030072603860b00b620800c52615500009600214402600701070384040c0442c5008024402e2519402ca18a40202d20407a10403080964400b070302d071102d000c2d8040d0264446428404600400c02000c07559141074030800603189000d46400d4400c688102601e40c106c0306940e120041d004042e010701c916270321207040c2800d4103d10500180001d07644c4d061003264604101203014002000042c104000e0710720b2901c00014440b0000c0210010000c1407046248000d80d41c03881d00c001042400b0b1b401060207102d84c6c0072000e00e1507864034214806400050000c0b56188000c100000c0070808680103050004070804426036031550407016400002444c4103c01d2182d01422010002c0e55503858a00d0010741c0d050500e0500e6080e041e810400071700e02a0006034100b003e5285903c050317a80503c84402e6400702042c0ac00c8400410020702c002413030f41d4010039030082d040145600105001510055006a0300d15000c40340054003008513045402c0400d202c8202d510807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 262481321 1250 262480071 262480087
    0x12031317120c041a1305041a03011131030804090204050906040e1c110d020715030203070c02091504110d0e010b18040c1715090a02130b0420 62
    0x1c004215000000c280455041604103500c5aa00c2902c040c12441a81c5001541c24a26032140101100412000f002002605510b800898000309185640c41c030a502c5d01c091340840c003404201791402d56619451000440c4001500f84030030100d083c2d80d19803407c50500001000502c4d41000380090b00f13180344096241ca1424080c0100d40c00040e00c218481e50510008000c0035000113818040c90001107912040212000010350304100d240034195118042c14003e0004032b600011410101c0d075940300d20340d5050300302041c00c908a00060301c0d1000041d0090014001601e41043e00e907800441e2121583d612002210000d4102e510f00c009074250910040343c80c00c0c400c4064070602600202d5074000344a010401c900082c0c0c004440d04400100041000c040340c240300001064202a00d2025002c4024824074100e240d40d402c841510110091b0b2150b0004001000100300b4038501540641548018610415400e0140004458440e00540d80305541c9c1d4801090f14600d4482402c1c110141d40e4890340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 262482571 1250 262481321 262481347
    0x301080321060d150e0303040b040209090d05040320100c0b010f050f040e19050303010801150501020604140c03120d11070c0e0406020d02040305060708010f0812031317 74
    0x180d0340d000398001c10158108000e03078a40e0f41d00300324419440201129060100140c2d1401403e0248100381d45210100410080000a4040c54043c900840d501025962034440c1141d45007100c5d00c98000181060100704001003d07840c00c03013a41c000035407428140d61781e00004180c0c0b40640c64082000a025008000180b003201c07900d990141030204100ca00c5681000040303000c000b110b44205001e030340c2d198505024903405010154080790607000e00901c42c00c550034166941d400038041c08801d5480c04590200c0920920201400c9030010307005031120790707240c2d16440022800340c1004007250081080d2035680e80d60501159901d0f03010b009036540c07550f248411350400c50f1070922403040c5101c002c0020038085080c0000d0001250b52042c80e06402d9652840c003600030380170301c07200010802e0020901104108011070401e01c11041a500c11350903a0f681c1c030280c0e40380480c07031107221342580003810030b4004401807000030360b4082140c804100300d140c499524914040240044c65004110128942c0d8402407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 262483821 1250 262482571 262482607
    0x1409280201021c05090a0e01140f0604030206220f300503031e010e04050a0f030905130f050718050f01020a05030c030309061005010e040506011b0507170a1a0711010203010803 77
    0x1540100f0303280b581400035400f8000348828116100f00c070000ac10760541da8920302258091640604800d0b20b4540071035a000007820021a0f00000081401000c90b01e11201400d810441d2800d01140c24107000414000c40c0100c02181c56180201f504100040401c208200940c0101c15100e922003444980201254510070103030403105040d910901480041400001c00d1110140c000d080040c0c9003102d842c00b528452020740c032032508080e40345400082008141d020807085404140f06105a030f64003d4115448140c08003560586101e1000600290030700c0c48010004c5503040c0100d984007405610f4451030341e08864510002c603407001041014a40c0c040c0304680e084403080d00c5206086042c00c1c0060041494a00410300079542c600003e902c40e8866200300841c140442215951640c0c80d082540d122003650083c070507140e4014081042e12100007800c01e041e9a0810340c0382c00c03c46250383d442d652044c00540810b00f040120305000800d002c0c2032004500900c1c0a030004d60381c503228500600c040750 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 262485071 1250 262483821 262483829
    0x204060303050913060b070b09030c10020a0e030105060a0b0f09040203040605181f0f1d0607020d1b02040515030f0c0f060703120b01051c1409280201021c05090a 71
    0x4d414682c003000b40b48079030340580c0d1f00181d2055004400d650b42540d850302c0d5000b19403c0b00d260380320300802c403180b801155005003445501c69590140200518080c1070a81d0020341b030383c58210104510401070102004060828603084104880c03030300507490001820303a001500d080d989a0f94032003d1200c3e44507842500080c030815503018002c44a448203400e0296441e40004003070544d00e4220b001329104e51f40e40400300c0340191f18042000f40c05041e004075a260b0f011600344c4054800d400260b00c54a016258502046000c0810344244030055070a001c094400540141c070903600d00c10110056031f034140000c04039106004d0040603921080410405400a51116580546070802180d00402e502c41000701d0864450000070604d030300500c004071054405c244641070015022281003103114841d0700314140c03a4505036880c07400307625401e240e592107084410340141c000070710040d1108e001c3c03110090640d0381303030050041d80c10345294040c4072460084911100030000d0000101a44e40d0701d80013010760090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 262486321 1250 262485071 262485109
    0xa03060e15030a03030b0301140405100b0f0a06050903120c06091002030705070209060a05040203070e010e0604050303310608010302030f06060a0b07080d06090203060324040303020f0702040603030509 88
    0x40031001d03001ca5118a041c1202a04254803240b03843c1080c0c9094211840360644109030400924090801503110341c0003008441d502410f20001c001203180c070441248a000d00200088038180c500b00081d6500d5000b008066094060104030501c1003100703c0161625000c0d6002401803440d02e20589411700f40000384450740a031051040c003103215400019150042e07816219a00a912240d00203141400a9400a0391043c000070801c00c802d5403240703076000d114201307032550804c0b180c4650420002d40220700860740c1660080c0035812174030744980c4034801c04c807202070580c00803402003440103804c1c1115034000740081025003004004504003000030705821850320028024606085000907002402e41c41001d00400c00400e85005000380c06049450000500400704019a500d08461010750011201c2030303c24000c182c1202c403075902c0c45104211000035002001d50396650360f038003500290428003080500c803000784240801601da0f1b02c1101e014600039220305889440140c20450300c1d40c03c0f14444411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 262487571 1250 262486321 262486351
    0x9120601030803010e07020a060e0c0a080c0d06020a1e0504180e0705090a140f06030c240304060216050c0420042102180415020301050f01030b04020408030a03060e 72
    0x100e48600243c0f41590f0700704501d903080f038450a02c12854407000c3d450103000d0300d2602c2c00450106000180b1500071101c02e03210b5000f01540c60318415100c841d40380e032964201e0121803003400000c40340e40c000c12481c045403c161000b088280303500c0d800c41d1032203c0c1c99804510001414024401e41012810f01c1d801d05050a01a80000310425926039803e40f103854022034040340890303400c20081c1c01046400c6000c11203000640f6150a011040c200c041c2c6149000e80210510400c442c00c00c040554103600c0d2809030010840103941102e541c903440140184c8407141d09004019265006400207503505004000401c800803402d41080220780103448800910540e480e500380003604c4040549048641600c0131298034440000b000100c41070f5020003d40c0100c5c00241001103040101c9070070701039801144007a41404503a4003a5040b440203020742d030380c8003c8486000c1610340c42504216105d8a0180c0058206a502e039209450b60b08403211000200f070b01d81d5024454801e0312101e0380d40c01a440034903408 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 262488821 1250 262487571 262487573
    0x17040b1f060c20150301090605120318010e2709030901021005040602090d0b010612060e060f010201090507141c030801031b05031002030906070f0207091d01060b0912060103 76
    0x4107a12500004003000d0014429418003d250740824401c1500580040154a41c907a05602030b6030003401030b0081c03e45044d201085a090a103c0d000340b0134903420082d032500442e4130107209501c504002103810000d080f04d403da6030392500488800b904200d140f413401501c001d004c21003a07407200200711099590080c000c00d100c6030381c00100f00049849882001800e80c9407810080040c0c03144000c100e40090310042c3d501c00b0083c902442d40e049a00365030341c51440e400500203030070a13a0503038031406409025840105030349180011a50300d403024140000956140a9951a4204603a075808215400c400306058505424a0030001c014404c0b8805110b0101d20755540240c18140d043c0409015940d10700340c1c1e070388104401721601c4c1c041d04004040318030342049030041d00080c1d130040f03c0c5a0100e01841340482c441d1406020314821a1049130050f049107410701c0500002080260101a90200c000c03040350840340b000e02c14031010b8411446003644c1e42a20005012207946403101600c1542d2007640108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 262490071 1250 262488821 262488827
    0x80906070804030207060e030703120504030309091a061804090303060602070e2712070c050f0303070c2d0b03010503060906130f0303020c03030f0103020f01050a0206040f0317040b1f06 81
    0x5c040c1c07101810107103030007103120005c00d02c1c0c252a40c0004007401403a03040d031818a6080300143c01240d01c00e81e100381c0c1c020b40b682280401c0c0cac1e00c052042c0c030b55003007201151202d078a0504060708a9001916201030b107001c4040002d0f003aa80e20301401d4010035a14041448215818020f0801501c44190000d02e07a09040b2a001d908001c8481001da41081001d6103541e50b4006211340030603004000456078642c2e001c2c3c1131a06003035050703101e021f22074400d04038608841c0c2004400da40144c2c0c1c0000c02c8c540201c2c500403078541200d40103040780345200c03440c0c1c580411504551000902804200000c00e8407076061205152034450041c01a8289501203c10440803514801c0c148101d136522440990314941c0900d4250060700801341280410701021013080207052541c1c0d0070f0741c122402211400c000c8008100103442c40d2180c0c0c0042c80050b00582c0004c1d02140d150700ca000300b2684030b850581c2000440e091005105c12003524222240040c40d0103020303402d00060f0034003004251035001d2001c01d501d0041c0c05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 262491321 1250 262490071 262490083
    0x90d0c0e07050f0d1505030d080601031d03121b0408010b0306090106030203120a0c120c020102010b090108120f0c0604031d010806060a110709060f05011404030305040302060d020f0a0809060708040302 88
    0x4000391310385400218a004120f03441582c02410301404548580c01c1c4c0744000350201c0c10890b00e0a0006e03150a800080700e000324121094400c0c8070340302961900c4640da22400020100800c248204821181c028640c0d10703207a0001c0c4028142d100c000218401c00b5810103041c910082c0c400045d1b6810200c040c000340e5030100d00d0b9682c941000c60025500c2400c079030140c0c1c0d12480044064400f40d032403502030340015081460180401e200b40d00030484c0301116820094844820301805401d0750021715660758851443e4001c0c203496071501d240740c2c20402140909481d1800c2128200d000030110000d034150044111003001d4041030074204400140340a101041143c0034040c181401c00c980c01642807103030386080c421704000d001031002c18008030392225050700486c100c40c451180041c010026045502d1011003d4800b03880d8140e40b610701c0e0034503603002c02c0302d1074011010380000c0640c20418100342c207c07520003e103805405a00d905a85180c0600032a00f0715500504400602000f1802c100000c4d0f404110303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 262492571 1250 262491321 262491337
    0xf0717070b12060d1a0403030506011b080a0f03020f04090209011b080a03051510021c0329031203010608190e0604140a081303050d2d05090d0c0e07050f 67
    0xc003c904181e01d007841a200e00314171840b486121400710a1009159140e00540d12803a001e89401030612181e01c2c180c10460742c03c01d4090200c40d014800451083c0c880d184140340704445150240c142001c940003402d15601580c41095010360005001441c0c0d600100004280011403918854260b05034403429401c0c032401620f10308159884000500e14403100340242408600900807852148001c0c201950711008003100340c56030040e61075034804191180c042c812260000000350241c0c001d40027840d81c5001006000c8075418020042803003000c000e080c010754002c0a0b50f41d203030703000c07030a0108040e002206403100f888107450901c1303090503180034000f54550300f05034090607a160403401350190a04040100b03800800d00c40002610a44800c8540088025a80078070192041c41c189144103481000b086444010004004c00842c0e071807405042030f441592009040240c0350041d0704000400e0744503100d204640341c501202041c403111019118a1754001554206580341000b040c80004c47c9001d0941c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 262493821 1250 262492571 262492579
    0x4030302090120101508070e06010903080c07090b0a03051e070801020403140d081e09011116030206091204030b0603030c03070f03020c0306040c0b09030f0717070b1206 74
    0x500007015034424040c48440b00078030a4841d100e09003a9140903181e11500c2607150a40b0b04001c00516400142080482214002c0000307000e040c0c5081d140d1107244c034000304000d05111280000101003004507005020000b0178401812034281000d0b10306003101c2c0c40401d510300881540005100054000604800304401d842c884500c0450900840d072078017070f098200311100d5001150000411940380284488c0030703500703000e4682812a1120498110804850001c0102d0b00c40b84842404401181100d030442c45940010628076450044006130780c0c00100c1d103d012100300514031050550500903642c111200102900c400c41c140c0d90751484c01d003d21301014180c001034201181c025501003088907071501300e007070540340c880c107090500c2880302c495150140d004d80641c0504032a40c0c900460914803c036400741d0003500281c2003400b00b00b61a000710390001d400d40320b040708031800400100700100041c1031b1840680100e10702c2c021000d0800f0803030f07806052165828070160401b10f1854005540c4010f09031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 262495071 1250 262493821 262493827
    0x281a0f240918070f09050a0e0a0b09072301110714061602040f140a0504020102150703180506190203010302060a0503040c0906031203060b0307083705060f03070e04030302 75
    0x208000b240300303000c0514955940b185200c006140042440000d00f141c0d041c090800071940c4440c841c2060b11303101c90303401e40b89400020502000032859030b0030a0304101c1d80c034101c0d0611a01ca036401c501121107180204210b482c8111000c01940e4490825440309440364042c0500a24005000e851101c40400ea50710404d0013007142d03411010085040864550001c1c03050207800e0300f900551004042400c50548400c10880000c3c0708655140140782c0900d6040c2d000704604c055000850038511400f9040030100f503100c08441c481552014080c42d01ea03030043c000f4040380d051a040180705a405001503485141c0180010070140e55024295844042c20f0300340390769030769074529061500714840d80010b012030381703400c4004c800e1200c100400360400340b840d00d04100f0691524407031040750200715100d00c00505004005104d030000640f4110300e12070b01800c44816004540f1280c0e800e0820b0b9450644620f580e201007051914210b4500d140413401640582030580c10201075a1310200028000360a00d5000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 262496321 1250 262495071 262495081
    0xc0201022b02120a020702030106150f03020f1b0606040f110f0c010e070308090f180a1a0d030c020f06070c0918061107020907050c281a0f2409 63
    0x20390115a1148240301c10f0503c507141c42c01c42200250452101a03009610704040030540c0b40380009081419071a82d1240300c1c418419000c11800ba520008982e84510018011035030f15000c149040c150340b00a07007010340325a280100c1844100d5150040c1000c1c0c4500344408404050302007011200c801c100c5402455075a0180011030b8007402d103400b109075283c80351000010900034007202800712440d0850310b60015502032000c0094a0249510940610600b103020075000031259101135000f03840102140d22208080c00003410649107070b00300380c0100f90005400c400314a01201d2800040004440480c10826503031642145070300c29008180740240e80d151007e0000018040754008540d01020620040780c400840500c0c0d6000403004030300803003405010411081c010420343e00b1010300d1200900362035400c60284100042803845048a48000c040440c0200389407121410609110410031041410030f03903401c41500e88000c1c00161144018000c01c0604980d280c02a00740341c000f1100c9490507102c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 262497571 1250 262496321 262496407
    0x15060702040e0114131a01050901050f0a05060f180303190c0c030506070c050f070308161104020706021e0c0a060902061204050705030c060f09011407060501090f0c020102 75
    0x150b00e60b20080a958504000c0001000880001681e101b158440701e12804070014200c0c0000a005840c0d0040d0880c0040c0035a00f040c1d80a06070010009240080440c0e031000417070641d5101d09450b00386ea003000030301a0806203240f4001c0032076041c268001d515003125801421001c80c0c40004000c2000036805004080c0420310791041701542e0448196195410002005032541c1031300d60045425010301d0a0032801917400ac0f6000c000c5a401c0280b003890907d144030381144410520703004880c260050030403900c03e91100d2001c4c00c0301d01d209400060340c800d1940864912145c0d0b0000e00b03418804100803101014801041e04100b9961100c40840c01601c2d0f440041e5842c0100b4000c03040c3c0000040801c800e0000004886040742e0080c1d042e41c0800d82218107200361031280d0b000844842c602044069015480b984134400e801d848030320303e142411620b03603941064440a80c41842c403661503d004005084040c443c0d84c4508406000852415211211502c0e261f62a80911200c840c1c03455000642114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 262498821 1250 262497571 262497581
    0xe1c0f1106040e070509090106170412050d02031f050913080a050403060f0b100e06030c2503020105070e010503150d020f0604091b022b0207090504030203070b15060702040e01 77
    0x801c1600d80c83c2c03038940340000500c10707041280f526202d40e05420002030040c4c0510410303200e02c0c10750840415a03031348a489580f0101c2e01242d0001c104607040002039a142074602c0514003403000b034116940060080511000100599003007584a54419428048500c110744210b4844aa1262903183c9400b1094401c0d40c42d0b0042c2c3c2d1000c0c200b58184000c14dd116440c0c1d9002d04c4076180100d40f100e040384062201164075610a00e85283c0042c81000892a640c200300041d250480e401440c0c052060700d0300c44400030185046000701e015039103410500c0f012540185c050941d0690a1905604505d048450b0641c907841c10212507004000520490003903445440c070081c12800701508480d0b0f1035a880903000b00801160b44232000c0e03200d00121100b440c6102090801050b0b00119101740002880c25036424402d07008103d14040d4822180300080140e01030240c5c901c524000d0700030f19141d0303140f030810b44c0c0340c51002420000c68400b0304044080595805060710052601075400044019041041c640144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 262500071 1250 262498821 262498829
    0x90209011b21080a0f0204050d0b0a0e0a0309060e01020c1012090606080a0b0f0606030f180d030605120f07060c03091e06020d020c0d0308060d0c060e1c0f110604 71
    0x2285190b0886145801001c0f0a00403a513048081040d01c01258000b0124061030280315070090002401e41e000ca40b40f48809a0030000074540001c01d681c5840c0707034918101c44070b6421004600a82020803c00707030050801c03110020280040c094415000700013a13a6141c489a000007170010502c0b80040c0e8066070b6001e580450b612080800c1000d8890f40c0d6a65200b489600c00c45400d16454005004203c41031806801071801400803421521480003c200d80c04e0010004100c80c21a0501c80c00074500401c040c004d58503040d00d00082280c02d001c20702003900c0100301c03080c40d01c2d400b40c00c44401001c400a000001c41f0400c0ca0305e503000a0041ca03088868002c164090315041d100140f0000b00040000c110320201c401c40e40031210082c0007410306a03112002014180c0d030001e0904451000700e400f8003c800c2e8044801810501b60007007558074000c42505a401c641c0000f049000501002e050041514000f40151921000c00e0506680d5190f4021041c080042009199001d004200d0316040e06841c060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 262501321 1250 262500071 262500113
    0xa0e0f07061805041a0603131b03060605030d20030d020c030307031404110d061d010506030f011a13090507030501090323070f030513170106090209011b 67
    0x86903030752034020920041005482d804004030840002c2918044c450a48140b030514900d810100340d4000b000041e80005040101840d40900c2410020380c4d41071002000300e010152511002e41107040c0102100e075640c10080c0282c0c010044c2d40381c02ca41110001c0103010f000c09241010b0b85501140500f540520301c006038030a4000709411443e4200440a103120f0006076408002001100380d861900748000e0728090b20b00b8060700a80101800c1142c0c1803a200782c016000412010000d58203a40079007403100302c4107901c0e5516030521407503140a01c00d44a030825908001c0c0400c1c005141080b0144010030912031040d100b811102d00c90701c40a401800115400c031040e14009581c03403e20038060304c400d102c124002142160602c40c0c500c00010401408201110305a081034130903910700500c1c3ca006c0030141d080c80002d00100030461514900f603400b8100e40c00d1110103030146641c2660035240f180d00b00c81440d40c01400607424590344401641d001d009400b030503620112140c1005130319103150302c0300345482c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 262502571 1250 262501321 262501333
    0x406060f0b03160309020d0b06010207030b15030c0907020705091003020303070c0f0506070c140a03020a0801020a02010f1a010f030f02161101031e0b0a0b04030b0412030903080a0e0f 80
    0x224444140142d403182003034814050100042c500114215803940e030303000354070252550002010a0725259040c0d4448d8060044a48403030301d0b9103c410400c082112810320011b01c0e40c005102504040c010790042e80e009442d40c404071b041400c006034441d051809054020f855100014102c16206240c5400854020b02941d941c0c0d041030500d400441032a0050100f0450440030008850070704000b110341c2a500701c60503411032402c2c003040c0b00052807510328207684078010150100160f07440340c04000c0200107050005a5840301508080c0c00e480d140218001503d00e00140b40030100601007022081603003d20b0704c60303030301d41001d10190024000759400c3d0318000e10100368800c40440e21900d11850320b015040800202070540011005e880c181c0320300c029400c44001c517022455401d504048070300d20380149141c03100d030b48400710302029030010b500540e0548604020f02003880b40e540d21f99140a0803618040c402c008480e00c4c043d00340c62014113840d00c3e850740c903000146100700500a011890440d0340079203035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 262503821 1250 262502571 262502579
    0x2010314040b1006020604050a06020c1c0e01090519030f0302120c06071b030e010311070f0c030201030b06190516120906020d020f06042a03081c02210406060f 70
    0x2c85290200c42c852101d0302503100214169000044441c4541d501200410f14254903a90f1a40a5000801d500c100b03446283c440071100c00a50070400c04a00c410790710300340c516100c04001043c07440d059015074003407100d00400c2050305502000302001c2d20340220b40619104401c1c41c04038030b05289500c2d00514401d01240c03c4000590110b10240034211543e100359008107691351401c00018200d1006020030010319000c1020350080e00800b110501551001c0d0400c00e40382c41e00108032103140411512041a204148215a003601c10a5040c0703000303681d00c5050410a21910841d940d041e0300345e400740000032440515103ca010b200503001a03201a0340d101440c840301020b801000e20b401581c016004040d90081080d2000806403070000c03481005040d50345a5071030b0103a01c04002c3c00c00c0103145141130040d4800155142d1000000d520600f01e0583d07848000024900c58240400001d40c554010131001c074000c00c5d0102e40304000203a00645081540725440d11800500080c1d001c44c00620802c0b80000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 262505071 1250 262503821 262503833
    0x3071422150b0a050a0f2705040501090603031b170f1810020a0314040803040806190c050306010305060f0913030306171905030d0920090106080c070201031404 70
    0x2030003040011003030506058841441031000c0c020303800d4a5001034028417482d054644900000f0803240c0031403e002803660a02ca002e429000c96018189441820003842000b46003000e00c52240100020001003110070f04664000304007400400c0c00819512102482c00700784010701c1004442a82000d000b15511590138802c888190041c001d03026810b0038511440d081418014000c2c200495103601801c0c1e801c00701d07901074030310000b04440108008028000454040c030308000810180446c980241003901d0103044080c0c0c2880311001810b0070908003814000c00d190030030280c07508540b0901b40450030741c1c1c801000c200d040905c0445594403030890801d00050b50745503114224018020b681c140070040e00c4000d08041d404007aa120300490348000b0010010200c890b5140e0411751082c01607a01d4840000100e13000d030340c4e100c41d0a440d0304200c0c119280d1a41e103a240b201614000070381c2d419503103615000029004400051aa0030f0907a000140342c011603100703501c140d41c56000e502c088206030425060031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 262506321 1250 262505071 262505081
    0x625050a260402040c111e0c0907020f210a08070201090c090c111612140604080306090f0603060c0f040308180301050702060123010306081f06090b03071422 69
    0x43e405186066450b01c3c00900c242401d561200f1842c00400742d04a0101d440d0f2a00c8010000c1c08600e070041540345061036480c1100540900041d5000303211402c2021171b15401c2281c0d124040c030825000e450001e0446009078141d42480e8a1340c02c28072016520218107a001d00000340000344011407200c000300d0480075641c0007004088082d40c0b20000300800d0700702d1584c0da5100300c40e00c0400b00714003041081000406005142001d1144411100c43d4000d044014907252003564110345060340403040100c07070b061482e1402e074000001d061140040c208400440c1c0c4a02010700000c40c5210000741962202c0061012034000f5076215844960327600c0554062000041e0340342d09070b17210b9400c02000c210f00d10710028003541a42d9010228108810a8040038840c140704482003038182750710fa0750b00080514051182825404104e001300c41c0c541d40b15000a0102d401e00e400c40030b0001c2c40c00720088807507100020b050701a10220031890300e1404020002446903078192b00b164840700c071000794a4850a2440d044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 262507571 1250 262506321 262506323
    0x706060618060801030b060105090a060804031202030f0613061509090c0507080d1505040203130210110a030c0614010b070614011410120c09080625050a2604 69
    0x81d014603004075003020080491544201c0000681850051011070341e0760b10410f41120050500382d1528801c440881e590300810781c08803000c80d018100708400e040e0003410360385142d002d00c1c2007189980b0b0030a5842c0f46007a800b030031407030044000c0030801d00e010301e180d0700941c040c120542c9050400c48040000070404c0d1040c0c000c07401581e042c0801500f0b42401340007510400c0d64800380031400c0c040352003006c2c070041155603c4001001c4d200d11001415807100d10095000303c0380d000900002c0c0304680188903440250300e20320810401da060803070703144100100d19158503d038185003042c00c42525040440280c2000c41074041040f2080c1c00020b1100f00e05002001458441c0406210740d030704034140449850300902c120030310201245101012460f181800c0d142e09003160a00c0c0d020420210b00e1102107800c4042000701103001c0440c288180241000201d074400035000c4040710103856450528402c8190000d51018040e01040404e103071406030030441048440401308410300e441c4011104000001134078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 262508821 1250 262507571 262507577
    0xf12040f05033c0f0706140112031b030905130912020703020a0602010e030a052d03060a050406080309060c070806090607081501170603030706020c0114010b0309070519080307060606 80
    0x1100a0010072401c0f040c26640c42d48200e42e410a032030703e0507052080c2d1041000311503c80c1e40340040e0070002c00380316400b4040d150368803140c0302d2518685000351481d0403c0100c0203c110f01c1c0c5886100199005203508107a079016601c1c034145049444540b4098483c402c8000c1c41c64401400c0d0801030303503001a007141141c0c0211003070440241c0d107a2081c0c1c222999403041c030002c1d030000c10101c603402c3d0240300103103001d04809182c0100b20b444080405a010921240300c0c09005c00002408000e107401f80222018001c1110304124842c5089402a034034410307880c501d80120408078022054107814442c031030051170000c3c152030041c42c0c80d020b12612081d0032102070020503102030102d010396000c103048039801901a16240d15103042e900301d40d00c030b56034010321280e03051204110081c0010498000380c50801e01da1000800c098903c2882c86d900750105820088807060144200300e0a41d0001420381c00315003003a2507040381d940d03881640586103031300c0da00300b42800c4c80006031a0341080580e03030201c01100e0346a9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 262510071 1250 262508821 262508887
    0x1050708040b010312050d0c0c030e0402160b0a111207030c090503030a08090316110a090b0603010e090c040c05130501110a08090a1208031603020f12040f0503 70
    0x4909031804002a5005040c0b40d51103001800003602500c4450018000c41c1071050038402d00c082520251801d040254001400ca800000b0806070412030ac00c044103801c40f000e50404041c840300c2e9400c0c03200c0a501505c440b040201164041041742c0c00010026107440c19503540703051001d00360701c11000548130540001d00d4504485421840740012500b6190010055440c10504a000f11542140604080071500003080004148030f80b01400c520068422410032522031081c004100c0802070ada44481d040c2410001c00c0042603071071078100e90540d0044681c0840c40d0b200c07040010320700300c0d84408554101e46441e100010417030300100a4610110048a0030800750b0700c030303001101c1139030b45e41415030b0a0b03a111031984e100080c1d0300c2e0082c000c4004044e01171200703c1da8500081c141a04640c0c0d0560b903aa200109129080409000c05c1540424070b080c00d518020070904081c0c420302c81c01044003880d056043c081410494045d94000856810401304c03034683da40c41c0703407440295064119244c10840300b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 262511321 1250 262510071 262510081
    0x203030f130803040b0a141302030708060c0f07060212010f15030e03030604020d09020607080406020601171504030234140a052101020705060138130315050403020105 73
    0x745000192a40c0151603508507111691050103108000d05048030141c0c580760110110f0b056500031a2041000ca012207804e8203481c0141400d028030341d0882111a00003008001803024468201d078400c518006500c5d40d2800f40c0e080c084020f009012400200c0380d81e4100008561846640640c00c0e540b070010824034604402c43c060b070460721002d0070016180c0080c40040c40030301e0305502504074401140c40120700490103074000f03217250b8030082040300e48110100c3d00b8042c3c07c0d0b04009031030150070f2038403a0031000364454500170740d80d42035036001d4103852071414009401c06200340702e80b5000001c0300c0c0301e0141640452200a0501e80360340d25030125449401d500051110100311000000000540240d10391400c4c0024070214000040000604410807110170000303600900c0101951400348001c0d1049504160311184803207821458901d40d092550940c1c0da0041c02107001c1440030b40400f2442e90b032014080c2c045c030707003050903540050003a5005d400355041d100c45c981c000e544514801c1c0e00802240d552 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 262512571 1250 262511321 262511341
    0x1e0306090408160213050a060f0b030a090606080105161103040e18030c0d081608010e1f08010e01060e0601090e07030b040b0402210609070f030902060f0a0203030f 72
    0x1045814991010150001c240810040c1005203104496411900020103190f00410b01d81c40964440308412a5103d0811118603400d04c900009041d850040c00c88051a10220f5800c1c1d01002c0c0c0443c0034290b454481c0c1c004c019096100000500b0602c000b4861450088a444070710ba480c418004003240003c00000030b10900070044038181e9906401101a0b900c940040348a00c0080084194251000700103806501070100032940301b84840e542c6402461403c241100c0412600e05198424001c0b10b400601000e2540341c0040c0d4090180b80107020a034801803600d1b0000d1403646d001d0720701940780810650403248107410070700c01e46181070500c0700c540e00d0f08001121134483c0c5216460004100902003030b4498465008010349001c01400829116004000a0100d90181c0c11107200310f8100840e1140409803400d089622042c1200d5003488c80c0341640000d4005458021488101507407010400d00319514002a6000400e81d2070146032212030010010356a0f5000356a00325040c0c001d900024030301c001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 262513821 1250 262512571 262512577
    0xa1401020901050d0b0d06150f060c0f020d1a011701050606070302030702060c03130b04061b11120a12110601210308060112050a020d0b18061909111e 66
    0x101c10303543d144c034288028070803c0c000c1000c200e01540c80703210004000f005c11224084c2c00303035030108003201c861442d00d0302000004001c420b0f8062400d10480702001004164456851b60350683c05445002ca01e1183c1d00e003038102800c0001003a50004a10000070515050f9181e00704441c04c102d0008000396198001082941d002d903590043c0140e10420062005080800c05400ca12007a842200c1c00d048013011860b5201c6110342000c1c00f41c40020a04103c1164011002408103910018140d001503003600c584c00c2000080c41000d0044106c0c04640c040c10ba41005001300c03568202c40985c1102030240c42c018804000325031a8401b51181000105442c039940403000f034640c540154029140550b60390541d000381d4003c100d181803081c070950048a080700c03402214031a169000780103a0b40c0059401141c11500001202801030443c9100c5500384144840f882d90804011280d0760500780010240d0f600003410340d0032501c83c16040c046080b0802060307030090b00c0615a942102c0c000411658801c4040d80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 262515071 1250 262513821 262513837
    0x60f0709050f03211c020901030b010318140307060216050609070803041a0702030a050f061f0b0d110a171b3702060417130b0306010c060e0a140102 65
    0x504440030206102c0c1c4000401c4818000034200541000000707030000e40895002aa0a98211b8000611701120341e13141c8510603242409090401c0550b1400f10005070300140550001c10b401d500c520307803603a105810001e40d804142e000c1c605550b250f0812114000041007010225600d00c500004240964070100b010019104050025400c162800103030310780c591408401c08145110070041100980c03000c0c4202c681c3d841c0500010140041e0300101e140c68020b008298912482c607100c145811081e141c0741305000c651400c0d10968640f00c44050920040406c1d47c01940c00b80000a51304010300e0700541c2c000f141c2c400d05114442c02e83c0d0b815060b01c0303541d03040064521002c14104034040ca0f000c0c081c1c3d22140380c02244440100010881d1503121320504224143c1030150307110404010800809121655810940880041c1800c050403c050f01c07203152402114040c407004000610544d1245c030840b9801030b0001802d001030645c4c419210344079692600141e0301c2c0c140d101c1000c00d030b0b06014000c0b82c1d005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 262516321 1250 262515071 262515073
    0x3100f0f0203070f05090d0b01080f070f050a052701030510050a231f0b280504050105071b06110d020109110d060e070905160306030201050708071103060f0709050f03 73
    0x812031421985070740410b170382903400078806d03101f00041034113026060b028112400042103032044d440e40003440c1640c41d6001c040b4403002c11506110f036485071306c110000c96009940c8034808015801c1c1c0e04850400f4100110003280c101000002440b4000030f00000a40e210340d02009a034669a031154143c3d40080b401c060607000340c0340c1a151200f0342e03072100d5900040146401ca4400341c04c1d010f040f114041c0342d00ca0300c110040441d0300403c0003d404200044140f0451414035004280310000e00640102d109031414000c010031441d044c00040403012540819156405c8515503d901d4044d20480c3c81080c64100d84c0306004100d02594014400e02d603620380c0020161082021283c10080040100f400454041e80c0f254000205000100210b0003c0e0000f000081568034048001101c01c5104060600825007800302c00c00150360004202c9010320b42001e601da40c0c41000742450301c0ca000c4000c40305901481001c0401c4002e04130340c2200750240c003440c1d81c4e41c242c6039500c0c001c04c91644400b403003050b41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 262517571 1250 262516321 262516337
    0xa1a04030c0807150e06071d090a05190903031e05090c1e1806030609030f0a030b0a0b0307090e0a450c0503070603050c031f0503100f0f020307 63
    0x840c14102c058001c5600c82c100b0b29030b071142c4055504056420400d011075441e1700600c113000d144d9403c818410490540d200781c107181c02c00640002a074131030000d000c07030181941c3d52011500102040020b03880340800c441d014000320106181c010000e10310080d4140110499240800050019000707141c0185040d10045c8810702d010700c204501e80c00010002d00c1c42c200023000c0d103541911400280058030340d25041c1c905c80b030310f400d505160420b0340c010021443c940042003080d80705410542543c111034070360701d400030b0b10300140e601180d6070030550741151841a0000c420000301652081040c025240c01140c40c04068a540c0303440025100b006e04a0b9a1a003450000c00c07595860800104100b10b074280c0250b00084105d11121055800941c002d807a2054036140500140c1030802145008042078035080203140b07013a081c00401c900000e40304440c2c1c400b1154100b03540c0c0201500c8140913080c018280c0310f00098503600c420060607a4101003c2090800d24040012080b904c2541d01c244002c0d11041d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 262518821 1250 262517571 262517573
    0x5010c03020a060b06091206090715050a141b03030a0f1503020f13060f08160509220c0801091a04080906130b030103030c061505030705040207030e03030a020a1a04030c 74
    0x3018082481081d90072100c10b000d054003651f111000010304e0b252000150095083c034540b06401c04c072498000003d00301c5c1c440c1d68224050340c42011a4661280c5240c01c00d4082006030320842e0912940c0001c005103960124010110b0070702000450080102140030000d02941507440410f848556001c8043d01021b504100094113004100748100d100040c0341c0c02c00e90701301500c0d1704112011a0080b00d0408220001403041003010050000d48200540303001e001c052829000502e00f40004005040100003d003e010103180700c100e885510f80d501031802c416003038444410f28000c1c20307040029143c00141c0320014588201c00c1c44010b01840c0c1118019141a1015042c05590b034400700b01c101d100c1861040c001307007565070940910701a6200b07580d078107407081c400d0600409884003c0310909d01980503000820041d640080c9200881d4015034000d03031104480e080c19a80003042c1031010390076000000300d464003a68003051401c0460b00c80e800c2c0844c1d0941d281c100c2c00340040e0807a0b0003404100000b000c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 262520071 1250 262518821 262518833
    0x102160b03180c0a090510060309080901051809010905100e0f0606210c27030a02040c0e15040603110f0405010318051501170c03030d09170f120105010c03020a 70
    0x30b800c02e0281c0100c910041998003c07918480702548040c07031080d620001c4c0030181e406020354900034605840d041c401406a9143d80c8440e05c0f56005d070b58140030002542e03102003205842c605c010060001c044242d190380d117a40c1030003d02002c44036941c8201c3c0285012401d2001c4203211070041100e0302c00c505250341e44002b40b00656101d108420328545042d40850901c06158071200e03c03e80941c0e4801e07072a00f01400050030043c003441764055018401404140c040c0c2c42c00a0518001c540441b40403401040c80c420070346822006038a215044000c050f0690741c0a03c28000410803a17640fa60100085030800d44030544030700035040c1c516842c4204110801c150b40c841c1d084040c003401c909035095050a420b603201d82ca4000d01c03c0d0403801c6a1070f03c1004000229150040300d40c2c0c0741000c030161021103c4c040c0029202c0c410b0144001805a444000c0030900501d644d00908a141d42c00b00c9503a260801c3c44050401e07040414689200c0c141c0c0d01c004941d40d4410044007800340d505070010315420300590360300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 262521321 1250 262520071 262520101
    0x90a051905030c03040906050108070e010c0213021608071406100e04080d0c030f11250c05040c020f0c0312042d141302040b1b030408060408090102160b03 68
    0x141c940703110512101e00104410f1005000601d1076000c00544185080001f41c450348008003c9024426402c40050f19a41c0001c940300d0419811114602d442c040c00c80700340300070301500050301d20942134030100b07808112140c2c006210042c02031420a8003c00500780c1150f0b650400caa501e10b02c00140c64040202c07071f650540d03064000b4800c00070781e070500c0e501903205012a441d00103100006070711548142c0000700e4034072558400c203107070960f01031a0520911490302e85400d9500543c4018109058003c14401040301c00c101900008000b4008950b60050095903002c141c00d140c03c0e0b034001d440c1d4103210340c0341c000b602c0e80340855000405804d05103030048a54500c4030300f6911362022121411403004046a40701c070300000c0d0144207514209021700c0c0e800c1c8900048009217417040c0303910401041c80a140100c059640e00c06034507140c4461004505406421801654003d10b11407061009100400c81000007904201c40300b03070308445103003104d006030046010051048500c1a4030030004500281401000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 262522571 1250 262521321 262521323
    0x61a0a0f0507050a23060702030f0a030b03030427050f0106080a090f030908070b030c03040f031403010605040302040e0319030f0b28050d122a120206090a0519 70
    0xa50404141e0303110a41000075401017100c0c4d07490000d401402e070b20a039090740c945059030a0001c20130341c5000c2401a540344140c001113114014042038401503544203811000002a010703098a444564560781d03003209091148000b42a0320007440718080c100c0c101e00c0f44520034500d2403204407003a441c2402c15155543d0203428000416103901700d26011942c1112150340d0548a44e8803150080d10304100da0741807650503081408030b20020401e0260f000c8103001581d070804d40007009807048508514080e1400c1e503100c0020f41d0790040110001403e150000007520849000391707406d01c80301e400311802c0c0d80c43c1e02c42d01004040306940003150072079243c0b0907031191640d0014043c2c0003c01010410004400b541003003580320302ca038001104000700c00302800070351008000c1500d0307420030b006c1150340e044902070400d001c0c10b08018000c80503415941c03420451180030550038900345810903440c04d100110441764020301001d03102d0b01002c101c04040c001084042c2d1508400504002216100d84020300d07444608 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 262523821 1250 262522571 262522577
    0x91f050f0901050403050102070309080610030b0609100e1f0608040201050706051902181002010626010605090702010b0102060601230d060b19090e010315180c0803040801061a0a0f 79
    0x4c000300010310240700030220795000392640d043c058544002540740000c0204840d244620207802080003d92107495984c0203001201c00c0300b010385c0c440000794121b07240755001c1c9115031011018482c105180080d545c06400c000050704031201d442d914256403008040c7c0340240010b40c2040841c002c00c081342e20003a0401c0204c103004001b440040060300a903045000440d1640c85600c11501c440d10b0110720400031a1000e00083c05600c2c5090684000701c9160424000400c02d403160280400b24203500060180400400d01442c03410b180350000d0081880100d100c0c050302ca11004280300358001c00c0e0034a041ca0002d0400c440c5111310207100c0030035820040703a040c03903291141070104007000341c03402901c1d040c00b461551100718916804001d1003119168002d00010818070300502c003041403c007018643d444007031008100290441d01c40203005003860400f41c8088201c6070081010280440103008440d0740c040284045500c0d00f400794416060340703d00c00154501001911801801034400c010f20042c0c80c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 262525071 1250 262523821 262523827
    0x150a051005060d0c11070f0314100501120302250b091207120c09090b0a0515100201151a0403110a0f0e16050909070e030c1203091f050f090105 63
    0x100104229402440310103d1640e11039801480c403a030b00480c07943d02c00d6840700040a0701e5140525a000a07680703804064007a0b4902241814641000c2042078588a2840001c00c2a03681d9290004501c1c03280040440041c0103c254100d40c0c0c1d01e4031141180ca01464002d078082d811f01d84180b01817a64001c40c10160072005084d41406a44428000400180039402c03440c3e9040407a813070005c0e540340c101c2d0070503504145807140c06d901080b0024809076100428580029840d150000540d04003c8075100c11a40a140300e22981e529a90641100344213442190600e241c0c0364480b9982d50175031180080308542018144002c201041104489040500000c0c00f0400e41c5a100c03030722010a25415002907100c150203405202c82d45503601c4034a0607500c040d1406c5400c0082c1e00300040c00c0c44401070300d01c00c100039a411040000b50303001e0110102d5400c000b800680c0c0c0085070f44a031500e0f07402031000c0030310940e03883d04401700d643c1001880b081034050566170b01e4507051201446e042d0540101425504001e028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 262526321 1250 262525071 262525079
    0x40320070b1204021903030e1c0602270102150c0a0e030304080a050c1e0d0c1706041101080f0a05090304030c062304051305060303070f0308090708150a0510 69
    0xe54010011500e2410400b01a880c040c014490110407181e031007100d4004200c0c080000c82d900c410711440101d400c480540c0410680550002401010380c2c001d4403e070710004040300c000c0313007500303042c0d12074205154400030036100c14006a8807440c0710089980c1c442e6074003000501514400740104a03500c900d042905e0194a80c00102c0d1039608543c1010165600541d241d03010f0003010840c8040403541110041880003c0d0035040746101f884400300c0303000d15021018641007007001494035001c0c10809017106900d480a0400c165154010b94042e80c8105c0a070240400319403103085928840c494201020140380c80d180ca1010040c0710007070421615010134000400001c40030540c0800401c5283e5844824a4103840c58550940e401c5111007207140081100300541d03118801d030b0808005110f2000034403540c442c00440c0c190310904000400c0b00c50b0b101d801108042e0814407117400b491629003200c1140b511030340e01580d14400c0c1a1041d882d02c2061000403005040c03600007a03401880f03003024000307041d56 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 262527571 1250 262526321 262526339
    0xa0e060301091205040806010b16060b012304030b0a050603120a110601030c031a091903020a021207060f1d0904050c0409060509010c03060e1f0f090203150904032007 73
    0x124110400004c2002408022044041041d18003411f401070a1926061608801d006500840742c1c00a021980380c00000c181a0b0107940010400d41d140e480c034442052103040003080c1c981c040e0004440035001e00c4041140c11b0010711071144619006001071a20110a0204a940b074000c2000301c0e0822203203c60002d820441409500e00a6200e5034041d4103240c00c6180100c0075230307605a104000019028104083d40b0800150840c040008803030154002c4000c0c00d04900701605a01b0180d001904903003c6140d070b280020b0000201d90940c0c1c0d4022409090102c21a803204180da001400c070f440301c8a00d000c4500e4001c621030b800c82c0c82142155101a002c0d00810160350b07400c1000e0310501c2d036600c01c028580c0d00a00076002004024a0b007005a030f410240b1208a1010107000c0c1d0200807200c85084001c00c5000c18118041c1c01000d1101e16240c3e40c454421010b51b20441d0f6920448248070103000c45401c209404600550303040c0c0318510032905c201540a10030344c10224070800c503c140200000c466032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 262528821 1250 262527571 262527593
    0xb09070b0703020d0e031c0302210c1e0a14030c16030e04060f081f090c030506010513090b061e0d0303090215250f0c0603140a0b0a0e06030109 63
    0x102c20b4000e0041030201d00800f6008107078034660a4000d80001c0081410000000090626010b43c3e00b0010f031900c4414100c200e520308440204000080c020042c4440305003041d0203440040c545a54031f45013240c200100000c10b029a4400001140e001e1010600c1220b1983c061503001418810990500301e103140d008174109074100c0240e020a10341c80302c01d100380c141070180f200908000c00c8650805407600252036078a0120038151103a00d90740541d00082d01246400c80030703095412849201030640c880c2403903500d511003846064482e010b103200c00061403145003d0f500c8015000314040b1156a00d42c410b01040c0c20310030161080d842076803801c4042c140d80b19040c04203858081d680015214a45106001607070025aa854031500300038402100c02030a02036180d030b0380b211221580381d044540e43c5486c40b02c100440500600a444404020440c140d140c1d1003417400403000c00d02c1c0c040380e0300c50422080445004204180c0c200001c0710041c001d405000c0003068110201400004d0304070303003940714251007071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 262530071 1250 262528821 262528823
    0x402040f0c1b0f06110c0f0c15070f050307031d0405070c080c0109140312010b0c0601050111030c1c030f060b04120c090c03061e0807030f02060d06090209032401030b09070b07 77
    0x217030001c100483c4802003013104011000c4035800030010306040c800080c4125041441c006d865400010b045010014040d815a50041d03004040346e031181c03d14640a801c12001d00103078040103003140741400083c5400e00440b4052102511280034608143d00d4040b8030b9070041c481300e003081d1f40b104580e000040c1745e10b54155101101c04040c5444000e8540544c01d09441a4410f4030b50b180c0600422010260119000f4110b8209080640b0349114107a11182180519a4040180d014040403510f0000d12540c001094602da6035040054000c043e400104a580d940a0501c080303109000a021807001600080405802600c1c0344c1d406907919003544040c2c7c0c589100b1f00d40003d440310070401405554490080c04010002c140001c0340d8180380002ea651a028800a03101d80c0f01d9500f81d00541d12050200c2d9125980c8000c00d028050f203610003400070350701201d2068001d01c5044508095803c900300031743c5903d656030b98070144903480d5407102110404060b041c21990b0054080c0000c0e0101403000406c0c5031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 262531321 1250 262530071 262530101
    0xe0306090318030105040b1305120a020304060801061b1713170601050a0b1606020d0216020a0f06051b070b0d0b040f0c270801060e0402040f0c1b0f06 66
    0x6024010040c100301c0c124444214004c0c4e040c00d00307100010724100c01540d800f480a80498007101c405003080da103090350750b004054200d00d0000d9140b0046070f011000300260389032501d6010071643c0c2c8000444405400903c0300140012816051002806044004110104640020f420060b904418054628481d403011504038034180390020300a03814807601e40180030886410f00000d2500c101e8802500c44e800604008200401d520700030402c5542c1902c0b01c07090408801c541341d405c0050150740d0a810644103031b1091100e2640012145da8a4800c0016074155540d441c0c101410444256070711a0001009002409580e001003101070002e000b81181d00e40074040810485401c0040c03000301c40312001116941424a1801029150801d00703411880606400b5a0303001407001300340903420700b801d80020a044d420590300040c80301a0045882c005c90084400300001151044a4070480f00f602901e4000b04441c400d4003080307441c2c1017046202c0c45004649010300b2103065560581122010b4481941c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 262532571 1250 262531321 262531327
    0x6050316030b06040c09120804030b0a050709080318040506030c09100f060212040b0d0b15120907060f0c0807061103091504030e06090a0f03030201020c0f0a0c150e03060903 76
    0x1403144001c04140c010703c0580d8104150009110001c040c20320500910a8800040d580c040402c030f8510704880c012b40c0c01001c0c17010300342445580c0c80003400040e83c0c05000505001c1c0701007942c98001c01202c0380c0060300d401440e900503000c001d000240c00d004245503814004c03070702200ba0b1500e8407240948101100039001c4500c500f4451101106459034102008560210074100400c100d000c0071102030750204d604464850306041c2e02035000c0d0511061054008601000400948054002510342041500034010342aa00c44136075030350b00d031903512030000001d4042820002041c06401e287c21800d00071982503150106a444010070f1703840b98003034809190400800c0000c103184c244460390701010003d00104040c106528020702c4603800c4818a48200c03030029940d48150703a489210b10040c542d45032207079409980d03414064000e4001a4244919006400414001101c0440c0029003154401c140300030750b41c00c021f03081401c7c1e14058848000c2c03204580c2001c01558080107a036100320f2070400150783d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 262533821 1250 262532571 262532573
    0x17190e12091e030a0b1807060203040308090d0f0c1a09090703021608180f041a060c0307060e150f09100f0605030115060f03020a1d06070f0606030b100e07030b040605031603 76
    0x54501d03601c401d240d1298011300408e210141c1d0100c200d0741205c0c0c101c9201c44e00d41307070804000345d440020918020703c949800001c640400103040d81c030000f1600181031000480d0394000081e07500b8825035400c0c540c0040c41c1e01c002082d860207030f4050611303815000f11004103d109603650800607030080c203805880b0342821281442504e4100e40407001c003041941e040c010005900040b5140105111441e8400d00c0041400f18090308104156910290081018809102d402c0e0140c2d072100604104040213850580c005090341c00c1920880e802199040010b014081601003000018041003010304401038682c4000500c0340d409018241d007807048150324200c1103250141c0980302e406000200010300d8014032007084001c0e00a07814107002c5214481e01e104048c40c0c100001c00034490300701c00500ca103107140b4003403040c00f0060f03000000783d03481810300281d5900d0310002da840c000000c0c0324000d4002e5a007000140481e201ea00007040700f0f40083d0010070203645400000b0f003454600c0c10307c58a040c00b0a04100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 262535071 1250 262533821 262533841
    0x21207050a2106050402031606051b010b0102060403080604020708070b06040b0118050f040608010518100603020d031d130e010f050105030601051017190e12091e030a0b 74
    0x400074a07285001d4001d0350344400b41040e2801e0b00c00809800c1558410025003951403e018610320b200300d0b82c00240e1080d4407071070064a81c0d0042c03941c820a4120306140086842c1051042c3d03070381420143c000384100d50311550b04503485030004010941158091040c1400501801e01518a1a11541c50b000580c5010414801124240d21645040010701e8100300035094a9000403400d6403816035461400c4100140401c020b042e20b40d00507070443d0300c0c02d020450510310451415a040360003100340e0f02a0f00c00303003506406450b240d0201a50181c601491100000c3c099209600300580390124050312000c2d5a002402a0000079121410703261207111070b848440080c82052244030805800b00815410000031035034500c81400303498040c19034040e03040e4065014000744110b0081a500920803031500c0000600d400c4620008280607905001c80c052810070080340c0c2d5181c1d6004420b01381e007440b0b8000d04000c00c1c0c0b459110b4024a8030b56058448600f070b10203018020443d80600e80c4445a4140031040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 262536321 1250 262535071 262535089
    0xf150902151c060b030606091206040c080d02030a02191b03030e0a240e0a0e0c04050108070f020a032010020c060112050c0103050a2703030b060f0d020d0902120705 72
    0x42100c50b2400340244419207013981605d03048102681c001ea1524041004202c42102d440412500d500c030b072070204000c125002026170103a0f132013041514902041d40030306030780e0707801055410405a00071a08150f80c0c003020120052283c2c0c09030701503029070300342542c0da60300d0300080750401e030006441201d00c5450344c10418484401442d108450b0707507c030102e94000400003000964940100071021005c1519a0342d1f2000303050181231030489414160400180c000410341c0f0600c00c00340481d0f92a00014483c13400703070040912011158003c4c2c12607418956007141c801040381842d1003030641862400c01011820811960368071104880141c0d82e030080e5962070f1908105a00ca1208224200800e80006101040d8100c000c02c0a0070302241d15110886030902070008444a40071a0f0741c8000346008103000d00fa08130080314040d03182009070f11803003000e010707940c465900302c40e40080c400c01668100586950040000c04a030b2000054070091903800507a800441910640a641c440d002c10710252a040001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 262537571 1250 262536321 262536367
    0xf03090b03090f071e0302210d1707090303020a12030f1a03100207022805060a0503040201180b070b18061303030e0303060d02121e03040e0c03040f15090215 69
    0x114102041d20404038840c0d0001030000034041c00320880907600381210308008e40000014001683c0025580f020010881580d40b5100081c0c28a10301c00301d45094000e500d0700e42500d800d64098030040d51251580c480b0700642100c0381e010965170b0210010300c0c08051040c4c816213010320f210b2000351003500b42058500309011407a40b180b548104956030050303a03126456550300c0d06580000e2030500f0010303079184001c201c03a804660800701c00500b05031170310350050085102c0c1c0d01c00d03241c0b041e0143c514007030011110700e1401161060241000741901040076403851139880b4803d9010f0004000096004a040c0341050300c44483c800c0c01d03468510b08150301070181c2400c25200b08004c40c01d601c2c20600040c02134860400c040d0007088110050031104005000f100d00700e0000c000514501500c48070855900c0e4072a00c1007101071001540456581004141164055a044101c0b07002c0c0102c5a185c00c88050f502c3c1e00044105a901c50a610041c2c6036002d040c01100c0005410ba070b11400710f03ca03c9156640341500c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 262538821 1250 262537571 262537589
    0x15180106050a0c050106050a06030501090509070f0b07050a0623070206060a050f03010212100503010b0409020303032d24030d09030305031009141005120a0f03090b03090f07 76
    0x5018996010040c1c42d10350007103242840e0010814200b10340100840d8000070340292402c03401054103900b6402c06412101003036000c1200f5030755400c0b41ca071541041d0041e04404640214100b098019074005000480e004d2401c0c1e0380d0400755903032032900721a5100301b0303008011155003403c0c5912a105d20030301e40c483c0c414009041e03245003042c0014240c5030766005040c89661200420001a142507058a142c1915800f4000d0103081c003501a0000b00c2c0d29114061083d03082c1040c0d221035062502440700e030142e001c5c0082d8295100c410610082002d84404102c0f21038002200310a000c0005603070038050680d0701006040780d02009120b07004040b62099040c02548902c251182181c1d100d00301808480d058a003264490300e03a48150062030700e0700d610a89060342080030310391041080d00881d500a40c01000b445ea516950fa06c2402101c4080c2d42c10411203030880f03100c420116040d00c1c1c1b4480300700e02c689841110305403110300011580d0403da9074803c02c0d0707000301680b250301181000f5160281c41d8881c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 262540071 1250 262538821 262538869
    0x30a050414070617070302190e0f01050f030402040207020d0803070302120a0506090714091e04320714070b0402010306050105040513020c070506040815060a030c0306020306030a050615 81
    0x9807180d10f134803440e0720403a40e00d0340c0000d400510a40c15a400040145418804030080d001d00400c140d00d0711040500c2003c4566400c035240d1b00540446007050b0113405220306540c0d4a400b000000e4001d0310b020303030304048140f6451000901c031400544c4200c016440068a500c1280c0b03c10032549801401e60003068034190a10119035240d000c03940d4400501c0c074001191001b001d006207030601035000d0250704080d083d00d107410441c4190650080340b80c0151010010100d0340c07008042520003007002204000b041d0b11580ca1086000b03c0000c0d841122401c201c0544004030111145a9108800503190803c0a0040c01b0446d0f0340342c094080241000d182071401c042c20710b40010f40d0304081800701d40349298000340040741e0150511204c401450b006150320744540d03841c200c0741d4a500c0709030a11501a6400c0001500c24130300b241d04482501d40000c440c034100d50943e51424001d41c000b0701360301e0b49032244000713100001b04100042841a06884094500141103078144003e1a00301003035140146110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 262541321 1250 262540071 262540079
    0x90f0e0c121003021e12010b100c060605130b030c0306090325050d0818010516211e0c021b09070c4b02130209030102030a05041407 58
    0x160141c460359a01c0041034072140d01d54403a100a542c42c642d00003500903510000901c00c1c081c0781d40f601c00301c06a068a4448055110342e00e06802c030307000c0b41042c41e4803059a100700291a44180721525126210394030016545440d100090581610078400905081d21110007080c14101484510700ca04815801060b8504109049a07183c3c041c0140c0328520061f50300d1412443c00c20801c1d204a0303070760444180c078000007204800801d440e02c1124800e2032607005c0c1c2c1842940f51014854a8800c031400b1080c082d0700100e03500e04803030f50306004505441d80707034098010840180e003602c0f440c41460307035085001d014603d0a26403442603503060512401550449030030700c8064600030b4520400c0ca1000c6582c030246135148a000e40d001000803401400d4240502c0644d140c84072901810703a05844120440d030b000708621182c19070300e1a100a0820100c000d41c010400050811580310100c00d03c0100c2e0140c1041e241001090898000310398810895071250184030034440c2454103101c0701c0700c2c6c0201130f00901d410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 262542571 1250 262541321 262541341
    0x12010312050339070503090306160e011d03030d0608010b0a0f15020708060c0c0c1012110d020c0c0f010e100f0c140f060a0606120209040912090f0e 65
    0xb52040c4035120000722000d80100b50001c0f404120a55046124241c448a6a05050f0b580e50000c2d503045000e44180c40100c1c0b08062081c45181518070b29503609407035200b000c80110380300700d810300035001d00e0b9141e040840201e54041c009400c242090740400180b1078505a005400d580001c014540a400300c03d0301404030302d119610742e40581d0110415480410300c51003003240b03000210ba000808501840c002c2c0594520318031f00822205070403c04541d5800b92030300c1084046074032120359038003103070207158003985680b510f40000d1514554071070380508194032000340d4026648000b206941c00d41101d104204c0345d1030310b01c0d03403451190300a190607090078420f180810b41100e06400303000203019081c4c500406051017800001e10841e800311010804448074141c0540e80c01c0724007a02d82803801404000b944003055440303504120707555641c41c0c10012581c0c0410b50001d503c00300189410039100d040f41000f146144626019441e0140c0e16400b1007840e06401840034007580d0400005407182409204228031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 262543821 1250 262542571 262542601
    0x51e010f0e010516080403050111030114010201020f0a08060406080607090603060b03061c0f0602070c030605061909150b0403121112040905070e0307090f0e06090d23120103120503 79
    0x26801c1c09540c0000c1030303042142a46c001d03030b84020429030810845a80b03810030303c00614100d4410700d1b800340415080c0801a800d03400b94641e00100400248a00c480851040c4041ca4100c42c014200043e11910b80d00864200a01200c0b15008038001c09800c2203010307494860f03040200304803440701d0f046007090800142030304801400710310b03440c8040003d0b00900c00b6224a80d40c481e580914115034600c46858a6516013801c1e02c002c3e034940b07143c1030002c0e60074200804040b045505aa010072412400d1805500c020304095000e10341e5031003840c4001c111809548018070180d800358204d6048107a5400005001100c4940c49010796000140c0c0c054400b24280283c8007138888a510108050396001012281c2c40d03118100f09a140c402c41d040000c2d802010b611010b508a5010300034080014540300e415500c403801d070b81140c02d41d40641d0400710041d10905414103103815486a00c170500d810b01c0100319454010f0603a1203050382d0013100410800083c00d14030b20200e072003801c00c40d045217007805200514207 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 262545071 1250 262543821 262543837
    0x7030f030c0c0e01030c030606050904020d0605090712080d1104082a0310090302010c050906041202040e160819120c05102301050a05100c020307051e010f0e0105 71
    0x3558611002003090381c2d4001005012001c0754030701a90b9603814080a58417103407100f51360aa15001001c02c203801c00c050011f101e01d4019000c42c0f103020300c5640750b42c000e010050070305d01a40685400130413a00c011320352507004540214a00c544814074001003104642440226450750700040204001e540c0000c2002e42aa080d101030680701900004a040000031011100a505008507100e201480701c03180d02c0070001500035030080090280100701a2074600c18040e2645d800b40050204101c179040b00070a4a11491000c1d10100c3d01a503501541444c0045501142d0380403139210b0000c3c4202c000400c0711b180c0400400e600d00903440c074140c96400e074000a105507401004004120388007440740400c4140f2289003104410071207200190244604800e200035010414100400009880e140c281400d10540d4402011901d00d801d80e50800d403241413103240103c0c5c1502940d00e002403a6a41d560b2000e001031034000d8048504010840014150842500840144914107898034180c1e613010095401407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 262546321 1250 262545071 262545077
    0x3090a0303020a021f0c020c010504050f1320030f06030a0305220807060906090b120105010503151005030603010c0c110d02180c0415020d05120a09150c020f07030f03 73
    0x10030502c18101c1c00c0c0170690708408010700c00d60350700d1443c074000ba902c001171419030b941c03c1d6488880f0781d40045406100f544030381075000d881c01c03140c64114548415000010042c02c407001820244c29071110a880707020410003025054080104040e500c15001e80c030303034880b804402030700d00100303141d4001d000d900601d01a05440360b48540000c5402c026000c494020b00000f00c116044640c0c3c40000810344141030241d00000790b0260070010705150884241c032001d410382c0710103184680c00e0400440e855080180541c1000d44094809a155161314084424400d103558071544d0f40d01d000418182900c1d0100910020031146510410200b84d00c3c0001410b502d6040390440e055040074000120310103a40174105072000b07030781d40900a012201d00c004004551602e442c0404450010b00c0c02d0f601d81000c06400e10200300b0411a518044880c80e28080e4454200a00000e51200d940c49003103260403d0302201003001e40c2c0e140000c8500c2c2e0104050a031141060b001045440d0855551440e20340c5101d03402018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 262547571 1250 262546321 262546327
    0x304060f02070212011b020a050304031e080a121406030601090509010b030f0106050a120803010504051e0709050a08011e090204140f1006032a0e04060905060f040203090a030302 78
    0x95424039404507054650003c004569125180c41a14000c2200080310021355106c51142c1c60076030f002180303603800d194200001d1070a0920350740f036003c82000780c0e4070307400e249200c00101c0c1f00008817210042d0482c10340541c3e031140c00800101080044030704c0c44d041c0740c2d41880301c00100450b5680c0092214155602e011003c01d00781c8a1408250150906080880d8580100d00c3c510000c0d100550006d000c680c8210741c1820261341d6004006601070082c3c0015040f8041000144054109600410b80054007004c030b50f041030b80710111f00303024001e0130354041000400440c4104894508009668007520070700e4020040c00b402180c160349081074002c0740a0105442c0da481c0000c1d56290740c020f8002140030081d55410340752910042108480840303074505110001c0101040c035911034441c080d40907043d248045020044200b00120b480f404140041c200815048004134640300c034082c04000f0b2481c07030000b003406e0400c80e040007024440418084d006a20600400045a000180c2811216098240160b07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 262548821 1250 262547571 262547591
    0x1207151517031c050c0a0c03020c060c0609061b070b190c2d0806090402131107020301061e1a0706060b09040b040b010f050d0b0a060c050d0201020906030406 69
    0x16a0040381da020000701101200c0100001d18040000c04040078041e0700300341e0000b02c460500701200c1040d5040c801d041c40c1482100b0001d400780c501c80200c0c030301a0046404041c0c03001d00040d0760741d00ca014000340ea0781040c0705008284100b0440075030481d0005007070901d08441c164181400b400b452102521981240d40401e4a00c0c264090145114240c0f810500030200600009420aa07a0111131309910748207034049138549a441210221802c002da07104040303030312200f0800107800340140c4140e922900186606030340440501c150ba00900300744024940707a2250740105421204140d10206500300d07243c510114404070004804c0549104c1803030070340300145080310301c051030160070002407000b868280302081300004507015040c03081e0300301c42c240854107403c014017050b90301d201c00250100700182281103419029a000d00f2050311100c20024083c17050000103881c40015a10607408504142e07020418014140114801941c280c0000d6107010ba5110103e0700c144001003001e0070650341c50345450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 262550071 1250 262548821 262548851
    0x20d020708070807170c0705010c03030e0105090106080708030c060708130f1a13020f060912011b1404080c10050d09110907021f0b03010b09010b0c120715 68
    0x5100a4000720607949400c0e40d89402a2158000c89040d206000c2502001d010040e80380c04035101c80048101034a545445c2c40700641c0c40704032090040f800c0c0342d2503c49858900c0300074880c482c85104030b60000b0851030310342001c107030401c121908801e00580080190301c6201c80001100c1da00072001340750245840e56a42c0143c2d004801e10038008004030704014100091042c000e2140c503121801401e84041e40d103442c004002004220341c40250410f900350070340e1040c0e190000c05000c4001000d0f003800c001402e0703482c1e07550031501818861146120000031041d2059806407407600702613038440d40c0b40d1070f03c2d040c04c9040350f80309201e0100c6032144041003d10096140306805030740782408440410300200d4003c8c6845607110b5541880580580000d9000030030180c07001900303842e04501c241061400290018074807001e080a1840e1603010340d05d40e0f008445a880f524031550007001800340c41c40e01c40d044c41c5c0c00a8209070092034034201c40320042c41100040350003600342e0844c425905500040001400b9000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 262551321 1250 262550071 262550077
    0x50139050609030d0c0903020f1302040815040b0901060305071e0f080a030e030d1205130b07120b090f06010818010204060201090b0a18080c0109020907030f0b0f1003020d02 76
    0xc200d40140e000340210380200001400400311155810f201d00b41c41620120780d00d9003144400f85d8414000400380030541042640c10114041c41c0303102501c1c081e2100b07250785c6040c2040c81a44186041c420802c02402030108a160304002d06c0c0c4000c1c0042403441d03c400341d0394540b0b4058a10414103403590b60940b07544100601c00113115110703501034032aa450b2059501c2d001401400d0b40410320b69495924640b0b03010030241c607418180d44602c44808030624020008090092503130b194001650f0706440400c1c140d0340070601c180816500e000100c140f40801c841550321820216018580388018480340c1e0544130300c0d15510070310a10f0f080c40680d5400900342c44c0c074040c01d0b01300c0c001c1c0d5100240120300380360b041d08940b10b00341c010509402140c40d07485c0c120048500d621440585010340d4a80000010746800c01003000d00c0c0094004030364818103400084240348143c8901c00842c0e52042d0401185125009600b0818022561031460101200108201c15129512442007542c0001d20016003142ca40c15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 262552571 1250 262551321 262551323
    0x507051e04060e07081b0d240902031801050702060c03040201030213080f01060b0c030a030b0102150a0522030f080717040602070506090708030913091e020a050139 72
    0x1050107101da0301c80305080050360903246100011442000214083d007601c8403581c4607905049281e21f0f001e0070004100081c0003a440d6014026251089050704d0190b120141c2c0141610307c82c0107aaa00b803c581080390354240302000c2070180d041004110742d0303e4010803d07030340c407041d1990360340d50381e55039440120008d200e4240d1010343c000020f00c0c003143c05900000d600c900e216444008001c2e558540d140503016018084200100364003c100d800078451194000b070712144810300403078000c0f041200207286400c800f200c061003600d036200300300201318203008510300a01004500d001c0030f880c00d60314010848801c0c49000810b02c03040d540803c0d0300310b110318985184a031000308010118103103031906601951190300c003900d50744142004a800c440700802c074001241c502000840c0313001c0010080c88400300320140b00496480e80e07641403001140c620b42008048d840002c201380c1c0c01c1d10061040200b80b00c11030300000c1c100a410803001c000078502e80720072a01c8840b10007400321265003018021343d0003454000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 262553821 1250 262552571 262552579
    0x7060f0e03160302031b0d080c070e0c0901030606082a0c0f03090a0509070c150b0a06020f060c04060c020607080706090804031412040320030f0c150301030507051e 72
    0x702101e11204070b0040006407442102641c1c4200c110303d90742e02c414613600c003045a010480e0042800011800001000941580c0e01a01c4c82160745040741004040100d0740350152400c0010040315642c0e02d07104a9029181c0c40c2840d01d050b00384400851100d09160a007408408540d203d401501c00c007030010b440e4030700306031000c17555100e1805000c3c0341c8039000b000d10340d40140c241110200d4545810858207210742c28680d646d07402c00e4051303295a49010401d014104000e640c40452903a2516640848800f41c482c03038004001c038200702d8603460b140c80030080c848100c10302c2c24441405941c1c3e011901412850f011a0500e48407511360401c424140324120700140f40c20314040c05003007040740240281c8101c902a0303144040618507001c3c0151108804100e420206108010500000d0304101c41024503015040403000401109000720b443e010310a55880f85540c1308080a88052429008040f28803022007002400c0d549182c4c2c0e500d45e200600c2c081c4600c54271004100b281c2c64542c012180c046558010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 262555071 1250 262553821 262553833
    0x6060a09080303010909021201060305060c0d060504061205100c0203031602160e040c0902030705070f03020a0b190e1207020f060d090b04060b0306090a06050907030c08030d0510060207060f0e03 85
    0x96a01d0001c090f46c1804074011282ca4001000703010040c41440112600103003e802c03d5901c140044003a94001c414100407c0da03662408503050310b5910500016010701c00c108040041e55007803003450900e5200490589070304244044551980c04010749800020a1401d0344000366071850603410082480442e002c0022034400c002804080d080c0214000c40c005d66104c0c0e070181c0c4814411080c0c1c841111001e0105204000503000504250b440c900803901030720655080160303a1b40e0320810a40260b40d0310b9001000f842010b44c100c505032041014800340700c0c0c000c0c031081150002c440414001d0f641c000e4031500310864105415100c9000312521004841c070104011205858560f08030f400c00e8500f6210103160110b80c4006040000b251070140881d080102041d03007403566940081c08005111400c0f50240c500004001095544a20050104207000e1519819111040c0c01120300007004403840d08600c1c4c0c0108102500032410b88103a48580c90b2840c150b4403465004d5410300039014205070540716817 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 262556321 1250 262555071 262555079
    0x70f20060f010302190e04030e0a030803090604020906040c09090213080607020a120801240201060506070803011d010b0307080a021b0d0207060503091e0a0804060819050103080306060a0908030301 86
    0x841414180c3e0310031201d208110030f01d00169041200b45002c3c00c9020061240800c0c08640035003566001040001d1100b50303102d80b00d0f40c4400c1c054100391030003030051b030208e001e120441c40c003010b800c0d50062081d5010001d071949100000c082d080d852140903089079001900000f00200040410041c183c0d0380c0c107e845030300300f91000035079456003080140d8010764500124600144240030090481d110380300c039501007461082d0415001050900404150346d038500380000c00740c032420083d02456000e041081e44940c545902d1030a0030341c001415040c8101da60006006a002620590390000600c0c41c1089086c1c0d0b0f00e11f07900000384245084d010094080c0812140c028000003040c42d12480c4070b07400e9980c029601d5009540502003912800000d4015122500074082e40341080000c1640000884601c1741c5640c40b0141c0fa40d01a411443c000380c0081c0030001240000c64500d03103400c2800800704881d624540b2400d43c1400040c2155219620000e5a03000c014460070300040940102001d803656544e403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 262557571 1250 262556321 262556341
    0x90503010b0609042c150109050112060e15070c060e0a02150a0e0a0306020301090b01020705100c05190602030403110d020a0b130204050106030501140f0913140d0c0b060603070f2006 80
    0x302c40700160340c20035a06c1c00810302c0c5900d8024141280c9074031a40f0302e10700b00c840d070318031014000d001c950b05414410701d29008000c03c41c54071068043c0250b030300c64580b840d419041c20390543d65003031800700c031a9001d04503000050300c0e8240085004221510381c0c40d214400098200c800310580b0a50781d80c420702c0400040140032440d40118100c5030703a110b08001805009005a85030f03d014417802e6440302003045820710142c010f119100d04c00d0712030010781c0e400da10050200c481c00c00250100f82e42513a40401000101600b144800c219034185030010040d00c107010700025078400c10800010302c00042c02c0d02107403034a02c00d0304004042950042c028000d9603100d0b14003e004000900c216201c481c1e414810694501304041d800c0305140028014040c644d0341c9214081666000d402e003100c000d00506540314210b002031051030b07151201551020140c94640c02c050700050350207400d181c8580020814024056000301c0072440fa02c415042032045074554014005516400441010060051004104001c0c803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 262558821 1250 262557571 262557583
    0xf0f0c0308030124020a03080408211005040e0312010506070303020706020a1706010504060215060a24030c1106070e01180f0314060403050406110a06090b040201090503010b0609042c 80
    0x180e9041c001c0000b5044d03034200d9403000c503200080c0200c6c0050001c200030400c5880200b142e405941d55100800ba20f050600c004103c1c02c4504048488807840d040c480c914180c0038140351140100011406d000d0111032003071452a06202d6244036210001e020b20803d40250156200326421820442d140d030b00140010302000c001040c44aa480b20900019034290f02030740030f98090f0380301035004107606080010503090b18180603240a40c8071b144610f000451aa40340c0010380e0b98102084032508000c0300c140060103070345a0900a0050085c6081038001103500040c0007580480a4504001c0c036208000069600e0890100b4822aa000c45403000c10049022481031341180c1c400d484034003a603100e801d8070540300c60341654000c00285003000108152031040e120050000301e101c050b908120441d66656040702e075134241c1183c618202c00200020b540e00031800d400204010b038000c0c01006050343c00148070b4450b200c1c00500c0360341d0310000401c0f415820342090072541e4100462044030030b2489000c80c1d4510b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 262560071 1250 262558821 262558859
    0x306040c030c0e120f0708030d0e0105060607022206120302060109090206121b07031713050d120b0402030109051909020f010c03020a0515060301180f0f0c03080301 72
    0x25060040c00c6815510a20503118400d030a0383c2c6084480740b0303003030400008100c8410358509034800c0c800381c400d41480900800d00103101c0d01004540d42c076903444440382071300c40040c500e10091349080304200c0301d629003804907114036604403105080c2c1c00c29110f80e1440d81000c0103240c44614502803001c01d02c52000d11488052078000e408941d0344c0e81e41c4415520555034600e4001390411802d20840c9180c0b080034102941190a4007004020201c00c9482010302e0b81000c2da0642c0002d02103600c101d484030700040115080b0354078910310450640c0c940c44056403503000c00605400c01c855080030a190300525440186140401001507589581da484940b018002c11749070400649488440410808141d106902140398068401c2c500920460010340303020451138001d43c01e40c007400400e00000f58013845608100c0180a80c400001e082c10010301d800c480200781c10200f8a0317101d034196004100c52820500c00c0d10303805240354108035094a006901c13842103a0008180c030754040004120185226000e29042c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 262561321 1250 262560071 262560079
    0x10f090804050f06030606180d05030c0319020c180a020c1501050a0b030f04030c08160b010303022a131404060203153c0a0806010302040516080a0c180b0306 69
    0x3c0000c8401c1180314030003a518a07902580c100901c209414115554128040c0e0003802c54044040d5502d40c0c40c00c40c0c1c4441044407861b00300049884a5104c0c0a40210030000f40c1d200601c40800d101002c034103101086a65850000706050000c4c601903d560116a00a2418025104008103a80300840e030b09000b130240500c03a940d050408180d410800d803c0c0c9200c0d41881e0300d011100c3d156a1010341e007881c08800c066400400c204106120000018a28581580b10341c902c0405d96145081c004d0403c06d103019010050f40c0307001d1441c0110702845e106030103030390411070791402c1c0c42980104141c000c22004c0440ba0300c1f070307203072004200070301500758051481280750001400321100341c0300410803203c1e064010300c141d00e81d4610507010341d480c8144406800000583c070203002110020b0001c0c00a8684c0c2c0e0050700d280d0300ca10018401c505007405542e03003001080141401400388484050b000e940010005008036503666420074076036100c3c5140c26091084a52220411501c801c519149984100d803581e000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 262562571 1250 262561321 262561339
    0x203010e0c03070f051606090809041a0a0329180c010504181e060b04030302160e040b13080d02031e06010818150a05100608040c0e0405010f09080405 66
    0x1d600003200301ca204042d259100d4000500041e0181e403990010307800621300e0b04018240000141441c4102003400780030300b404d02c1e2612207140411003992011082160b2040c1c03c581c50f0504c40d100c1c2e1180038262a44017802d41101507000009003c0103100e400310307a00036404601800000302c0505042104860b800d400d0350010b03800302006444a11951103408150501406c9a080550a6500548600c03240c1e907810060706541d14003200680346a5040008481800941001090303010090b0381d94000c08031450840d82460402e04958602006002034091303082100092203801ca000d56400c241684188803903150300d0035020a100941003103d50840c100a407001000011516400880c42094140d41c0c288031a60f480e901e03445040d00001d0342d00c10521944d405c80300385c5109a89611312400d07036400001850314003032303081c0300e448003d95000c54184040740d014480400d4030010944261000741d502c070340e010703121032518030300505011904c1d0340c0c41441c0540901c1002400350050084400448844030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 262563821 1250 262562571 262562581
    0x20f07021f260c2b0c0e090f07030519090f032d1b08030109020a09050d050a0b0c04080a0309030b07020c0f13020403020303030a090221030901030510051002010203010e 74
    0x2d641c950030200c0910403800400600340035008002082612140c0034680d42c04514807070b9008441c03003884003209505895020200d01603030302030984060300300101c03221a10741c1041c201c1200180c030040e07ca0400c15840c4c1d400128500030001140c5811f150801c820400c0072030504048011a100c281e0460005151041a10806503102200025003c00317a22440c91701075001020388018001b407100e80f80380f031020402c00e07000c241c800014500800c225140903a0b10340890070010306007d800d42110744101035040411001c00c1c00065103001240c5d01009034a150f44607150380280320701507940300075424819204032008141d40306218600b00c900c1509004c600303480b40d100c10b0b83c5552402d641c19401040d0340381103500a1609452524980c00480401850720382c030394010078203652044138800306094944a4050440c1421641c0c900114201c9290b603c2246078070744601c0d264460b942d2840d0405845401080c01e0040d07028140d401070100038103400600d800010b000e03000c0d400034401c1000d01401400020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 262565071 1250 262563821 262563857
    0x9021206070f0c0218060102070801020a09050301241208070c2304020c1f0212162706120b1f03050901060b070314040504090609060c020703020112020f07021f 70
    0x255503035000342583d85d907802c400305042c10100024080c034114400c2e00c40c0003866940030320007031011000658031070881c10f04250500d030943c1c42c03400007180801c141c0c0c03041c2006000da480c10007081e01d8402c112400c0000660424081070302620401900445a0002c00550000d103070780780d210920090556038000c4080c034010170003207001e200c1ca4a581d07508040382000c0d03000782030b0880244001c41c010300141031480d407500c65102800211680044c041c01203614000e0682c02241d450030f61410101d4204100d046100680c0350142d292280d007090142041040700c4c09001a0080341c56948091720a5001b14002580c444079618140c9201002c289880013117280c0e03c4041c0a5038040d1810320b814140750240a03a030443e02080741d503443e02000c00c0705010201e1140d580d806034100039030040e0b0340030903c0880ca08121080b42c0785140d84409560100f00c003040140d0b0000c40d0100d00a41c030780d500588502400d60a1102407081c3c020082d4801640315891030120402d4400408005007641c8045066001d01c0d844 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 262566321 1250 262565071 262565087
    0x90a021003061404480207260d080702100c020d030b0d0503180105120903040f08032803060801180b060d03021c1b0b151e060a0309021206070f 63
    0xa4664000e01c0c2d000405240d400d0140c00601d507000144200c2050300405e02c1050380b0514200100503044007808000020f41c2c0400040074401c1d0043c40304002e850600351039039552008614105210845c40040c07402c900a118500c0f8202d0307160700510508508d004000d494401035480440864900500c0301d445003007120701c83c80003a83c4880218a0315200074030303030107841c071344011514104041008032825003501c01c1c00850040502c2c10085444a08002c00b204200d00b0f20f41026a00f03070320a01140c0c5030142c00405c078403401c1c8245184041c508a5001301140030b40181d40020031251700f02500500301001c1011814010b600407400e05042d5140c3c0c1c02045104001c08801400503402030055032032806000b004120400303000d0034180800e01411a00b00780302403c040080e0303000c40104040255442c0ba03a00c0080396080d044460f404459411500c0480c099031480e0258010100800d520369070780d009500c00704c1200d0700101001020302c0ca130544190382d0402281e0031000141c4c9500d9403100d1500400d56 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 262567571 1250 262566321 262566341
    0xd020d02070819061805030f0c060606030403080402010e01050c03040b090406080a05211b03070b070305010503030a0c05010b190602010c0e010507020f0103060306020a05070212070605030f090a021003061404 91
    0x1450201e2019441300006030400080105e40070803541e88003c0050002c100410f200c610f01c142140e1500c200300221030404000521185c014041041008000790740841c100d40e1043e82420701e01204000b490040300c6900030400c801e03d252000081c0442e03524448400f0b40b12440044a0600540e9100c640b501c0d120642030400038099408510f0710850381c80102d80b510440d902e48101d8504150500c0c1000c12004484818264150800565441407114071801d5551000940c1018030040d490680442e030740e441035038848410421000c141c4030810400790098004004011304c00500c00c00482e007005001c030320303a200e09400340d840c02c40080c4ca40303801030101801b0000161240d500740425070702030250700c003e0010b28034101540d41c5408400540644042c04183c001c59840e0b03170710383ca254414071008000580043d00389034400c00c403c000082d0b000040340d0f4040880b0a0550403912074901c0c40346803040d4084002e5001c000d048110700042e5165101404030340601c80030700070ae11500410b10048401c00d502c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 262568821 1250 262567571 262567603
    0x902031b13151a07060c080a0b03060603030405010c0201030e011103090d081302040f0207020d030527152208060403030513050d0509010903150e07051f0305040809030d020d020708 79
    0x100c1080f5426a0510001904401e203900340e00c0c00b201d40e07a0310411a040901e10102040380141803210421b428031400c090280c0680c014111030400b0000269240920300c18541080b8110742d548085900c00d820400c0030100c084024840400c02554040b442d4000300e65500c0036111b0b07100c1c0b034500346116031202801403182c140e4001e40480b081d000d21011b40621000b18208580822054006844076404025414043d035a1503803248980002d0801c070a1b841c085c1008840000c0c1c0c924220b90f40c65140c44482c10b8803808601e0303608c01d901d41e0024801e08000d03d01820100e189034000641103030105a02c2c0c070803480780d078040050381d5580d11401c0b840c80080b5405041503000b000901d8242d8011001800c030003c050600050441d070303031798550130540c0e440c45103120103517103410204e8031300c40081080001422046504030002d106440d83c88035402100b03c1080e08060f1154041814003c14404540c80e1041c05010b80340f0f407441c4698040d56446196250b40c006229400f000165894041000c88031404848 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 262570071 1250 262568821 262568861
    0x2010f08040b04030503281b0c030905130e03040608090d090e0f090111070f050607050a0c0f1a130201180807090f02130312080c070b0402040f0902031b13 68
    0x1840403145038000920b0b900d401010200b1001d88007100c0c100b80c061030941080c020230210300c030890032145402444441001d020310340492100282e0446a0305096036010b484050242e0b068030f07030322b0000e02014a083d5145000c000303804101a5401301c211807044110400311400420f400d0821102c031043d0744130342540a11804046050200a0304e411908140d484001261401c8105400c40b456070016030100c031001c2140075000d08001092140641c0070360b0750300f030490410b090800c01509000180c28010000d00510251500b007250001c048001d45500d00c200c46a40d20f0301e590b40d80c03188600644141d0104901c80002e0300d03001c0f01045410199451040541641d529100c8107002030020a005080d2880e0248510304080c244c0005040095004144802611000c228068041e030740103804a1301510003080b1722404a00651035040c1c1040c0d0541d4002164513440380000c0003000b401200940c14003480820004840884c82841403d00046480b2424000490300e540c048540e410700e01200c100c800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 262571321 1250 262570071 262570073
    0x20d0c17060105100804050f0f071a0306090403050f1204060f290d051e0303070f02010e0c010f1701080f010c0c0f02010e030709061806060509132301090902010f08040b04 75
    0x80c1d04180d00148aa800c503071023504020b982a0910807440c2d4060071030742c88070300104107515411807a180308091100710305246052030300104200150041015060000010703d410756000c108048413002a100d81500c4130341d09007854848086e04680d8000038200d420070400b000c01402c5011301c130000244003004101141884400d00c0504c0582e400240c034180a4520f0f8084403c00c6201c41c018000d8070a03015541c3c030310301240003400080d003544190045a15080807a4400500020582c015032400d0804014075901501c08072542c0088030780d00365000d494400001824000010030745021070520b00240700344401c46104654003495540d02070702c0003203400403800255002c1e05510000c030740c0280c11b40b250300e9290a5040c00743d80075a4003c0b114903044100007642640e643c4640c0300540000d1500d103183c0310244002510304186412080b03d095981c09440050b200022264000e540030102c10042640e03480d1134410081c41542001e17400303c2e42c90000001d03924402d800c4c9921071544a21781c8003064881d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 262572571 1250 262571321 262571327
    0x5040b030f0c0120011812020d020a03210c0207080f0a03050403020d0302010b030307080702011d09070f020102040515070203070e010e01210807060515190e0a020403020d0c1706010510 81
    0x1000184c846841c00c85200d4884200c028054848681096814001861450302d006060143d0b00d88100045400400d10502c00350344c08650041419050710b0504c1c0c1d003c12078251200c1540581c481342079854540300c1c00e1a10b01e40c0114004003100e14083c142c80c0035904505c1595258404640001c000400410080c030045c5041e060307078024035000340f0000454070b4400c03012a145600c95901580c40f0440840ca0004541e44000a9080b000c903514502810718011008074003500c2000c2c0902040c40409081030321445d00c01d505a40c01000020500f00c4041c81d4900c2100c10340c1c1c80303500b040c0d0284c040c03401c01080c8114184081412201c0202042100340e00e042c1030350081c2150500c040024200c80c208420106017510050310100f40203207000501741c144251f88069a403c003c0c83c01e801060740d008511001c5401503005000c440001040117103d070b5920001318000e11891300002c2d4000c150b41c094000b4040030315032881c161411000742103105041d0012150b51401f003442001c0c0c0c020b00b0307285c1013280144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 262573821 1250 262572571 262572587
    0xc0b0709081f0e0d0503010f0f0509071d03030307111b01090b070609061a030f010e0624060d0209090c0913021606060e070e09090607050a021507020705040b030f0c01 73
    0xa8010300025498520240f12030a2600c011082c80002c0c030040014410301c035542845200400d007a240188a680c50640803e0f0000d00c018019001e00c10010850049640034240c4010f00001c01020789641307107000080540710034000240c002c10744c030503800001044031b00c682c11018204016107a0902c5242303064404800cd62203280c00b00c131140e4031620743c82c0000700240103240c0104210071000e80c0850700441403520b0861030411070300300c2d6030600d502080075a8011071700d40c0d00851911000d034480100180b61210b2085000602d0b50004000100d40c203030192568082d0405070403c5a040101c1d440b004c41c581105e004a803c802d134441d07000042c3d4003a40225500800c44140350f035525005d803511703548911044900ba60712580007240860100852540d10000e000c80c0003104550158160503c101d86564881c001010034060042c0000c0c0751442034000c04c10000c00d0032407000780c0600303480d000c0402900d4007850b100c0e5900641c2403400400c00348c40e010a030645406c003034200926031500d07a02d0044401f45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 262575071 1250 262573821 262573873
    0x605040506031e071503020405011b0c0b09040204180501051807021c03110c07140d0b1302060702030d0e0907030905030d110409060f0315020403030807050903031201060c0b070908 79
    0x13100b5060300040c0560070940c4481ca10646880050700e544c5030400140c0f043c006150348240d13101c030980401000608a040100a44050085290300c0d40307043c0020900070311580c0c00c00321509450182c1d000c1d10320007642043c2e058503004d4a191b003c90440100c030200014041d10300c1005038002085581c5c81500602180a2038034241c41e01140b1140d902100721071540c440d00d4190b2064005103803d000c014540c00c08004400f00580d156a10301d2866226139584003c041c0040c028207000c08070b44000e55444000750380f901c1d500101500e0324800c041202034407140f85082a54000d100200000704030078041c3c03142003102a000b41c051454055a480000001c010040e00e05201d020240801300340e00105110720000b6000814105d0442421414070440070400840c0003403100c3d00402050000907480452a0341040040c2040342c0c9400c03d881c0004c1c254010071503500b4071000740800025403180d100041c18211801400100d40503200c0010464840307145001c0c0c00d82d55441400988260404007900810302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 262576321 1250 262575071 262575073
    0x60c02061617030903030928020904110a0b0301090b040b01092112020d02070b16020d060612030c0b09010515010e03010f0507091503060e070e03010219120605040506031e 75
    0x1150b0000c00c815050340054602e180280d10120070015a15820040f210318a03107503201c840140c41c15040c00c240c00091704003009028481c1000450200214034004c81080d10000300141e000540f155107607a010b810903c07a86146908001c1e1103000350810b4800d89d50181c206a540401c102e0808001504075151141c0d98240908961007a1021800c0701c2c1c03400140c290140d002d06405050000000e2500f400b40c3c10200100d0030070004c420150307022050700708a0980c140e8040b1000e9107035003403000041ca12940318640c1500d0b102d929008040e4045003501e0b007148904406009900c5081402d8201c4408072400b011baa01d2036070428604c0d44c010f12002c0e1074501c008001180c4000f45044071410390f601036605c0c901045002405006132940903480019150042c03034100a85880d00e1100d24840e00b0140001c3c00303002c0e00344e00c0160755481c2901210380402080340c0d210004010202d004200c2c2d09081c0c0003002c85442d110b004555450940595800740000070002c1c924060440d00100e260383d6040308408035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 262577571 1250 262576321 262576343
    0xb04120f0b0c030105031b030303010603110c0a0b190b030a0204050903070204060806061c0308010b091f171f0e150307061101140705161b030803040c060c020616 71
    0x40c14498003920902c00c80300d00c2900c951515040c0b600d0200441c01101c00381d00d81c03102ca60036540f40003003903c1c1110214940420700040c411143c0110b88116242d91110340a8110120140301c0c24210b00c0e802011b00082800d144246c1040f268101c1d25203a44081c0e0540000c4c4000c00585404e82065030080c252505a901d001c0311540082d081b90200c3d48624903a03080401000228602038a41c3c40036140880324030b4034104400e54006009000501034884625000308503800c1c241ca0300c2e581002070064403501c0c1c8407100284140034210403103081903110b00c0e502900000b4007180175108078a007010fa00341c80d21101e45041801d52070025000030508020402000d090080c9640c04115100080403181c0b10a8020700d80005581c5c20b6400840c902c980c141c6441041c840d101c3d500404413811640c82110380610540035242c41c003102c846140d8000c4c00c00e40501004405c1c03040300c1c0c00070350081d031080401d0703162039070384080544107030443da60007962104d01801690f0b1001038200c00e01420300e10132026411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 262578821 1250 262577571 262577573
    0x405070b04081018150911041406030d020715050304171201091b0e011b06020301140f040c0f05031003050703140d09030c060507150629040b04120f 65
    0x4155003095210b481d642e40315004000030440c40784140c110001c1104800503c0d0103468035140c105d400e1501c4000051651281074200f44400e0311502280110300a1080c03148000400d20072a584c903068642034840d0041c84103840740180002944400c60700da000300c10f0f540540481d001c0e10369410080059403100c0b50b004000740d0084490009241d115101c040d944a5941030002c070a086441d0514000d40305200d000d000020b0750303040104c3d040282002d2a00c804200d41504400850740d0703441100900c00d80c000300003c20303102c50301447c0b0311061780183c0700c48120000210800c0103a0307056444180121780d203441801d640c0e901c541300071984141501e075030303402480d42c0b5038515280082030350054610b032020785004441c11005118001040d1098078100b0764540c11074543d90303072040e0144140404d2080002d80c00c400c00a14080007507058458900400c005940c03108003001b01d04144110130b41002c2403014001d0002a65420b172010340700700c80560b5003003e003090300d400740301e180c03689050741c0038040244d8407c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 262580071 1250 262578821 262578839
    0xb0114040207020619120209060d020a050712110f0a0809040e0f12040e0f06090c0c010608160f060906020d03091e1a01080f0c09041b090207200315040507 68
    0x102c401d40600b80540d1031281c000010044d0306c4100e4105000703401080079200541e070f000d040d5100c8101940005a8680c40110151606d20480b20014000507000a549d60743c0c503002800c01e486440c12100303844c0d08112402c8400e131114583d0320001d00030f8200b4060707a4040d050541c060744c401568141201c114518599040e0301d824468040d80582950024050000d9013000c1c0c0c0013900804000e60540d81070174054000b070480302c0000c20b898100c4c1404123840d04000c80941086e401004640c3c20b071900c003140c840e4010110107180c092000d038032507204030028502e40b00d0920a012035040ba0301a00750308440c0c0c181140036180414007078810a906059844400c8400b100d4030310005c0c0b09942c211040740036400008000c4405038001c0b4110b4106205003000441c01140d100d0701800101e88000e800d03541d40c5084440180f081c915040d404440e000007180c0721041c1d80c02860b9081c00b039038029403c09001130b01c6021280d5100300c9543c150300440032218980241c2c500709508248560195289152211020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 262581321 1250 262580071 262580077
    0x906010c0309140616121b02030a020904060f0213050f010903020306070e031612030f030507050a03110408010908030f150109030201030c02070e0c13090203100b030403030b0d0803041e0b01140402070206 89
    0x9985003007030300101c100502d4019841d0f00305162007c41003c4128215000203441f800c070740401074002d0941e60b0000d400c00020790f001c180081100407085403106100c030009500c9044c0b60056a0041c24080490920b03507000d20401012a80d004004020303ea845040440c2d0603c1400300d815010706c60300742441c0102e4880075040c0040c00c154030364044007501e1810300800091a81800e041072500e4031051008040e0b004040f0381d20001c2ca428080741c1031840700c1d8003032000d1007950700c41c1d903465207001031110030011400020340c020f1485140851260702c0e034140740c80c0003406040304203011070307403d030820401075000f5046041c0c02091801500c030440c0d611494610445402c81381c1310000c150000710b0824400361031000b903010740562082182076144c02095003449000740d0003048164600400003030304152007a0400103070420007812611005406140800c51500305443c00c43d807240c000079401842441714264401e449811907600a6a64070308850780e403001c1081c01400c0c2d0016003c218010240e1148801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 262582571 1250 262581321 262581323
    0x11150403031a010f0813050f0d02010506090a111207021005011520070306020714030a0302070c06170705090102120c03030411030601270b1c020906010c0309140616 72
    0x3244000c00c10560203400b0314034080c80c82c14081d0340103484020307990056842e40c2c8540308404088203000d850030701610384091704800d042148510845c1034940c69041d04101c1c002d0030141d40020844d104c203415001981c0b11110404a400030034000c510302c0c029285d42c801e4000456006640744c42c0020805141600d0b4241c00001982c4158006201300b103510285540f04412401e0511100d280c403580d9031074866105100c0503044940100e811424405501484110720301c40200700e0361385000858024000c0d400008040d280d0301e20540001843d14052921312003e021118040006980ca0302030640c0c03980c204c00c480504510890101310442c2c141c600080510014202c000c0d0b07200d250034a00210403000d128400b5000f03403c004010003441304000c614104101861070040c82c0384089405220081c00c00821641c0d2007070882481c40c0c10311401c0c980e0a59075500a0740e11621aa8424006454100c4103a80003800100e5010003003286111800307059103000c0c801000145041c0520060b0f8070783c8031070b040c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 262583821 1250 262582571 262582577
    0x30b07080402090c09010c0f03090b0a0315051512040501060b0a0e0a0603091e03030209041b08090304050f15040b0c030d0b0d0c061b05120703030f06030203060711150403 75
    0x5000540c5003455800d030f4404c01d40b80d0070302e10345050341c00024144000014014544c261824407001094040c148180190280360807036030301c80c1c0301c0002c010082d2142d11231140186801003008203140c10324024440f40c8030b00310102c2c6403502d0700342050304c2c070300c21801002510b00395a60b2801180d00b4802e4801006a520256901102142d0302420006035641c1c590000c024140ba04030403c0011300101e0004800000c02c6400c1d000c003422a0a0a401030f11900300c003150f0140c9010884140380d140366401e4030b0b0303804840e13403680031564420740426903a1240c1d000d01680100d900440311070503d080d0103644500c2d8100c1000700d003810703a40d83c0350711a2500484000200d070b400c0490a095091202c0c0329401c401901142d80e400502c9207a00c42510100041c000c6030200100300144032480c480038044504010b610400721807294103a6000004603401010084000905100b42c0c0c1e00301c1031007800b59500341c980040c090211502ca4041c1a25240a6691049020701032725040030164001c0d400300034400d41c0252 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 262585071 1250 262583821 262583837
    0x4020c030409060e0906010302100e09070804050607020d0206150604090203010b03011a070b06210706030c020d03091106031e0a020409050a050907140d050714040509071a0a09030b07 80
    0x103006041520419001001004e010030100042c420001544d1411660140c601499102c8049000c4540c01130099410750000c0a03007007401a05540401c84a00c035901410070354140740c9601c481242c442c0f4495944000581c00038001c20360301d07120ba03415000c20002c01044149825034600d810390070703a00240c1c42516a04c0002c001001344036a81c00d4030141c034000c1082420314221041d03640600750318000c0d0442b401206141c042d22504d04481c80403a844000d0f40040383c2c4019618100140a0100c01c00004014000d400700400400d00134010440100d90142c0204031180d252000d00583d40c000800c03582070002601000f180040854003500d010740507011000d43d4030740c100002041a00c0f009054442c0341481d000c01c02c003844a01040c0d0005842c038404e41c40030301002d280c00081903080200130185c01c0340108500002c2141e01d43e0050000c407401a1003d11180d980c44514646410003072080100e514941050540202030034801042010500e003010303101c05452742c4450480c01030407141c81010071520 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 262586321 1250 262585071 262585079
    0x1201050c0c0d05040b040612060909120f020c0303030f070504120302100c08060105090d03020304080316120e1e03120f270a060521040b100905071b060b04020c0304 72
    0xa11201000b240305081c81807405140102c980b980c1d1156110f0b100400c82e1a03000003203c1205504000010412003d05024141007801c0014000c010040b00c030002c98001c0055254240c000f02c1e1b0152070400042c003840c2140e8502201001035907004048404000c0304000c0030411070180600c0d618424040c0d402007104917513040e00d80046400b43e181000034400c6800400c0b403603a030b102d811100400000c5d221031071010113034a003c1c0d01c6d500071074110215600020134141d80040c2000e5901c080303140038100c955614200b1f11403c4d2110340045421702d401c503008507a1044071003429041c40008500190446402c141d076015080156003102c0606c007070401001800c8a101c0100025203050407240d075130069112031804000840c810702d01e104500a008000c1b4410384250503c95560b40821566500c9003c10b26140c6001490400121100d55049120400c0462049018801d4a116040e40d45900c0018154a58003000540c8191402c40700703951504041d42d81350701d030360010b000d102060b080115103075418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 262587571 1250 262586321 262586323
    0xc0602280801080c0906060705010908030a140c0f03061c05030327010c02030901110a3507020607030c111207060f02010b030c0f0114030c040303030f02130e061201050c0c 75
    0x1030303005107451307400842112000c0d516414210b40090003203501c0c965440040c60050302400c2c0c100c0e006452844040200400c510b003e40000f02207000502d1210110703694507050b00594040c1c44c40c184442001400060742601742510b9085000402c0c1501e8000c410031907135402c0c50361340704580c840c0308180b03d540324140700b00403503010031614600b0000a004000c90000025920302401444c5810403231400e43c4e1001055051090721110780d0003624100340390180001c03880462240031140c00405103202c540c8034800041c00281c5401540c002c1c1140e14200c4982ca048522010300310040e00c070902c3c28000c203000d50f42d855100c042650045000342004030f18000c07000e024034101c2c0480c14196410900c0700c1c0030554010695801001d0104c0c0c14201c402c5500d00101d40c45180000304503030303200d8000180040e00e1a108041c10032240f00741c3e020b00848003110341e4801a401a10070481c09079400c543c040c82901d030001e5138203900040241c02a800c400700004c0b81401d40e282599884444040000c4894100c44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 262588821 1250 262587571 262587587
    0xf031306061215020a0509040608030903070b0f030a0c0905090403020c03010b0312040902160f062702090f0603100f060e060102070f18060909080d0506090c0a0c060228 74
    0x201c0c0c2e041032407180340301e44882d1101c071054401c081e41c4039400600940300a0107003069401e42c41d80980300304809515542600d50300d80c81070306200d100c0d10a81c140024500041d03001c440d13100c1d00700c00410703041d501c4200c0090090040d40c81910b003030000d0702e032011807142c8079408914401c46c0294018182d02c5443c006040c2140e4840210714000e4200000701030485801c001102e00701c840c1c01d1801a6520315160080921513040351004140d95164141c000c2441983d4010000d0400503c1c1e50710000d081201056846002c0442c00030740208240c000141814240120300d0b611801c00ba00b641ca002107004001e000301d4450416020850780c2d50b10b020700c2080c0030341c1c03446030f803100c000c0c0024540141005072400c1806503030300c07404c4110002c83d03110b04454010350b08068000d060a0f0340c2480406007a141038001500001c250a00103450a80000c0d054034104503d14000c080003018546054942542141c0035456800d00352400d58080100400740448d4094002000c0c5a44141c0b441032101c1c0900100112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 262589928 1107 262588821 262588829
    0x110f090702100b060403152408070f051020120d06061e1e03060b04030f05100501060e0d020325050307080f19080f03130606 55
    0x25500040c101c1180000d40c2c030240300c003040c12000d002c95400342d8400038040596854881c200128540d204030341052402007085c2c080000d4600c0c01114240380d9204108650001104104400030045040d01510341100c5e0040c20300c1408034000d001500720750009a82c40c103d400307803800301d00c1c0c04c100c0c04503804c8400521710b44a240001d4910f0081119100324004502c420301c00101c02070111b84616841140394640303040c3c000c419650740074480083c100c1001410799175080425440c11402c050070066210302004921441c25181c00d9007482c05c0d80341005882d60a0100500c895a001030407500125001e60320ba900510541c00044c0c5803049044000c0100c1c508800494403921249403960169001075088412041c0d0762661a82d07105108540c0100750b0704011901c520803565151030044160003080c055083c981d5808072440142c3c002d4400c036810305d42d1405500d0030420a8000c2c40010 = true := by decide +kernel

theorem cover : BRFrame.Cov 262410071 262589928 := by
  have h0 := BRFrame.cov_init 262410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 262410071 ≤ n) (h2 : n < 262589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
