-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4654
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:29.4613+00:00
-- url     : https://prove2.me/submissions/b52827a3-bffb-48ec-b1e5-d7278da12e56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 836870503 ≤ n < 837050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 836871753 1250 836870503 836870533
    0xe0a0c030b0a0902030304061d221d0607170a0624170406060609080303040b07050c0313060201060e010603020c0c09130f2d05060c0711220e0d02 64
    0xb50403044060340020051400c0e80030a0641e0030580c00031002c5648100c90b444208140d070010b5181d20401c507181070a2440e01901e642d98000054820b043d900d07560070314000082c40301c2c2020340c810407040c0129903091a1000005202140c61304c4100714012801000c24541c403a60300030a005da60034034500c0b0501170b4140c11125000c412204841c8104525034031410030f2480a0340b05030740954080e00c0007040e281e0601d04080c03c05c14855100303610360f40c02042000040303441d4078541500441d03103180640d601c81601c0c9685240d0302071840b403e0051a81000006001901548005c0031940182000752484c0c0e83c0b2a0305804900900e041c05030581c0221400c848186031580b84654084d000020100c43c2c070019841c1c001d40c0e4202c0250458401c62810b40c0410021900700d00304500d0705020041d2140e80055648840d240c107005003290040700030102d0f459003040a80c2200d02c20342000500402d001038030a202d62803110001c0022480541c0c035140018080b05004120f000e000e11064008068800ca00761803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 836873003 1250 836871753 836871773
    0xa0503150105040e07080402030d1106040b1b0f03090615010e09071211091201110a0806010905040908030f0a060b04030209130204020a020709150e0411030109080a0309060e0a0c03 79
    0x441c10008100808543d40c1c0c82c0d0040300340258440e60b50240245800d00c1807600d005181000401031080201021403500c00c00600681e100b5030040d00760700151220040d03c1407450f40301000218000c00424011509402500914441d1444008a60b0355803a981c0301100c903640b00d208403a000030030040c5040410300f480c081c042d400503854039041709403000780c02509040390707c40341310048403250021b07000c226440c0c400300e10b802c2840140020088550031840b0040030b88500c0c0c0c07140040c085074a00103a400da0103644854024407000e8400d1180200c507143c400c907160f0084803451403c00480e80894481d0b5400d1213040305031800c0007030051400741180c0030440550740c0100700c180c01c2d000740302401006031202e0000e80b8188100781c00600c64641814440d609131407446003542c003646042c40042048c100035404554106402c501c0c0c440c0009488030109003d0406868050700e11312000a000d51340a038590301801445000e628104415840d0041340360320303800c0908000e001031111100a102041000030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 836874253 1250 836873003 836873041
    0x50612101a030c1b1c030f051e04140318090f0903041a070501020a03050709120510090204141609060809060f06030a050105010b1c29040204090608071a0a0503 70
    0x2050070700d8015044c03186140a401001801c0c58101804400c1c83c0b264244c001d81152000d091428400b40c6003000001c41c4a40c110720140e0b8180c05001c0124092144448405400603c00d03400c0d02c2da603501c04207020060070180352109024030300302c4002900488140001a002710311540c050343c07809141544454610021000100c45801c0030404c000c00100248000d040002c00c035140400c5a1500d81c0340036110a140d0752204d024400c04810f1000052000316130390082031310884000070640701500128000b4030403000c94100d03496105051001c80562000345020701c140315513421a20701d86502c400c803121441074510300c025500038808101401d0a044400c0e91104000d0b0860721300102c01c1d2601401d50b00203a0180c1036074940010303023103c400e145c2d02c202e801c42c3c1900c00703052024110340443e9516030510001107c01451101c00036284035034071501144d008040642044c00001e072640c800e5a01d50016200304944010902040238a5004500545144d840e00e500d03100e0565589203899003200480c20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 836875503 1250 836874253 836874277
    0x1a13060815090c01020601141009030602030a06050a05040c020309090c19050c0705040606021b06040f031a101a160b010608150306010f03060b030304050612101a030c 73
    0x600104051034100000d905000c0c000001e04100d080802c076080c01d250100d04070344d0444d0402d070018024150101d40403840340350250361404080103100011031750303000a500020005d5000106205404205410039030a41700d04130380000301150749404010448910303404034030150304103111114541ca8880c8509030301c003040c031403503d10f07100e611101c007040d0851852503240814004504d510140b101000100c002c0c280a440030080350b401e040d8003941d01e825403c0d42c015185120000111151101c0095400400842903203440080c4c8070314003126501c0900104402c0c0034080c0c4001074100604401d148220f80e2203000c40c140e5850128040c04055200a200b0380f103141d0054828070018580100b0103000342982d83d42da00326800c144075a0904502107241d45c1c0c7c13081e48110010301224010080c018101c5c1c2d4065400904694880c010a0071405650700c420340c07041e0f01090381c6a10804417482c0c01d200301c0b0700080b00741c110b40c3c40340649140c8150a2641c0c0da0a00801d20001d0f14004221000b800712035002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 836876753 1250 836875503 836875511
    0x6020327131503020d140c0102030a080f07231e070b060111191a09120406110703080a0201090212061303120f050903130608061003020a1403070315091a13 68
    0x190b008980300003045c82e070484003841841c51001e00264180020305490b00b00340b000d0b504e0b1481514004020b9907000d00001c00c10f8044001249140b4040c40d000451000402e4800c036032512103030b01d00d103004d80003519800c6103100400740d02c82100b00310b24200d5906642c00608d50300c0700d44a420046880c03000e1040f440e038040c82540402060890241c0c850030180b440303031200b80801500d270092252400c0b0084c01c00200d5a102c1c280660750030700021f090f1000d980480c17801d90014502015080d28020301a400506080b0000803070b1382c101503042d0004000d180c000d44000c0d000240c1c82100680d201c030119440f000b044540149070001078814001011180106c05001c100007034440804000c8a405403030740c0d00e03684e000041c80c00381140c000980b000240b0300c604210003d0300d07200001c01c0d051701801c08207100301035000601e002c3d5a8001c561101d80d0040b0003462548a180c140c1c03025004140540200340d418928080003c0c25100700e00070307001d2030058020b26495071a0307604240205c000d4012042181036881d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 836878003 1250 836876753 836876759
    0x100504120f0c0615090606080f040b091f02190918110408060a09140309010804080a0528020c060403020f010c0507051203070b0f160f050d06060203271315 68
    0xc0d000c0c5460404c4c131140e031385940e5842d10345c200d000c40d0039a910410902800348204095448244003259000e90044103041440d501d0030021804c0007048108200310b41c00c40f86452009220641c041c0561715200903810005500161040e00ca5041c00c2c8074a1b034010403d400d10820040540d00510034400b142d800040c140b645982003942025000c4520b03081c02c5a48120160a205031031411040c41c0706003402070341c50500c0280c002030074030200030805044000c0000c0e4220030389100304201d400c40c40c00c016003069580305848480c6584141101507030010b201e00c000008107880c0040c212070032282c0c018006166010001c00540b01c3c4560700b4401e94503409030490000756600c4a007150b414040560001d141d40e40c1081c5400800c040010f845d00c10341e610542c003002001c1c103601c0802d03140c0c40c802c0d00f0025030300d0122140885051043d841c00c40909030030048002103c130703000806401078107647d203040030701e00801c00b010088500ba10b4404540c0541c400e80c03114001c54266000c01c3c61560310a60702501c2a032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 836879253 1250 836878003 836878013
    0x2030a110a180e100e0309090414010203040b0f090d170a060312021e01020304022202040906241d010f030e011503021e0d03030f1b0302030702100504120f0c 69
    0x791100641a02c030741c030b4402c0340c074085030240043c510203005850200320700c540c880900760b035a00802010500034003104000c130b028019407519440000e90b07200c009660380e2800d4540030000013000e079005240707000f4140104105c44008603480c2d400001c50354420400a81c8408041c41420018040003c1c0d51342d101000320208184007a6080380d800707607800900789a43c2101d08110b00100c10124030301603900c144180001640d40d03000001e04c2c0d802120081d03005150032181c00d4000e10071030744080502460301c6000200303c210400100c4100e03150071080e88080f1150802500d100c1e00b130180c1c0c40d17194001090824079942c006e6000d08891540c92500040011604045c0c1e421207071807800201000007200001c000f14505840000b9660005001000541c41c12340046500764601070380c0242415120000c2141180050b4414a8540002001c0340250740304c00101a0003035209076900f40041c000c01c441c01c2c00d060302a000f924081c5c0d611501c800c1c50800017120484c3c505024008513010000c880d900580400c0e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 836880503 1250 836879253 836879279
    0x109120b0a0914070e1906050f0d020a0f080d080a020a080c0f2a1905030403060b0f06162307051311030106090510030b0d150e03211302030a110a 64
    0x1244141c60f2804d082000c1d44031101c0d10f0106c4000556400d03da0140710740e4840407071020004d00280d0f28500d43d1101440001c024480035044440000c0c4000c4000a40200c001a82404e201d50754031f03049469152088110164814824000003054250740420480340c500002000d240d182c000c140e9003040d1241001d41508c2d9a0820b601032503d00c1102c2003049200e090108108020054012507842080c607520b450310b81c015403001800700382d510503030300310b071512150a1002c1814000b821079075102c0f00b00340300c10b40000d00d52801742e8000900c02d031402280a50140d1700c130f0307600c50031400038040c091818041006441081200311a0030b526034070307400740c8204002c2c051750207401b02d2380301d001a841c103100600c62558211101c810415041048642103902c031149505a00c1c0e40043c00b02038080c6100e580da0000d0082d41000400c640703c0010509802d07110002d090500685211380e00c513250310ba62003104150508014042e6041c0c2002008100042c0e0081007081001c4001d4080d500300e41d640e0304010724030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 836881753 1250 836880503 836880509
    0x50d021e0604270204060f1101090f0b190b030a0f050a02190e09070605030a150806341e090305191a070905011202160503090109120b0a091407 63
    0xd00400b9040c1003070900340750b80d01c145840f031200c1c11400c003450840002c008070250341001c2c0601030f003004803280d500420342002c48483d40110340d00300c03040010b181402d20820110380a6044010020b2116a401424002d00421400050042c4504c0ba416100d4508401400703008907024400c4010440058580100c0e0510109c44040c81c0303c11f4038503005404000000003000d148060f000702e103044c090703250003030162a04203c840400280300011030703500c48150203180e003003e0391510031481042081c1c3c002d8a00d0318407400b8041c1141006a800750f031044240907202525601148501420300c0350f2b03002125211000c0040f070b14000040d1581c0c0c2e00e82606150b030b41c081c040f0304070319400703a440705002035141c0c200740700c01c0301c202568058079203813400a05054540c090981004001410603505601ea9010350342c480c01707400c44040300444075113030003070780d962211885502084000c4400203c100d013421140c1551500f1201032400399444620000c01480360110840b0021320213031003225084410810302020f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 836883003 1250 836881753 836881769
    0xd0606020109170a14030a090606090b040f09020307050d0215121608040201021f020d1a0111150f071418091315180807150b01050301050d021e0604 65
    0x1c1c0c2c04083c14400e503004440d51a05280c108204150319226505c2082c8155004c44003160310344907200d045454010304485100a000942080000700c0c0b0790101d0342c0503801c140c108950800c00b0703042d6490014251001002e000c1d40c103170091003042200d070a003100c2e2081401d1004000514001c5000507038405904205810340303c0740e002404204045001c92143c511903652401c4c070440703500e016070000396900100000841500b060700743d110703200d150300e8065032010310794801d0910580300b1411f000010b1070f03421110a0f0008071480c1c1c03640d659000120302c3c45002d003042c0c50301c075400c0d56900d540e0000d50321019220204012130100035960b050200c6000d130094045070b1140c8e0080227030b084100400b000e00601004403150444803680b00040c00c01061017050140280302161030044030b141d5100c08000e5241c00342c0b0610f400907010b420495541510a110050b242040000220110044900d8082400340a4000164420701c0c4003620788030840600c0c07403803848a4140865010000f00346160080ea21201c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 836884253 1250 836883003 836883011
    0xf0b04030308061c0f050c100e0312030709090b030c101d0406061205041b0b03010303080a06030c05010503150a170f01110304140a230d021218060d06060201 69
    0x2041550061500d50040700403a04110f10f00001202d46074072011450740117107400403013a81c3c40100079041c0001c3c40c07040c10040110140000e00354000d400040750b40310461180c059403200b4038104c5002e20680c1c0c05610580d032201800c03801d180101d0000d018040c04240c0c1885010300c010071070351307600c40c0c82e402c004440d50340c10040b4228110044139043d80d0202c242e216509164082c4003c9612003101c11409800b040c001c502500c450a1001d8415101840c007014802c82c07280c042036890000b401541220f02c641c2d9a00c405e51350361440c00301101c941d8080180301250b1040c0400a0350310070300c0039540107086039071443c0501c00181c0018480c1c400d964001e9540c080c180003000c40c460014040c072040390558500921403100d015946035500d2000820051035506000089400d220b0f0400001c045150f004048409155400d5105c03000071b104090300000e68841c18010010b0284041080c0c4040c1180851450030040c100d581c046038651100011508a00c0501451b030b4031881c1401544000c2c90302da00009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 836885503 1250 836884253 836884259
    0x41106030405030d05101509080d180b0d050403080115020c040903020316110a1d011a0403060f09020a14010804061109060d270b01090207030e03010f0e07090603080f0d060f0b04 78
    0xf05100e0702441c4041c0500c00055000c20103200040380cac1200e40c105921f05a0030300d0001f26008464a242a00444004500070885042e1520182d0145001e03900036102c15116a98440f400a0726039404240740c0010703000103010702200d00342a04400c24240c883d005403414080d282004c400880343c2c00009a036043c0f02011401c84e14103108807120060000c8092010080080203c0c03810109010b20400480780c1a00072881c42c869008000e40c1c01946d070104050110341010b41c444806002c1545003a40b00301207020001901e9004030003150024403040e1160740c110b42d0765480c2d1000824011108986c004c0e8200652605aa03c02005100040e02c1420002c2c002030070b5010300000004500d40e0011241c100703020100410304c4901070504655082c0d1000d80c1d949040e180480e01c20045000451301907013000d41c01c44003004290400d01c000300d48181241d0740140c0e140b10b514240c5566120160003024200215480080c558000b4402c100005802048240d0703544c0d016890025264000da1040740089814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 836886753 1250 836885503 836885519
    0x40608060709181505060906120c04030c051e0118051503011820090a0306020c0c101d15040f030c080f03071a040609140706030b09041106030405030d0510 68
    0x64441200720070300300904c81c0c140340344a00b003000c140540c5214540104812800780e98000c1100c1801ca4645640a024113040f9141c040326001707800b08550419080c0c074042858240300b450b129448500c5640d43c900018864015201310b820000e004580c901400008107513600c40c3c203c0d081148a249111a50f0b96150142c0100c040344071782811441d04d410700b0b00c5840310306101c14041540311440015255205a018005541c200c1c055000600080c00800c0301d680c0050085200701c00c000040d56100894008803c04035005000d00c00700080c20480c829100c084d03400c041c0c4000061854041606203043d4a59121424081c800d0b4401c0300c030403161208c1804040402d00c407019041140d00021030410b10329542c0c1d900e400018500c0c07010444a410300040511115401005100b50414803403081451108085611020b49001e10320109060241000c05405c205094502c11134100700c07469400f0002400700302065101030f00540c0d0602c81440607081922151051900545070600f120032040e1a014030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 836888003 1250 836886753 836886779
    0x5070b04120c09060f0314010f0c1d010e01091217070b0106140f04090b220605010314090c0d1505090d0e2d0303040906080109061b02070302010806040608060709 71
    0x4000c3c0344904001c42004440c071805d11810079280e0085c149030a14200302601e03230041140b50046282c0f54100740004d82d55540018204048940e09000c10300c01c0c03410381c5c2c019a4003505030070100d40002c3d2800c1c0c0070080f816524441e940100e2040c612130200c0c40c0e401c015000c40c0c0d044440180d45602001004001090f040000c11110019104949003010103121100700c1d540940e00c6141e050036260350ba600351995480401c151403200c0000702c03c400d80d000740c02c1c0304011700490207814086881c00000e00b88008018030700c64400c0001c1001015440703110400d00284120421088400c00389052410286455a0181c14460400340000f40340159040200071b11815829111380d02034002c180c40c0750040603074010540c1c0c00c5040d44001c052032040305400710b0307d10312860340194445441d010b80400c02000c1074100d003071868000d11090080c1e0f2462a41c1140e0340850054090141c0e0040804000550141d8001c65002c0c86c000c000180307195541c0401414103004407803640010302c0802040c443c480500807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 836889253 1250 836888003 836888009
    0xa0909240308090406052b0c05121e01270309030b0a020a03050109020313030c1118011e0b0406030902060403120c05010c1b0f021f020a0512031b030405070b04120c 72
    0x6002d141c1c1381d0082c07554a502c140c13007a400c2d010781a03081d030f00809102302c8142e0030b00100760181510807000c00394142e03103849240d0343c00d0790f0424119660300d00349001c01c14083c1d020f03090404000354180f4040042e6524890b510150200c090014041c0300001140c06030015074850004590f0140e0f9130740d52148024119001600114900b62041c401d010120340c08030004061030b031345800c0c581d194610f68101246c800500c1e0100b9035200c908419004451514000f10034100c4080d030130300800038180c540c00201800410701030280202024081005111310a80019a00f036002030202443c0030b44071b40312200ca04919442d5100400d0f408080441048424840c510041c5c07040d15040e10340d640c20320340c0c0c0030311202d003c20f002d003801c0d071061544c0c019540d8440c83d0040c1810003030040021048003190103501c40407400d100b40c582d80142c00b80f081c0202910340450344100d0a261181d52200070280c400d0006420150007030710329200d440b82c08228514518020800b070010808155910340b0305140007403c0c034440703030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 836890503 1250 836889253 836889259
    0x14010207030f060b0301110c01021b150403080a0b04090f0b07110c060f0f041e06050301030b0c0307021f0203180c0d12170127020a090924030809040605 67
    0x14000c1020034070300c4051002e22540440f01250700b420070b00000b805403640c3c006081d0754600000b4144a8104154001c02c0760041c59112203650782c100c0510640c030341260680310340320040c480002400003442500c02d039910911031a4000340e0303041d01070041021a030404c80c0c201c81550003441210240700846014035031000c2d03d8900300c50b40345505800b680c1c0f58110f046000e030081c034011414100340542c1409031505c42541f13001ea2900c540d0f0314600d10507607400b051001c900e015001c88000c43c98038441e500b1241a03035005018655540c550122010b0740764002070241045000c2e2445444030b2804622100300003007491500035849050a140800c480e1680142c04640b070b52000d030780500c054603414015030380030360031518907141c02141030b034280c070040440d0404141c08516480007140c0807260041901c14900d071000980c0d80038090341150350480c82207034000700100300c2c074000420206049412070320312a0f07050003418030342c3c03054108000c0e108035142e08201c66910010a2601c9030341011b1050f880102001c0f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 836891753 1250 836890503 836890513
    0xf070305280c020109020d0f0605010b0304050327030102120106020601061d0402030705090d03020d12141512030a0206060f010203031902030903130e19051b07061103090304140102 79
    0x286258030300701c0a1000401805454010000005000b940844800ea0300500000c16000c0203207420f0450040000c03085030803910306000810104441c10989110390fa20800940c502045100d40c041b18071006404142c080040a0075454151000e001516002400b80a01c0b5003a5061074406400e04005030002c500300241c84650103011141c0451440c2c0200003070714010780d0794032401c03000c070780c14400d490139284c10480049089040603070004080300c003c0c850760b0381c1341280c409220030302c0c2c20b48208070a41c01d00038400c0c01c0400c1e106018070b608141d5151004001d0b8070a64500c02c496401c540003000480096081001000344a0401c1c800c0380c108040244040c514605e01803e65540000703200041c190115808400913030810000c100721106109001400c4009991b84d00000d030001c1001c544203c2c03c0303c8484205080000c0e076000d40c034007031100401c0c07603001c4c103a0340484038140b600011000d45100d921542d60101c860100d00007140a07030000780185035602c2c01c06440c1028440800d60250456010b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 836893003 1250 836891753 836891791
    0x60b030c0310020d0603060207140115050d02131d0a0c05102c042d09120f1b0302070501020615030d05070f0219050a0e01080a0308070c0b0f070305 65
    0x100b82e4003901d51840c9001a12803140500001c0185400e40005090620014a2005000f07941450b1104001c942009011105821081d80e81c9503c162042a40000034041d500d0014642030f0b624002040503d0302c000794070303410410114907480c102045085150000d03e01e07a010701c400341101d04060113040c3d03002c90b042e4944800040808040c9a400b0810b0707030060f03c0040c100c0100c00060303600068002c00a00c03403510309401d280310b40800f01014000b5500d454507030440a58241c0540306c03100390060302d03000c143c002001c1c0c1683c10301a81c200d4001081803050050748403450060691203210f000f0740c01454164101000a03180403000b51428601c00305000c2a2141ca540010f8490f41034070040c500981c83e081c031032a020340b031159100310080d030101d03008610748001e01c0e0841d42c43d01101c008884002e08550780d80280c0c40713141c200b0701440c48260403c00d4000c01090181480e10b41203000c510f02501c40e2507140d141c5490105050340c001c94420111418000394a40c0740c01a1604054180c021440c0c0d02c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 836894253 1250 836893003 836893009
    0x605042001050903190c0b1314040c02060103170c011a0f030708070b1c020c01150504024311030607030507020a0b090f0703062f0717090d050307060b030c 68
    0x41d0380541703000040262058082181d003040d00001000c114044076214500d122446040799902e01030f4601c24411040708480f01c1c681405035114184254010780210b90968030b034440b03034021880400f07007480c408008081c401c0d4030074803520710a454040f6040d01c51112520030000300b01004221144281d00101090001e07c4001c10f14008a51030740d216540e070b45042900611903245202c0740380454910200d030400c80001d040d0454400c4910340c0c82c0708084561030300b00700400c90203a0030040780001c41010503858001d511542441c540c084110303030155040400074001554400700c00e42240d80c400050b0200080d4101089542d070403030a40d0400b40301d1440c10040080d1749001d040347c01f600c080c0032000444c0340036900380400c42c2e98108440c01c1e5180280c60741004405888600410030305c1903c0080301171a01c0500104100b8100c202c0080d8520b0000c10752a40707024001100080444281c00308486000f43e503904060003074661103076000d0b40d12942c290414804840f51800080c1c040c0d00701c100e0301d840b169 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 836895503 1250 836894253 836894263
    0x110c03030c03040f02130b03060115050f0304110603101805130b040201030f0c02031e18150c01050a1a04110a1206050a0e1f030302071a070605042001050903 69
    0x4605107801540b6681d450401d070120b04903440001c0c2d0000c00903607404d080540181c02c00c502119081e421110280d0340c464522000400402814000903018050300c2c510b860030400468009008080315910312000e05e00182c05544280c0701341c3c0c40400180010001500b6240000d042a444018104002c1ca0071500c40d8604001161005100b090400d00207011a0f02990011007545500c0e4070400200100e0a0065925404440d200c1114a01c2450550102c00c091040b55003a0840805500760f41c540503040c015110500304840312414028400c064010b007092007924818800400040750740191192030201d4408600400350040f4100104001041c40078030031601c10032914a00040e019002c00c408274024110340c1c011640c05072204c1030004800c8440384140e80100d20801ca21120704000c01c0092248030f411388130080160704580806c000c0381c07c2c0d6108414010340c0e50400300e454900346030340e82001c40b141144e0403030302c031445840f26118045c01414040e00c5c91100382010383ca03049030000043d0343c40e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 836896753 1250 836895503 836895511
    0xb01050d0b040e0609010218030304050f010f0c05010c180e060f2704110a0608100603020f0415020f010b030d05070210020a080a0201020d0b0612271f110c0303 70
    0x6880e80280741c0c494403070380c0c0003002542c211401d580c039600304415418040c1d4040140c80b05242287c00700159189000f204480803902c0051a100d0b0844c030a50040d00d44001e6800302c0003d03c01c416005801040c001e000e8840710391440e99a007100c10b01d0040e00007105c0c0009030401d00c1e8103880d141c1000280c0c0ca9101038090a0305c0115503032001801141d00200c178204000a02c05000c5440c5400d0104108550302e154001c0340003111402e403c2502c40004131403a003022603004400180415041010f07070f000c2c1d402007131405000035601c0d113003548504400c0c500e4220b207400c0000503841035100340c039840d50a00c1581c002d0903007100505a00c50a400c2d004100f070150120103445a030f02d0210811901740204501d80140d42e0010540d81c407181d042c031002c3c0c006c1d000500c10f0f1001904081c0a61007901e4a201180c00e4100c0b6101a0002501c40403c1400701c181440380c1056810800341e001e080a02040220200c00c1e004d8000e1104221810741500c005d5840c071088070595404107000703d1158110100c1a6540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 836898003 1250 836896753 836896777
    0x303131e2102120f0a02041b020703110301020712080901050903090a09180b0c120a051303030903020c0913050c06070503090d03020705090a020406170708070c1103010212190b0105 79
    0x2440c0002121560f01c004003401038032500d00441c0800d1800b1801a0140d8004c40d000c0024501c00d201d103c00c9104034403800c03030058102c80021310005400c8110005c1000c0050001424000c05945051011210300c0b00c64020410410070010009000d014582d44444460065410030204c000496100080c83c021140c00a03151190794641102c56a4030003529038000c0141c0352039081540101d0300d541d0244d104030b44100034040021307001000300c1c0a150f00540184024528400380c80e1012070090102d4181201180030b405000501b81e17842c00d45841c000c04282110f0840c182c200d24150b4542141d010702c082c020300703042c0704a5012410100945680072070a45007040d8a0071945012810810580c004a40c8002d0b40340520892400c6a4050003d13643c82d13860342603450014015207144207408542c040c002400490000312180d20403c88611170510640000d001c0a550100007800d903001030b4004201803d4900c1082074000c0b02ca0400d0000d40300e0f0305000c01403144078400081ca94495045481a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 836899253 1250 836898003 836898059
    0x230c01050705120a0c172106040e0706020606040b0301050603150c0f03070e04050604021821030f0703031401031716140606030111090d0f02030c0303131e 68
    0x3444000c0c8030840500303000d02003a940c4c54020400182c402110f02c4800d03100384c1104102841c081c60064202c03680ca10507890300c034140b080c0c00c2c0700c0583c2802c001808a50040d4035803285061a87c000c20124010382059005400d06141c000d080c00200c40040c010544203a0416050103d40c2c1c50100703020100c0c20004040284036901d010000c55144030b401c42680f1018400000c200752280d0012032940800001c035000d00c40ba403581002c0209a00038180f030584240c04c014030158051501c6000c00ea41c80f4810000b107050302001640d50360654100d01d820500c1e42d200007070120308140d414803414054410021180d04554115201c010b00b0f000b6045040d80103184c00182e00284880c0c02e170503018201d6001d444e00705019039a1300095120306e0f0a950383d5000390f0074005c3d0040c14004074021349003a100040c14610070914152181900410101801d036018002c00403d5801900d041c0024141c007400132500412451500461802a940e55210306410304240344041c4168900d220a0210314680c00013108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 836900503 1250 836899253 836899267
    0x40b040b090a0518090106061403060415050a0905010302100804050d0c05010b060304050d030506010905010e0906040b0a0b041401021c0c30020105060f03150703021c02030103230c0105 81
    0x90b00d0359695005a90310403444541481c0320341d200501c0a10030f2034008000c4c45019a100c5054035180c4651001c40003550042c00018800d052550003881d8280386e101c1c260395100e40d94404035280524a0300103442d060348507001070040d402d01081c404024135247c9403041e0140b4051300d50680716603190007124104510903815034203026094212104c0c000004118030303501d05003803a00c955039900d41349446011a041c540055141d60190741c140080703580607107804031211094820082c1202d802000d5903806940d0303807405072240d03c82c4680000985003d1810a6499040110b000000040640c0090455010b000f4842e180b00e42040c032001601d0704d81c02c00945d58500e9181080d00c0b40305013a0100702d495456042c01f400308056003210b02c580722060f00200890b803901c2e400c0c05840700b000d9103080d405030b0001c441014804005035816a018030341c0e190060401d424681c160310080c20040301a41d8290700840180b051000172041700060a5007141c11407111049040c1d441c0d12001048009414402c01007003030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 836901753 1250 836900503 836900509
    0x803010e041506061d1210090c08010501030c1d040305120606090916181a0901140406260603060109022a071a0406080606070c0801020c10050a02040b040b09 69
    0xc400c2c10302d1003032040c00b00545030b1038010b0010b000071000b500a10200c03824605141403032104451180c4154001d4202c441c00380c0401c1020708440c000c01c9901044080b00080e20000a01c503c40c043c500c00c001005032103140400d010740c5281102d401516110a11080c07100080e04a0111030010b04074011425056460600183d45030282681e00d43e002000802044581c04121003810848151500d03005100300009022080800441c000d02d1009040e0242070312640c4110f001800d8019414034203034406100007507100380b640c1c026500480110b4180c40240e4414050040c004c5005400601c1d10070342c0d45440c41c0002c4e40c5180610490414542c0011402d0b6143e030016040e5081180211600720400342801c00079968031710b5482040882e07107181ca501c95030380b40c42c80100d904480083d0f55590150311040104001940001011a580c0200580c0021407400a0020f801d8890082019140d880000c600100070f8401c028000d00001744100304c18050400580c2c1500c1c180e84107070800c141c0700d004c06808 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 836903003 1250 836901753 836901773
    0x81608121c020903150906240405091213140111150601020106050a0e16050a020312060319060c09050a082d010509030d0c0507120c0203010f0c09031b030803010e04 72
    0x101e030b416005d0003621444194581405c07a014030b030401c3c1150074540d140d017031418020079480784414401c46880f00c0f84505113040d400013501b280d00d200c29a4011102140916601d0380b00503030f02803502d4248001000402158000c4a82059081c01d09103110502000a01c0d180d25520b82c3c40c1d00640c4043d8041100c5134801d5000e1800b62002400c850445900e9041000c00b99804072050440590350417101c103201c80c807407400d907140c0b049250029801d100388510140c200c00002005548c0610070150f10b0181e2007808520260b00e60b02403400081c0f5000802001003411045400680c00faa4414000308001c1c0d6000401d01c41581a814001b09205511010f140d455070b00c0c4a015032196003000e0138841702c0032010005100455040100704481103200b00700350307603034014220040c02207102e40f0700c0b00c0e0000380140508801d86100900008252519001400032a01340980d0703440058441e0006004001c00300180d0140d40e541e54461103030503403542c0d41e60030440c8414040c0107403e01080c00400e04210040030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 836904253 1250 836903003 836903017
    0x90703020c0708030c0304180b0a0e04210509010816051c0e0109050601150e0f010f020f06090f0d02150a0b1201140a1b0e040c02030702040501081608121c02 69
    0x384d944c1c41c54017898a0303580303800c507020350416400f036000a00c2a41c131071841f41c03a40c1ca1001412010780645881c0004516046c02441522030641c2403215080d061a50360110300960a6070721400d41b151040c0300010300006005125114072910000769002d15504103064815680007808070202030500d81c0540b2000d45001c2030719403019820031008074100000840d055050360030704055441c411211000840745003040d46101c98102443d0910744076203520980b4101c410080c2d074012540144a030185c0d481c0390078012070702000590000044600c02ca10140512042c660f81840107240c519104140b12840250140580c452a952007056203002d0702d41000740004030f41c203180204001c165101c0b000605039011500900c038030341b0702840d20001200d112041000640d4542c0d4540043e010342d02440028282c084030b84d025803006101d0000140d42d60300504d400b0b00700b8040548410150000f10032115181c0ba001000f09422124002200d03800786010b40c1d40a0104100d031000e40401c40a03007200910900d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 836905503 1250 836904253 836904269
    0x60212090d0e093c0907150e0f0d0b060f03011e09111002010204092a180b0406031b0903053c0a0311070f05011206080613050607030b090703020c07 65
    0x141a40d070071040803c80701d80b0039580026000795143c1d510030040e906c1d0f8110380240e06560801c90b500550360b81c070442c1c12038000f42d00501241808030440000503504050b618040b12181d1030102008414100752230031800400c130a030000e121681c181d642004c02442c0c0045103001680d507a4404809000e003ca0344031488601c00f5000c00a6680d0240009000c0e60050084078851410252030309041e450502a000708800300c071114081900b04040116400c0460b02081000d17510500e402040f0801c10340000d00041c500da4400140c0e10203d5080011102000e0354800207101c0d1280c03007000402c401091103c02100b113010700c04e440c082005000b0440385212240d0198841600000e4103024000140c1c42c100705009803100301446940c0d03c5050781d5416140166010100e01100c00c06c802d5000e80301c1f27070340041018400894829100d42c03115240c25002c07a011204520300d0900c003070a200c024000e4a410180700e14052002c0b044d020f010424220001e0154400c069000807110074505080c4080ca010701942 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 836906753 1250 836905503 836905561
    0xf060d020a021e0303010b1b0a080d0c0810080d120e06012303010e190c05030607022a031e0f010c08071d030a060902060f0403060212090d0e09 63
    0x24500035580c0b1003003e104000e80b4901001064002000400c0e28101d41c68a04094a00008042184181c414940000d0507900ca132030320030340c0040c2e4140c0203820001025900003454121104000f82000e00c050702b007030316806100d04280806c1c8404211501d29130f2243c140300851311032101c601001411501840300c01c9010742030010074030414440800c41d580c102450f107024800128801c050032107200b80f0082405034842540c401c0c44020200f0740d1214640078140d061017265858020900703082c0c0454001e070050b04141d014011400c1907400300414801c40c809104040b60248020a0341c8030415107600010741101d002c0070314054410070507400e100c000f0380001c1c40f143c0300b0441c01030000341c000c0c1c411102050f03658640e000042400f1812802c0154000c00500c00d2400544440b40141511041682c20807001c020b40544020400024402184078440042e0360740000c4456860203100540402459004410000ca140e644095445198841106da80e801a110300c0c08541414500022a0f001c40f520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 836908003 1250 836906753 836906767
    0x2c0a02091003242a1116150306060f0806011803120804030206150a03020d0f080a0c11102c1512090601032a05060c030702150f090f060d02 61
    0x100d00c420320703205022440c05101c0440c51400700c99121113a50038082d6500e21840c4100f091a2281d0802110b2012080546160b0501036403402064210340c0c00c400c6107041c01c5071414404d030b1343c14854040140003510341203201004a40c40101038504c041d0049040204000b44c0c50000200d100b01840250350010490f01100f12112000e00307108022502940940151400510b207036540e0341c140d00a11000034001844681140d003004503001d4044030544002e400d140c0704600181e003c10041001c0c0b190750721442130b42407040c41c09a0160406040c110f0050b01004c0a03210915040070060f8141400840c0d0780c514451001500b9001740540d0203003c1c2c0c0541403510b03400000a10000805076882e40120b4810980d642042059030b8840a01c0005c00948004002c00c035440302c0400c5102d564060703119941d825565500010f0b61a0300050800d07440d50b00000340b4181145018409420241500106070381890440c00c0c4020315800b4a0840301d00842050700d865006503600b008403071900718003100454490704 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 836909253 1250 836908003 836908043
    0x3050a03140f0a08060306010e012916050703170a0e0d0201111b01090801020307140703020f120309100b03100e07051804140316060b19092c0a02091003 67
    0x4000d0700c5d507601901820002240a0580000c060b06960000c42c9001d15201001d0203e0240500300c07942070201d50040c0820108c0d500358080480300b89014100030041d0078190f0511030350000851041c000c283e8030406c0100d680a40007107103200162802c80d201e804007401400161521060400c40521030700610a11903062006030460a030481d4082e40c890059540311850340c1e00300d10041c0d0b6a078010640b08060721901d6090fa00040c1a014401d00c180c5e442070303d4400300c240c5000310a1089601d0031070301004005030801c04200040c00703c541d1070740600004030311202082d199045400c900d1011038841241d0aa0700e131042061000511340648100600d45204003010386400d81524100d03890300d0344007020a00007500001341d4040d002011009007610159688400003403485402d1a0341001640742c0c4605050340c182c48000041039a002c0105a81c403000c2a90400e40744000311098200c0d03100d80c0c85a82c041c00014104000e1a070503205482c42e40c480c0c4031560b03200d0302c480d0300080440708030341d60b5035220130 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 836910503 1250 836909253 836909267
    0x30e09040818030a081905041809030e0405101401090305120901030c08010e15040905061e060109121403090303070606090605060304031e09120b011401020703050a03140f0a 76
    0x9090400c40e102880d0b5080540310340301c000c0301038240c3c07406020000001c2e14403120060b20b5125420303c2890190303100340200c3e07a082c2005941064554031000d070380038150411000c11041004036404c0100c2e02e049408041514141c1c0122041d82403500307000031687c0d0003000701401940c2c024084800c0c050750341c00c43d440310303912803440d06000a06020007108c5060151111a040c1c1c1c0b0342c000180303800e0780c1d1030003500d80486014520343d92240d12006510003240050052031b0044801c00d9150f0700c0d08040c000d606007120310240c045410403e84030020022202148249503005600800001c0703801800c0c20a94503500a000309564036020006298003040000d9000380100e5201030003d00140b65500204100b42c0030413500680072071404854014212000072000149000c0c0341040c40c1c1d2240c1b0380040f02c0800100040c1199401900f02c0184840503415120051081d404d100510010741550707103042c1c03030b0504060000c05010400000301c034000c400100303454082e505600f00b00d03214401604002d00e61 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 836911753 1250 836910503 836910517
    0x70e030303151318020a060c080418020f030411090c03060d021507060c091d0c07080918191401030f020607060618051e070f050f04030204090b060111010e0613030e090408 75
    0x50405006c00181e0107000b100c0800561f038014800300e091600d400380d04815040701e400014030303c590800440c0301844070f403400b85004500410a08031040c0602c000d021800e0405070000b42421014801c0010550b50700d82c58a00b8298181e603140c042c4038041e040c02042d802004802040142401c1461040a40c400105030458801d00894400c404100000c444280c805441c59903039088108130400101d065000105004000070301210980822000d01030407a90050343c1d203403c3c500d1206110320340c1d0113250040721207140340000001c0345545140c4d6014545080000c0090041c0e0011400e5420710a0a600001c000c05c4121402c1e00b00c47c2402e100e0000800e0100d80300b1104102168894400c0d00c0190350300303485021103480b00c09006066070829207107500301142d80c254a5104000100050702d9600aa2920f64130030100c0e44e6003400c1c0140090010070f41980c425085030325041004e1584034000510b10b0708070900300744420711629603090031a61480344201c03440c2c001c00b0078410b00c810860356400a000d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 836913003 1250 836911753 836911759
    0x50c0307140a09050904410304120201080c070c090b1c0c27090821190507050403061406120c03152a040e070e03030315131802 56
    0x801001404070640600c001220020303000c6501403000d820644403054020740500076465200840056860f0714100c0803020305a0108510040ea000e01c808100e8074004400c600c0c069402c0c45c2c03c02022944d0800120406410021403a0104c2c440d202c3c413074200c1e10510380000c40041e00036210540c80001d86400082c1501a010421180030001c0108402c0c061860740604401c070200e00d811096038185c0c08402e0030b109403174248408041703540035a11503c14050b200d54440c41e140ca810100344081341280c540c0104601b48420200040458a04c0b9071001080e80403000003034944030450202d80d1800340780c00081699143c04984815400411101440755804588035440c95003140855620b1b64601155260194040710b00040d192070f603002d036140c0c480b002308004900c402001903109091113401d400c1c40e0f000c1c8000102400007608005501c1e0344403682d824100420802180425540d2000520043c07030526255411086550350102c500740135142c1980034044079003007511140a4040080301248 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 836914253 1250 836913003 836913017
    0x30305090f060a0215090106081f05010e010515070302010906020a050712020706020316020301091b060306091811010309080f040602010e010c0f0810081005010806090a080a051c050c0307 82
    0x20707142c0b52049410020055014000c020300301d01c0a92210761015000395115501c0d9100424601020800090000c201c011003000c2e6000d4000c010040b02c5040c0c20140d071608220005110a4550506043c0303d45c50f0342c1100f030750f5005242400ca00600340d501c2d0091405000103a910b40443d030100150510f6130140111040c070644c03590003030341e03140740c2d5200c0c0c40c0c00b58100340a484031901101568070007840c00580046002902655203814005804010801c030303480c141414084551f05203d0341c005001e481004100b2103c103440d4412284081c1603000f084100340c030001d2881c44e486504524081503100c03010a4039254082000300194025014400040d031038003500c2980903205010b108031640b1306403200680202e01c188111a60b01005015460514a8420006880c00c08000c9040c0040c5841400070315941808042803c07e40050006103041e0310140741000400d0300b01085803910146410003036542c0002c10a808107200740c54400010300c52815040008108024006601c45c0c440b581d5420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 836915503 1250 836914253 836914279
    0x804142104140d0b060f0a09050a15150507020d08120c0c1005100b030919060b280605131d07080708010311040c0e03011805120c0c100c020a03030509 66
    0x30f00002164001c2c022070006404030300b550a282d90b010910b1140603150410b1180c840310450190b950070f0710a1008140d80303c2040e08042004003849002d032840351a2107100310030380c1c42c1c001c006010b6114041c1c4582c0451540d0801c0007102400c40c0c61810415840c021103240081c1c809159811807500081c0c640941088800949824801c581c03107001c91403003521001d0306040380c80c0c469030001460321055101d0f14080c1c401012042d40d01e02c04061003910080742c1c01074160301b4000d6604010b0b2515401180018480091550840100003510ba0915140d510340030903101f600700f4902140e010301201d0b1003044003004907103d0100031520440c5141c072205900e80310082c1c02c6410303200c02d22000d806070b1807018000c980c82c03401e0381100c1d842c6603c92412036018160b4900003800c45200c507442a01081c032030401401001028032280d0300341c40002c0035050500c400440107a0300c1d050340e4500ca40c031071405925140d00303a5005043d2400703000c0d00505081c0c840d0b0349915001c1d00303a60180070501c1c40703a9400d61402c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 836916753 1250 836915503 836915509
    0x40c08010501300602090315250e1002070f080a050c06070c092c030a2712080c030714060a0218011b150b01030e060601080414210414 59
    0x501001000c94091024480f1169000041120700c401100c9090302000780501c0c503074041001400c4400140d526030722908000c4450351040038001410180201d040c54100ca507503030000500801010309031800600002122070807410000207801200b0040a405404a8041c0001842e41b04192081d002c45032100350080c10011a4050701070018520310907110140301440290304803807821380e400704107800d80480559014186094144003250261320200d46942c2c07081c0c0c88400c0c80c1d1b540c070441142440101f5840c407602002e0400340106000506429000000c20450780101c9024072030083c20b0701d45070906458078014204a18072014175510404010034048603c030701c01c03903010403501801410511052401903804101000c0009003440b0b80c4e10319200450024401181c0d045d000207000201c000f034000024084401d00d00315194964000003c2000c00d981001c0000c2e00150400081014151000d0a1a1030880341c242c42c00c0300c94180300803440c3c01000d05400341c0251030f031040008110942840074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 836918003 1250 836916753 836916779
    0x21909050f030c21030721090b0906130801110a09060504060801031203020702181605030c0a030b0d05010e07050108181b0402091504050901051c080d090506040c08010501 75
    0x1695040d0002c69003d078051500b000c454a054800c011309050910190030020305503040080251405007141c00b10303d0380c1d41c010307003050100e400407402c0421056082903640e040c00e00407500d400303006100000d80b005044581c40c0e003200041102c6c00080c00441009042c05134940c20240c000000310390313603010209003c0c1c003170300554041c0d907201c2d07940542a0b861610307102520805c4400060500d90300b000300c0000b41c1c4605240441510300080c2c2e20700b0394240000e00f003800c51103144025080000a100b48100010f10408541d0081401e24012503031041c9440042c01c50342011030020255843d049100c04680d50100305030007210426212a8856030350502010403040140041030b00940101c04000303400d8185140000c906c2e00040c2c8014100000000403501c0c030785141045420360440030900b00041d02c0d00c0907800b409410140c602e000c400321035803c0c50194420003100100001400b0595000b2444075034030613204a0b410004541d01c500342424690560035084c080d555223035007040000b040d011625a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 836919253 1250 836918003 836918029
    0x22a0c0405340c03030510030803091b03030f121e0a09020315060102031e040b04030507082e05220b0912030618060a03050105400b0411030102190905 66
    0x6a0443c1e00d5116a400c5004243c014014044600c800f9404070102e0380314400345129906034001025070f0ba00207000c2c1d4510a0448035030354404d610400c1070b68820046401980c0d03220f158650403401d103441d02c03491100d8890184100c8040c142c100401c12583c130405811a402c2e007802903050740c02861440102c5003042d04220fa01d00c0c00f60740100840044c2d200209200e40d603090070f6002c00fa0600351550000c959030ba0103a8019600d60344001d000b4441c0075070901c00c0c5e010010001d80321303541910351985003888040b40c101d02001041e81d1400000c041c0c560704015030035000700714a03481551151070329044000d044262045561445001d054a56030072050701101d004140090004481c0c05104d07880b004049002015613820056101c0c0000014000340140b078050120200345c0048006840e804410b00c48501c24a40130703814130b035941e01000e034041c418489899604082e04400035596400d00131002e205c401d801a40561000420181000100400c400c500700550381c0c801006540e801004a502c01c01c0e2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 836920503 1250 836919253 836919257
    0x17030910240b070606030b130b01051f0f03110a050a0e0904020616080f16050f060115080405151006030b0301060b090409140a03050307030609022a0c040534 69
    0x741805406569400380800a203e9000810311a407240d40c4d80784140f02c1030307a412460b0a0404650740c1006050301c64035015000c1a00d030820b0401380820100340d8410469081c0c000c2c0b005030400340215522070742200c05c23501c02015249a80f102102001403040d88550409000203c881c06d20043d2031811010a9010382e40081402c0e080000c50006084034100414046507002401c1060821810780400170740210030158804900c031181c103052250506220360700b50076080d0440f1005102080e10808404120400c511b86281e80e59200d2178143e01d0040f07500d940b120340c10041c1c800c1144034008060100c081c0c075143d60f410b00c01034540350141402e0f203215000388810a08144940b00c90350501c2d80c011a42c2502544220a21250040e0807a081a050f01400e800040d0000200a142c80e00360042900900c1203101c110301d001484503490404c0c0040c0d0a400c22100510001810100030400400d110100024010455030410b40142010ba100318034280d400005106202001016000044845a5025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 836921753 1250 836920503 836920571
    0x10e06010e2224060203070b0a05130501051503070b21060d02060d0207020913050606010f211a0616060510032102010609150b0717030910 61
    0xb0064030000c2190300074800010207201c0792018002d40902d00d02c102d000c4580900300010441c0100c00c1c0703a095085101590300401c580b20004286260103a80440146400183d5464580501424800003a00641250300342000d2000401c048104007440e02000c40c1151105503443c030305040c180c0942c102d4105160200207959645289040740c50f40d204070b00500c6016503400942c0091a00d4011002d582012580812100114204141c0241c0c10400109150030800e1040e0745441c1c0d10f04e8010800d6040140602c0c05511060142281d00d1224001180100081d10003180b02c8004200d44903040d59161541d803055961820004c00300c0320f400540202030803501400751698000760a002d0101e1540c200080000030128900900032905c02982d1403201d000600c0d008002030075280c80c0c0d0406d0203d00d2401c940000c0d400f01401c10581221302e8444829103480440c2803500900c10784107203020308014000100048100003260290105003115020080b0f8a103a020900268002030301076010701c451 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 836923003 1250 836921753 836921777
    0x309120501021812070e150d03080f06010306030206040501110c040e0a170a020319090306020a030504110a21030201091a1017070501110c030d05041d13020f2115010e0601 75
    0x1b07100c0d0f81d06e9005680d02101c00003c0b480001007801610004403d900154019044c01444000f020384c1c190010002d2034248002030a5400084007403155115150600640b07044050710201300380038001a581c0c000307208000c202d0490501c01c0d107426110008407010f4041d8418013003041c2611054415180842e40290304003400060b801020440d1b5440382414843c50300d90000c001101d500041c87c4680c00c40c0c5c0c0100712800d103450244144464a0300c01031207030f01a400e0034410022103610600d58030070750300844081d02c8401e0a00741d004254040c1c014004504801d21000650300d41e10840d409090043c40c24a0b40d182e07030f074044a11060b6000144001030b001043d040090398403600041d00030b0801c0c0416035644114001c0004c6c41c2c0252203061501042d4080360130860031110300b1100c25412036070740c2d4000d0765242c0150343c2d14070f101380848028480c218650704a07029464090401c0303071000344c0605400320034083d14a0255904088030811810740300b604004034601d0240b0a40074002d50068481001d40a2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 836924253 1250 836923003 836923019
    0x6050f0d0c0c0503030903090f040e0607081e04062003090a0f02040227010e01050405010c0b0901150b1801110a030804060b04021c1401050d060207030912050102181207 74
    0xa4003142080c00c1050b644600c1c4085070091000f180a650018010760382c490484003840161201c44511078170440c5411542903d064001c940380d58002500e11b0034503944e5444204450304413096002551380382c0d182c4002c01c020010313981d00c00846401c1603110303c9040d20f03540300c0c04c02091101710748600280c0c100f01003240014000c0c1200e9440d0350f10045c07026090060501c51103c04c51080031107061400342d403551441e038558000309207400d003c0003072030001e10300707030070200060400441010014048820400003c80c254401c0d03120641448031022648085590741d0340004564200480148a000b07a00600850300d600070090222044140e50180030b03540c3c200c3d2003e480703900c801441510400d80792884040c80e60b132648000c040003440a00109000f80055041c8000c54045450503120200124014800b6030b5803070b5a2043c8896001502503a1503085140446100e401039005400000f500c02142080183c103401800313080f80c0f608072410071b49030300400b000b005c00d103030880c402410340295100303010001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 836925503 1250 836924253 836924261
    0x20c100f090c141302030f0f010801050c042105030304030c17030103020f0d0c080607020a0303060933031a0a0c0305010b0a031d0f01020a08090c0f01031a090c1306050f0d 75
    0x4600610f0306546000130559501030b43d100301c4040303001c440c000c020070900b0325492205a02500c880300c001c001d0f502d41a4140320b02d9114074026007652155070142c0e044107010001110200b99404800c1d2074403403e00d45009048400c607c01e0484155420301035003070f0030b003100200b174038120707a001424421482400f07414854a00910b080070780d2484007940012580746000c200650080426500500303681039107040c001c04072030040d001080e210f400c169031070003200d481010800e000142c0355800041145850030380100e10500358002002030ba01d110310300b5440042c0740540c0340f0070010101c080c40810f00d0f0a40480459109000f07074109084240012071009100e640220014048215108664910740088918041190340c000e2090303034001981101503030b8001c030125000320303a90740105040300c003074070001c1c2c044a10381c600c6504169452126002c010200000e1400b01507010b0f140b03c41c6810000c0302c0850030781c004a8450381c4035080007000a515803203007049600c401c05c0f80b41c07041d0610388040c040074090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 836926753 1250 836925503 836925539
    0x10b06040302040f290102010b03031207050f0d1404060c02030c0a060509151906150903080d0f0c0f0e1918090512030103061407080f0c0409020c100f090c 68
    0x84d58038445d0050b199094142c0e00b017484d14110300320060203c031800090944a40d2548a8000d03001440b407070255000c1032564a40250380307810301c00c1c5c60301c0001c0342100382800744604104803a418841500c1140c01d06600c0b5500450140005100b08110000140e98920541e41c0556655200c0d0350380c0d90118000354411500b00d0031030b0080c2d07080c00c04c0e900d440100803003098034504a1415103ea42040802491241400501034850403a2001c080d084029000c40f00a200c00781410100140c07540c4258241d9016404000000c02c04028182d40c0040050200c2d801303246040200e00101c140c982585800c0c01c015401c480d0300640e85000382e0522a0007003030040e80c01d00d01005580c6840008000540c2030200403042440614076a840c0d6140d0b040500035102c008a5000c0441c40e004184040c103039100d00125480f00d2600f0404000351070302811100b442c030036507000408035840885c003c410454040340303c0340c040452803000d114603c10650b4076402c580803140018081c021140c4c00700451140d180e420056 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 836928003 1250 836926753 836926781
    0x90612150a0806190b030102130e01050306010b030f070c0c121a010f091802030304121a130609020d0203060c121b120703060e040605010e0f090705120a140705030f010b0604030204 79
    0x1710300018020a099801107841400c10848102050010580200c0c0785401442d0480c02041507524020000340148805456440c0b6900d05030b0010341181d0007107240f1b00c08945c2c4a01c1c810440c0d60b40d544401d0307420314524412240074070f02c226881c2e4180c8180b4019030588034082216074071203141803a0390006202d21b40c120101d90414940b200c0140c0e90600c081d20062400d040300d10110142c80c0b070100c00012069000c40340e507807603034400e00c028040945200081194040000a40707050319000250042010311320003035152241d001001039012000d80a4081c0f0004c1c0c0513111015160300954640d10005c0e040030f1601d1120030301241c0500c0d8036000d48690001e81608001071015206c1e0a01e400c2100304980c199422600c81c8010840504c007801c031642d101280030110240c6013402d254180d100c0c0c00c240302d00c510401240d18502d82411042c0603d00032552300501c84004019000b0100c0d49602361403141512a002c3c01c200f204410006000d2b500c9006d000500c2c0500d028116400c11008281100940710 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 836929253 1250 836928003 836928011
    0x1a090a150513080106030804060c110405090f0d081504200f0405010908161526040209010b07031e03090203011e06060c08070f08090612150a080619 65
    0xc4240940403140242045980d40d03a68400e240e02c05982200c6103948110f100382c0c50030300100301041012042c1c405907181071804c0c40c000030782400d121a0360350b010345440340c1c85031a110a010701c401c0006801d50940300752106440342c41c0080003059039000411240d401c030829441302c210f0300c1460700345d0006026604041c880d09507181e4144010781290400440e60035440000101442250707008803404c8010f02d00d100050118203104580011040d0144c81032501c0350159800b4092900d000740301100d19805030881020154820704030590341c41009481c02c2c0d0052900d603001140302001403044455031070b090b4450704078030801d0f0240010403617100c42181d41010b540391551001a90700f801856844620b0016109203001049480c10465003035501200c103103c039041151000848104c181c5488542110002c103680300c050800d42c000e44aa6032032540d1000000800d50031141e050640c41d4042e901c01e08424240041550504c913200c0000d003e001c0c499840940002e9041200003920300700003190b898041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 836930503 1250 836929253 836929259
    0x18120102070f03080702120f0901030b03030d09080403140102040803070330050a050a0b030712050123010905090d321809060a0302010c0f0f0c0f080d091a090a 70
    0x1409000202d80840c0050489003d2080203641040126105e4001401e602c0c503208601403421414494190076a040c180c0755901001a03540c1442a50400c0301720950a002e0440d60b40f6040720f00e640140811144008100d0550202440c14400d80e01602c0c1440300441c5888004d45080d40c28584d00301d5207210146179070070305c03e0042c502e140c007044c4800100d01c00400d0070304040e0702000590313600801c041c94442ca40600d10696070b1700060301d002240d854002411146909040a03400340c0702e0003083c1002d07001c011020043c2401222141412540c207000100400c0d250b07081015140c000d2213400c0340000710380f042c00c1044404401c0c0022400c02c0d0040401000d503842d0691000b280e0804010803000070304441500c50b0303a04000928562005048904c04034440c00c50740040d0112120440181c00c51582110450400c160b034450143c556811070f541d800c1496035240c810102041500030703451240203028891414900230424001a1222a40c1c0c00001804044030071101c1d410020388550b202003961400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 836931753 1250 836930503 836930513
    0x1060c060e0d080a05180712140f07060801060215010e0c1e0406030c02211e0403060b011b0b0f060105160c08060106081e0a0b060c1e031812010207 65
    0x41e004000d00703910f81100c2440c2c5481040b0407100010407070b0020b8030300350400084103140403c030b0000b84c803034000042c40e00b40424103040310b40344100c0e03c01c105140701302c40203852241400207891003214070550b9000141da8903000103d80f035001034690102040900801400b200c40500c8040303030321001e5804094101010044800b100b815862100c4861440000d002e0280c16414081e06000381e5072b5000900016204200312000300794204041440440082810042c0c81d11000c58154060031100342e0b00e45883c2c407030802100501070b005646e40814810720617454205101500b620b80326402c03040c07082c07003071b512100b62400c8208001e20180c100002040b040ca0901d10242c410604907000340201e100d07045c20000d40e1841c0142c180c01101c14040250104801c00c1c01c2610b840032101210b90000c0866216205a400071b4105e0504040d4090b070082058123090400084c1a940180c0b94068441c04606a0f41d20503140c4c490134003130380040103201e0701d500c060717040c41303c002800f801210b40014a4440c1907295 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 836933003 1250 836931753 836931763
    0x302090d032307080909060f090403090602070f030317190e010f0506330d06090b040f022104142b020309010c0308181002040317030702030301060c060e 67
    0x304402240c20180706000c1440310b8601c0c42c86095540c1c10451a020007926024040e00071800c01c58840d96445002072520785446c013482d1502c4201500c6940542001d1401500c512414007809006209501e40050078081b01c0002c401201e400d6110080c0c500480d581c510041e150050038500381035030059540241584911403054482510740c00068004148000704090b1350000e40201d2103020301d21900007980b090410102130911900400340300003900000304c1040c7d40510a100110140b030050f000613000c0c41504104030b8120700711010810701d0005d050320300c201d000e2407000e83c040b6445455004114520034080540042c0a82203400c0701b504403400342e130714040f00500e0180102800d14101400103032600ca0150203400c40780099810100c812000a200440920000d82040342038800320714400f48050400340d5050700713a02500c40c105110b07802d0402962040c441103400c2031200100a00d115495016240a03892a601031803640c0d1800500b194070703295613181a00d503203903540c3e5000300b15103041203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 836934253 1250 836933003 836933029
    0x507170304080f07062a060f050411151804020c120406090e0f0411060904090308010617010f060e0a23130905060a0c02070e010b0c160b0a0f030209 65
    0x35a61036040c80c1506040c40246501c50307226620081d000c1c13120541203e5a1600c004000c9110030100f44001d45004d21138006c0030300980340794602589400a40b02a8011920640c003482e011b0a2110301d1500f0700c40300581c821442d0b10341030390500030300c8841550000d241d414528001c00144c182450300520908000b0000da8028110030b00080c10800d031500401e07a400101104c1c42c0710350661410401c1000000d90041c8002c00303959200c0c00d156481d41d500c0c019a007a180020300204005c00440ca0041c010180a00410011494102c01c011001140f00c0c0b43c070381650009a54001e0403071800c20191003c1e01340c011100c1c3d20504036003010505000c0039600c406014003100007a0816031041d01030040f1180107480d080f010905010810001c9507000400c5074100f4241034000641a19410f4100d0900d817494000700b0299502000028030300150030f01038401d20000c0d0099540c1d400c02080000c403c1d000c0fa11500072881d0003806100304507402104800c107608814200545000c0d03031b41e4001101c40754001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 836935503 1250 836934253 836934299
    0x2060d020a0806030f0304030807060207081603030605220908070f321c030e010c03021905090307060f031103010e1501111e010609060e040515011d040507 68
    0x108503101c1540e4030000090300a6400c0c0c0c0606070300007681c00030685030701c194000a040f40000061103403c2041c2a0304039850a0780203414680c90341c00e02c4840c030740392801c0c00c1402c0d00000c0c00c10501040d03a19000340340c410b1000040044c920004c0c0041043d0018080805090714040c0d02440600c0100d80804856a00b041c030820301d0b00352016000010000071028142803080e402c048482c149809400044daa08621a82080040007804220011809001da9440729090380d400c180801400c5a0150050043e440c10070071850480d0241810845680c050850b200e68194800141007104500a40242d8288002868042080c05e440490b03c1c420340c6c002e83c0134a883c200321400308100d6070240d40c3d0b00040c0f03200074030f054140303030300340d24402da41d1901f48000101895108050180451200350320002c0105441c0ca8184080e55449020101c041412501a51503020344042c052000c080202200d050720020b07400703c14014480d0a9902940c40003d00417a020f1090410100364904c0541004e10b42003041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 836936753 1250 836935503 836935507
    0x1318020d02131502060609010608060a03051002120a02070b070c050c04050421020723010c051b150903070e0a1805070f0b0c1011160b1b032502010902060d02 69
    0x402000c0003283c10385811500000e040c043e01c2d645080001e4112103580c504111030f621120001030748d981b584d500007000361040c0c0e1846001c1c8446a0050726a52682c04400e0708242d40c2c1c45460000c0e4850800300502010724030300002c2069002c0c21700780c0c0d1014015021200c0020000c008030702259810355041c0c8101401207200a08856103080f01c41e400001807001d441803d18004003420022201410501e0b00400410603000c0ca9100e20041001c1e070750010100e4000c03402d81440680380031030750251103004d40c0142514051141401c0304840c044400030300101940e9161002c09100820060f0a901070f041d115070180401303000100755060802d0049000e041900e1404e05144480143d40e400304c0d42d82c0805220803401c0c100c0200303000319022068407011514400c0da01f2984e8035031041740da020002c03580c00232207081402201d665142c820301c280b22001680c48a50034801c102800101e841841d00464880c440009591821400044a0036030001140c610b00603800140f50340c000c0c022803607204d640 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 836938003 1250 836936753 836936759
    0x307020d151404150207051005061305010f08010b060a02280f120305090705011e020a0515061c050a140c130b18010e0103241803030f021318020d0213 66
    0x10b8185100d104d400300d000451604a10b9030360785440d0440070f4000c02c3d5040c4e035039001404d6900c40c0d40003614007a1140350304001d1907031070300040c0005600c10b006a06a9600c0c5c44920156420180c04072100d100558000b08850029441915480c03d2006050740c0d41444800d1828002611240c440c91030300c0c030800d0361480d418800c910003021140c3c010140341e0158091502085642d0f044030030b44200c0900800300072944e10031100d0691800d00038040c010310320321549541121000040f05400c1c0258002c035030f010518030300b003452070000b006038101c00303030071508510b40d1140051083d0400d551820040c000340c1d000842910005800360701c410340c9405007140c542008881618224008101c0040100400d00580d41849000e04004405000040c02c400c0aa25455040e581e1042d140d0f4079a00441020302a15001c52607030112032107143e1040f404071b820914011100303540c074000d0b40c2d0801c201c3c9460850b05480c10840f4100d000c0f1010343e011902c1c1d4200241c85445100380018010a03100101a003e000e00d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 836939253 1250 836938003 836938013
    0x30a0510241e0f0b121b0d02030a02090604080601030b0112030806010c0510150e0105060304030917101a180919060f020307170f010e070c241508030c0307020d151404 73
    0x14010403204041505c00303900000350721b0f100251071400c03421000050322075403001181c50092194203240755010307501003030000300d4100c00aa118141c0e84250180003069980700b041c00a000044031300200410703c00b60005000c1d51150b01681c00141c004c80407540c4040380014440202c03262810403410303002d083c520900c040705224444070700611050f41e055255252a880040c9165050301890f90099403000c41030111140400c5014400340d4030b06401c01c6919000759074480d082c180041418000ca80c0b102500d002a3304041040784100345c52000750030000e621800c1c0d0880070048940440d0308070707628a507440c042d03c0540301139841a20a5226071a0681c40b11305000e02000c1c0040011458481e644014005810b545001d0303500a50742c0d04001022810501d09401c85500000071150313154050b0304c003a901032480d40c01030703030100c9003500c44481c40645a8001c1510f9101c0c2060291259000f0800300c00103003001e06003030380021300401140440019039542c0009503543c5002405546602e1801d10041c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 836940503 1250 836939253 836939287
    0x30e0f0d050d0216032a170307150515062d0c0c060c0c1314041101080a0603080405090405120a0509100507030e1905030a0510241e0f0b 60
    0x2000c0710513002c1d15940344d6178419040b0001b0302d0800c40c00c0c0800c40360421101c0071a01c80c800144c0034000f05201c040a03812015a03498001d00e20540d94240d025049070304c03c11301407280380e000d00c600000d040785031000700c001d0244a0340508001c44103440d141007811460446044140c15941d001410030341c0d640807507040a46040d14221002e0321031b910030001b40d018140c0000340c107407181000f03070381d6503070240c18202d007580003011541c040f000b0110201c1c042104000002000360802e81090f20b580d425921410360b050100c030700324007009101c44410071080c03082d89041440d16074010f00c13810450368074004140780d02d03010790020f81600e40440c0010410611a181c5201282c1c80c402c0c0600e0b105c0d081a1054400814101002000c2c83c05400c030107010603400142011090003030f0070090122a2085101c1c58000d0b900c045821940e01e6051a000d4809070309a25258800071091079074414039425030030000e5a54400c848da08042c51491201507000610080070525000201200505181c5819200103107035800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 836941753 1250 836940503 836940523
    0x70f08060601210926120108011a0609030304050d0b1b0a08040f0f0501180606120b07050c010b0a0e07020c0123340312090b04030e0f0d050d02 63
    0x802003034402e0b103180c001480086928100c035648013003095010350618240e0704600c4550b40c00d01d1304000701900300e08141e0b000100072104001c02020b410382c0c0d0f641070b8a0300703c6241c074128504104590b00039141c24944500030705580310008094901d01561940000c000242228044950100c400204050152070350b14001005150700004c511b0700c0e00071600101800c02c01080185030241012101d41846040d00701c401c0340c185e00c00002c01c000007a00c10120070303840241404031003881c2031a002203201d40c4460401103016501168121098807404d20644898104610a05966513280135440d499a20050690014420403d41001c41d040c90f4000a04046407807905905100c80d8021801c0b03041c40900784442c036600300100c00c980ba05001180d5440c10303034081070362a040c6c010002c0860504182c502d4a40586442500d408001c00c0707515811105850103420045c0a00d41e4010004021a008106140c040d2000a11280c5100d010f440019084c0c184c11130140e034680d0102400ea0380d400c0c1c04028074208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 836943003 1250 836941753 836941757
    0x91002070b0708040f05011e060603020705030a030b031f1406010e030a060c21060e16091e050306070e040c05120a2007050d021501210302030c070f08060601 69
    0x50a1190348401103400409440c2c14100140c940c0040d0520a0254030141d1090b48480240100c0c00c03c60162402d903c40c8000450b8458a17101c0002a000d00034803c940d51164800040e6041005491090380100b00303802100d6014050fa403500f078046006a0f51000b4070561913040020f000b242108800c0300b0f03010041049040c82050088804c590350300080591000e60302007004613100d10715813411103591403c085040c101c2402c1914941044076990001d005841100301500100c0e95600d41e9403c460400d520f044001c10030a01060001000c075100304d108007900f560500302c000b60b40da00400c0c544082210028000f450140c0c80c0080d61519010f14102e0203568074003141031181103d441201818082c0c003880301d07a0b0351902d2280d2081d00b14120310b01521614190701340c68008074209a902c8907490743c600f100501841a000d0350007241c0030b0800381aa150a0101409096461101419510014429011740c030080c88070b00c403c1c81e0204012000740c402c1403102940c06203001c20031440d107800a030800d81 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 836944253 1250 836943003 836943007
    0x90f2e08330d050706021b04054c050306070201110301090b1c060b030601151205090a080309150703021c05070201060b0c0f150408030403081003051e19110f010311040608091002 78
    0xc1d04e070410100340d46002c90351a0444141c1d003004651012b0300c0700d22074161402c00f06415000c10130100b106280000b105e0080c0c040d00c28507644c10108078201d4403d0151403450302d5081c0014010550180e00500034850080e04e14600b4403030041e15100350b200c22120440344180c962094603081d003428443d490061020980c0301d66003140302030340074000400080003200c085560b000016442201040310690461700400030307980e03a00300702c3d94031a1212000300d10130544c0011580840d144c03070311034400c440340419400480c3c0340d08440044100007030301003c0c25500c110b6480c1c10001c01e4045100004103401c984580090070600e00c095852400c03d10000546091446024100004100c0765000c4a81c07159242c0fa00007443c1d960084001c01d00740392a04068294843e507044603000312284811000200e200b00101c51030381304048041c40c511502040c0c001c0c4040c48580400c00207007032000c030001014005040c046030030800ca0601244641069101800251028082c0075034180305020004550501c1c0c00158 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 836945503 1250 836944253 836944261
    0x503100501231503011e14011209031206090c09091a0607051203040b04170c10201201050a0f0b090f2e08330d050706021b0405 56
    0x2504814a840d02d0000356289000700d0341d020342d1900803600d4030142c000510307601ca5854504160b070414010b10341070160441a071000c50000f401002c3c2103800c0d40144e507003802c03090481800c440036116030071007201403107c0800140485013803030141e10040c040040d00010501602240109140c01e0b070381c0a4542d00d40381407580543c0d2503480003c0c072140ea03025500941e4402040c0341091a004014080c103c0c00000031003800104000244034500450158101c00703038030010f0062043c07051041c441c41380e003280d002c0406038080500c103801c004074006080d130005081c1e1540e04a50310030390340325101072040e031054440184039603d000001d0700064440d1402c020f180b1418000740507454456410001c0c49800f01c0c8890f01101e0b9100400810080d601d0701609400c0a040381249401140c84066200882c1900c0300007588501030106181e094503000f0304013a01444080034551011024210303154202140544100100780c00300200d000414a0394014106c07602001d007044584540c0300718081c40756081c84280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 836946753 1250 836945503 836945519
    0x609011a030c04021b150109150602030a0305070e0a030803160e10031a040603080d200d1812090e010504060302090604050601030615050406020c0904170c0106030503130503100501 79
    0x9400040d00340c030010303079540058010302e11190400c1e4040b400307880340008800c1c541b060305010030704842c8480000c1c000907102440c40d0510020a000f03010040e40b050100d200a103109411064101382076003420450441d0080108241640e5074005a51008c1c0c0001804152000000b40184a010510b442c40f01075011200252681481804260416480b40348040e40300350110380b440c2885d44001c00820005540c0e1070041500d8101d800c3e8492518640b2001d043c00500317000c8001100801324040da85490080350030f080c010f2250030a0b107210710b4002040e4070000303200081c40200103070301da071a850046072070480040041a0141c05c024010b50030420100300589074002440d0300440300b120042400d03618200104c0040c041a40310780700c00d04117800038511094011000f8002c0c0d82042e404d0f1410400d5200910107551010340b0000d010b105803820265072220020094013410001c00004034a06680f510f40a00d580c03c82c418000c04210150020005882e0030403a6600804c0d80c850107010540c0b409020b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 836948003 1250 836946753 836946763
    0xe19022103032d0117010b0d03320a020c090112020a0312110d03061503090c03020909100c030b090115080601050d0b060304151404050606010507150e0609011a03 71
    0x781c088121465101c200460b00d40d1007000305040c00b6070110050945e503c068845409011501c1d01d1419403a243c3c480a050802021030b090b000d41580b1059140c41c0c00f10540b02906840084030402065a030002c422802208401052036040070350081c00904580002c022160710182d221900c655071059255005844000c00d040440e074100c20311b600001d110340416a03101c0d000105081c3c060040e11000911981c065014005840a02032080c01c0d03402100c501380c0468200400250071090300030410801031504c5010a5030060340c0300c0c1074500c1324100f00c586005941e51502c42d0b00c0400d848036005911418070f941440c0c0141f907030039620007400d0541c0e00d010b40351040180c1000d040000004100303402d61955008812a8040504070f00d5407032416040401c550302d802d018500b45c103414010400c0c501d14410075010b00030741d0000040c050f16100c036001035a055002c05001c560032086580b00d011008001d01c15500d409d0f081c60045d200a192113a20f250071100708000d1030300410200d0704040a40e440000da = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 836949253 1250 836948003 836948011
    0x180c050108091b0f06070c03050f01061a0a0504181a0d1e0809060406030209040501060309080f0a20010c020105241203070605071206081b060d0e1902210303 69
    0x8082198040d046001c0b403113a00c0409030301d980003440083d1150410603003d40b07003001c5a000345c09462045201d141c031182a80d800d44502a80003a1040582710304502c42070082c114020070782007080c680fa60350700d03299612903040340f007000b021036071541c03403001481c410004c1407040c0c0ca00320780b030281e141420313074a2500003685842800705001d02c01e900c044c104202c40007240c541d140014141c60300e40d50364000003801703503001c40300b6140120306110001810502a000d103520156001c1003490402c3c41001c85c905440d081264001d0400014000032400322145c1410401d000c81c000c0008910a240200080d0a482c400382c44c41c5030400356500c005035980006c01220307080e148100c5090400d80700c1c1d030001903c4e41c05a0040582490f150405016001d900440c201c5001c4015031020321845584141d00341d2543c0104540307510800c002402da03a917500d4440b00030460400710000c00104401d848882600e132406528001414010410b007400951034000411881d80d445803c0d840a82025800102e03100c0c007002d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 836950503 1250 836949253 836949283
    0x1150509040b0712050a2c0715031e06090b150405100e040c02060118060803030c220312031d07090c0207150816030509061b04030204180c05010809 65
    0x840e088520803500103182d0703c015081840a414101c100c1c0000700021850000c1e0b003243c0aa400403402281c4c0007c40c1019003c070042c03d065071814510502004500010b80304041d65040008490710344648131940f50759012a0001703416080180c40390885a24600c81442043c4c15490310050f9920b0408031016140b003954810b8103103c20100554240041c0d1140c0c42c0e103c2c0c203000c611400264000f03503980c100d0394012845850800c040d0300f81c60840d100d500600449400400026045071021001050030103800e00d21080d000002c10b07210b42c00c440280e0800c58119091030420380415a05005031303900201405001c1e00006200c200c0c0395605c511610444112680b60327204510020b00900003c801130020351496400d00c0c46080c0c0003000d02c52b089034058144645d141d050210031b4803a2181d03500c101c1002e001032206845500128900c0740d02c00b00d1300b401802040101100584403402a00c5100d24036403210007032500c181c60032100007046a00480e040008890400ca100300c800540d00e034504d1080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 836951753 1250 836950503 836950523
    0x50a0801320409060f0c140f040e040c081b01021209090f0a1104082a010e190b13080d08070215060301110301060e0a0e100b0f0c010501080d020115050904 68
    0x40c00442c000e04030402014021a107050351030041c01c81c56801c100340140745642c0c0d5030350a644694030301c1801c0c081d03a45d460a241d4018001400300060703039201d0b01d800601030046034203125500c864641c43c020b1002c40d20300040038003d0721880c0d0f41d60100151090285101e1100d400c00071100c0c041900500c00130070640112180f4000708840c020309a100001030720f00e2a07800c9070341e07a4464404550303401d607440403107442c6801c9002d040d42c40648030a0000210b84143c1d40c0c03d40d00a03c500800c22400609038030b8403000a10040d000034000270384001000300404d510182c0e00314600c2e152034141026a443c00040030302c999403080000c81ea80c0451160090302c820a0080141d403244004a8014030702440b8041e4004000000440c1d05900a140e09000b088119010b40340151529007910041d102501c0b03004000d529258103028074203c9030040e0030b0000070982e021342440040700c04c80382903440071f130f00c800d83d1500403080c0900c00301d9080c001e804c3c0403600410000242031608000c0f9005620050018040d41e43c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 836953003 1250 836951753 836951849
    0xc0e0c0d11090d0308150108040f060f150609050312040b041a121e0a0c0815010e041b0f1e050d0209040504030801080c0f0f0d1b06050a0801 62
    0x86402e03600350050140a2a481c1d1606160240000d0000e81d80d40c000b49681c2c12003601d0790361046584034482c80c0d004e2030310241825545d81d2070001d0012424100399054440c0c40703500c1c481903e02500740c024481680da00003224905018036003040b0342c0211000e02d414080205102e80100c50003150221410011200203950750b9040381c0b4080d00801445521850b0180c090204100e01c02055940b992010709404102c0e850b10a1948101c5084010b184045480900000c80c0381860300c0c280c0b01142418100104034083c158002001c0780c90212940300300c600d014003124000fa5001890007520003c07800e107245820400d03030401b004680a19100420410700003141d002e440c065405a45003140e000c1c000780560b003060300e00900901001d00405881e031186420020007450802e032090313400c00015140410506c0e4040500c4890a01c01100b991a1403400c8181d00b042d200c0d2881c544c005000d5039840079111140c668004002c400306034804085441c4980740344d4140150395004450401c0310030216200030007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 836954253 1250 836953003 836953031
    0x20102070b040e01051e100f0905150c150106140703050c0f0f10270c150f0f080f0703050415020403060f050105010f080114010c06050903070c0e0c0d 66
    0x1165001001d0103030021500007000e01000c14114162041100e807841ca01102841c1010700307072040035030141e000b24660f1110000c103005001c84106c40301145031019032103880700081410440e140030065082c100004a04050110600020007400f000e060841130f59450030390300802ca401c108220b40d0440c03000050030810180107104564021819000b40c0e44015601d04140d03031122080c006208031030191400c0e50209049903c81c51302491300e0a94009101c062107e20291002c00807402100c00f072010701c502184161002c14110494a200e0b500d6031841c101e860401000c070020007640c0340520070ba081c00c2c46101c800c0c0b01d0300d00346e014549142c0002e55988908182e161000340019000e0704501c0002c021007442029000702c145008130070010f02042e42c4c2c40b03004443c0004030001c803d00107500800180912486020801e81641d01403416000e81002c540740c581c1141c8055851203059800010740d6410041d1005502008281c6528440c0661a00c40c419130020311840e025844003650f11004002e00c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 836955503 1250 836954253 836954263
    0x118050a0212040b0f010f21110a0803040609090915020703021c050c15010e07050c010b040203011211030f10180c090e16030203030f0901020c090a15050f0913020102 73
    0x111101d40840744074209400e1070080d403401a2594590f01700036100103d107414a080c07043d0101c03100340c103048182d100da401c0907061003000c4a01c1203c0381c083e5003a903021282d031403000610280c0f02e002c1c003855071140f0b0120b001d4045030b81a800340712104d0a24004c6008a1801002c0c01208008000003503903d01d00c0303250480c20320100706051020020031506414000f94002c0281203d910341c441101e40e12060220100d00c07141c0300b4416035080d8210100020056441000170b000c035041c0280000c119a003005c3c00040680c0c00903004810011000102c000134480300d003401d41400d08054010f04010070103500d0a6480b40c0301203801040081c1c4810f194085008144164182d1035008683c0b40c1c5125181e00c80311010303140030341c00d022141c4141200c003401c00b0101140302c02102d500800941ca80482c5030340c59803e80e004002440e05500071182c1500040d02c030201d4036807080600c03a5001030030020803c0c0c2041c8601640e000707140209441c0883c808240c903241c02d0b598103c40f21980c030078007900075807004038940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 836956753 1250 836955503 836955517
    0x10e070c110f0409120305180601050a1202060f0c16120c261209012712230f1b0a030b0405121305040605060c030a320706060501080118050a02 63
    0x400d643d1740310704036a950503407046005420942c2032a55415248560560b02d180030b005880d40008038000030400c81a49002d801c40043c0b0240a5030b0400c0040c08252850707400104461340f141e00021a840c184240c4d900c2d55001402c407450a2041c044880d44510b1181402400741e424a283c59171004646400140e00f41445402c03120125203c1c00345144000703440d504000360060101705040007100414003111158950341c550390044d80c0c1b11a16014000030030600c0944140c0d101000f03501c1c8090b4905820401c1054104064000c0510101242441c0e01c0e0003181600170512080301c00000340b0680d03692083c1c0c0100e94008138482c3d190307140d6040c924104a4003034034100c4907100001e41ea010b46004118200200c3d0000c41d401c110702562101400134034072a4280c01d90240c3c004226912506015076140d07054014641605c440390350120840460341ea5040c070581001d01404920002000040d02a12000d4102860800419490400181c4500e172a0882d0851507940b1000001d03180e40b0140e05603030310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 836958003 1250 836956753 836956763
    0x60108090106170a0b01140d060504020402040f030b061e0f060d0b0301022206051c0c030e070b0408011a010f051c180203010b0306040b0a0e10020d05010e070c110f0409 74
    0x1401c41500d11560307603022070b040c0c11905d40100c0d000000c0d070a103600c1c004284514000d40003503d00c030300a9a488004060040040364003560920010401581403040e14010b50312625a040050138074004006080305000825208550350304400e609544644207500c1c42120b0a442e1903480e9041005004082c05010034070300c0d092341c40490180c1011402484100002c0d1405940e41c04050700ea2004032254419145285500100480707807041c50b070b488c0d0703000030022403083c0b800094000001c0441418025182d004c82116103000c90240700d0744100f84031b501a021912005008000c03202000608918516086041403120124220400d8a046601001a02c000c201304105c0241c5851403142e000e074120500ba8041c0d860800c8501d1179040000c0c601d800349801c00ca0000c01590f4030311200d0080c000c01500d812481c0103662413501c0c801490300291a44500034130021a81c1c5d81820240c00c84180010422000c01a94880b11400301e0903182010508034011789206100c8400d40c00485c3c060702a511000703113 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 836959253 1250 836958003 836958029
    0x4270510110306010f0e030a0f020f0409080c01060e010e0f09030d020c100b01051c0203100806040f030e0a060503040308100b070b040b070c0209060906030109050706032c0303060108090106 83
    0xa0590310300c40207501c00c070801d032542d241217000440b04480c4c18042c0000c1e207030560b0012000d1004a150401c40d140d2003440205281400c1002d08046001e80d4940602162000404284029003140a01444000e01140d0075200d459601d800300f90020000c002d451a000c04203d0b001169202c0b5060049a81740d441101c400d42d520000c1c000043c1d52440654028094146000c107402d90701d6200307204440d0700c2c640e40384400c0380e2007e05213200002940f0180091140071040e07040081d02e40c3d01440000d105070300030644580001ca1500380507100340d00030080c0601ca503602803000e02400e50000300307803900503405151230f00c029913900e45242c0a00c03446403c035070321503240440c103c000c00c07624501c182e01c13a0784603c81002003074844c908240c6051400240095020000c000000c40c5401d02021844e07205c40014000f08821450340c4506050205917003080f000a9100c2212404482c0c040ba40504007404501103104ea040034a8450341d1030340400341a1504000001010446d140d07400d41200c40034150000d10a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 836960503 1250 836959253 836959271
    0xc03060d0f0809010906210c180b070605070305190c020c06070506160201051603020c03090406081006061704031b050d0f09090c0e0603130f0f050c04270510 69
    0x102d80d03084107100e5800180307024400f0421502c0b600c0b03250000d0003040c00c81030045c00e03402200c1d00a44902201081000100e00800c6400b0300005901c1e0018a0b200764202d550380058141340050b1000108030030300341810001482114512a9105040d1420030303400001c407912002002c07800c00c00300c0452590b01100103c1c0c1c0c00b09001002c0303403440c0650030f546000e03002203140c41c4050303099540488e8020b020001c00e8818010a5019400410089084074143c07882c250f0a1000502261842c2c1c101840a0707000040c00320140b0103e105440c0500a1402e01100c403080c081d071911581070004000030100203422902d00341c21400404600324080d408425036030980001070000b0074010b24005a6400900c11a01c0066052201e00c540900300703055540740f00748080501c0900003103500241950b00b042400712200c2d40491885440c441c1094481c4000d40c45640c240d0400038540380e00f4100944c4240c0c03a2644908112a80010076600740c08008180c808003181404d0480c20301542070700c01c1e902d01d4180301c101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 836961753 1250 836960503 836960513
    0x33012a0b15010f0309081902160f08060c03100510030b0d0303230f0c0c07030c0303031e022706090306090a051212070302030a06081902091b030c03060d0f 68
    0x2660200200303a0743c2d4891006082c0e0100c0170f455400402800b20481045420940d0640c8194044104407a0040760404003c42000d0030000300c81c1d82c0800c207048030340b10007804031260600c8143e0700000d10401d00c50440c1040356580c0085100c0784205440750907034040310001d00740243c2100001110050685c1c000741103d040181c003400e40c4c2e000c4500c4102c00101c01442d80031604c2c8025002e04100034051a050b52188e0411215520000c0328284911980c3c00010015000401c000003862181d640841c45072142c0b18600c160f00c010746402104240148800b4121400000350208041030740c034007440b00e1a80810202d500d40c07190494194160013100100b2000c050001034041c905886601201c55005006070b044005008465400280005402c080b0341c80d588250041e54108420f4039001236155074410f0750a02d04400307004540c016400c15401d01b01580f03405400260300140380080385c80845d9030540412100e100051031071409880110110b00f03e41c480c0400d40100365404105484480c3e414189 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 836963003 1250 836961753 836961781
    0x20a031b030509010b030118080307020f0f010f051305101e020427090b0109150504091b0501020d2a020306010e011a160b041a33012a0b 60
    0xa50f41a540c00c2082008050905114480d00304107048810200c801d11070340e4080140c1d00181020046215003640781c0c502c060244003112014640710000a0002802c105100640f007008181742074854540010134040742020444201000781c401c00002c01d8a000c082d121050b01071646a240701520200300403580700580f640700003107042d444210002640002c03590310141d410001e40240300c000300d40010400c036071150700f141d0300d0045050f40045440e600e41e004a0100d03281303505d0580b10f240c2c1c00f010048640400b010f941d4040d06007071010300703000c908030702024100c2900c895980006590740c01004180003400745410003e2075000302903580759603460405d00e80480081c0220004001420030295844080b8030850f41c100d1404203c0e001c890345c42d80c980745a008001001651105510202000807000c509000c0d88580401c041046c044005824540d00c0901485031001e80050f400c080d480f00c1c0c0e038118036a0040c5002190f40c500780110341075000d00d0a020305560003860021048144000e2142d501c0b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 836964253 1250 836963003 836963011
    0xf0331050105060301230c2106010815060a20070f0609090204050f0909033603030309120c03040315020d1a150c010b0916030501081f020a031b0305 65
    0x300901a0b611664209400c07545800c0c03800c4501c3c0d101117505111081402041e5500079581c0c40d14506050b01100f44284070b0006034002071400d56013000b001107668003e081150010b2707d10590032132010b2490003240c1c041c4030300754551040c84400c0340f5408803075075241051580e40c5528010380c0ca8242d5502c40000b0000001d00484002c41d218400c0480e0b884d0041c0f090b1011107030020810035034441c0c041b00348680f0400181901d140c82c001017209103000c0c01c92584560710b14828280b10450301e0548d140c800c40d21121601c016200b80c200300103002c0d4032103000944405807010111340301c0d600d44e01a03c031985507100d00e51005150b044810b00307e13444400c5950103010140ca04440a00048060340400040c500c54641000c0c0e00040c81c00765666078410600203482501c150314000907140140300001010800116a40040c06e02401280d0011981c94007d040c0180b0610006142c2001d09090817903180040c40e00c002001075004c903410000903c2130700181c8080506011419000040040040241004036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 836965503 1250 836964253 836964263
    0x6031b0905010b07030914010504090203100311220e0a0b0403030b0306060607051b040b060c030c100203060307061211030109020703231813020415090801110f0331 72
    0x40000303894014042200c80c09170303050341c50318905400c1040d07803c511640014a5030410409010124420700c2170320045000c3c25010101a044c02e02e1460304d4144803684c05002c2d4041c4580c1500040c03030104600310000c10301501000031604814002c00c4624000c940392000e00300e480c4907001c1c8001e058055009092000c411741c00c0d50140c1d5500400c5c800d0038440c40e04014096031201d400c00ca01d0000c488034440d07002000820102d0003040d4200010596004103803070b284150000900031066020400217002410740c101002d5007140340c40c000013a19400d841c8103c109014041801000000c41c55202004803048845c069843c0e5848000e00c000941140c501100400d10654400d0241103203041a0310a8000c04441031740f40c49916040c010b0642c0000c40c0040d041100505120303004c0c00c05002a2001d40310405000031242c0d00d041c0001d00581e51680840c150303034548480c11000d000204100c6000348202c18000b5529100c00c00a1901106c1c0c032580301c010086141c515010747d40c1d5096407151040d000e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 836966753 1250 836965503 836965511
    0x807051c1715060703080907030507060e03280b070201020d0507081e100b0a0e090103082212080304020d0f0305092814011112030a0f0c0804140106031b09 68
    0x280086142c8003882815500040522a940c0000d104000380d6521031250700036203811036070b20303541c081c641052904810040754030140c0c100406c1c1020005420301c1750050039030b141000c1c0b4034041d61407000400358018158424103c00103480a0003501114540801180f04000710f00d0001c0c0c008015007010b54425080c0e4001d00c8492440f004880243c0340250030113000341100d5460100c048043c0d81c000308942c404e11404155445850b520110410300950086400f10350714001486240b2001c1a41042e014028000b640f050125014041556a00320381c0b2400d22681c0341c0f114000525156040640240001451032154003010f5020300503102d02c3c0c03415a17000204040d441c070161b0141d0611058910700ca40c0440d0100484d03078001510100c82c84040c105840220031044900381007c0119001034400c4400001f0302c4442c540d41d10130004140440303442000322880ca250000d00041000d000a840030010703d000c00c00b44031017940014002d55000d0100254102d01c3e01c285107144c180d6114190116242c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 836968003 1250 836966753 836966761
    0x8120f07091e090e07030204090c0501030c02120306150d1a0114090906060a050f04080f0d1704020904080904020a03090204050f040816030504210b0901180807051c17 73
    0xc501d00c10701030b020b101141c0c15040c600700800d200081020080301040d9208040001025840c0d40c443c203131140c0c0c01940c42040c82030600b0000343c2a181181240003c550081e4110402200c41c002502d4000004540c4a0001e034240a05800d144c01045225a40140f03001600704041c2c506c1d0360152002c4800b0380340c48103070b10004983d24120b40610351102c1d82201480c0002503040c54100001c0008940382d040031750401d401c00603144a9a081034200001030b6000036080040e00208110402e0421070a1601705031503004001d601c24000070250000f8001c206a00110341000f03e410143d88600310060000c41d202d40751a0001009080d01c03c9003070340100e10b4070004c115407509043c0c0b030310303c566000f500d40c910784230091050746c01c406100c000c2901000f1082c40007060301080b2403014124003096800a02c0c148010382864203d48002500e4002e82c0e0b1700d0300f400705000d208160b4502c52100c1e048000c568480392075080080c201001d101d2240c0c008802c1c000740401d01900a0b4211031488110303402801141c0d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 836969253 1250 836968003 836968019
    0x50f01050310091b0602061801150b0a0207080115030201091e0e0c070c03030c021e0a0b0c01090c0e0f010b09010e060307030b0a0e090f07051c08120f0709 68
    0xa005181d09900400012280a0856000b00034224840c403203144d1070ba002150110421031150300b14400581012060101100c043e0038000344104480c0020454014074000c403500d500c56521420028200128441c4d00043c000e005280080003c50000e0100a83d0a003158010034400d0008901045003402c0c0030410400c445000504400007162200d030003402c0108121250200500c03c50b0b890608111240c00613000f43c10510080d4071079200d03620520300703920400c0000f800034424900030001c0558000c01580e03902c8222011240951000c680d0790340320781d9402c0d000d801500e1f03015000c885c0000c00020b0082d01c581d03950b4403421281015150690320b40039150f201d807244045250010355414440d901c1403805400568000e202ca0500203078202244011a12106495100d0714203161786004029000b001405020913980c41703078010b42282420f220000380500e5044003040300034109119a47d0402c1000780803aa00c01c2e110940d600c50318500002204130010044031a01c00140801c040098004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 836970503 1250 836969253 836969281
    0x30f0608030a0c020a08160911091f0522030c150903020402090f1f08010f0f0b030a110304080703090905040206191b11031513060b0d12030b010305 65
    0x103460360090352900703051202c03c4070025082d050aa9000340522400990f0311020021150300c3c03088070445400031440c203441c1400303e031380d50310358010280e40402c010341013655034811410f02c40c013030a0300d1815220f00c010011580c1d0701510856003400d0303684940424018601c43c0620080741c1c4200000e11500e904d5040e4040345506a04408022a1100340701788014681a0050000c402000d4070051044110100198103100103814004955a111850402c01c640c40b182d03003809000300c1d200500300ea9103010503044a840d0284505d02500c81c01001080e030002e41d84e00040005072034026455242c3c142402c200100d80e000e09021404603a10640010743e81103d07009641c1708580007000700b410f2101e14004940f40016080056080166921203403040341c0030941c07102e05541c0150001c0d03480185100a06203002e244050310301076500c3c02c000300019400044840c080507070744500c2c0450742d2a6140046440d003001c40700c004161640307000c03415401c1640b6601080c03140c58240d03010310041e20f56903070f000306134 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 836971753 1250 836970503 836970509
    0x130c050d0f0209040c0302030709050a08030f0f090a06170a1a1e04020d06090e011416020c061605150c040611070308031e0a0203090a03261501030f06 66
    0x4548144810448808150300049100c464044050f280c000004001000c5a8130100d007100404d90100900a8041e0310100300000b81c141038460f0410f290815000b603541c0e008030320035000010340000d42c5108402030802035400c6680050541400b49440d02005400032045880303803030034070f001000003a803000c68030700681d407035130a0240200060006000600540000202c0c000328510003000f08080c2d56150351000384064005c604000880504140c122408e40700c1c0f0613000211a8102080740324998014039200f504114481d40a460000034040140d08221040400c640e211002044200c3c04010411820390303024031580c261358000315000742c84c5044240036554005040b80a210610145000d08000800180000102c40c503560f03803943c40300119481102d1108112034a601c0301e10840c054092901c1d00100111825420751405a44043d6512034581003c0c2c01c1043c02c2080c520000420100d0900250300c001c0b207881e9919103095030a80c01c0309100d041c1400030b4030384800c0c010f11040c0c900ca19019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 836973003 1250 836971753 836971757
    0x3040512040e070507080c0706030b12120315130504030302090913150c12050c04060801290703030b0d050606100c02011d04180605060102070f140904060b030a11130c 73
    0x216242d80504a130950420780085580c404100400c07480c40000704a00401401265004113600c9000e40500601c01400300780518103502024100c408902601d00380d0717138481e216410b0042240010400211700c004484188540585800d00340020304d6071640003482c58000644180c6c100d502c842400c500e8a021980000e13180c401407240a403d2030003aa004101c070b2001c50b1426038900d1442d001283c04840f02075654110b00e00000500b0051240c0242401d03004040d140c403610104400f02c2428069502900300c0c10713400210000b00d050800d80694082c585801014200c00f1100701070340342035070782d42c0e00544025218070b00496140350b02da886042c01e1701c0381d40c1e410b03076601d0181644448940b90341c00c106c2c51800d90040d100d64288903281d504070805c03558603000e200046050b0500c0000a8201981a04851900c40c0320000a10920100b11401401c50b14140ca40c92642c0c0e596040c0007004000c1000c1490740750142e21003900c14001c2c4e040000301d03100d0080b944024610b402c3c0e810708040b40c4140150b200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 836974253 1250 836973003 836973029
    0x603030305010e04122706050d150e0403050d1112040507090c020c091b13090b0901030f08030405120408030d14040c050d030c05010603030305010e1506040b07020604030c08030304051204 82
    0x184988544040071001c8071b152900c41400d0034500c54240c214115401940008401140390811181c09004182c0362034070105c0401c040a043c20303814120300a0040014060000000c0e0f0050810703200d40c44103007103008030071a160b11741211200c45103803004103890541c6c15100d90040401c031580c280c4944607020364642c000701441c09800042c407030014030003841c0c0d0541c5c80242c107a10400400f96030043c922900c08162201c03155040c5080d41c0119a1a02d903814081d013088030051001031715502c041e90455410005291316584c0e1491302900d4203d0440792049002804900084c1105001015000162060303509110708860622840b480c100f00311006030031000c0042d02000141060301e05203010600918029850400350f8035682e00355961075000324006541e4000401035002a100b40682204501c0d640d16000401c0c8130001e840750081e40250340301030100060301411540c034481140c000390782c002900702c0e0b40307555001c080740c0765001101c054a4502502c000c0030b900d294007a0807201070312501c1c50354030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 836975503 1250 836974253 836974283
    0x301061106151c0b0412090e1504110c0d1e02011a040e0a1b060f02030a1409030f0a082215050f09031501171203011202061c0603030305010e04 63
    0x2040c0401d03d103009482006062919011620552415100314040d2400d946c0490600b4001001060701c0c2d40302c103003034240c20420f0001c40c44400a02542ea02800c41d00424021005d0003802c4091203101c44007100e9101d11798543d030046030441180405044151300d480c80f008410030040e0f01b030790500c1c0d010740c02c0c03500480d41014180c138140e400126100c0c2c2150460b55108110313500c2400b0110b00d03440d540c071070070309040c020080315078401d0251013001058030155040014081001c4e0402c82441c1d0b480001c4000420000342545081101010a0001400700c2c0d109110a00f08030615510413400c2121000003155014000e0320740100742e10485003100d00000360740e0f150756421039040d00180c0690316808400c000c51071250354104503500701c43c445003140212551400f110440902040011048103401050010280035900001d03a411101d01c0c21203203003070000e58400183d03a407103400c2d010385840302142d42200c00c50381203511000680384661010406642c07128201c000f41742003220000c120f00c260810310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 836976753 1250 836975503 836975509
    0x281101020f091c0206070309030606060f0c03110c19080f0102040612050c0409050f07120b0105070204050903070501141012151d030c0a05060a0207030206040b090a1205030106110615 80
    0x10500800d92010003410141c0c84e90000300940d01c400c0050300010341215003030060101c584030740001080d550903c0030b6440b00749103001c4d050500c16500a824404065003c3c4080101801a0007000000404803a800d5151504802c1941c0305801401d48501c2080c100040e0b0301c60500c02c44040d24001d071140e0081310b0720400c0120250500a2422138005024880000c032250640038070346c0905c12800d40844281742422004140c41e11070400b0290160400c40300481030390308502210701160f010340c2d0104890b40e031100f03060700e1481000c0e0300a28641c0390010a1065030040c140c0719006500d160041c1d01c140e82e80e56007210822110b1400905001c5100f00c400d04889640d510400c02e1081c4440101c42c0c0103940144103056030042e1074020610340003032100b04104001840400e40c801c50109007103017071984c3c0c0e0702c2c005c0d9101c2c0000c01c01000b03e001c1c10080340a03200308201c1d01010681c02401c0714882e680003d4003c2041d0820b1281d0008501a083d03240142440464480e11550070f049003440600000810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 836978003 1250 836976753 836976769
    0x20c120618010b130606030f060b030612070806150108010803090108010b030601020f1506010905040509070504181203060e090604052509060b0406080c03090c0f06281101020f09 78
    0x29085207503603600d003c9811901d031541009a803100c1c3d50350010f00c042c540400501626008000026180d2400c60207003c1e008003003080d00d4100a042d5048440b45052034251464101250000f2035640b141e102001003007074410900040b00c440a80e0b07100c01c266a600c41084d0782c0e0140c0d00c401408190800018000c10660801440c1d201c181441180c0c424444405480c1c1491100184100190003040401803196003101d691780041c20140e0b010012444d041d82035a40301e05241c00b13122312454982190003c8082540c0c81c081c0250340115560701c1081c040c140c0540180250311606800c00300040005800c8900490351034411500b10340034119018a13150b201c00000b0450607041010501907030b010a41d43c0c1113202e15405001100c030030300d60b00c42c1441e501400c849002803a40c0001c04041041149411002c2088400940b06403503480c10a070b40000011040e004145510021201c5103107901c1e07144038203002064540449072200604804000e540318283d11851541a000301c00030400030000741402c0c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 836979253 1250 836978003 836978041
    0x312020412211b0821191808090d020d02060d0917071e26090f040b130221280606020d1809140403031b2001090606080a03020c1206 58
    0x1880101a410200b01c008074207065440c00c0302e0360100c00c51b000030301e46140f0804403840c4826407490352802c0e055441940504c1307008642c500070f01380030941d201152602d561010205500501194603403901c6002e010080c000484242c0780c4006031071130404864591000c4503103c0350403075560000d004010508d00c1069200b4001203800759008901c4280e80554103089090b0f2082c0e03091555607841400781040841c2000380080ca20681c03500515042030380c0c4400203614402000c0304096201e401146690061800030030803820060b100004214903207420481d0404145814114004428001c21000044648500410025a106810701d0580c240070749403510450681020324441c4644171901c001c20b0b541c00c0c02000240e0302c00d180500c001c058060060380b200001c04245010b81c20140c41d0002d10350780c1d0400c5008144894001400c5280100303400c40c15099401181c140714083c0c0e15082240e030b61480300d8050303005005100e449001c0389040e20300c0c080509a60030043c00390303403140c28045000b010504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 836980503 1250 836979253 836979277
    0x1d120913020a0c050616032003010e0910110c101b03090807050f0f0f0604030504060e130e07061d030d08060d0c0e2d040312020412211b08 61
    0x6100399001404c10000c1d90b10030454440d4241300381c0c40303541d4090180c400d55084c06402141c42000000d0020003181903e044035000810510306440f001009820b0070381050f0031056903030400704120682e04800c4024102d1070004811100280c20455101c01110b00c440d034061100c3d40d0030300c84900100c1c402d401c40c2030554090b09a0a1a01002d03131754070361604106210409086e008450004c4a1003014402c0c0e0301840001c130054025490a950001d04502c40e0340140c070148a9425041c0341c2c903850303543c188240f410300500c0411203010818030302540c5590501c01c020004101440501d460039044181d052039981c00b500800c0d99403c020025680c1d05030041c651504032030750311445c2c0c0c040703003d01450100404484410090608180799103401d04821402e50284c0d5890b150351003005119403941c060751041e014604a00481150512000031388101d520456035040000200c6007440170300c40c00d071303e14024541c1d06002420307020081070f640c054141d4051601071420084c0140810741c010001c0940e6990f00f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 836981753 1250 836980503 836980517
    0x6070c03060f020f1c0b030a11041e020d0e010c020c0f0f01140403031707030e0d0e0102160f08010e211c0501090218090610211d120913020a 62
    0x44644040c680c201c005c2c8510300488041040910758614442d443c0914030550181509504989604040800c501403d07400741d6510113031000790440308039900d40700c16240307041503542c0c0010140a01c0649503031000280d40703502c0c107103660019900000d00d0070811400540542c025080c88800c010b400860b60510f40d040c850070301071894650340c0c240000c2c00514400d4841d41c1094207015118404128020a4241072514003020341ea001d0000042c070740201149031500204400c03800004030f09105040002001c0881041004214500c2d00303020030042c0c0f40f4150082002c40541c0c132502d6902c0401d600c00daa008c0203060306c98001420f1440040c0280d415400101d050300c040541010200d031000d0340065181da03400700f08444101d0440c4a0803694082c100e07900c0c0400d0900078001540b007510802c00f0000d10070720300101d40031071403441702821006446190030042040c050501c075041d58006203034504036000f03011103c409204134a0507a000e080740a05803001c001038140031000254000310005042c0440c0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 836983003 1250 836981753 836981767
    0x9080a0327030f06050f010b040b0d0b0604060207051201090812090703020d030e19030201120b0d02040606050301060f0206010f121b0b0418021206092a03040b010506070c03060f02 79
    0xa6405070700030b5201d45032030700042d50325061400480c0c1014006502d80004000100200440442030301c0030f80d0940d4600d1661150011080d000910707440c207045401071808103000540a402040f410101c89065450582e00845400c0c3c9600300c40361504000c0c15140c090140c81240d0481c600025131010404003110149070712500040d2070615008000c5001a032003000029460828605201d014a15131100034011801c6034000780201e80d04000742140702da61504400d03c25998454520360711a0042d00810806440780b0004000c1da00034007419000c1040d000340c08810a20000d403040c125103840d00e03000703201d41c1008030460a4056000068503000200c100c90b004140007801e0040c000d100d22540d895449260060b2620700b400f0710081c484925105000c0e80f80000054200907a20000480f9041c030103540301e424120050240c10891b21052900040e0041034a40c000d00440c0158000c108154041c0e84c0c035810003e040c428140700070007440f00a002000002c405801c4013036442da1100006d1f0904c48 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 836984253 1250 836983003 836983067
    0xb03240403050c2505030a03090315090b09031e03071706120d031506030603030206060d0206130303021f0504050c13110a0314010f050a03110102030712020c090709080a03 75
    0x441a15100c4844444040e52104c0c0d104903002e4000f01810340c090180900c0c1a10094180d288601c40034083ca081c461210345c913104564006030280d50702545120319410f000c1e01c400d070360760400c42c1d10454075103030070340c00402c01080041603a120f410f8079134960480c0c5c02c400301c0040c008500601b40507004800b164584001b00700070304c00d07100321b0301003036500040e800e01030410340d60110290b038407030340070f15160003000e1000c25404580f05500803000c0e254104100c03103510110301c6a00c669542c19681e11350f00343c004410140d000c28001e0780c2101c1c7d613100c00321040c054140c5608484040c0c5000b0040d034002c40250066051004040d081401c0d400720018501c00b411100724080d03803048020000281d66401d10016a0b20706054650140c10200700398803902d0300b00340106891100f280801b0f4646907009107965942e0380b080080b140d038103a009099442e80c0b00c420300069900d0040c140f4007445003032010005458148a9002c0f9402c90310355038002c10486119803001d64111100031009100300406400701c0708105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 836985503 1250 836984253 836984263
    0xd150306051603020406021b0d02040c0c030e041104030f0f0605090c0301241e080109030302120901050c033103021501060807050708030603101505040b03240403050c 73
    0x60098801181d10315040041c4407551045500d010141481484103101c40c039400510500e0203450b1800b00c2c038125042e0310019001c02c0307065038001d6005060000c45450306a1101c0f0286886200391951404521140200415240c8071020306082407400d200400105994400d044803a60007107000d020000c0581c0c56038425142c007190200043c1d8000c6249907010b0a0910583c46094005200007801260700d000b580311000307640c4582112001c0354900c0420806c51485c510005001400080010183c030346805800394100d8245000c4220380ea500040091006010b80f610030240007400a18658030492040305d01c0b1888072403049170600c400ca03c5e5440d48001146003844038020f400411244646041d03010606030160040401c06c810313801800305094000060302c009980c007004441c2c6070b44c1d614010a240401c0d1440b0040301c01d081001071170209114041c9030043d5102660b06104a507140014907036030b07045551044400315050081c25441c001d2a93380780f6005403091524038900301c81c848a00d4500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 836986753 1250 836985503 836985509
    0xa0e01050702030c0c0909071a0c0708010504061a010c140f060f0f1806040b070e041b020709060e19180b01091a01053106120614150d15 60
    0x56440000e00078000c80c410070840c108a48101e81024061800d00e511a48a06040c407035240d10006210391102c030880205c00381c0b075410ac030a9080f2455035554246140c00781800b50f50a540451414110004030201440c8000c41044103858070004a10103990300d065040082c804030707500f8014401e1200310000c5c18805540510000044c082980c203014044030502c00c4060440941d0b001400140c6040c0b590100da56940207400c4402039513184e40301c3d1400d0b5500850320040341e034003c0c648121914545200d44020b081c1c81416802c071544540c0f1544070001f01c55207401910050100761000502103402c241660b00512036124001ca100b421284c40f45041d40c202200460740d20000000500019800d84203400202e403003950116018a64400060b016208002e81030a07246202e580009403900b081c080d208071040031015130380c0a5030382d030074004000c0381d8050a404900e074245100083c1040b00d80f1081d441c0c040c0014080c402c00c11900c4a580601e910600042c0c0e14103031038030420070b0300140490b594002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836988003 1250 836986753 836986757
    0x150c0709021308030702011b020406052701080309131d030a05030f220201180510030212010b04080304050603070c020405180c120c1c08070302031309060b070b0a0e010507 75
    0xa640d5059a040a401520b0300600c0f0194401d0056101607a888100c00704610303a80200c06241ca000750010070050a06504100d42001d00f041012045010160340070743d08140540c1c25420790791f201e09010b03891303124906440e540f0070152800140000042d521680ca0008646200c2018403035040a0a0850704000307002d20100300048108200c5801d5410441c3d0301403460b4541d12302d4103c3c0c0c030450301c170749008603d03000e81009800300466201d002100d10760740207031030f000348260248614202c00074060340c000b003a040c92005080740005200c0d6851011398055030108005141080d04100070702089400c020440020007022515100150701d89114a50007080305040d040381c01e01c080d0480900c0d0800c08010030703000c0d09582080d804120000308640c28000d07412903481071629504050500034002e04000176115020018030303802050740000c01071140c0040c03014010a1203a80b80c02c2e10040b11014450680c410100b0801c040008071a14200b0b036101d01003000000e981c007003800b0b06500b102d00407108140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 836989253 1250 836988003 836988007
    0xb01152a0c0608070807050c03281b0c0519240f0f1d1305180105090601081f0f090f02010e042309010e06280218150c070902 55
    0x28000a4640342000d031815051265407404c140c4002045080000d04590410101092903806084144200c407507641a1251602c1c085141c4e09002d0300441070a41e0b10700c04204111180603100c401d10310800c0c0f0311a003240030506213515010a006c060109002c1028400c0c080d06000b049070722400442c910403410304000840c54452404010f80142599076400d01841851003000800ca984004113010303030102440803031254249480403648002031568000807060030101082070b00b066612005e00d40c2103c0d07034004e10998450150946d111b000a00591540390020107084011403800000c40750044070340c01300013806d038540c1e40602080750000b860440d14610403c0180c8150361b403018400070b4802d4100e40420a210145072100b114100300e0710140c804101200020f4020b41c401c0d408265100510819919a4a00710a801c2610011040700c03008141000605088140700c0d0300c2500d4a030007168100b295412000c404114980503a800701564162041182030480c80003030003190010850028056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 836990503 1250 836989253 836989337
    0x2190602010f0b0607030e04020c070603020304050c01090806040303090c030222150b0d050417030f0f070503150121020c0c0108010b070b06060a05040b07080918040b0115 75
    0xc1c25a040b903004806050b09041a4500d10303a07410085540b025403500b02403040a0800c0c0120f0042c0c0180e1645102034002d03500700282c09600740e0000c52165206000717072122800c1c02001581c0b06000c0c4e020703d0322076502c254001000240a41d1054060602079507203800d642d6540c0d8001984007507961600a143c240101d442500000700740a041c071612000d411805a5909040c0c00c1c10305800303583c1c103024901d45c45401140c06d200d85201050151031740400d40030303071301e2901d2041c0a800c120301759840b03805500301200041200d0b10480c2528061084c580104004440000044807000c0494000c02e60000c2280904ad2848485100403c100114000a80501d4451034009058000160310021440343d0400c4802c001480798045980e000600f111480d4803400e04181c202c1c2e09018681007454107680020b94207040c0005800a03200c900402c4400700f14013a01c0c0075800b104400141d0780241141540d80051000c1e01a05049072010031207460300e00c03882c1c60380704600074004488190480078290384c00c881ca = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 836991753 1250 836990503 836990507
    0x3080a2a0305070e0906010c140105072106141e0d0605071815050f19051309231f0314150408040b09061207031a0f0a0e13021906 57
    0x10603800103c5007014840c01d0300c181c4c0482e075502e200402c0c450400601904c90003c100040f0703480d00ca40c40750303240200420300e0000d102810a41000040d501400100c0014401030b610901038442660640b560007948861482c05001803029010312000341000e9650b502c400a85942108202c800d005040c0403500303091800014014184c400c00304500d410011105101000e46444103003401002c51801039520100c0203803580f179500a030441c0d8090120f40d0543d48103150341c442e010340720401c02a004e00005a90f02c1049004039176406607102643c041e02c1ca404841c688203034003041e9102111408401d030500d140c1402d01c1800c0b07da500100e5140010030691003000008118103001410098565243c905003915003012a0007140f040e0368800d031000468009540710700003a101c000c0e000a0fa08109402c01510140180441203092880703201c80030002d10051070609484e10b0355100c040d007041d138207a081c040041101200101807540d0300104110040060700c2d000000880c81d0340c0d030080e5010b003605001e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 836993003 1250 836991753 836991761
    0x16031413030c08430303020303010312030e1c03020d06121703090327060c0d020f1c0c021f0804201e0102150a06030515100303080a2a03 60
    0x22502e50100c2c1c02210320386107254101d01c10f2002588121842c00a02018034413014145040d06514a82800b00100b05500000607505803845145100450035a407003046049590702c507804201944105105601c4020092400c036801020380b50144c641b008a08002e82075450301e9100043d500001e04c03a0304d042c400070707111059203c5056400b43e807440c02c0110546903240112080034500321010100c1e040a242c44d40b40070320070040c000d0002a00c94041d184595141d0041c003100c0d4001d40901034240340002c1e00464014881000040a504030b0308484504a440d1030305080101d03000720900380381034801c050b08070040c0c08a01c02603032200c2503490240340c042c16000c5040751108802c01c4032084a8407580c0d401d041000b422110305085102800c3c07449c0100d241101300c6044c00e5202512005204844000c1e4104100fa02e01440850742c14150858815401410490301e09040c040c0d41e01c020310010380b20b601002d410210b130502c0491140c1882c144803900043d814001300c50700c100c166040c6201501802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 836994253 1250 836993003 836993009
    0x71401150603050c07020a231807030e16060e010c21021b0d12170103110f0d050c0415031202010212011d0708130b0c030f0c0a0516031413030c 63
    0x800c079403c1988503030118000407800c1c01422080004202d141400c114146159010484009c2c0b60460aa5a041500788104019a05000042c0c14a10180c40d920000520540406004400811868130740760b4122550001c1200396070402103200c05403804200c00418201850210b400d00d61420144071001920b4400d07200d42501c000d542c1c903042c64082d981c5080b2084035042d0010410b689042c9841c5040f02c001c00c0c9140c0020100c20303510000f00c10310405111070260300409450310a0308006401c01c00c2400b21207800010020b0b80f05803a1070000c1c0c2007507002485050768040d04060b40d2038072076441c0400d21281420b42d40042c3e501040c8ac040c0c0d6403010804500504400e80b0807000149240ca1116203000014111400e1199040c00300b0032110380d072011980c0c040e8100c0300e011207600348103d02c0c4032141d005641074042185004040b4130400c040c44120b074140c2d00141c440030301e44000310508440c40558500240c0521000045c040d480301e1040c40208184420501e102d1607a03030561030104001c0c81290 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 836995503 1250 836994253 836994271
    0x32316030b030610210f050a03031d030304170403021513060e010e1009090603080904110c06040b041a0c1c1b080c040306092102160302040207140115060305 69
    0x341301058450201031800e9407501c88400404220700219051542044000201800074010340300701070110103d51001054443e65040c09282c800c8100115803001c01408240305400400c01b0400041102d214000402d1003143c200342401c4d66600012400200c280c0c06d0122140c0c001403040007210850b5031080904a542040141c04c560900003d14400c1e40350f41c414020701d03031030721413200c0f00d4000d890010060420000c20300a1540300c1c07500c2c5840e5001009054011410824900201c0076560103071605003540b03600401c0c6c25a216180d0051400d4040e009540c4529052170345501d000c10181c880788a1a00c0e01c60866880b4100201d101e13440000c2182617220341d1821a420001200300032100580e82c00d5440d20300741507110084603115500c19540028416450001c05e8402c00080400310301c540c1c5a4450110302c0000950410703078464921060f0140c0100c401c1100740014501540030b04141405100c0e140d010f1003079a07009500f100d40c05082c6000000000b06c0400c001c030350500400764488001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 836996753 1250 836995503 836995513
    0x1b0c122116081504240503100203041a04080d06150f1112070201030e0a060b120a11120309040606091503020405132f070b071e032316030b03 62
    0x4100801c0c950010301003c071000e48080c01c0c40032075510360700500b43c00e40390f113003a841800824046118041c1550b114050190061205c0c060030100b040c403e0f00c2c03140c2d801c40d0300754541d811600032055084130006d004448598083c090800402080d1042c040a0303d64400040c1e0351300042c51021342204184c0b1005010000303110184036501c00e000c5848ae814140c502d0072103486032080d200507009441211410007883c455820458244652600320900c1e82034251190110381c0012010f103074542d954400d01804030300c4e0351a107504a41c00e0070a2807010701c940007000d490800140100040549400d684a0400521240d6041c40141c1000280701c442e030903141021407038036141c41c0120b0490700d00a014004810b40d1940d200b0106090840f01c8402d940c00310b00c0c5160203030107124079001d90341c10410b0182d50082310040040c03030550185564031000c2c20b4000c1c06001c5d01042c090304a000c1c00c0c1280c501842d003418407046020321a420881c403401580031001e06042d90000d42c40050841d000850014072039031103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 836998003 1250 836996753 836996791
    0x171201170102030735091005060105040305030a080a090821070e0121061a13061b020906040b130b03011404020d0303090c05151c02031b0c1221 63
    0x1213112540c00403000a031190180d0080e5050700401c0c0103c810904051240f010041c6c4480301040c00e55034507910340410062a11141c00442e142d014078080100590300400c038140000d4068203800b507003c0c0e03100f07502081001c49a691a15240c00004e00040d9507185608c2c5078112a820f1007003182d0010603442c065620700200e200080800f00728140084c5855801f07600a9418445d5401c0324000e01050350a50300d800e80110400d0b070720b640c0002d03180c400400030303540b02103001c5125140b44080c0311070342e65022862009a408000c509100034020a41c05a6159005917441e01d0ba060b460080107941000005c8003c0c1c0a024103007503e00c40e101042c0421092800c100c01a0b40352503001882940614002400782e0781890940d1820304a40c101d0f95110b43c030f2410f000341503864207006000e680410941243c2030b40400e20f078902a0301085e00c40f60801103622a5101c56418404050001c0008460481d01d14250b2100031201e25032110100c81a41c0c0b04502607025110380364114641c0040383c1103010748000b40307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 836999253 1250 836998003 836998007
    0xa051809061c060b2107090516050a03091b2405041806031a1801050c0f09060f0703030501150516060f0e060a0c031503020f010302071712011701020307 67
    0x506180e0000040e8080365071030b410301c03843d070f03014510003503020340424030010a0300d6412140041c48206580c0034421404085049900c4d401014082ca20841040f540c0c005010001d440302d030080084c0200301559190301c0c00205122801d60985003c0f2170044084580c104034000b640e40d40004609004402091407060800c1e91201c1140e00b107982c050100030030a02004003107006030201d540701500c6400b2208210607110b1080c81c1050080341e400341c2e6402ca0035010b1981c0b03820b032801120400031282081c040c0003494000e200040080f4507004280c507240070480844184603401c03006040e00040d60351070041c401420f030702a20120341482d5040460030b02000e450491b0500c4487c0c0c500501650300e8003c5420030206507000000c800c0164815100c40745014801302c401010b00c0c011038400241050321440320303c244070f0189001d60313801803d100100141c0d00015000395002c0c0a00300c03a5142ca03a181c254a02c000b207009009201605d009984003545040701036201301d0903e020707810140e4810070900181c1c035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 837000503 1250 836999253 836999269
    0x281d190f0b07121b08090a0201080f0601030e06190e06010f06051b010c0c03120b03060c0c07081207030f170411031e010203370e0307080a05180906 65
    0x1a60041810645903110b26040712100c9a10781d1034100141480413145041d0f860b0401c0d07400d00c0150b95600049a910040e180d0f50300c006d105006030100d03a621010800c82c07080e02c0f01990307000e08181800706442ca4401009454114100c0e40912440f2940c007490ba0561214001c00300e80b4078185004040b40e505041c4030811109691140500b400750000b0091040c90b1410320751034003034151100070420010040000351102c4a11341c01100084c1e0811041070510348035220b41c2c507041e10040e00420082c1d480d400461002c1c0e000044622503440340c3c0100003640c030010001c005c40c122020741c4043d02d0351194580541a0143d181942040c407100c1a1891000c0c0128043d00342e20682107000801c1550b80b0001203030820f560b0291000306080707240d4044110450540040d80107002503001000d040800d606c0782200603a406c04c0d00300c220110b40100c00f200b82d10542040c5c40d13550585d03080d2494840e05586083c2d60fa0710007014079001c203c012070000c003903420440301d54800100c19505c00341c0034940480010411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 837001753 1250 837000503 837000533
    0x1803020f21031602100c020c0a090203010f091a030106181505010c0204021305090c040305060c0403020108310b150f1f02010204090204030503070b01090212281d19 72
    0xc3c000750b408401541c1d1082080d48003080841604005655003004000d4490440c2c41a083c01100c131000001040300e007d01c02c0705d0407640f642560108081c2858918400342014504a60f500000c0d8038004d00159002e1052400501417500407201c2d40c04490386d014140c80940b4505100400090001c1100b80d030402070281d012035045034016615038602c1d4903c0d41e1030000790070644e0084c406500300040c0f8140400180141c038000d8040780c030241d03110100c600940c4031314000280000c008002048045202000441d0404030030101c00c20388281141040050060318002500e112209900740403401d206090031800000041e01c1081d401400640882c14030305500c6280d4914010020505401344e02c00c2d4141c401501007841c055564981d40e0506d40c1d40da0b04441c005464107080d200002031440c6607842211403d00441304070441580d201848603d103460000b8912011340048446802080710314864410500305075840400107000780202903103000030380c140ca9160f03076604103050b8000c5000e1840001706 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 837003003 1250 837001753 837001771
    0xc0201080609060d0b0a05092107020108060d0f0303020712020c180a1409010b01021c120b04020c0303070801150903020a0e060f030f060108010b01171303031803020f2103 75
    0xb0340d10303803401040441070182d1000d0a0301d0384100500004410710b402190040d1540d0044480250031010003410014000c0310040c03100d002084800c0040d40281c040e1684aa0000c00c2c5040b120b801c2d8490882007903408000b18002540007900700100005c00488209180161008005c0004c18030b001c2890024480c440010340e118505c0020101c41c4150808907000006101021450510141440c06091540c1605003d0b02801089640102465000140548840e620020300304810002e2200410000b8841e80d086a020040590700020400086005003103039660080150302d410308048580f00a411203604000840d131041000d69900b006020036103c0d944443e017425160600040d000b082d4905010ba014040c61100c0b4402100210306c2a04881c6c4000c02030005404800044485a580080122050003600086a581c2c0b22004400c0e0450340b10781070009400c3d0000b50100d42d030251000f4100c00690014034450b1150005024900070020350a00c00303113600b62810320888550000418080c0703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 837004253 1250 837003003 837003019
    0x11090405030c070303080a11090603150d021c02030c1c08031f03050703030e030c060d2f0d0e0309011e090e011d071409100c02042a0c02010806 63
    0x40c04014400c980c11040d82004603207116540740f5018288500c100ca03088113181c0741080c50b100c0c1814201c00c541c28190014490351440d55140c41300b0995558000085070000815141080140c0700c4800c60031111408070002030141005204041c64280e001900c103001d00c000582c88034038000c110701c0b4100c3d0b403035102d03881644a54650702c180800000500f414202d03c2002c500000900c04041740000c00c0d81c0c084e982d840f5200c10510281980c8031a001101908017008120382450301140381e212030300d20b0314844880c60000b1640089000041e54090040c1c43c12500099900e895641612443c0c0c0c901c0042c802a6041c980030400181c1816000e1114405211411940d135142a00c1004070304041d00ca8000b582c0da0a5841300b20502600980c1026440d0000c1080c0c0859100780c052042c964142080380c02d00b0380340c2251407060041c10408501c2201c20b20a01030700381c800503034560140d02040120204060000380034202d082035450034103151030050001030056180941d07031252080390300000a4500710 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 837005503 1250 837004253 837004261
    0x403050c2b020f04060e0f100e0a09080d060b041d0112170706090302061b07020a0b13050406080303040c0b07050604170c0a0b0601091509090f060e0405010906181109 73
    0x604183c1d1000145a00034500a4017217038030009491807034040c0004801c0448184d41c1c1c4900b402d80c3c9009801034116603a035000000e00000320303640000c00b40c144611011400c15100710b03201400c0c0e501300d0f040741c1e13820070020400b402619842d0400c1c042801140070b126205502d01071081c00c92400c0350030b000d4048d88098100050305c00800080324800c030b80c001010031042401d070400a46418059464640510492141c3d009480b105020f454006800602016803240b070084902c41c00c0c6c2c03144003401c203c48c81894000440d50b99501c14800241014000b079a50392909181c0000d200046410420546d04c1c01c0c800a0b0100740c0c0025100e902581c00b2a843d8141d100340c0c40042c855010b03101c0351094034401e10150004201044039800c0c043e03202130b21101000c0f5201d00c441c840725190781c80180002102c2c0001000fa80c20300d034020002d00e4a0b85d0328001052600c80d246100f0308841140d040e68030380e448445410400c00a0b200e2400c0d0721103449031282c460002030b40d4400d95000158415441000358401203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 837006753 1250 837005503 837005509
    0x507021519020c1014060d032c0616170310090c09050909010e060f060d03032a1e021c030507111e15010f030b07090e010b0403050c2b02 60
    0x1200c0c5044054104d840000c14600e07010003910075204480c00400d006004241d607410082c10400c0303143d40c5a1602800d0b480d00c461011911304845130004140d100040402c0d5407601c0303440042103011080c02c0c1c0f5a9842d100c5080c490040007641c0c4880c03d50801c02c000304a0300003150f02000c402e6401c04007020610000c40d07001181d0995150f040300354000b0402040c0415640d055111011742c1d035001c0c00b40c8030a50b41d030311014020107008403080c03500001031b810003000013482503005400c10303030800c003104100e40100316903429441c5080d02d10070301113488104041c00d4004104180403041d443c07840140030400150311811a28503404900d04149500d640101388020b01a40d0f1186111010b002201c62401702d00c200711000c0d00d0000098410340c0a80401c002c07418440b046440c0c10f9a2400b1005007d151640c2e55411207840c000703145c2400c010720000c0100701c0c1804013480a0081612194454a46056051182c1001c03100451544144c520780c4074981e0741401440b209a1000c400d0300030034019001d60006c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 837008003 1250 837006753 837006757
    0x230030403050c01050a0e060f060609120f030c0c030f030301151b050a030f18030c03230d0305071709120307020115150e15070f020a031a0406050702151902 69
    0x10301c0e0f46942085d042000034861644054450301d280400c4440036200c3c0034884640000c02d40b5020f4000200b00701043c0c0c142000005e940b00c0100b9a01114441c0c1c818a00e09800c5030064841c03900c040d0030000e00000c0c5841c9c00c024a000c8030f121a0060f6141d03514112101106886901c004401d01990030129500080510600c0c0150380c2c02c50144c4040c02d4040c50000c3c140300303c8940160210f9282c21301441c107407610902030303c01e50340d10002052807642140c881c040304a03035100700000c2c0c20411110303080c46a0818801d8020241e281e8402007204d050070030f00034025aa0000c0e80c00030000845c402c004c51200001100740d600070783c8800c110381da5102e00d08224054480c12198074003206942c88009030703c0d0b00086031030300b4600d859030b42c41e02509901e204004001071000402118504c2c2444040c01260650000311005403006200040a5569a82c3c6c00081c400200d2540300760501c0703404000070711045005040d40006188042c10a0240040030513100e00c1c030180541c2003802d01c41081041140d1240c0c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 837009253 1250 837008003 837008017
    0x3060601050c30192a170f0c010509100c0e120c0d0c0510020307080406030506060918040201110601120f0203240103030e040b370b0901023003040305 66
    0xb2100780c2d50520410055104086140c24800154000c056a00c1e0741c0128003110070402c1c058a130b10400d21105445155040c43c5c8003d61100c140f06c100011018503003081c00a041c04506500081410b02e800c0500c2810b1840391855807900038100003a440c030340c1303074007003110303592414111400c50156143d00855403034403540904051301b0020090301c0d4818000b00309000b4040301c0c070480f078100034114100e00c22600ca001d007500040038ad0005100030f21143c2e0080d0095075100801420607410500700800041003521480d00000c186c460400500c8255640b280c4c2032450031030100020080b952601741820b00310410007a0141c0302442c4803141408640d0184039240340c50184440038442c800c0f00c06403125030303881e080c40128003003803e0380310840140c200f902410800310401460201c514a4103039855106c0441c90030000e2089000c03445440c0461140c2c6481c00240840d0030f80103481ea4217590002e403a15a01c00c8085080c20503000b810400444400e44070400881d808a400e42c680c1c582d89000e40301406628 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 837010503 1250 837009253 837009343
    0x2010605040213170c21100c0903030206180309100c0204020d1d060115111009060209040614030a0f03091502060412110c040b010c0213050603060601050c 68
    0x194402c810303c00710744100540c0c07080514801d6180c2c1c4a82e0040e0381c0c5d107894561300e40010b139103400c0d030341d41944400b104440104104d064a0300083c262003014100e0794803100312400310302000024000c0c1541045501c0e401845070036140300c07005000c0c0c0042d03500e01401d40142d1190308030300c0140f90003e1044030240d80d003980c06442591562580b446200c0070700398045125030034111080c0c000c2080c0b4800103565040300c180c03282110b51103143c00d0048500a0b00c0c44904405031040d0031441c5520b804911440c0c2004d40108401070b16030302e07080c003000165002c2d58810510302070707080c802c0680c0c0d6401143c032100789548140e0312500e040640c601900c081259600208003403404608131110f8a130081030452159100390b130100700d51001818140d465083c000882c0340c0a5018569048050606a010042a80701410411035807a0140d0000b810030091002c180062510348007030048604041203040d0300039000742801420114801422941e450095507140013030303890301208554024640e0903101284900d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 837011753 1250 837010503 837010507
    0x20c2202040f030f2117040218090c09070e0a09050a0902130609110304050a0f0204061716050306061309061b02010c0210050c0a0c0501020c030a110d080c0910020106050402 76
    0xe41010b240f5410322444c25503513061303125850840c6504800180111840715220100c0d111075009200045040082c4126042810314000000d01400d0082d618416500700d0002c00b40704036014140045c0d040c01415000501c81d680102c403600d540d03005545e07001da407010240060301e641c03011006030141c40c078007502a40042d441c488003003034013400781c2080040e43d403414424070500c940c0810142032403100b110302030007640082030b00c0340006021601c0400007600003807020403070740d496041c04150402c0841d60200244d100c060b0340340216a140081200804044024100614050021503040e0f484800e02000b070f29074034014502000300541c0502044d46121301e0f10b03120181001c40c080d0007002141440c40140c0b191420f4044103030302c41d0240a1040e59400d41c0541800d8500c50b054906003100b0b001112195020f1204140b8640200051b020380f9800b0f075a0440216a503c105a081040d0100c101c002c0100e41c1081081103c50030045403242030094600241001001c0d03001c03401090140c0202d5841400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 837013003 1250 837011753 837011759
    0x3060e072a060216170f0403030e0f100f080f040b16050d02030408040302090f04110d08210103150c02030306060f0c070905061804020d0609050a08040602011506020c2202040f 77
    0x502003441c252039103e9010809251104000039056006e04024140910720401c010701c0000d01c50000b0f8000e10f000945180c110b64403a400042031102c219806c1400240446001040c0d60b9000c8040c580110006948683d41d092640303d50101d080300030f01500449581484580c0410b20074000c64880d81d6040300d0840d16400c00c0d00e440080c1c0e0f0320502c0181c1c40780c8161000f10f10401c10030310f8043c0c040c640c04405444070700c4035002408144051518183c0b0039103010310260304005444140c80811500b80903039084258114506103070408080701e41d012085140c03038003683c01c2c0380c2c000080b20342100c3d0840c2c101d9150250a4060306951058641921041c01407450001c1c482c1440c0d0022800740701c0480760400400000c0c03600c90940b0b08101c5001e54000d001840c2c10340440e8a90b030040c0201d9000300140d41c2000d0254071420f03010740c003a9010100607075403a0803140da461096501e1030060105031000d8100c81c098600040c4021120018580d074003407680000c003102195a50407a0300600d030306100c280c04256 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 837014253 1250 837013003 837013027
    0x5060109060b0a0f030b150d0501090c021513020409060c0206042315180f0a03080a05010b030f0c190306172d1f090303060e072a0602 59
    0x40038031038454190300700500401d00500b01415181d903071a040d039500d41d03501c01001040340600070b012485034200c40940144849500094020052200c50110200e81c80d4903052003102200e88c488903010443d0056442400031620411490b60040300441e02e984d804889800042c1c0148404031008000300d24044600303400030f80115a8070b21960161548825400c03142c000001e100041d131084e4079840d04011709140205244d031401c150005600580d40000007440e1400074074107510307a55924030640c84003ea4808040c1e00042d41765002103145014003095240c040000c9440c000076140c04800840040002c6070540140c09071130f030306910002003a126061162001d80100b805000f0100c0e04a141b0024070a111400030300a54030a401494810492500248160106c2984c040c01d220600500c1c2c00c8041902c010842c4102c502c05402001070600410b280142c01c03078150360701c1031445940c0402000805a049075034a90320030000d040c0181070a0072528503401c0f81c006003078000c0c1000e00c0441c0080e4804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 837015503 1250 837014253 837014263
    0x4240216030801080706050409050c070c06081f05150c0109120905190501020a0213020904021b0d0201050702030f07020d0803040308090d03061a0a0c0b0a050a0c110312180303010305 80
    0x80d0103610b410400d42d8885540c075460b401d440c05014085042000100324010042d03001d01d80c00011707003000300c0c00c2c2503c5594181001c2030540c44140050140402c0c0030502040035549100210811002c0303000e00d01d488003254000401d11204607102c1700c0400d050010403400c1d0041c041c41a4465600c1c4582c000d0a14080d002003224003825008600952116901800000e540020b9610580017411540c55550130841689440065115180c0e001d12190a00d911280094941c40220100d00000e110a2810381071620901c071f84038604583c1441d084c001080e13004811200c5983c5182070030b0356200414004180c0410f446840200490000020041403582c040015030040c4400001c0c0c4584d54202034040b81980e81074024690521038100d007040008070604020940901607050a80440b841a1100d00380220200d660302c222940391000c00015608901c140e04151a02d401c00c070070340210b428546276480c00782c40c0041c40041d5940010855600c54194009054110f0400300d958940e140c1c60400c0d214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 837016753 1250 837015503 837015547
    0x20c100e010c0201090c05190801110901031116140f072d03171c1a01230d05040c0b1603020c0904050a240e03180105040e042402 57
    0x55180603030940c2e0543c0306000d4810440d401525540c0c0d07080c00e00042100c00c0c40c0d506400000703060405400107282c10b0a00400c1e40452003070141c540c445a01c08005001e950004000007038415003040306150002002410904013a0842c02c6104040e00f0f42e822540342c280100c3c00d0942c5481000c0002450703903038030003071401d219000c1848201170016070030344000400340d18003004041140c200509081440f07e02c02400d007080d1000294810381d0a129070440032904444108981c0e003044443c01059540c10800c2001306420340981040c1c4003002408400f2a80180b0140d10708c02d54480c00450180a5503030040400b9114404070251364074240c0d9648841c411a40d00c0c22000340c081c45003000c10528040000c1845181c00201409101c0d400e541c2d480c50344c10803611501c11400f03000200701d207080c5403403090120f8901c2100095688460518038000c140c669182124100181000180030510405030004d030882e920820420602e441500760000100c5240c0315040a24804940c4aa00040ca2117049801f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 837018003 1250 837016753 837016781
    0x415060e060a0b0c060a0f090b0c031e090d050705071a030109061203081504110c010e0f0a0f0311031c050121020303030115090b0f0a02060907180f020c10 68
    0x1102e030b844182c807580d801380004d01d0f8000d401c9040058507400700da4005140406403518001a411980e0780d80074001801500c004c1544800842000002c048560134141e01c0460903203003526610746407082035503504e1708e10501c3c001c0250205401c020808100403070710292120747c50503c1d8a40140e21415820b0f01b00744200304149080c020002004c102000441440e59015a40d00700240d4428190805043e0850307422900140e0751065012076040c80b401030090484c51038008280032171201805881c0c42501810351340c0541003140c103030000644142e21111060391504064018088003030042c0d00314007400703903446c1290102618900907981d05910150582d008910101405c07801d0b0310300c45c0c010048001000350903600070801071010600301c088100320034540380740000002e80c4032030800d0031a811031101c09007004404144007424640601031a80d01c07180140007002c030070740f030803040b954586646c05c20320401030b5450303c0c0c0d15032030078168044035900310740d210466208900041c8240d0050050004007a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 837019253 1250 837018003 837018019
    0x1140705061614030f07050306210607020c030106140909031204031701060206071403090a02060c0105162d140a09051014180102011b0f14041d0415060e06 68
    0x36440a0202900c4c045d01409031480b8555541200560302540042c02595101d1210030000d11000044050300c80030100c588064002d40c10560f030040e240011811401e44240d0409505100e840d040e423155044480f000c40300c4148a0302d8801d80203040d44141c007018400c0061030810071051641120140032084a030b0b10480354243e0703980740101c0c4c5440c402e0340c40e080040d0000d054170b90300607401005990000303030340c4043e60001401a800100c9543c44403248104a9446204000c040c1040e13000d03401c1003030302a0500b4540046100062148071012407010a1500941080083c1c1301d0b01c2102d04078404052201210b83c0d40205060240054100d03110704d5116100c9130f03802000051144508200c480e01a41c0e48038100304041d1601e8545d140d40011290443d91703640c020340c03601c07401040046525401741c0c03603d1a2000c10400001c04410b61031031503404101c4100000c0142e070b10301d014114259901c01003900340544a500c0c00395440e203580e405880005061000220390990b00004490007079104440312a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 837020503 1250 837019253 837019277
    0x42012010b0a081f0b040905010f08030f030a230705070c06051606020702061201030804030c060c020f0108090a0c0f05010e0d0803060d060b0a030f060506030615011407050616 77
    0x100e49442200070b079070300080d0040049100707801c0000c0c21050a0345100c06880b5155100c480c9910960082c0d80421003041d101c1c401000700d4100b03c48000007908810000c1c0d843c1c034011480348599403002030720721907050303a65480d030106040075500300a0540c080c4250702e144c242416140201523800ca00402c0d54609842c100010f289402107084902480713500340c2d4952143c50b50b45030b00c4025000303900140d03003210081100300107004030286c2c03050180d0700c200d0401781c5403815030802c06001c03451900075009105081510401583d00c02d40084021102460010341035502c1c40d5074503081032024080141042c019080c0811040130b079030000d41c103803482039a034030ba00c030381a503000c000301d16a811384041c0c294401003010406d10b081203c9583d0740f075030003442c001c10003241450102e101c2944550090700c102404004590030001d03e405140c1e0424012001440c0505140b447c138607a0b0b00d0b290070000d06022451001c1c050451030300341a03c0c3c1c6140c10609544141c42d244410b106691061700d00000051000340d00d103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 837021753 1250 837020503 837020519
    0x2b11030609070c0c0504110d2a0507020f090403052a010b09010302090f070507050313090f023907080721031e03020405030f0d03050112020f04050604201201 69
    0x426095404c44604a80c00d807170070707041c4401400444036062001000b00070000c0d440780680180c4040304540d02c6034440c203440154101d001c1041c0b0031404d00c10007000b0800790b00507940d1880302c2c400c03202044404100f6915a4078082d00e09220780300112034401c56401c150800024088501c50913001030b18001c4c00203d5600c410030900403400d0000940c0b04490b24081008500a01070359503111034a42089494480161156031a5070000d42002072750304ca12072018130210041e40603d4684802c01c03070702903081103910780611981c10083d02c240c00404d0507002006503038000901004403240389031000d44040390b403254401c0392030320340f140181d40000300002191004504010703444087c2c15050f548603900d02100c13040d041120001c00d4440c408258090101107915641403140700800203006c0010110713061445009019074505030700601d003d104a000d03000145e01c4e003400c0d040b02038804503000a02d558481001030014123007a11454056840011203603071901811004120606114500c54a543c0c0d81d2001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 837023003 1250 837021753 837021767
    0x82401080d080c0703180305030315060a0219060b06070b06030d050f041e0f140108100609030809131103090c09010f05060a030905010e2b02032b1103060907 69
    0x20756000180280001000784000c81c000d404018860300d000003806402c4080c00e240c12402c0d80058940c1c0c0c0001080c050380c101084080401108160b51050404c180010041e4031041c150021605d0101902004002c01031541e2003000729000081c10706884215600b050140300300304565090081c4988404039501c41d0140c015212000981640c0c5d500d41401c003900704055039202242101c490884c1d00c1c0100310050b800d110140030f0480c070704411148280302c00006018200c081d00e26040e210380312100b40200d55004001c2c405803504000802c0d5a07074032540108000900500c901d040203071030000c43d841403009170401135000e40302c08001c4542c0e10308901d00f08040c10000b803040c030b00303004200001044103040280241c084108207040c00075035400749403501403e4980000b80012103810002d00e8030078410440490702c854680c43da112210148492a000e5580c3c4141090420f010300c00c0408190f030484040d44900310b031030a6403814840031246070a010074580083d203005e88035810882c0010f07140c903c9140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 837024253 1250 837023003 837023023
    0x290103051509190b09180c011404090b060f0703030516050309030403030e040e0d030c170c0a08190603030203040303031b09090c05070f050c030f060c03060f0a08240108 74
    0x1042d882103031074816044128080b0b000000b00c01507150440d4103003075510f42c5100c40c407910180c0310740e102075102800c0b06400d00e040d800310603042c0829803002c014221070718025101a10000a400070700510540c00045850244400701c001e10f40c1d00003030001c00c0543c180c000f9401541d80c1c10008211001206050b1000c0c00112407070a215802888204046031103416807440540000c0c000080902d403c0e200c1c0d0b03003001406030450010030b807180c121000707081c0d0103510909500380e10442d401480c2002d961070f48451099400704020070021070040703500c0d0b02c5540403140030320190b040200103650f66460081d40f44c0e00588010b40120740390103090503021030f81c18040070f090425595509880f5042c00c05820041c42c102c91a4001c0040c240b1210f000076229404c219041c0e070048008190154184080500d068050743d5902c00a0308100184021070b11414190780c3c01000c1218650180b141281c00300e07030186010783c0050a5440303019580da26002441c0107944018026860b66107040c1e0701c45030815a2011020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 837025503 1250 837024253 837024259
    0xa1704030c020603150d05011a01020c0d110f0607110109050a081515030307080403021905010c03050f0d110d0609020a0e01030f1b11060a0b090103030c05012901030515 74
    0xa0324510040c43c00360011a800f210f00160304c0149001c00c800309942001000084038240c0d51824440721340524111720301000002403004042c00c07240040807800d40c0e000480000c0182c0d00075030752151a0780d10f142180381e102c074010304078039202c0c2018205100380841402c1800c2c041600440045000d050440076a01540c0c0e11f40000e02d10014001000d070951107000f0510304044071140301d0b0040c9070340c0910080010f1401003104d0380d12107045004000300307040841c07801802e40c40185130804c0030741d800070b0b00340c43e440c0d400d0708000d45c49400306001208144101040703019058a00070060740d20314991001740c104142540000c0003496201e40d10102244201000c00d0007040120001d003485600c6500b05c2c0c48808040080414121004d01c0001e41d803031440741d980ba0218450004076102c200041180c9584903007030500a205400003480411038a06040c00017400300000113580c00240704094010440c106414400e565420042d094081d0780181e503012224000390402011507d810704200c00711316014801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 837026753 1250 837025503 837025517
    0xf0a0908150f1008070906030605060409050705061b060a0c08090a0b1801020714010c1b0b010303120e06160f09052b051605090106030207050a030807020708120a170403 74
    0x19107a02d0340125004001c604000004607011840603414404400180310400d40480c2440c15480e06a05840b0000c04481c0103926010018003c10400240c031402c0311020f80d80f8541e030381c2c2141d1106801200b19900358203135100c2c010900c690710085a1080b540b40e0800e0741d81d8510381d03ca01d0003207612103202d0383c80a04191000300115001d07034041c600514454814400044c6400b64a5607029001e5000006192032030755100780e00030110350460b802c0c2c4a44203e28220f40502d204a6a6038903111f00c0602000c0d08100800f407000450140c2680302152240c059022500c5618125507850380c4200d84c8290300c03002580b049000101c00d8001c2c0802d00071348030002c114480d0708101031032281740706408200d004c004080341c00084000c14010300c50307022200c9200110144050900c414803040d040c045c1e100004243c410000c8a01181000c90b882413125854a4400e20302d0b101c0c10b1080b8a401583e0f007006c400b80c0a82c40d00c042a020300c14000b00103030001921402c80052001d500e40307109441c1110060049511 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 837028003 1250 837026753 837026761
    0x601080601020712060b090c0f0d110702130614030c010215070c081305040b010507030503041428050d02011e020304080d0e01092d020405060607080f0a090815 70
    0x64146254085010702c101e4280d40c1ea14440042e4412504000751000b0b80e9030790800300306090100030b49038402c02d0650307404d1804414100074965481100c40801c0074580c2e820320320081d441c54000f00c407546c0d5002091140c1c1031407a005040000e003400c0c80390804e2060342c020003031a1801c0205458082e580140c002d043c02d00c00e030107155501400000c041d0000c0082615900c030010760284043c06100081d0100d0720f10305030a08051008503000555800d061003410701443c030010f540301040b69407055014034400d03102c0d81107225041ca030810403102190542500740d8104084000c006401311518002c40c11540e40300f0448078260f0885685282c803500c2a99074582e201c040e240aa001135070400d10440c1501c0ca4005000400421580317038100034080344e515900b2450034840c0510b210b44a6001c106a0104170240034100d1180c03045d00b82000901954031140000d0065235500c007520005070308444c40c159254001408200c4562216083c6804101c0350b01c0003084282000401050303d1006102c241d60380d441e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 837029253 1250 837028003 837028007
    0x180d030216020402070b07021002030c160f020301060b0d050109020f0426150402031c08011802040f0609150806030318040b120303070e150f070c032405090102120601 73
    0x20020340d014042440751112080103803524401802620302a400c212180d0030241d1380241030070016410603803c0c500510501404907071040895600380080c842c0400001158600165940e003800c0001c2e605500e002c03130006a42d407c45001b01440440c0d01000c0013940c0c1c0b2030103140304038000c03928411606101801306103c81800b52a101805000380342c510286845a1612a860200320380aa40d030040c800303100303220460070b0400040718185413100406803180301d07400d00100340c510148115290541c041c0f40f4083ca4400560445001e06822100e100002d0f480e0000501038042a02c00d60025040c205000721410740f14a80160191000030051883c0c90403030301c1d55003d01d0342000c50440e44241c0c4c90784c00c0d01d000e41d14416080c03004e03030400c8040c50b140d113050500601490200d102090141001060a400d802c3c00c01c01113510307107420315201e00e48402007810a810324500a82000f043d16035615104a034200000c80c001841564104003400640c1d180b205403400e0340038400bc482400300340300700460322940c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 837030503 1250 837029253 837029257
    0x1c1101030c121a04110a1413091b0207060903260409090b06041b02060c0315060a0509040b01050f1206121e07050d080301030809190902090405180d0302 67
    0x80250700c1c1c0204542d003541d02081c1207424550b540a0521440700340a80582094060039001034000d01c504d50400e00440e1003d844181d1008141c014540001002403446c0c0c00302802102804600e4010440416052102c1010140c4950741c00c0142c842c100000070190311901e90308084da503110900081c4c0c251811b10700380c100401407294410464061001098094080c030900181c0b90091442d0a00c41c20442e05000403a4015190002c040484035500342201e500052070a80000710800d00c81e0f44c039503462060240051001a4940d40b0030000604d4004140e405400380001078800c460801400040100640d8140b0400e4034031348003c6010710544c001504146401d41e8480d9020b07008a01c820050740303c540c18281c0000801a00d00100c001c5411402e50402291010b4081950020140c0c4000e48619245020501c00241944070000b0540500c1c1c5408001d00c4040300f503150a42400c9840c3c0b1040d0020390444102075001d2850000002d44040700101d8846810102101a00081c452601c00718041c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 837031753 1250 837030503 837030521
    0x31a0610201507120b0405011202012d020303310201050a0c1b09050c040506190e06041d06010e13091b0e06120102190e01110a060b1c110103 62
    0x380c0512400e0180729682c081086115495540d50030143d2021402c004084900c1d11210b180036901d400b0040c403031008100182c000c899024286501c54101e5070100011321107004048141050065030010b826603000400745028281c2c0001d401660540c0701c9165507401208040690503d02610100700075500030002050b00052034548200c1e8640c180d1183d07010080d40300c1c002840c908089508100c0c040080c0708650300512040030140c6032a260000203001c038000c3c0440124403540d070402d28070703005002e480110904000130b01b605d51120754850102d04810f41881c101402c0940d00b8001522a6110b52103241012100607d00290210103001c2c08009003814074084440e1901207500d0420707e41c0d140d00f101e006124005034424245070a4050010802d8003210b01c0304140c0c01405641c0c6020640b00e10491042c0042c0307002c034219014400100c8443c1480880c083d0706000d84082e0805002050308040340e00e080c01d464920090b00032a60303c80d40c40c1041000135010018000344d00f4490f40c0719410185407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 837033003 1250 837031753 837031817
    0xf041205070503120705040914010b030a020c15070f0906110706050d060f09242405041815050303070309170106030203070602030a14070209060f03030f04031a0610 72
    0x50804400c0d2418914005545c40c0d130200e1000308040180c55014041c190900641000c040415490900c5048203400007400c181c0300c40340c02040e10380309148108014404990b48410943d002d060110014002d0702d140392003440040c15482e400b20740a4095050442d20302c2d040c800400340103160641c1185e99410086c11220b4407512804000381d031004903140880a0140840c001541c90031a101884407038071a00c12215140c000003404020701d8040c20350910580b0340ca482d0501c600320078008101c900b4812504a91030640e4825400e014041242c2d104284495481010f4200c2c83d403200c040541d64000c0c850014000740342180288100d44900c18446003015944002081e0f59481340d00184c01c6c000d541c1c103c130b4011381c004900044010342c000c00c00801540c400307410034076000c913680101d4083c440017000c980c002c40700c0c0842503409440c1001141c80c0296007001c150346a03a201c0c50304009452030240e1702121449030328041a654941005840c0d045402c03521030070b9404490720b140e80c0303070314a408030038442c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 837034253 1250 837033003 837033007
    0x30a090c033f112e0e0c0108070f03140c0903010609021e070f0f150b040204030309050d0c1e060e120309090c04121103061036090308040302060f041205070503 70
    0x451900380120503284040154001c5403240404c1003020448001c0303910010a988502d00038030660b40c02c0b08003690004090324010807040a94a4190301a0420700f05041d5140703002020031036580c140c10090807001004800a206440d55449880d060f030084c01003a0905481f07200d00c84c1190ba101c0c9006026080c407595280c1d40e988600c1d1950030541001c1007045e1000c02d00e0741c0020481c5019881281c036074441c00c80e821810141140c41c020001c2086000f081c0c001c24407041903405100c1d0001d286002411564511276a100450224400e206000e11035500411442c0702101201e1a2000116040225072001142418030030360400141910151841c11032000070000800e40d181004a84d00056000d00d00702c0151000c04014107182420003170244100807000745052180c0c0d840c5621580041d20788241e40e1580c01c400329002100100c44600d9000698075251450b02055009030440b03104900076002c1c0d40003a0b0741c0b01103e4141c1001100c00a04161090346900380a90054016107503560082007200c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 837035503 1250 837034253 837034273
    0x40b0d02040906150f0807060c030512011701060806010e22081306110f1506010207050607060c03061e030314071208040c080a05070506030a090c033f11 67
    0x1d02140e10b41c22060302d80e591150b042c40d00412401c800b0000a042030500e02240924200c0c1031500e0300b007540a00010000421040e800745441102590781900c0103000c13840c0c0355695615008181c0d150024107a400d5400c1140c005913400000c21014100e6894030146040782d9a40e0003c400d02d41403c00141031b442481c4803150012404d60000b600703485580c031003011a01c900b440b90140c840319040c0d0351914560310184100740d4031240801e194420482440c20301c00705032202c40060b410104180c0107180c001c0d85c0841e980702484442d41040c2c0818005071020444240c9800b143c04988669002d9031190710541c1c401000028415001d90070101303841d01506003428100d0395003114908100a600c0002107200041c0424007031407105220050280100a04600d941c5540351602c0d0105072140360722409010001481804294201a042c154451608503401c3e0300c2e441c0500d1506c03144880072401003c4043da03040034402d02a00707004040710901070f03080305903581f840c00c9481080e81e80042409014114400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 837036753 1250 837035503 837035509
    0x100602242d0403030207050613080702010e01091505030103150203130f020406030209150109150905190e0108060f0903040e010b030415062c160c14070b040504140c09040b0d02 77
    0x450040703100755005030751446c050804a141c502c2c0600030040c02d05c600503400000812100480e084183d0a090143c1229001030050784d084019612a82004090300920103c0c2544a40218183ca00c20000c5410800c5224001000c900013102c610701650301c580740280201d005010b58200f450f1000340302080749a2070740c0c003040c3d000400b50740e02038216039120140c202941e00b000c3c51502620685c6180402e2150142d401000e4045501c140c900404501c1c2e074142089403d0021407000d09036070f189040055170751756040703a950102102d004009001c0b1030f010942c0e802d004011641140c907500780a120a03424a0348100882d84003401c00c552019105544484017103a80c0a180010b043c44400040d14610248580305c68004510b0f038030b0050a10349003006072042c5810748040a04c0e0301854285040f2299142c01c0c2c100000c040c40c0101540301d014000036450207814001c10541d03405071818482c4c2c00d40c188801050300d0058403d04405c69090259115504043d404880182001041c80040c04601d8001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 837038003 1250 837036753 837036841
    0xb040303050a02010c0305060f060d0e060403080919030801181523061204140a050a0b10050402030f221a04031b0305040905060f040510060224 63
    0x104401052001c02c854801540a2144198064840c1424041c500d00300c070000341400117402c80703580310b24400f040c03030074400301c00e54042d5200c0d104c848201c40f080e0609047c09008104121002265482448a12180110400c400c80b845992584501c40c0c51703400c0240a002a6011b951940c1d1455078403295603051110b26141e8078000d203080303c5003944400d42c010503c0b901e00b81307070080c842c010402000303c6d8500001c1c500c03016600c03070b030010b50101025500601c07071818414001e0300509944541e0851405000d80510321501803918940c10348016a80c0c0c0f003c0c84181d01044564825440070b0340b000860481103032080c4800f45451744e0400c618002d441c0e031184400d091500303c6503244c011300c02c1000105a000076081c95002646080240303486e0303840c4e070020081d102e02d01070f4450f1140c80d440400d0290f1582710400c604003100410920480c6441c2d6164943c0046900c07844005100300c55203907101c107450700302c2402e01089901e622042566004108880c903801d1064000d00340e402c4040100040c0c8403111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 837039253 1250 837038003 837038009
    0xc070f0219060809010209030a02060c01151e0e0c0307110c0a06020115170304120206040b0c0102070b070e0a0605160501060807180c27030507090e07080c031e0102040b04 75
    0x99251039070b4102480200650001842c6280036071040001c0d020b5030f500080c0100c0040e038101d07960740c0d4a2242c400c83c507014050800c03040303402c109000d5021841950344000720641c130011520f0a0246583c806080990740c1c0107030380c0120b940000300041010f00e07105e001e2040b50341803080d0443e00b15912060108081540c103034000d40040c1d6540710500d0000c107036402107800405d1141800e61300c82071006400c0c0d44034400c2d40b02e24917540c804880001c0840d1142c9054500820005a68940300d404a0001e54040e600c0010220f07100c509500024914030300030341036000c03030000c0a0401407882d0b080078000e0751594404540d03205003100043c2041700141003400f844014290807806004480d00c2c0114003640364045064400020781000340b0f11030341c5903024a1404289201c0c01e000c601c0b00082c9040146900607a400207451801011004240c100c4c01d50008035003030840d5401c441280c0c0c4d40780501d41d101c0340d1050300154076030801020141c00945401d00600400c1524000510302946e4030320021803a4001d40c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 837040503 1250 837039253 837039289
    0x9100513020405010912080406120e1e0d110c01030c02030903012d09030822020a0305061f0b0a05091c120906030216060c0311070807020f12060c070f02 67
    0x15042c0103a50b4030450285c02002c0000000180c00303000d5603110b0b218003c40c0260403c012801000726001000d0750040c81c41607491500f69440c00c030412804d122801104640c0c844035105a201d600d0010344280502d010a611240140c01703100c01c000700440181001344081d4085100c00d000402d40340e6801c1c0726080307100107540124400c00003071510b00054078040f00d2690150a01e00412903002c40c0d04251029400030100100c4100302055014401c5060100700c0041d402c05001038002c4200940019181e00a0120007950201200000d0a46102040368024009451428040f400640d030090029050140000f0712015101120368045543c074046904144d03214036464203081c0c121a004244030740501282e1400f546060798488000c0c1440f401d03076500400540da0380307042c0c001407480faa00140c60104003110380e40d5101c80d113040c40700d02030f080b460041e441a500900b04000b50b01d00000340b0005589154007900140e5034100c2c01442c81c3d04602000e0741c1d18520222131000607521400e212802000903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 837041753 1250 837040503 837040507
    0x1119080925081504080301150507050105150102010e010b0d42183302040f050a0f060f0311040b0d05180f030d1a120f0d0201090b060910051302 63
    0x10031161604090001d040c0e6250200300600010a03103a0703040f41c7c15101403d01001d0b80741c0c43c00f40c0440e0a88030381c0001420952902041c01400d1014000b44200c04000364000d04c0044101811175080321000c1080d0369014280c0100c0d0310024060034000038076042e804044540d002c0c0e124a41c00e1101d205040780841d0030a144000b1501380c490340c415021100c20200d0581116000d55803061f10311000b4014010380340c9545185815643c1003580504179803800c03144c0035501c0e2560740e00303907140a00303c0e4026248140707c0e21101248000c5e8414040707044500d03642c0e80c4440c4c8078508106500501c000040c22413498800c200c041218040d000c01400b0780ca0720804006281e140115a03c58140500300b100840741d00489982c0d04144000000d031a1180450f0074005205500b00115098a824a40b80190042c0c40c80040d0044000040364027152183e208003079404000203800200c0c00c0340c2138035200a00600e0707450040341c141d06101c42292342c801030601990000c107469100240640111141d034035400c03600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 837043003 1250 837041753 837041759
    0x18020c031201031208060f091b0a0f08090109050d080c040b18120106030c060302090d0501230f01270b040510090b030609031801140c030d1119080925 66
    0x522a81252001034a041710f468101800050313075072025007a82c503204402e104041080503010564503408959a04841907460b030107880e01a1805940c85d007500c01003010b1a0008410741c0060142e0588950f010018101e1059801400e0340c1c44074000d0039a02c1c03868011f000114100c40a070004221881c1800541503480c0050070030420003080344040c800150341026410400100140c0d404000c0d180300b030030003507255040400428540341050700064031541c01d0084020002c0b0001090144031108541c101225a0300d10880025601d02031103000100b0401e181d1013503800d00351409025050500e0003001c507585020340001802d0310415030b000f120343d010000040106440500c03410380000f0007640684001e1501811f061740b24013404152482c139018054020038070341e00c42d07840c018003c1c60440c03a807520b80d441d00c45a030b03980750030401d07100030010301e0043c46801402940050761401c502c18034210343c051214213802c170780303905000d080041d452007000d0310041035801700f2103103d40d284503907031a01603503511b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 837044253 1250 837043003 837043013
    0x90c0d0c1e0e0a091203020d090204050c03090c0d0b0105010f20010c120603050a0213020412110901050d051c0201020c340b070b09190503030403020c01140418020c03120103 76
    0x16001d0f0400b04241d180031402d034000f4401e854080402c14050030016160180c07103548001030440d000340258054030381010080d1449100016501600350202151005005d000500513039400c0e1030380182c4132181c0c5800400c0350f036100b03500e181c200030440d161441c5815141d03808001810260805809940d45407241004103540c05031070040948980c400600035103255807035031a1608032100e006030044481c0c01b20b92000070001c1e01218000c10005d401c007211840d450501c40e000e0744000700854480d640c0790000141c94a0400b118110b40750704400a042c1000401e501180000e090382003140941d50248100046903605008104001000855130340d41000003070050322282d02c281c403200340341b04800e18007800b110b107000c015501ea00b42e12260028090303d40300b1100c1d16100905154441e00d66034030030344404100c1c01001075400340f4425000c80c1e070400c00c03100055a030b0f502141e41146030f10354140002c102500c64564540d50b0640035410051a0810262025045074849680c40764441c105000400c00c02c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 837045503 1250 837044253 837044279
    0x3110c04050c0f0d06270f0c09091d1603060f05250e0d030c1b051309020f03060702010204170319030b1306180e0105090c0d0c1e 57
    0x290215010805032074500c0c041c0e402c500800c100941040e00220712151844090b0344200080c01500300b41010f0029907400c3e0000b281044486c84540d9410441007124580180c051000030b01982d442c0c0301036440c14162544010f0541420002400d803490410036061441070103034841000d800d024002c482402c5017001c0f0140e4520712000030615181508106405d00c24008092000c2c400402c80264960f6205040311861030504c01d60350310981c0041034608041e04022181c00a5208003c2c0c41202c01d5164107040300419107219a40e08248012040a02c0ca801c946c4416030140c4000c08002800c2403481c046486e240d000c4500c000540e50025052103018015000f94211086040c010b600c1c0a50514040303004810005000041c03544840d007404c00e039982c44c0b603c080303e145d65540c2000043e41d0380300015079108484003407542081c500740380409d18040600401c2d1142c1c42040003403100d03d071000140240b440c076003502512082c1e81303c0c2e030229190103120040c01d08100a0b0404401050510541c40d00c8a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 837046753 1250 837045503 837045523
    0x206070e0109030f0f03050d05070206060a050f2809020313020414070e01050703030617011d0a020f06070512030c031e010e04060510050d0602040801060e060904061e02070311 77
    0x404040c82c0200006134900d1070220307040382d0240c080d4803642d07903525054034140140c504182505040c001041300e81070780040c02c030f4419101240c0c0c3c100f15070340d03d006020030000100c1d9410303041106c2c041c103101c504012005200039180b6414200e80126600c4081e4400c036081542d509121101018101c8154609806007a003a10303988013100100342450340d00a4107201c00781ca1814144003000c6110000d02d0301039402100240300c41042d0710711a40950314060700a15080c031031440f049444031590354069100062092100d0350207820341103907a0a400801180c1c5e00005c80403103140c41040000c440c0742007000043c5014915161000b83c580c249809202601d420900c200700701c038001100104400c2d01c000c0110341c0c0098114400141d640c4811120000020300781c0c210039009002c0c5040801040142c0c4d00520440f501c0d04000c0000d603403640e452011b100f400750741c1e140d40451342c0404036011420300e60240c0d050744904090788150005040f944d00603608031030000d8000c11552505244104e20a120760080d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 837048003 1250 837046753 837046757
    0x904060b120f070801032d030f080702120a0c2a0f05042901140c1b030a0302120c0705091806070e0604120305041e06020712240b100206070e01 63
    0x7503032815000013007800c0d00521018003011880d19040c1c0014141300303450038890b400307240505c01028060401900b00882000e0300800100c070130002803d51031001c81d0030388541a80d00c0019141000d400342c07c40f0f2072242900c0a40320a0028074400e00c5805141c0a6805403002200900340158501012203100c07200701e0388424080d5040400d1400000c0821082c021162086d8200c40140c0ca502c10040f240ca540180307940000700000507010805101c00980340000d02004000d46640240c040140b41d02d0350700c01a0002c01503840314040d6030100220a02600000040744c0c211a001c40c1e41e5000075030308041c1558410074014660644000801003400002d0340942d41b4103005880f0300644001c1003079881a881181e80c0c00c009a103c900400d03100784105d41c000e05007100080f08800300c5c0ea22041d0600c6072845044050700c29140300040340c000c200740c0040300b03a800031003a00201c4804041141c0b00c4541840d0b41d444a07076200c8503046655208109910858840c3d070083c515403a1010f000f40c045044440f0f1141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 837049253 1250 837048003 837048031
    0xc020d0509090601080c09040f020c0f011b230307180503010510090c0e15030106020f06040f11041d071e030f080d020c060f041b030819050904060b12 66
    0x24094503042c41c095000345003032902680c0c1e6903400550582034025040c1c9181d01a050003180404542039030040d00700040c00c0819103240e00080100113088072845100c0c460000b1241c0c20025686004400c03c1100c0c07138030a03002000305c140c00040d010107540b007140c0d4040491030034180b41a046c000120041c000e400254000c022074108400d003421502c1d468402d45440c40e80342d0240c400d85a20600b000013030800c014210f0044045000782c05050740e00240101c02c010320444400003d400400206a405181c001210a080950580754841012200c5401c550010f49a0100c03a190084404c100340b80f540400016004850820403034818404945100303489401c420001807000c1200c1601d80711056038811506a40c40c0071903502080603001d0140b0035060750180b90104904400c030408800d201d18450610b040c140e56405c0350b10f00725032030f90f400003422001c1e0038480000700e0488a04007101c804c03960304090f41020700000005094403084d410600610740c011a502c860300541c400003980003500502098 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 837050359 1106 837049253 837049267
    0xf0c2307090e0f070e0a020a0e0d14070e0601090501120b0603090703111e090603120d1e0204080307030c030c05010c0504080616020c12120d0c020d05 66
    0x740b600e000d448803950142201003540010744806003a11310302c94507403400c094000d4100b034543c08184010720f2400c07000d41d0781324080383d01018420a0340c42d02d840520104036040182030b13409044184200300501c4240d07a0062203c1043e280207107003400c076a03600c00e25008040c1805020454102e80d0000c1030004031500403e00c041900d0250000c00b40c00d50340141841100c1030044080c5d4180742015a03010064a002015150070110003800c5458240c610440b5511603848003d50500031503988514448004452004040c08401e0302421401d203407800c050700342c9a10903444020100112101c05600705400f406400c50040c3d00035008200c1500d2440700030b09194001d000c3c5500a00c02c000011707034040b1069030324040d0130000e0f5015010000d0240c0c2806407500d40c3c802008468024010300790340c82c08844001e4030903681c14910119145038010406414000c4980788541003220422040c = true := by decide +kernel

theorem cover : BRFrame.Cov 836870503 837050359 := by
  have h0 := BRFrame.cov_init 836870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 836870503 ≤ n) (h2 : n < 837050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
