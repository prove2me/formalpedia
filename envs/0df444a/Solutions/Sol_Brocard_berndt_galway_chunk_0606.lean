-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0606
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:42:09.872243+00:00
-- url     : https://prove2.me/submissions/b3e739d4-1909-469b-95f7-8f95a712cb1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 108812949 ≤ n < 108992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 108814199 1250 108812949 108812969
    0x3070b01090b15030405190c05040221060d05100b06040e040b010303120903020a230118020a0e070f1101060b0403050d030c020f1f1506170108060705190903140705010207 75
    0x20805d80c0c0c40ca03443e480e404c000080202002d06061082c01300c0b0300806c00c02000000d00456542e0886d1000e540c4011a600522200b080403800290344d81c2400001c0c003c81075804400f81c00c6858126610000502d031100800e50402410320001c03903540200342907903006501400107080c01d50b14518005104018161100a0603800c002c4810006038000030321800260741705c0c0c00c0c0c2003c1110f06031a1304081800318030103180356003042c54038401d10b582e0710f80d10040580241e0781071010750340340c485000c0c0b1404180c8540d40040e0045200c1c0b41014400c00c0141c441185000000c01d605992702d140c0390060304680c109035000c6d040080004c107800e42510802510011310b0000d4040070008080460b00c840d084c1001076000c000521400b140c00005510182c01c1d90b00500b40c4545050701c03840300a042c3c100e5036041e803d107a5149000442d0000f4000394091160090b030b95424500207400d0100c03118a400f040c40b0905000340d425001c4002010101e80300742c02d04c1ca04e0024a1860300e410002403915030745500070301840b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 108815449 1250 108814199 108814201
    0x5070302040e01060c17040f060e0d051509010b030601030b07032004050f0109080a0507051801150e0315010b0c01060b280c1403040e010501030c02071703070b01090b1503 75
    0x2003090210f0450302142480c80c4c0784001400c0c6a14482000c100d548410600010041010007495101030280d4079075554616400080a081c0070890444e6100a041c0d03512801850300c400c5248400705900035900b00000c10381440300341c0400e25112080e001203807510300882c100300103541d1500c6031242440d411880010179810500d140c00c100d114a0203130901842c0800700c0544540d004801b00740c002c1580350202c5006a5807400c10980358802801924400da5110501c0007032150503401143c140e420403400550104010722050f210030022204144c0c050203012241303807030316a04821700c03802007e41407100d0740d0720204c9a590340d086a0643c0c0100d848131005100000c29031006640358280e43c0072144070b640d0010010582500d00d062041c0f00108040c03d10071007a21011400300142007103440d00510080981d8031a40198140d54410a105006078000030080017000a040004264644484151f03032034644aa29141e0a001c026006136030b9070f0b5150700f500001810f1151400b045040d0208600b425 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 108816699 1250 108815449 108815459
    0x405060d1a06190b0306040b03060411011b080a0206060102010b0102011107060f0e070b250506040f080409020a210501031a062d0a060e030a1407081905010507030204 73
    0x9180440458525110090000a407860321004640c0d1141c0d91040b603030807000f40c0e8904001802d5070086800a02403801d04401c0985820000748150041707a00c00c03041c00c0d000301c20788011150f031060005510440c80013113540c080482c0c0d001c8000c15006900f580502058030f400703000a401c3d43d40300c514641c116850b2040160410081d00c0c1540d0070150b2024000c02e060006070745010207403120035402803050041c60000216810315400800898440e4840000c20070f456983e405440010380e000a000f9400c01e100140c006084c0c11b210000e5148544160340c189a22201100d04a800002a10011a1141546818050ba00300036040d05001c03880f410300440d815661541c82143c4008110004101403002007400c0c2d0359410500c49503110500101c00603090690011704a90305842c1c1d80d035000d900d1500000c44c03c6440b07803020034030300e1801030020080c00c034040d40c540220000044084515002c0d50f140812590700502100c408400b4083c0720010011084c140242120006421a03040c5481000708000b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 108817949 1250 108816699 108816713
    0x708011e050409050f120a0323010302010806041410030605010f1a130905040b1f0b1902010b1305100902041206091511030907060507021813060204140405060d 70
    0x3566402d640200d5800750700d01e8580c0c03400d1441050350756540074407000303100b040300000040c1420000c80ea600f404000241c0425100e581c05a05080c071440a0360790044c07000d54054555a0381245021380000b8841c288541175240112003078032008107405c00c040c001c03c1401440e01403035000d04006692202e40c10b01d0604030030031403000211103e4503030f08080303203104205001080200040031300d40410b1005117001c1c03400682c004011503503e4030840800311200303800107031001c4c1002944d100d920307e09d10b00500b495400300e510350502d03a41c4085648800310111561103413404052005010321020500b801c01e41c8011824020a40025103561b10501080000300c4401483d01c0400383c100000040310f42c1e032420a042c50404003002203000030b003404e290510314200705001f50711410185064402458a5000484581c85241c3c00690700510b0b620020300c1120780e080c1c1094000e12140c0044407455426651042642c009a10518800c40da2203290b00e131030f0506004050b800402200c0704924203645035145d43d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 108819199 1250 108817949 108818009
    0xe03070f030212030c0102030a0606031409120c0c031b0103060e130b0417180406081b102006010906120209071101020d0f0f0609020304330e0105070801 67
    0x30744900e00d4102e02e0060f403031090080f1120b000300c0c280259136900c1c0a13440d48010300094403925001918124500d0b0354100c032241c0c1c03103002d15102c1c0003030200d00004a03517484a54001b101c1308800c6000d120340c0480c00d0398003000f550b0503040320b032001041d00547c0100050304440702ca60065500030200350400201e4100608640b8119910540b00d03402c503100c904041c40d001c1d10341c810140700c00d42c0002e1019520303404a00c5242100600b04c40910103281c40e807500c2a01d44041002d050507002d0b00304404c1c4040e1800d1240d06078620700c203141c015000a80d52002e02c0c42a88000594101c0e600329100500101200d0300981e00a041a0306e58070500c207030140e01007641210000c1c4400b04000340e0000c06030328a0070a404442c040c103100038040c0100480c501d118402082281102a085450440006907840081c002c0ea8462a0000302c44103004e1038500007180740210888818003000c0d0f44255041d00c05c0894410552500800c1000040318606a40003030b2522106802503c661101b84140c0800642980019 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 108820449 1250 108819199 108819203
    0x801170f061f030c080319032007081218010b09010302130509150c0a030509010501060203090616060203040c14040509030d0b01120617060a0605030d030b0f12030a0e03070f03 77
    0x902d10707800d200e0025190405454000038410702442500040115001015182500741100b00c4070140000c05016000c503107400550038a51100c95100a104244d614003a21841e4005d1144134070701a00710340300342508402210418a45494a100090141001d20480680010175101113103075504640000700414000302215101d15100c074000342c2100c4051050074400c0300f941e44010001e041c2080e40e0a040d030007001c1c8a50000c0d280c640026104a03050091034104c0f01581c0107945001d201d0740500c011039010380c1a140300814461003400000310303148002e42c895070207401c0c04985e041c00c2220f141020550341d21224882c03402e240070702004031000300450f0ba0030000c00304000780d02c541c0740006a82d601019040c0a188600c1c08600281c403116050281c1c004c0645201074407020754419440c0e501310780309401010340503880300c4503204400c0d000c0da120b9240c42000400c0b08040c0b803210b0f400a01c4c0400801c9152003181c20209017440c00982040303004941640c2180030b82942d908100072441500814800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 108821699 1250 108820449 108820471
    0x4030b0402190303050a230306010c1a0901060608280509070504090807060501050d03170c2502010801060e06030606070f0b040303060509060d05030d0f020f07030801170f06 76
    0x1140456540002040d0039100da185460a0b95640341406029500542e40c05804584486041c1c44017000b068401c0e25030449921100b800c548641c00111800504a0340c00c80b4140c0c00b0580840d601070400c100940f00b200e10f5400818003a081440040c14020043c10705c840c02c001c0c0880345404100340d2010002c1981c0080320018003690f50856462526240c0d500080d00310785044002028450b440008114850007080d00740440c3c1d90307450501c5104176000703070080e001941011400700204c2c1c0d806441c58201d4079100c1c4240c103040b0109000b0740c00f00201e03000e022020303909526042c04c550708001410f0040005003828004490304002140c00c622004240f2840781100103900300400a101c1d115030400c80d0010340c5850705141c507240c09401000c160041c140326050100c00039a29142542e202062554050301950900000005607009008080326414080342c00b031001078074049041c00a00a01030199442180d954136000c004490781c10745130b442400582010350a15400100015401c4d0041c0561079 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 108822949 1250 108821699 108821701
    0x403030b0109090c090801110c0a0b04020d08041206050105120307080705031327020304230c1005090f03161a04050301090b0a0b120706050c10051617070504030b 71
    0x1242c03014441d4104100c4a490500c0310585164428450b03030550707140304020070a020034902000c14600440290300480c0d48460700c460001100e03950641d801c2403024002704540141d580e00d140d00c130380064011a4220078901d03641d0301400304600400303005000644a05c801413024907806034803407040250280030704a0000760102084003c100f19102c041c0006c03100100d071921400d40032840d1540340815030710a55241c0c800c41c120030640c42228040c50303118900d41e0103e5941c01c105524660242041c00b560700601501c904940c840401148070761085544441d9102040e030200150386104030701070360003607005041c00d10b400c420a0860300c0a64440000d01c0d0400d41000032071002c0740c03040b60030203605542012641c80411000c850410b000b051083d0042c06882801d03800e11103204a0758660000591080b0820420140590002c09a103989030b0700341e41ca06041d21880170241c640a480c034441c4403218410141c10154000c140390000109800c00075100e041c80b402c003d020303000c0d030301000e484880554 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 108824199 1250 108822949 108822971
    0xc140406030207081e09090901050105010c0b040f060509160b032e090606030b0a060503060a0608071b0b01030203120301150f05160501050f0112020319020609090c040816060206040303 81
    0x501a525049102d00c800200288800e45d010318030303041440307018052081c85020a00821042c05114103a0310117a4421803484003503210508005405401510f000d54880818808201c00b03002e268403a0308400000d107441c0705280040625404a507203c078001314400d00074007a006a4161b092080c50a50a0002c180091048a51445040c141c5d100c80446071410b1400034440e0b40541110b11601c1040f80c602c80202d030765400c2a102d522007119081e601625602003402114003a500d080c0e004109480d04140e942100e02d43e50644882d860800d44510b44403000401c21481c04126001000c4c400c815240e042d54945085001c040304128420001c3c00505018081018480ea00390350b10301411a2140d2040f00050402074001c104c180c440c0103008000c0700020882040c4c015900070b00983c007400408202d00c840310074002d0301c070441c84203d1f840b01080041000701e986040680b405049407500081e55a4030f402046880d0028070714641400040900081059035000702c0d91580c4039806090100c0c414900d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 108825449 1250 108824199 108824213
    0x50108070611060f0a0e030301090510050a05210c0a0311100203070b010303032301060807120c0906030908040312050c06060a051807020a050d02010218030606030703170405031b040c140406030207 86
    0x41841d41b09244404000014110b4050708000d000700c1140724005235154545041c0292103d05001b00c50b045001e81e007a030b8030f05208207030703030b928104900030282c88000e0b4141000036012002607200751417840040c00c0c1181c070392814584018444906000441c5070032815900d1540301d141c140301c06003c2c1951071041d8040d60715400107220009070284070450007503844280141550100ba201800080c0404083c1980c1e10a40d11450750030740c01070f880b00c116071450044224040c1140210132154410217000000c00038600c0e84411a852681e1303180c46482d52000c040052a00e50003c00b160302c5014a1b036010041c5813611f00101c42d0740252400d10311525904c9840c03ea2600c80440e10003061841a100e074200503981c10b50107003c60140c204200015106803600301991050181d0320550306070030841003000010703a07000d08060500c450043d002e08bc0742d9076100103410400000b0080d490010b0290510a281c41c0c64400c50680240d5401c14404420b0500d41c0e01006000300d01480c3c091540c0024203200703110318 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 108826699 1250 108825449 108825461
    0x18030309010b0103060b341a0702010b0f0105250503070819030203040c030210020c1905010905090c0a030b010903080c100b03010903120e010209031906050906130615080102030406050108070611060f0a 88
    0x800c546480c54201c120003900b0341d81c111502001948cc4c40d0300c01105180500d0004e03086a030503528030b4101068a030280040e20400c5008456901814000d03200040040c4003804c0b070756010794103480c0c5400d011003080190782c500d4500001098410020080040c0303403d80c1060659406603103051100c0354100082e0710b82007500890503402902c1507120904204581c0244090342c4013070782e581c0c41c01d541e5501480a40001614010040401440a814014880da0040d9901d410515003640e415990381c448813030640c010f8201d80390903000800075007049420f500a0f11204030043e0000c0051840e81d48004048007004501da80c001615540c45546541c4250141d074400c0724014140e48030203101c0c40311034a41c110318810440e41c2a01300000074010718008501d40707100d919004034204646c0d9655840c04c0050200482981d64105c0414001c41c60580034405188543e1062a00151341d5040c144280d28280322580b12008210b20150081001e140c04110a500080b08036203031055903e51a41000c05041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 108827949 1250 108826699 108826703
    0xe011505210f0a0b01030c020601170a0807030504050a060e0105120712020406020c030c060a0212030a0f05090f0114090d120902120a0c0e0f04020918030309010b0103060b34 76
    0x140703800070b01502145030818240544840b03442044980c81e440c0041d829901c10007030540242c0c20480042140c0404401e41c280084c100509449001400d96551051500f02d000182c00048003c94117000604115000300042d00e801e00303209100070b0300710380000d03c1031064545000080041c400030a40503802000c5499070f41c41020030175074503203881d440000d66910303101549901c81d21601403140b0340c1781045400c80d41d08840302d0f40544500168031182e02c515a00203001c010941742c2e50301c9801c80c489864494580901d01c000c003d44241c80a080e4081d095404024030441c000748140140300750f40708001079801d1030360b04070f040a402070800d0804440090440d180d0103908a101d520510b0b55512012a8455007188180a01c2506544403104910001d20480344040c0304400c40c40820091700e42241c2d040d030300040c003861919101c0c41d411006800e607042a01c000040361345401c4503004070368040c001d1101500041c0b4555092417441c0185825180010041014500c801c0342140c00c92000329520800380c1e070b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 108829199 1250 108827949 108828007
    0xe130f1b03020d270b041106030103030801050306061009060c05070f06020309190806010302151611011101050606070201030908191e020109050a080d060305060a05100e011505 77
    0x218000c10301401a40c094500741c090b540c03800190003041c01486000c03c0c0154920410f98201240c0341e40c0741d80030034801610607034418180702640c6095654042c001d501840c825910482da6514040c185450716601801c5a8030403510240035200296001010740c04661241c608400c1018903420182e04148442d0400c5519090346c480c0882c0890b0000002d2031540b100b5100402c441c0780c4407000425802c410b003e50407050b0801401000589030020010300d2110440106a01e030400450002d21002200c00c0210b64070686440307080065a0004e07072401c06411414024002c5180050006900344148800241896513601c10301c8140039207441a9500d1007240ca80792035a0045114026140e82d14143c2054503429004601251891040c094400319a601400070541070b0307c1d03130350b900f1595001003031200d80540d5140c100002052081210030300442d0304c1880050303d0309140401d5880b603ca42d42003180c0c1401558010440705640e50403901a0340300310310304542c68902c100d0505a01d0f03a0b9042c0021905 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 108830449 1250 108829199 108829241
    0x3061609080703110a1211010c02010e0402030a0c020f0304080a0f050f0d0c0519080307030b12010f09140d08010b0d0209060703030c09090b0d060b1311030a0b010e130f 74
    0x3103030720303480621184c20031114103030a20380d070341e41003805d203401c0f810006d01d007410006c144d034101e500a00401d803455105040448143e042c1101040403600125203110086444504646086d501881308101c1a1b02e11400741d881c0a00b007010043e40c40c00080e50043c2141100350460050002c1030010368490300b502002c0e00c05104107000d00505500d5043c400759440c0c040e0781f11003841d19401c0c6000c0481700e45d0148050f4110b59801c10140c00030200480f9094120701c0201c45952482400c0c0300f0b820411440783d00010b0420100d0030003010307016110682c0d4507980d02ca1b44003042e01903000f9941e141103c00000410303985401c0b2520140c064028044025000440802d6800400d03030150803282c1040705a640d10380c00300d81e03150418410b980d01400096009894800d80c0c40c04554240c201c00c0100c03030060040302080111000700021208004a034503003040300401846240c5040f40a0b034401803000346010546c0f40d0350f500010f0b0010b0206c2d10744110441d564103080d181c0040302d4014090b603d19503103054101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 108831699 1250 108830449 108830453
    0x32304030b0f010807060f0815040e01090b131e080d0632010807110c0d080c120903030f0a030b0d0305040f0b0c030d0513060516030501060203030603061609080703 72
    0x10070409845100064105a0001c00c2110740041c0e078408403502c0c1d9892464210300710005840c00c600c044d1000300700c40e5a5882c80301c410f4443d4014030302c1420301e602c00010003200d9400d180391508806050180804001460780010074a5100c251030100d4035007001480101892416a0641c40780c8070980c4045403c1c079000007100d04072440e00f10408443d25440364105c24a200090207181c0507a190203003c2500500840d032014440c0d803e80d41803441c00003ca462100c0820001001080174040c215506800003a14001c0c0030000d02400c4c000c8019924007604009591001030748900401041c41e2050714042883c040c214480d40040c00c404401400e10000c80100d07050007801a4070030300429600e81700402e000103400403004121481d6040b29006941000c011010750005804041c1181c9892114081c94402080041c4140390244812202500310840d43c500003605a400581c00700041d500140b003004200c0d100464030315802040110001001e4401c403006840000b4140c0121842c0e200d800300c01700c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 108832949 1250 108831699 108831713
    0x190306050618062101020c010609020a03060e100303031a040c020606041a010903140304050307080a02030d0305010b090906062208010b12100f02071e0204050604020c0a03230403 78
    0x1005900c15030341c422041c001c4052604403540141c0f1050740004504000110100c640c5038002400c1d000c680000d032524035030811a500750b0f0310540009058950000310366011641502c607800040c543c60064243c40d2810941c6d8a0240005100203818551a80505501411004078090178404024410030449200110095030b403541111100e0286140c4120200521a0001c4503e104c2005940d0b0040080c2965104152a108541001500d21003400041000ea80600c407480285c60780e034000313004440450041500d4100e84030313000000e1514010060113442845030448002c04015140441c1a407246004a4141e22428100a80300c000c100d901404800140c2844000c4440f0f2038028442c0220b280d00704000494000303542010b55220b080b044840c4605030f046012280004540182040110b48403c2c0031003025111007440884616851421807a081c070803c0d800c0301c1c041c1d900f14240000300c00400d60300c0418003c05024040171402546106e0700255402c081082d806c030303003143c0315a0780e40b910513 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 108834199 1250 108832949 108832951
    0x406061701081f0e0a0501110a031b0e060a140d06090b0301020903030702100e060703080103050f060606040501030b041e0c201b030c030d0206060f030a0f0303020919030605 76
    0x4204012a400001004035000070a440d0120b400e0243c151440b02081c0f07010010500b81c030700c00002c1e006004900d00800d800b88203040e10344004c9000c541c0d68458481c00202199242007051001903045039100c07601039030041d50121014400c0c0c1d207590340d03040c0303645d4252280442516201549240010a10030900a0340c00c10811140308a00a1012235280001c05081c0c2c002c00090641590043c0251409841c1410801c6000000380c10400d044003040804500c0c50303404842d0507000f003012900100708000007000301f5455020b12102500c040e090080004140c0d204510500741015190054441150760315800440c8102a00390218a041d880042d010043c01000244c2c1010440f40502250310602c05150560940303403803000f07000081008000c0030440080d0a09142c5c061042c0c11030300201c1d45040010440c880f0494000b000b103450b040040107118049400c100d8040d40000b440341c03002690401010a065906060260f2034144800c04601c0c40d000071120541804640c07900041401120342c021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 108835449 1250 108834199 108834227
    0x160609060f020309090609060a12060207120807020601090f060504090c050414010e1f120501061e030f0b0a09051b09060603060612061201060e0907090c0912030509040606 75
    0xd120304648071000ba070302c80c00342096980d04946158009181403602442c1154007041c01040081c18a8490741602000400690116621980001c102040c40819030460014078101d00c0c14800e24501100c0003502c0300018801c0042d000e48452a0703c01d0a58980c100601400000d4030030000d4841509000d0040b204502c200c0303000798a00780c680c68403094281d4240d07040c0e4503c80321041503034035140324102d08101c444807091980c1c1e5002e0000f0501e01801006420060b00400000c101d0b5410300c428410740051940303605690440c0e5030410000940003c840c1e440180d0802e0104030650746002030340020780f1240348010b28a00850409500d40701448c01c903089851fa0075030300215260395003414080c2c1e42c44240c44040d4024001d01c00c0102c851101078440d540040060b0000e408000d669031000d00355041500581c503a421814100400389404002000051a44020900a00310b855101030300d1030b0700c1e0b030150f601c102480116600078540218104c404040c00948104000e0b5943c4100801907a01d008031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 108836699 1250 108835449 108835457
    0xe0106151e080601020a260d0212060303030106122406050d0506010903020a03020405040609020402030a0902011205060d0311071a040806180316031101151809050a030e0316060906 79
    0x50501554070540d0b00b0740c03080106800030420344029403904c104103400e0010a01c1c181c0a010b0300d0400707000d503807006480d403a50010701c00758a03040c01c44089508403c0091485019600a000404c850f82d80650291780314071050710001818031403e101300015006101d61507501c0000c08000050041d880030080c80ca00b1410703c000c11050300c41000450304805280320107513002e803800d2000c1c809403409511494229101e040c0004081c54284d021805a070030445140c3c50840da10305001d01507503044200807005000741d9400300203601d00a0006144440381d180d02804000c08901264100c2d0801c02c42900680006641c003c00c4884050b85260a50b02030f000d082e00ea0300400000c6a83d00d4145c4112180d0229250061410f001120ba01d004c20015800002e50400000d004a00c030a86000c1c42090140284404408045d074141500c14030181d00c040c0c41e122115203888032071404200040707000300940c3c1d4140303002c2c002181b45100092401004004507140380791600c60004e49190405200c104407412a06c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 108837949 1250 108836699 108836747
    0x3030408220302220e0d02030a0f05270d050102070f03091e0303050a050d020d0207031b0804090c031b02010e0705060f0306040b12030d090b010504060b07060e010615 73
    0x420404051042c0c0b00003500640c40e1007100004100700300001d004900f00c3c0100052100c0b2050b0881d10b0042c000b528140035810000c1c5003403900d030307115645980359070b0320303042c91441e10444200040c01c41248a5801c052600c400c10034075003a40c2c0750038400c00070300c0e0000001c0d0b440e041682021200404508011004124405000501303059862031881000481050400d0410300c0d60b241655207601030806001002000c118240c41c0a2592010b0000c0c088a18001a01c2e10942e28025110101818a802d04d88107001800d50002d004d81c4111001d480ca076001c041400280444181d000c3c02c2c1a945440b039045c3c0c9076250340c0b0b0956055015403c5071020504a0b42c8003a616001d01000303118124485600344020000100f45087c00c0c0c228003200d200280c6040010b00c044102c043c1550480c035001d1040c0c5440d150b4901c24004441985805401c0460303081000354074058002d202e41c4141d68005011507210405140030b0781f020351096005140284102c000c2c4000c2440082c410101c80d10000b07050950b1074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 108839199 1250 108837949 108837997
    0x506010c0206030414010615080103050d030e030406030b03240601080703270c030605180106062607090503011a01021905060f040609081603030b0904020312091203030408 75
    0x540e103009250340180aa510b1030f22640c950002e401030060011403159201c540002d00020318003000010341d0140c0d502c03151954150310f442404c004500070b110781014102138823a01c05c00800700c100c500b250b242d0304001409040c4080401e040095103400d51700c00c2d10585030410380f81e40806082d24810b640c02d80c2c17201020307512003e003075040313441b28409850b0011202001c1103001028142281d20980500265000c0d6581c954800c4c0035500d00301c80c01d00c4d00f146a0340f0751450988003401081c01401042c203009112281303120000b00140440c19201d1060b18512003c02c0f2000d020b01c0b0740c50040c09002d4000d00c54101340c2d0350044800d0399021085801489003201401608602408080120358880050602500c1d4803140c48414030001e80140d9041c0c0ea40c01d158000508403c0041028038051030741f185429980b82806411121101500e5005074490410040165008070b600c0401020009403680c5980301c100c04500462a600342910081c80b0000c01d02041c0440400502031001c80c0044182d1001c03628 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 108840449 1250 108839199 108839207
    0x9220f0212060a350609010e0706020312150105090a0e1005010305061305041a090109020901051f050307110601081b0303040b07030305060609032d0f0303060402090307030c0303030f050601 83
    0x44c0b0031034070010040b03000b804503801d00041c000e2195018034060219109001e0300c19007444005c1c3d503255913980d52982e0700d00000030240801c00091040c0e002550404862150700b00c030700400202026403400307a44c0012100703031780540c00755a4100c502034105150540c450041c1c1e079003108242c40424000c90442d6001680e50310a0203040d02c0360001030064205145960010300180c113001d0011118100b00442c0c0c06903040390510a90b200754642000414840418010b1007400c2d541a005070340594801996103041200185544990b80c5051030444c2e41c80c0e4508408a031201d41140032607003180501c0d0000602c80030700141254030807203204151504151100c04041c1d0760710a0344108801d2420500c150804a0700036071040fa8442c8018100c2c3d0310f0304100400003403c01d200c482ca410031480c560001e280c00080144c03021030540e40c44070300900c18000000112030707a074080200242d00c12500080d103a81c4584060094000860348140c401e442242ca910300540030301004840248034916140000da429841 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 108841699 1250 108840449 108840469
    0x915090f1205040e0f01063509100908130902040312080c04050d06090b070f0c020f0a0b0a020604050c040203150d050c060c0a0c05041109220f021206 66
    0x40030248420108140d5907202041c0ea80ca40c0701400d00c2000d110004021046982d6940304041102000a081d81000b00141151149200500d4548145940703180b06030907603402601c0c0b540074155200c11b6a903e0b103c506103082d03001c0108002082c100038201042041c0f0202600c500c3c2e070038024810395030342c80c0e07103c00f8100d000b0380c44041e1030101e2520381105c001c0d004d1040c05411240d0307421400d14007602d503004204440030010003119034030350f0b4104000900804a1200f5040300301803030a86001c0c0703240c4d90010481c4181c800003a1050061500c3c5013001c0d0381d0116030000030003030f03014022346443c0320142c041d445940c21101038407113003c0e1100c0e03c4400e103824422031f071140404103d0101d204c403802060080010480904a0b140e01c0b03400349409096882002600140755084002d2040d0111340c600000b1840455000c01e01032130a04802003000300c5604180c0c1d40704001942d208400010292400600d2141420b0030700005142074450584440d403038000700201c3c0c1382402e40c0d05594070380400344076120305 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 108842949 1250 108841699 108841703
    0x110d05030c0a021c090501180308040513020714070503120a120b0301021c05061206010806150612040309030b0f0603060403031518050f0108070e060f0121091509 71
    0x10410001e9100e54410000e000c10700d03154030444201c4c000c24859090f40800b84d40100010038084082045250f07440078268001c64a40085c6080207460340da60b400440c0240d0040358802c0c0444901c0ca981c00c3d16540c1130322100b54112400300c05c0031b00c88004003920b603107aa000d124001d000b101d01402ca002e042c00200d5100d241e56036100c0c6c5ca8401c400c3d051a000f400a40c1c03c1036415502000040421708000007518030b01c0419400c00151800c1c03100820004401c040c1c4111489d41000004203c041c40214a0796806200c0d03041c1c05096039901400681c0a108202d0507451100101041c4010b00d9400300d400c809407841801c0b07214041c2c03200d148100000b40c0c2101d409a0651060340091700080c869003090740d1854510198902940d00d41070f101078008410a0041d444603612810454401035445181e401400c240010700308a9081a00030044003000420541c0124090300c0400f2869208603030381c95095a03180f10080f06120300100c0e560182c0400301058801002040484030b8081c00c601c28441c03065 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 108844199 1250 108842949 108842957
    0x603060f0601030b0f030d0207090b0103060b1c02090d03080a0b01051602010f0203130e1009020306100809070e090c030609060603190510050c04090608070b0f0702150a0f110d 77
    0x41d40d80001140070f00329591020303402260810b9160f485403000c1100509060603078028040c00c03400c2c60500001c030b421b0411918101820a0420086040501d084920104e1511203495040d680d0030388a40180c0f0030100f140e03800011581c41402490380c0900b00034050b680307900062007034410310740045410b40920341050095000c4402004010345c0103c82c1c022480c13150703005890400c140d80e0075044161950754864600001c03100d0801c031403001141c500344081c1a200c4404c50545c1440d00100e00d00310000c00101040c041d0350004121401003c021510003005041c0b60f814181c038000300c40035100c207090552240244921000b20304010300103c0d220f8410701d406030080880008014100324018801c001c11b9525004085414040c00b401c6d004840c811031180342e2181c2c3d01e40c90450100308480c45a8881c0180303811220301808004900c008940d00d072a054400d240d1240c1079070000030407400c5030399050a68424005011380c0c6490b041011940001000d440f20b00c0b4507010f803400161240e03240d0700000300007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 108845449 1250 108844199 108844201
    0x1090501060c0b061c150911030111041a070c0b1c09030f03020706150305030306091803070201120209030604061e090f020d0311032106040209030a0213021e0706050603060f 76
    0x1410102c074420041007170401d001031440f80301e80703078031040c211414200e001b03c80c1c55050f0794003440501c000b0000c440a00360020042c0041441310b8035080d010b40c0c0180805178035003d405a0303641a40d00140d03100c41740c00c0600b01d41da807035807418006401c0d031000c01c01840051501c51540d10480701032091085043e0907841e001021840b00c4d0741180250b011080444a960b540c84043c04200c0049018034051440340000f907649041000c10020003a00c001c20b00e05440032041d010321030741341c00801641c4100b1781c20f0902c0d103001a10000c5100c0039008002446805200c0d000401c0244032441d00044004107450144030340742003240c06120192020000c1c06084540ca1160010050621240301000309006c0c0c42c00000c0500007070f0107107003994001d10000070740300404956030300340c00b0302e40c0035081d08070008039000c516065884d0003203521440003030b0b006846501c0e008042109030300140c040707426101e11004c403001008078244054900c1d4100201c20303640c5500c1c16000414500300050141d000b0342d110b9044c140c003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 108846699 1250 108845449 108845461
    0x6090a0504020f070501060e150324040807320703030c0209090c0603040605040201020105070c02010c140f0106170f070e0117010b040509210a050409051003050d0801090501060c0b 79
    0x40c2d40100e0484541c03040130007512000c91028480c02001e0900030101d183d05041460b06e0300542004802ca0a209820044442c90030442030240d100038084800140c80c0e4a99440c00e01003041d000f00c403000380aa590303003003078620072000c1d02d11040420720050500c2001e41d003085039000d641354010302008001c40d802c4400c420140c50400c2c500c59206c0c070400c00315079001d00b00c1004200180c10550f801c4601c3c0b6140d805210440d0f030203005242d40120030b032601100041d0240c0000306a819446000b40007651003642d4500c0c9101e0901000d0342c1d003a804070080c0103841d41d8440d4a01e101c80300d100c1803441805011a0090400e6004c905903044541303002140c69541d0800083c0585480d42d0014411a5940c490400d44181c8550007260301c541004000391403c4005000e540040d44210350902582c3c400402681c0b400c15008020b40302640c00d036142c00211580c03090305014000380190005452803103941600c09010703030b005240728143c0d40c41d080180100e9903554401d40d03039092032400c01000ca1800d0b1000543c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 108847949 1250 108846699 108846701
    0x9130903091a1219090305070c0801092f0307060509180c0403080c0a0b1305100504030807050702040e190309080a1101050306010314010f051203030603190510020a180506090a0504 79
    0x50410300c2c0c041020100c94a11940800310f0f45c0c0c2002c1180400c07404207085040c060b800c0c183c507000b40101d100901040c0040d039100205040030100f080002d00c00c1e5922030f4100200500010100c4a01038200d54a07103460312000741064101440042c4900d2403141c4c0c21342e401c140420340d60700a5802044250419003540e44000542d04441540000341c0704110f164408105007801c1c4a019055040720701010203013500300b039820040681188664541441f007840002580124a80c1c2d002c0181e1810030740f50301d214400038000d403200c84c2011940348140070744c100007204030102d06043c191080e00e802c0c210f00e1b0741d01105901c803119508090540c100502200f071155008000865006605160000e02035440c00e44c2c041080344281c100d0f00c200c40c40314030148258202102c41d003030250107800003581940307415000641d480c003200c0c00e000101032005801108110003000f10312210f04903000706540300c11070480014046800c030280c0d001051098140010709003050002c80e05500c00c0584007201481c10941884 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 108849199 1250 108847949 108847951
    0xb01080115033914120a02101b020402030a1d0708070b0310050301090c05030f01143402030a09060e10081816090501090509100b01030209130903091a12 67
    0x884a65051401203451103c10292440501420300392281448408400e215420744584062038044d030090740341c1c2c4056521110baa11680c4030501e00ba0b00c4c10b00c00305540e40304a20600700001d4105001100748150907000b134001212000502e005c0d101800e11426459030344003418420f10049800c41c000038006440075200542d030082400b07807101c1d43c4c42d541c1c5012a0071688110001d40e81c06c00c03a040103024070318040c00324a0907010300400901c8540480c085000303078001d003d89600c549040c0d0f44031940301403208040c0d1800e0f004411031000307018403221101a440c0d40c00341c88240c001440d01d080200d2450f000703002c000d9205070040c0040c11728a0114105681c8554040d041c008100c0c0c603120310707103090042003100001c140041441c5603081440d1070800c1050b1b40043c0c1040501504007800c210668000003510101d454210901107080d00080c001030f4001c0c0324520034130f60043e6103100c44024034042a0085506588a0303075030140455076461110241281c0710403000048803007040740f210b240c04452045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 108850449 1250 108849199 108849263
    0x111c06090503130612060e070905130902030118050f030f0d0203100806130506061e150405090f070f0c030926030301080114101a0315030a0b0108011503 67
    0x202e00e0409960f0300203600440c1c1c3ea21040000d0700340c0d403007155130440c207014840c02044110f5400f95542407082e4081c05410550107840e00902c3c0e840f01c0707040202842c0e08040d5580c1c0d009002040101c400a104109a04070354400f51010f00c2098042c138a840c90000842e1074031520340d4010360030200c0700d42200300603520150401d0049a4070344004118235000b4040d4900500e000b120380e0b4400350580ca0000d08080d401006144511000b20300102602c07010000364012a50454022455400540140400b4013554001780e4001fa100000c02016001d004241405a80d59843d11048011000c00485091041142c01400a44000d0040244c080c91162070b8400f84185a00300e980f002e086107429186400903802050f00ba91921650070b03401e8084400d040d040703009804503608040c04e200d4184005081d0740b52071080380c080000001c60801c00d480c04440740140c0181551102803041c00c041740703121028019080365510b001c0050303c2c1c404001404000300d1354003411010040055118035040b900110b1a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 108851699 1250 108850449 108850453
    0x403110609030309030f03031e13030f2d140310030204050c04030f0602070b0c03010e0114010903120905040b0414060d05012304031704110919020406020703111c060905 74
    0x505400d03079040c4440d41c1b01142e4107000b036480e40750403080d6a10a05803400807000100b090342c24800c07110136443c90046090303014142141c0e101451881121000100c82004440360401d5100311301c507681d5400c10754074400650355004640124840140d2142c03005540c03480c160003200c54200010b0505400c1564850a250f2009082a40e642c41d6028900402c503c12205c199002a503d42003001c2031301c0d00b5070046202856581151304010b0048031002d4103014043d040e40409003a08426803003000030340040c5502009480700400b8004000c0c12883c07a60040034412800d1a8143c03401d820300e84034589542245031500041902c45c1414844c00840c01c2d4030903a695500d5101ca200c52504c40415001c60014201d4a1020703498141002012400841084490f90a49600380004208150ac0350928400304551145450b00c80a00381d030050b02c0550700202506001280005003a900400c0042c1100e01030654546e41001000030414008004061103000417401e011110100f100ca5020240c01845402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 108852949 1250 108851699 108851707
    0xb1902011e020322120309050109020d12020601080d0c0308190501030b0a051f090c0e031606180509011a0d05101d0601080601050706060315020901110304031106090303 74
    0x1080c1c4101c1c003003840c4410207642c00000340040044041315807085146002000b03c0c061240e42e803000c40460401311110209034a4640031400d109080d40100011a801000b0751410006482c0400f0024a82060000540a5003000050b04000403c075400b4070905a6112882510a640c4c1078401150283c9041c80b0105088a488480207141c41424041c5003d15088961464002651802d40c2e40061601c0c010759428002421b12401075145002561003c1e08003140c440b5a04908a032440300c1d0102051b8580300304040102a220030000c1001990351a5541c4403c1d0700e2041c60300c806407040d038840e1035080303405c0ba001003003111140400402030385a5180c07150310b403007a4881c030380003600c80541e4004c140141d608070070810340345500d41042692122074000c50071403501e0750001e400c030780005001d00d0501a00061030b030100146540b0900c040c50388410301d03805015401401c400290001c0d032205001c04d034502d407120160840041568210780e40f00000e44078807842d81c42888904d800c1640001e400d44402e01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 108854199 1250 108852949 108852971
    0xe0c15040f0308120114010822050a08041a19030c02030d090317071107090506010c060e06011a030c030c0d090f0f110a051503130c060c0203070603060b190201 70
    0x541d44401540106021a10383c14250800300c101d82060f840301c40ca0014440c0c080072940d070401c0d042a8803030b41d4000800d20b2079101c51150380c050003501000600b01d018100d81030040005082c09482950760000304591071810344607040129214800c1540030006506001e540814420741010448103110710580e801d0020001d40401030f12403d01085021940c1c811221018011000c1c02d6035114909107070075020740d2020b4203203d13200e01440c024008007507180c800090059006260482d10a07074842c004015030200c8000b800e4844200307008948480145404a0342c204a0079002d4034052180f0001041c40c42e22070b05020903559001006104440307450304c80c00303004503110300da00d07801c0a4003404a414003c2003915029051041905015106142d411170a201e641c503425a0030074881c207103080e1141d0700e46070740343d2101225420040080004d003002002184036035100e071141c00003a20a500700c0d50595120201a41076035000d0095045044050108040c406001200340048014500000413552134031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 108855449 1250 108854199 108854219
    0xd050901110c0d030f050105010c021e15030405060c070507060c03170703020a020d02070b0409050a0605040903050d0c050301060c03050904140702070501110604033f0b0102060702010e0c1504 84
    0x8200381e4011030700b2884507003000d1900741c02005010617449604020540c1070500207454403a0b0b041c0041d0251440c180740340c0c1c10303800d5004a00300c0c80a006180d004803510524500d03c0540c03044800311903600400303001c264404d481505580105612201914005042040c00c580300791001c40d003a4100910740d05080380710030f401c80c1d895008621559000d81d0302c000e0004040d00e4034848404103c00c5610507541008110841829501614241940800c203601ca5003401c0300586000c0d0801c07648035203440c44400c1010381203001000c08550384001842a1032a001701924540001d10484020034061400c00000900c50402000c40300c40081000850200d000c4418841c1107088500d50050b0b4083c88061203a581c20117949040302050000400061a29580040c0f0140c03581003c1c5401d8034003594402c0d02016104082d400990b400c44c8109111445200c442010b0204155481c1c00f5028520203d61440c0c8180203401120007400018200700300d024060000e09083c9140c401c04e0500300780408600720010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 108856699 1250 108855449 108855457
    0x1207030e060d061a040302100806060409111c050412080c030105040c0203130f05011205011d04170309010c0813020123040f03080406020d230a09081e190302030d05090111 75
    0x15202c1e00c45e8655040d07105000da1042c1070001c0d0300c1808005001c00c0405c1d81c4d1301c2d0881c0c0c140d440c402d4001c0f4402c0070f149142c103810b0150308450142c214080520345000001c0c0d51020307100314000c0b40e0500b031468031a40255400c91013640c812040740c1d000c20041c012400c0c5500302c0902000c042c412245008001190072940010b580c01035503840740c175080c08001c25a4802c4840041c030f6161102080603500d403102210074403007000c48850482e041d0070005024010494491501c01b180c2450983d5a85448040b1034028031802c009140410ac50602140042106000c3c51600c02d5068450f400680c6100c0008081396585038800705402e041040f010904034072024407480118400c0300c20646071810b140010342000901c4003a0000c10000300c00040302c42c9020813a000c408414840390b0782d0380c3d600024040720303101042d40083d1100d101c0c0903424101c0300742c03000c40c8140da440c4030400e440c030342d000411000c4c3c92080e0b100ca0160060f0b0041c0100300294826601003a0803000c110300010300703980041540192500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 108857949 1250 108856699 108856739
    0x9280602030424060302040e030a120b010207050607061415030604020f06160b010509130c03080705070918020103060501020102041505030c090907320d0f06090501171207030e060d06 80
    0x134940e942001103040c10300031254410f035000060b50411010705001450a42d17a54a44589503803180c1c00385116034001c2c48842c0c0500400741c10240d9821150409802034036520b50011501c4440c240050f80c1c0d48041c8100c40d25411b4000c0c0900119121502042002590000d41c02c1c1c1c0940100a050045550703150080001840340721584880c0d0714000070001d0040c002400c202c805160044040d002419107030701070381a02c1c1d00c13000351a22244c00c1d003002c80c0b610b0701c60742040420514004240c206001c0495040a00318400d030707001d1088585503c0124245d000d00d1050b0200f144c0000000800d1600881c0595442055080d0b80c909040703141001400c61902030700d003e4041800500b41d08040b041840b05554082c0004c906005508195240107807588940030045596986c0c601011101000b1a003008000300f000e00c105000b103585405205071510012070482041d8822060402d4407203000c10181d514240c0c05448204e070302c0d1134800034030040b60b01210001c05401e0341c03200007107146505400e240c04401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 108859199 1250 108857949 108857951
    0x30403320417011a0904020907050f03040c0321080a0209010e04050703051012030c0f05030c011401080f070f0302040e031606020d140f0408090d0503040e09280602030424 75
    0xb000000085084659407043c16164511840707407100c45442d0001c10503002541a5441d18103a40d0300c0108951900640c0505d1041c88400410302050000c0240b0410991b800340701d54440d02010f0262102c0f40641008419020456880014003c0c4c00c00e0b50140014142c10f04000464100420000d02154012102203010039507800500c5040304400340e2203009008032274003a107461841030710013400641201c0d00003090302c1001407410003040014402e83d041590400000c0c09400d4261161a5503030509003c1c140c8075204915035803150b00000241041115045c03001c014190b800c50b005e0001400000d0980780d01488100300705006412004030150510b8004d00300144c49120171070506050310b0000126600121601c17052082c26200c41c2c1940750415407007030301142d07070303040400c04504034810525014103640004030780080c41d5280d0070a090f20500303981c005e50310f11449d0308800c20f100c1c98408180100045030898240002a481ea00a41e0403900620901000d81c0980085202c91341013640224409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 108860449 1250 108859199 108859229
    0x402040b120c0408100f06031209050306091506151201080f0118030807030b04060f0803030a0509060c03011e050904080702030d14251b140102030304033204 69
    0x140500c4109500444400d030070301e1802e0304d4018403076502c100d520110302d80940d80300c88400030821581d00c208011a48030312202d0010000d0707400503201e20103c2c40b9403400780c00382c0000503a8240e00452911003001204607507030703260b440d1341c1c0905c2061301d02d07900116910325041040e0481c0705450b0103414001c003a810010000024540049401e4030701804000011003205940c400c0040c2d00b10714882c1d4403090031b140004590207100c001502801481d48452440150004c0120302e8600100c001c51140780345220a200b103403540306250343c0c0c0707032001c444030291310038240014011080701c0801a10801c044856664890340c44000040b4410810b49080f9040300c0009214011400c06000300104c100c20303414415204102041c9000441c41028ac0302d0a42c030f45415100b14640000220543c03060f500002c42540030a820350b28102080380303901841c3c1c1e110700c0182c2002d5107076100000f100e100e1545591100c0d0000e04030300c6d141421340401d8114049080701d5011041c019002100500001d00404590100d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 108861699 1250 108860449 108860467
    0x207021c0c0f1d060103020901030609020a05070219050607030804030201060518010305011a0906010c0519030503090708070b0901030e010b19140607110d051e010603021003180308150402040b 84
    0x500b0000c0d44011040c0501c0180c01c11640c00030304081d64800c500b0f09000d40d480c80142c0040340104159004454281d00c003151400c1c40940c840007a006040c82610600d4110314030903440c0d66046070038803845074000010061503000910600080341c10034420700002c2561a150b03000610300c0580992540c403001d17500c0c40100b013800004d010385581e0a21052005250811040c0498034441d0004d2203c0d041c05481d241020401100f00300092589003000070324041403156190003061540140c821a03e0b512032180007045504020483d5021101c070074461500e0b0010103030040d0040c100703c0b50a503055558480b404403d5403075440341d0000d414071000d00e241505003030121501c80e44005802c0d0502a803414021800020320f076810488280c041107441d484c60401c1e514041c0e15101d500c110342c0d80c0c041503884011024081c15007100d01a240700721100304130003080345003c500700c58902c08115100a103260011010034060b6606541141d4189501c1c84c00c84410000702b4203990080c0d00c04035100900051600b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 108862949 1250 108861699 108861719
    0x9020d050106141005090a0501081b190f09060c0f021206091e0c0109031b15050d0605041413030e04110316050c0604060b010504091d0606220207021c0c 67
    0x8411015040450429841601047c6101c50900074141070144000200345614a00c041c0c034482000b400d070b951640d4684100b061040600740c0041400400d03c81c80180002c6030140e8001410345800f81e6034a4640501c80c2c80f15400d4090400085c1d811144440f00d60000041c180400d91255404100030300360883c0b0480303500b141c0441c20020506503040450094130340e0381e00c585c1050440ea003107030050707803048820520503400381e84035070100b045640481c0c2e8840e030150f00700010302200103140d40c00304131183d91001488155080c036084000c1180310400010081030490000c0c0589030b01078644580c6002100b0301041c106c0e441703170003094800d1001208000c0e0008200040880c0c030480340c0382807030034090300252882d500d4802400040880751603426806440e44500103890041210100a0054540c4c140c6014100f649a8119006070b00550000809034180202610040f4118200083c20008004c0203070b0025080f15074126406020303030110130300500755021200c40c0e19000315002680380303207403407040c013 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 108864199 1250 108862949 108862969
    0x1b03130c0602010507110c0f09091e0a03080901060506090103230709050a17030f070f050a0b04260f0c0a060617060714040608070e040c0f02010c0c08090409020d05010614 75
    0x40c0c96808000c05910a031503508c4654100d07801641e800f205901d42d015a0360030070440c0481c1c4640419030f541800c2e45681c002441010070380c001d448060503070715820b000909a48080c000c40307402100400107800c0d15440390740844034071102200c584107005061a61000042000c2e240313480040d40c1180140464030b055030313545c40105592001000c00155064070503450780100c5560541820300820090140041d0100c0740c3c0e41a6440b106035580142149010700030010103450907240310f01c5000b8011800c0a01102c8601803c4481268500b081040ca000618a5116040511407409111181000141580500805059024411407983c4c116000f032500d401002000381e02080490b204030050001144216019110545041e02e6142e41c0e0050035a1350f03000100685401500e082c1c0060003003a80036004d10100e6074183c3c021302019130000e8040312101a210350117804260300700b0142c140c40c58107504c20704842e48041c1c80c0090702091030311010308440c0194085070001076000b00d00c2c210780ca4544514 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 108865449 1250 108864199 108864227
    0x60602010f02040f140307030b04050a030306050f090105060307112a010507030c080304030e0d0b0601351312020d09090908030403080916140a05091b03130c0602010507 74
    0x2c604140c9000804a0380100c1840b81d000501d0101000f131045840602c504006940c0280384800076086c20300e07207160366021001c0240c0009241c00d802080501c0c2c0015920700c41000182100c1f4540d003418200142640040c00390742c00d00424440800c0034500a01156180a0146c032078144c0c49200d0300104011000756181141c100700c030404c44800025042a40e201d100358008004e65203c3d40e6500c1c080e00c0c0c9031065442c107984140c0b4400c1134030400a20b0a0801e104140a9231000e001e82c841c08015000098056485c5000300c80c00300b8009001403c203011164010b5001c03800448410081d15081d0b071a4508945140050304001041038a40d500600c0715401484050300c100312400c02078890600d18080500014200014032021031181d0808201c1c0c00e03269480e080d065100241c0d952100095a43e2000d00f03140900c030600b80001c0d1524100c042184903507800c3d207105035655510751400400e540000c0120f00750a00d00c081d503101240444070220040c201e40d4000040500f40b40300082d080e00040450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 108866699 1250 108865449 108865451
    0x30f0c03071703030c1c1a190501020c09040524150108012111150901080c03061c03050c0106060518120705040906020d0c030b010f0c1106030618010801060602010f 72
    0x20071a450b0700000200c0e94000e0f500b10741140c965007008100c000148545603d502003e091804400303800422030100000704500b1200741d04604152202421030144500c00c1902680014202d140281004040554064401d030f003642e030341004403029000207028140111202090207000c020041d9484240d03211407100c01d003080440d0b50302d0011810103400c6180070758100c030340c6008200010030420071800005403d004211443c18961085951007a4100d244000d0000c1c0001d004114100b1000f0b00701c07801940f014003030040d030744800811142d03018000c0108034100030003044080d24a0000f0700c91040036045581d5400d40d20781c1c0319000140c000108084061060805041100d88460001842422101c003507402044c0ca003510b081000003402034640000115061140c02d800166160b80000001c1c0c001340c0707078542c03200103181044602842507a401405107030791181d0041c00389000d60265502101c02092000407108001c49620701c40000c1c7c0c001c41071a07440b50003c5c072141c0d80a0103441c10005440300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 108867949 1250 108866699 108866729
    0x20d03050408070201050a12050901020c16030f110616050c04060b130306050c0f0d0504021c0b27010c03060e0105121b0604030218010906090612020909010b030f0c0307 74
    0x29450710511031460001d040c8480087c401a00303500490006000c10500c500412075480c10785142c50107503001d0608034103513010f0200c41c40440034000740300c0d5083d40d03001807050302d200c02e040d036400150b03a41640209a014005000c4034009100c038122030042244100041d04d854150802404203555581d00400d011041c28419807a2032900101020101c3c1e400c044003103010b86400380703810781c64410940d80040d800400a034142010810b5040700c0d004078420755078010001c42c0711042403500b5020560007041c900f40d4030042009100c94191550620721150107000955159520850841d1621400130303000c25114107081148501e0011b107240102815280820000b100140303640d00d501c61260301c0c409000310906440841c2d1281819035015550103844a07a1039a11003056402d64030017441415001400d01c18041000019070003010200d0300c0c0c0344000c041c0100b00750300700700c01c0d0680102415080d6581d0b8804840ba940c041040404040c000c1e8050103e07450710b10207141c2007955a4100ea101c900a40c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 108869199 1250 108867949 108867953
    0x311010e06160204330801060609090509070b03180714030c041104030602040b0c070801020703171e070302041a160b0a020f0a05030108010e010603080423060d0507020d030504 77
    0x20200c030451005a00c2c2c0c4807079201c2c28070003e07004282400d204030100380d400d0a03034451900c104c13800d440c22502d0380c064481c51503626210705081e01c610740a8032000410402d0200000d258540215800070300c080150f803540340d1111101e51050300119590b10001c0002e00d4135203680003003842010064030042040000e41e0207000701280d03407580c0034883e0741e000d40e6650404108003100c80003920083d55000c0c0095660707950b50030f441c02d02c43e00700d40202c0e802402004000141400148201e6007644c0d4103444004071020100501b00b0100700040070400d2200c2c0d0182d540740e10001482017039204403600c7c1c0b0300603180c5013801265141c00305030741c0881d040c1017800c1004038001c07400e0a4418441a901030011a816958140b000019015181c03001640110120f82d80c410990058065410b03600004020041482c214080c1801d81350b191101038185041000b040c000c12803a420103513400c1c244801d02d030404001e000041525039001c2207110900c26070711003e015001b5070611905048102c80d1406010500f401e03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 108870449 1250 108869199 108869209
    0x3180303070f120b1c14100203160e090115210c0e01030501050a0902071505150f100f11010b030609010504030806100f1d0927011104090b040b060d02040311010e 71
    0x208420a817032101d1500301c0300c00c01c0440d4501071144903000003501c02d40444910010b002e07400c00c0c1c40e8030f5403043d00c980c9000c203030301c7c4500794020713404500914000701c43e442c0441d1040e041c0c1c95080d045041007200c00010211703404660046000c11079034200007411600040c2d00138014a2001e044c2030405082100401a80c1e50340080541511144480180d90300c10724504841001030840c0c420441c50b09280030000724400440c0f8503921100282d4412640c40b990f01c0401800310180381104000c1140e1903d40c4074000c0c411424440c003c0c80d00380001401c50384c0000020318203c0c04480304800c50791194100410198446d01c0c0c40d401c40010b03107441000480e14800a021648000001000c102e0a8204120035845000c02078149450141c00325a180c1013003c40c654241844d43c03082d480041401549881000052180d030040107010601507041508040145000d4484808021351068991030040c0da165a01001840c1c640c00804005039035030702d586003039003440d041881c01070305100149040301190307112 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 108871699 1250 108870449 108870469
    0x161b150b060a1e031e0501080d030c021c0504090f060503100e0601030f061107260a09061107080105090d0e040c0903021201060806070509030106090605010f0503180303070f120b 78
    0x410801500b010007110f08400a02e8035a4801d1606030401c080c0700b0a1704030b130b5805181030765009000e60f1040b4543c240103900341d40344d0060326401a84a0305104c1c000f00c0ba01000411601c01e18035100d40380a6030b4000740b90541c1d00c540322081c091561040700308131525080110310703010300f0f1564007401040c410700059915280c0c1440301811040311448070078100103141c3c1c88484034a001c201c8075a1a0800e0b0309000e41680ca012503a1440c070548650050711800324101501c8501803207603184000c580c02c2c0319045a40a04140c01010244560040400e90860a000c0c040c80b85540d40e0003800300f4041c002c00103100c00e81d000e001902841c500044007010359400442d900a40f07405a5001007041144c00d92540140f031142d101055502801c0284003901e541b01c0010444420200c1c0242321454a0310400c03804c4540328450710740412000c104c02000c0e40d0080e001f03503500044454000038032022000d5041c0c2158821100d0300c0005006500c1c105c0250380020880405864032802080310b10342000100e80c580760 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 108872949 1250 108871699 108871727
    0xf0f0e0318032b0c200f04050603060703020906070c03030e0102070b030705040909050c09040309090f05130201201605011d13020f090303121608040308161b150b060a 73
    0x1002143c2000303038010204800007075409484580090445440b0083d6101a600c2c040e111301c4583d00c1c40b0900e40ba00d8000c1ca4000c0c0b900030094502504c0d0304800360000c0d84411fa08c56080401840710b0400b189116423294001c5010703896180e030304108e80f80028104002070f040010107000601c280315125521030240e03800d464206000003001c446500380245020b00d01100d2a03804274030001004201507100e06520112041840107100c000303191904402600c00485a10b05420b10f40d00203000550b2046425141900d040e2440c100b09540114009040030f840003621040c00b46902000c010070359010f440c1c44210101c2040002100b01d00310300140e211200c0c441d0310a40c058000c12005084007581d0211004110010112035517030202010045640c0e2044580c0342c1d00e01c880c50b10b42607050780202015881550326542d804065558038180b00a881d41d00000300042149801c46045020104e000c148411800303500b4082207102d5034105081618408030741030340125000d21103014855007101020380192 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 108874199 1250 108872949 108873013
    0x6060a0c02040b0105090d06060503070602191214030406020c060f04030804020f2206030c0506130b0d09140303060406090c1403190204030f17120a0f0f0e031803 71
    0x20600000495207801080446a807201f213050240040203000d030702280854400b0b80946d5a983e964140c2681c85905e00c580d0641424444a1031200113100390001c5000740c582400c106a11000c505c0708041c50707030002c4408840403580000c49440150b01045016404101c4000c49166403420b03980041007524098002801174492841140b003651302d212000c2442c03490414481625140001d02c040504428170042d902250b8054000c00e05060180403200d1146604d0030104080c0d1a01c0d03cac410140e4801e10300c01518580d6000c1100025407504105210f03449140008c0d526420003104110032a040c0303034403030359a062400780c1d1201e00d19040703226104034415803035055880fa0742d52440a40505824803134488460f200050100801a581b07062281716070191295407001c0c0700085c01907900c1d200311142000c2228444000440c0c3c004180c11107010340c0a40380021400851482c41403003614440001000c4641010a5070002d001d0700001810404a00b2030041c002a45078074500f8070115440c0c468820340d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 108875449 1250 108874199 108874211
    0xf0504020327071712160813060906030e07080c0d0c03050a0f030f08191a0d0605150d23070b0406050a09050f012c0607080c010506060a0c0204 63
    0x24a0100440d04040303080b0805100b440c201e11110035120030740344c040c14807200c142c40040020796000140e00303c0322040110481d450080102e0b1500e216000c01c00045070040c030304124845124505001d024010403443d00e84c06103240c140000901a81c260015014080e0702c0203004129100d8002051040114161805d8900d5103c505240d040710701340d504054000e1080811761800c121b6441c1715802d0300c43c003e5031414414141200c08a91244055564501050040d05444110f43c0c003540503004001240070709180c07110080021402c2811100c0003a10f80340d95540811401d0b065400d000c00100c0d400301c41d4092a52915a101c14913611403402c105040c450805518400358000c1150384064111081d155440b0383d9a12001042a4021482c0100103280c2000004081c2480c40d0303009050801610f0350460002c548448002890319000d8044000d80c07000340103c0d8580303e402c0101090707401050b209030b4031b41c000c1c02014291400900654081c41c020815100b103135510206028042c1d46c11103001c030325 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 108876699 1250 108875449 108875461
    0x25020c15070204021b01050c04030c15030e060a05010302040b060405090c130302090108030c0c15070303050403030b2205090a0213180b0a0203150a0803070b060307170303010801050f010f05040203 86
    0x524065290003d400902c0020150540c00c01c0300f10816211211000911081d80d8015882c4c0e4a40540d1000404c8404001c005000d070681e41d07010700082007c94600050b00d4024207032402e1074003406503454031245075180d00500a50800b4028521070110603241549410f16000101e81d241c0402404000c00c0e02c0085001c00303040110090758001035800510101d15540c403071011949076440484880c4840c41050581001401e00100f6910b081e03080f030602d10304003421600c054024185c0100110304040c0d0326805090103590340142080e454107880c0296035203030821518202120300142c807005041d803180b4039020041e51044628030400004000114040d19114281c00d14074040398001032951500c9070400140c3d980d141d001e98492428503806d001c030b0a00107014810100d03544e001e2403910350070400c580c03004900e00c09011500030300054101e07580e440e5607201e020112180605541080c0d080040104001c10090003081d40101d880d0300e0030206540340000e80503030380c0d0042c45901d009980100010719 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 108877949 1250 108876699 108876739
    0xb1303050a0b011806050901050f030106051215090102130302060a030f0212220b0c16050601092021040302010212090d02070b090603040311070b1225020c 68
    0x955020040300c04240c0c0380d1a01c1500168240215500e8420700168040b003d0185d01a00089a070302505180c4680d00b00b10921012001c2c504d00142c166403203220000303058491a40b10450940d00d00090944040800c2c2c08010101000c1c0090189a0040c050682500200703209081103c0d411112256540c6e8803010030350252414400b2044030b03510100e0000f0290500d04840c0d4814400d1540e0000f203000701da40c1c60341307561600f5500a040c8184000004941d00c144400800c245407000444811a110f140d8901d440c084090300195259034540d100020381007034012490301d869160f4a80107040400300d820148503021002c0f60030040c540200f000c1400d0500039070403554a0520b4017104109032030100724442d41d1344055011940144956000050001c070b1220694400d039400074019851601c40380c608445681c010312815945004060f400151040d61000420051030700b00045aa107141400441144002c018003004004843c221203c0c00558046584079840358200c500804032920300070610 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 108879199 1250 108877949 108877987
    0x210051e03070221030f01090b040905011802010e030d120c0e1018051503040209090304080a050a0203010513020102061906050d0b06040b0a0e07030507020a0b0114090a05010b040b 79
    0x1164450010902030107a6000c540d145485554000e90306821038503c50103052171000300d6500001882c1107005120700c503100e1f0000d4419060042001c12256095111142111940d040c01c000f5500114200303c2196001031f000504980c044000d09500c014401000d4840911400741c80e50095954248000e00c5000c0d1007126242000134121200c1c0d00c103d140081e0003c05d0076500121308003090b0600041c285000094411803061042d105411500c5079030a014400c2400341958525000c14040860100000c000c3c1011141c064802060080c50500515013143c0300038011882d002c000035005130250341c00180194018200380081191000c0701c004c20f00c018035460300219800400d040036902800091035038030740170303000494003004030700f003050b00b005070300c0703440b8420f0007110864040015100d90290348082c0d404070441c0142c52098100c0d03a16064a48003d81104a10182c81984a4500d00302140c03580d90022461208028950401e1001c41040c01503100d92400341d10300041515054462007454 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 108880449 1250 108879199 108879247
    0x806040f09260301141302070b0705130e0606090f040902060c0706110a111203090402040b04080105070314011a04080a060e0609010c0c0b13050d0305060418021005 72
    0x1008001071915101425041044450742542c0c0c45400c0001c0c00b00c40b110072203040310409a211212200004180000c805045041c0c0c0c802c0c0d40e09000000100c0c0c20f501d101c4e8441c0900e552010303500c940607a9007001071889a04a10007551a21040004030b0321b500c4110f90345481c00b1141000420800710014001d4800035000a405c110b000c25658424100002c400d825100180c0b42d031241e030b06c13400118954510703480b00050303c0d062610350040a98140400004044d0101c03009032443c050030070700420203036806940190250031000030708100f042028800c0701d0304606140340c28800c00c510316030441c4e48200180555018145080000c00107814002c084900901141080e00d030b262074141803120042544803400d0000e40169800944403030010720035642d0304200f58648070300000240c0c0340e007126042e0042400004948000c42c3c1c00100d0000c00c1203080c8034080c3d58010540d03161000600081d541c0795031180b485180e14010500c0103030340c3d00300000011612450702030b844050005400104040b04881 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 108881699 1250 108880449 108880451
    0x40f060303031a0306150d0c0b070305070605010b090108060402090103021606051f06020718061d0603070605040b0306040c0e0907030e1e0c040f0615051201080c0904030806040f 78
    0x10075805800069140795802c0c64428101c052005140d10350008403400c00d101d82907400f441080c0d18000c1030703d1541600a081850f070098450804e030b110703130b40040010342c045000400c2c00020840b05004850242029040c07103800d001e500f10000e0502500601000d101c0e5401048100603a4865810341d159101a40140b0704980c82500b000d00082506991401c05410380c01d10302c2011800f010b004804032500c0394024035080d850190242c0381e000000da8a45070413922113000140c3c40c21004c2c414036501c0c118030241302841c01c00710205407604003550b000c5803e109060108000c6110040c058a90040040d40d0100303a0002c585012600e425502d58659071004042e02800702003a4554404880050900c00308c8403482c04440c8a410100f400d00d01c2c209155111070807108540c01c254001d0a0740600c4d500c3d010036201c3d1900c0170017529400c59900200000c2c00483c042289000c1580c81600400718003000d0300c2200030b0782000c603081e604000d20107824460314501250860b141c83c3e0185090f945c04000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 108882949 1250 108881699 108881711
    0x6040303030218010906020a0308060a15050c0c0a060c060e03131d010503030909180705060c0c03060c0c2812090503010b0405010e150d0819090801060b04050f040f 72
    0xa8081c00039000b004005010359140001e80c04654082c5144400341c5410307400a04d0040f101d5942203402e200014251500000c0e00c0d500000c41465035101e0440e414620307220700303440c1c0034048001403401500e000d45d2071040c07800c00c0040200c6504100003010a0b40c009a012904d11524000d10785148216a03418540c000e0305a000603000740100700e04001080b06925040031303641d81d2401c0550701e000c1c220b20140d119141e100401c100040d91200e0500c0042c480c0c0a030380455590310002810b9400c4290310443d25002080f11100a14041c072000364040149050315041c88035188100f41e4621102c601404040080e550452481400f0802c58202e198800790b0580000b00381c3c0360080900d003e62280e14007a40c2401035000d0603141500586068541091109101e6030b6548d96541e1850380d01c07030015030031030490b11962020070010710060195115002c0d01e61200803a40d0001040800c1755845101c45900d8a0710a000024004044404a0310708491480c0c1010710100002c00400b10082c424940e141303030070303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 108884199 1250 108882949 108882953
    0x121c0209090c1c090812130203010509061e010b0a0302131e03060b1f1d040504050a05070803070c060f03020f0c0c0906240c0106080703050a050d050c0d0c03030b060403 74
    0x100040c840000443c840d580143c10031510390307040d00c0c1381610042401005101c800201244007000720b9000c0040c03152140c42d6001c9801290071140d0981e5507003c50382140c0c04100c0010340150a020320016100d0b5041441d6162001003101805191140003c1503000a1411961f8149000100c041c11a10b00407021000302028040d40023000d0b40704c02c0756003504241c11b064441c40d2400b0503c0102c140329010b20f500345c00c1201c0032620811580318042681000c81701260041c0c9a0b40b0495110b180300710f00400408090341007082c80c1a0301d551100a00c0e50080108800080e0181858411281c0c1ea003403050000071460420b60190007614404c0c00e018402082c050b0b03603900d00203503050825070180d81c0f51059480d040d0500500e40321000481850b0514005031101409445d0020300c0000f9607040001003041e103030450b0900b090410351040d02d00782d204c0031480c02484000c0c06888005001c90412900c2c051001310540d4442c804c0803100c030300744000840b15006050090f007001c0c011140050140b41e440ba164 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 108885449 1250 108884199 108884221
    0x20301030b07050a050a030b040f150f05031c031e0c1205220b060607140312070206060f0108060a0315091406060a03170708040603050711121c020909 66
    0xd1006645044140d070114030034a0065044820480060b40e46a2920303441d000103070041c2c10b00001103a00950798881d4036015015600c83c030400c0302c01440458501501c1c1c0303210252501000d4004600c241c10480461221400002042c40303810560b040104032101d1602b0103500c04000170384207200090626100001a03035124103180c610074510300c8100810f403500d040c0425820703109100c3d105916600502d410206c1c401440c0361ba40901c00503c1d0714900001551106d116a0080811080581c000b2450019140030380c01031917400000385c030041ca01854405c00145c0345100040d01c44d414030003400040380d225140c017002d8a010f960000c549024400048426000428032424199401e07055540c20100d50507001c10305034041c0400805516466040d0349607500080d0070440d018690b010100510000184184090001494a51030008091420107409400c55003800819030301034114200074180040400103950300100c0d110500840000d154481200070300c6114001640a2014400c0141d80d00784 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 108886699 1250 108885449 108885451
    0x30a0b0103050f090d0e03030c1506031e0705041d07260a0c1a0706110706050108010c0906030c02070f08061b03010e0601141611040506010c050322180203 68
    0xe036010805561801148888000150360104c510b4000c2180d07128083c1c42040001c00301782c001020341e440d25041c0304549250840400340e200a55418800300b00781807806004584041580244091080c20895411901c41005000b114030441d40c0f6079009096101c9040d0061890782844100d40445448000b050500780320710a213803d0002d050782005c0b08104010400004442e4884804100541000b4040c103400c2c22000c81c2e40d050745010f00035440429102d02804110843c10a40d440c0c0c0da280c1030511000381c400c140c01451440e130500f43c100b45a2640400704004841c22450005446040c4200881c2030542c4c1b42d003e01207240c80e2480100d40c520700411824056114500d4801238140d010020f9907550009104080c050003860000800301c1d4001c070802c034202061820303010700e44102d040f030315480130301c0380301060780e10fa1414480d100d250705162203031fa80c1001c82400c00140356445035940b0740d524801c0040003e10f414031000c048890307441c1c01142a001d401c035199080843c03001961450000d403c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 108887949 1250 108886699 108886721
    0x7200a12031103220b16020601050409031d1c1109090a020d110307150201050405010f0b0f01030b1507050609010c1407082b0c0207090203070503041511030a 69
    0x21600e0990860900900c00e0310741128858060606540c0e860180d035403c81003007443d10000428080d01c3c04001844070255a201310307a40c2c01a80031851880d40001d240c018140c001d207010300c0c942101000441d4005144410401003081d009400c2450f880201c1e00c1d40c01001140c81d15000d0110801c001c008500d42c0b4030b8040e400565000646641d000b03126581c502503494003030b40019003410a4008a0004100d9503002d0070003904030307000c41d6580d4540c966070802d00c142000045c0d56503014407003004001e00a14a0144000d10148121030070100001e510b240341d410b0303190500d90b0b180048007154a0300c49414080d850501c000701d880790514140b581d11103004840c0c1c1e20007075183c00042c003119400342c51200c5021078070140142c18010307a55a515007692001c0c0341c4c2c51f400070010455041c141491910100403501c0c1c0080456006160303000039280c03201d150840030340035005008208041d40c2c401d0a40b503100d904920005040e02e407003d00f990040c81d14003250380c01b00c400041081603402e029044060351003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 108889199 1250 108887949 108887963
    0x102070203100902100c050115060305040b100e16020f07090605130501060207090203090f0d050c010c030501050607020d08130b03010e070c03020a022803140c01080103110907200a 79
    0x9042c4100d20030880d0903140c0000c0d0710501a0143d20150751040800d91203480c071800c000030b200c0b04004003c0c030700c0441c650301400c0042d894004001c02c00494183c0755402070203e1a1521065040440e40008480002e10200040020f0244d03000020f01c01c0003035003011040442600c0703005455180c0c01010b81901d001e41d5010b85408a809000034403a03114880c121540e41d400740c5011414000718401a60000d0540c18281c4141c018036000d10a060004015201d01c82d20303216601e8445070991400d44800407030440506103000010402515080121162181d0444100000c41c256240c580540c1c0501e106403400c20030700d80b00100f0b200323810800940c140c03858048103940c00d958001e01240c01100d03080d0000c1c0144c118603044030060400034086500e0210009a0503140b04500c2130301e15910580c0d40c0103995a0300d0181056950600511640340d15200c00e180202031581941c0301d0380c0e003248512403d00c0c02448900b0005440920807820701d0441684241c8910b0900d001e0001c86a864200c0c9200351100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 108890449 1250 108889199 108889213
    0x1080c041a04091b120b120f010b010816090b030a0905060a0501061407051015050301020a030f05090706080c0705010b040204060201020a0801080303060f06130506070305030108010509210a020a0c080102070203 92
    0x710807080004d24400703056030700c61500340780d80d0001d080501900003100750080d0924429510440f414005284000d83d1400001400d81c9814001015100d01414041041c0e00030f003004d0f0215035005a030403055400008115940340c4507086503600801d00c4c0303070024109001d07807014481d1f18000c61300440d04849265a446180c160b0a00b444421442110300041160b8407c410407030003009980c01918040d54200e0800b00c48030354400100b030036a4030138000b0b00002a607405507120103200500c07400303810084002c020303d51103082010142c00070b00e000d84418508880825801d04000094001102004011b0001d6464a40e01c10029001c0d4001d03980c40d0300490002d01c0081260200081034070b200d00300042000c01d0700580074080c0411741c0d00c40050301c00c0c0b21068130000318540e01c0f22030040071081d1003942e23115601d41c900914182100c0c030290070601103410003105204040110511401d44a607504169941da0750f040c80c090340360205001703004203e075120010003d83c0d102c040d03000d80760b510700030b9082e5054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 108891699 1250 108890449 108890471
    0x206071a06151207090e070c020a0f2d0302040903080a05071707030b0402310806011202010e010e1908100615030507021e0303070e0d050a0201080c041a0409 69
    0x1d090034074800c0c2c101d0b80003807002d40800c2c88608000e0350031050905202e40f08546800f1550b2014030120380890203e210b00200380c086003040b02400c4018020b13040b0b0143c0e12410141c0000910802c228148040841411801e400c521000440c1006550041c8100244c1c44035180103000180100e5100b0310f21841d0400140f003403406881000e043c24900c407501c2072207a0b01d210081c0c0042503445146500190309100a84880f40c140004141c100940b00201c02106103108a0780351448190300f0440c00c1e5081039004000742120320078064606075090801d24945207682c40101c81b44285110b07140c0d4003440d46072080303010020b080042d1081d20000c209071041044411005400e960441c8162445401d91f00d65143e89284284d02080d0400c3c09441917500d15040500c8080416245001c031842d550000024001d02a410040d810880001660740b03500540c800d844240c1c0310b1403144d41c0603051027054800110101d4032102190041d086034800c4498030008103443ca400c0350001d000c0d040c0d040740703020145a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 108892949 1250 108891699 108891709
    0x4030e03150105060307050d050a0204151b0f0f0f1b050102010603020307030212030c0a051b04060612091e08030405060c0408071502030d0e0102030603060a050105030a0b130206071a06 81
    0x19414008071020070070303034603020602299920061a0707804115040c8044601e0703c03264010180101c2d00e4000c09620781d03040070b102210740400c01c0030150601c0480d00042c102520942c08000f82e00303400484003070070f00c015410f1042d009020400b0080c45006030100720410040405206c85180007200305511701580c031140164200c03002e03400040d61681c0320081c1000141742a02d0403421120203101a2820900011a8645460803040003100c503900442a0348080603030031600220305050484d002c0c0607042c50524003425a0000c4c0f18130011254545202d10140a0a4449800703861107410204040c6109820020229081503034116410701903c004030342d10100b14803d54080e24910f034090b01c0e605141845100e000900020300006501082c4500360034070744d0f14412003890071001000943d8a02d17001003050b043c030400420040441d8074140040c45581c40c0092550078490b480340303000d046619058111400d0341c00810009500c20000621041080300c45095900c2c4610048985407007130715000c003008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 108894199 1250 108892949 108892963
    0x510080c150309010204120305120a050601050a031a03031602030c060a050306130e030a0c0b07030c0927060b0714060f071407050f03030603120708090607080c0d0804030e03 76
    0x9a0101a204078604074141c0d207001180c00030056800103240556a00a0480e200e515500c15004540301043e03000301d00e000c0404160348074100d05070400c680c1c03a01070b002030114000c800c50007081607a9406107410398584417200340c08031178008040b00c2d16229030310070045031000c18a500300d001c0c3c054840f01040394103014040e0307001084075494a90239680c036002480720340c500040803c0303221600d500046041c1e48044c001488107000c0342e41c0d20b40c00740d0090b040900d441000580708604162034854003100c256840491402903469040c028916844880c0f0061300c0d40b604035814141688c07904500241c4a07501324001c2580ea4410030b000038001f100c603899940c403400201d07548080003891b000050407103407148044801d50380b0310002d5a424130341252200c92030100000c0107042c56920000601000345020403032140040c01c0034844901c1c0c01e450740c2d52403071301c0d000790b241c5103000d0000801d244e005c00542c038040c0d03200c10b00700c80102d0f24400c41c04c80d0010801c0388161415804141259000040c504000c5080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 108895449 1250 108894199 108894223
    0x20c0f01090807031b06050112200a03170c100e150c121b1c0b24090409050f071a0c1c0201021b070e060603091b040207120201051008 59
    0x45400e0040304c1c0c40a54034041e00210036144020440d004800081080c400e550203400248000d441600c0030340b900002ca02030203a0712089084501c01c1c030000d655190201c540030340c0e1b404021701700300503012001d4041c00d025448003a8414007403041c80d420200940c3e40901c81041030102191040040d10010440222050350384d051a6082080280c6500d0010342c42c04d6080242d00c1c1c502d844103040301c900030585420599551404480c482e00f10070b0000341b28058041200c1d022502d0000003002040e1040d4003d1001909500e2503d0119189100796580c0e44095080c5421209407200100700061640d200d00c800c2c020360703480010740304182c0d030314030341d038034260b80200c0c0d0f250004140100700b80c0980d091001c04501e4150842d902000b105002026009881102031401d80c001d110780b41c104200b01c944070b070009200d40d00415040c000c00c1840c01c0006a100e01c1c1c030407050182c05513042244040b0700079100c0c03d400502544009003560120b10fa0562025105500075007902980e66281d080554490304500e00d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 108896699 1250 108895449 108895463
    0x1a01050904081305130b150f0d09050a0506010303050a110307110d0507051201060f0503030f09011b1209061d0f0f010903060908030105030d030501030f03260901020c0f0109 76
    0x900003000400240f0b054400c540181140b195501c00141c0c81078414070b4840035039601e40c1400501c1d400c00d0054125042d044120a0f03041c502c014800b540d1b54003454188052858071880c01f1701c18404107200c00304040d40c0003004d80da203035038580c100940158029005c0100140e00d1140850f8070420100664009035400030f80075903040386000811014240c81102070b0b807a40a410000212a40c3d00c20380201050440c1d00042162817030461000c1e103041079540101d003e504200300c007400300b0340c030141201e4200101b400c020a0301c1120000100c250b50000e10014010302403280c44042844d04001440111945541d032420042414000c2078024541c2204240d0006604010310b4807902d003841121070805010724007038200f1903481c0c4030201920100350060b1441d410000c01803105003014000c20003001c80c103060901c0b4a51441e541d080c42c082d000c070b0026080100413820300c00d55447c0c48510100d0030400594a81803810300c2e50700f250007540001e031104254401c9610715100300006008041c0f40c2608410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 108897949 1250 108896699 108896701
    0x1151206051f0509220b0312031602070b0703020c0f010e0102060417091c05150903030105090604020d0213060809010e0705090720010b09100e04030f110703050a1a010509 75
    0x480c251007080080031905014084c46180d40319119003654500b03a40d40700300d03103100c41d002c1601c07000101caa203110014025001900400c0706400300d40122a006420f15100c02d00d2030861507412810300c0c03490740044000e0345c40050071320103040e070010302e40702d901e5000c849030807040910a0043d5240003200182c9070260304541c000502107848195200000300c003090120f86000d0000001410510052441c502c5500c0c1e26954a410300808001c21040b254440d64080f483d070410070000d59407400148070301807090032a800040c0c1c45448540686907064450742066448003544400190410a9802000e000894820001d98191014011030300d00c100032034003910304541401d0034072403010340082000080c840c140076420b41180c07101c80380c0d140024006000086101c042c0e800c1003c804005002804009503107003060000d034132484117060f042649030600030003a401644082da580d01d0f0401d01d0341d10300d003e5298004280000821a94a02c038414020480074455110561000701000c0c002d4a0708110303080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 108899199 1250 108897949 108897979
    0x10b010314150301150e09010c080709030b09100e030702121906050612030f04140103060303090509070309120f080a020a2307080d1b0e090705130e0115120605 70
    0x70440c51003008002e400070070300c45d51030302e007003196043c140d842840400c02d60010801c65200a03c038103441e4088514000300c56081c0300000500d601030780e0001030180605030020980b900401c0040000008c2c03020810f100c03404044c0d252035120782103600141c4c0210400e07060042c1c50900846c1c0c520010402c9044080c1c041200d407200030041800510890300018003894400b03400364100050811104200c1c40d00c0d03034550405483c403c40c41d1500c000741e411315003407a0041c000241c201000300300780c91090b02d100840c5d6540342800c0340a04001e00028200302d0316540c10b00301013a4400305040140d12661105000e9403101d4000c20101d11680e5200000951940a0358182c040d00b4403c80d03000c500d405100785d0900101c1d49610183c4e521030403000f0b002a030740c0c145461801840c80e21a6810100307504140500030240c0002c2481031500401950802c2000207050031004401118000684111000000c0642c0c48416500d5241c68400f80b14002c100400320841c4904070301d0207000207903030002d03040b03080d031038014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 108900449 1250 108899199 108899221
    0xe0f04031e0c050f0304050a080c24160b1b0301030b040b0402060c0d090e0717060f0d06020408010b04060b18060d09060c020c09010f061d0109050a031103010b010314 73
    0x30082200c1004110100b0301c020560400034148030f0702d120005150b996141c14200718180070f0320381c05289107401001c122030195558003d45903400039011b9402e684030030080d541e0b800740d1103101c614036110f03030f02406090700b8010140c44503882038115800f038440010050041c4209030109100041c4500440000a000965500305140d00711340701400c4203080134160b041d0309040c44807a00c5c1c94000161603501c104a80c1c00c403141c04d25003201e201e00340300b801e034103940307442500d00710340105143c0c00340c1d090150304001d176101c07402c001212940156045440d507480d1600ca078003070300300406150700c520305216000c2180448038089950940402100101c401840c0050210380e0f0060080300142c1503a0b8101600441d005001c0c180700078901e640070304002c02202003080000d0206030446144c40125240c1848020780000a01d210b050250800440c1080582c0040b40d1900940d040b09400130b910a10010401007944191140705508078001c5c0510080d00c0300440444d0402282080159a03c00c00b01e5440c40b21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 108901699 1250 108900449 108900497
    0x30e19091112010803070c09090305070204090201050405040c05091002070e0106030b0103060b03040609030f050c0d05030c2107110102030c030c03060a09020f0c0f0c0303071415040305040e0f0403 86
    0x503107980e604000c400402c50082c1c0c50300f40d0001d80b09800006405080041c407000e900f000c1c1c20448010480d03000316803001040c502411000901030703030b900d100c00c2080d680134409036401002c0042003800308075415200103106421003000f05001c1c03002c402c105081d19002281003002e45401c100800d00684c6800c00480103042152007907810f00d1f07510303c8042004030302c400c021031240e400b0311000325010581d4038005100451102c9440d007003243c1400000c1040c00f0202c2c0c403180d542c04d1803910f1922515442d588a046220f1010b4211116480d100244501e40306251883c1c071501680d2140b034015201c02001078282c0c8403c1301c2100820b441080000c88204229018680003030703001e001c2d403000645401d02d030303412a480600c0310201c0b1000818140301041c010006080c0d000103050180000c4864070000c0f0340e40c0c0c091000014280e81c54120300703c50454040010b12034154403180e4218107410107050140c8103034080d004915400c1110350004415402c00c0000c40e000307550659406151031409040041c000301c07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 108902949 1250 108901699 108901721
    0xc0b0a02070b220321090602041503050f13020411030a0c02070e01082d07030809040e07050904111f09090f0209010f0f03140f0a051303051210030b13030e1909 70
    0xf0b14850019170032142c0e0b102e14001c80d4070134400103948500300308010b10480300b095401c908160510701005000850070301003a8000c054400c1e40012a02c444c80000c000d8841c50180c0740c02c484c80803003005400c01954102c8a508810f80d02034502060710740ea102c0391099000d004204403a4001840a0282142211081c82c43d039052880001c42d2460003150301c3c20900940e00c141c8d40c461000c10001080e14181c07049010211a03440241441854000401d84070640140050550b0782e603809080e40540399400300391907903010942404d40b00902c2c0321010340080381600500c90707094074000c200c16003d0b05601c201c84000c1c0c416100c50010064807441281c100045075855400c01d500c40028550070480c0c1100c65004210000300010145800030f000f03c11a04010700480c1c3c2a6001e04880b000304c2e03046030840301501e40003219000c95641d107005c075566044035a40000c210f5a040401c0266554400500e404c0c001c0c400c1e0303500e00100c3c16803020000e0b541001b20351104081c507464070030010001c0ea43d00c50300102da = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 108904199 1250 108902949 108902987
    0x10b0a2f0a030207050405071b020409060209030709060e060a2301120e010506030c09070804080304051905060f070201050114041505091003050105090109150c0c0b0a02070b2203 78
    0x462802030181007070711010040700541d202000074825454140102031340b1030410325181c4094584042c101c2506072060030040c0c00b4681c0c440080c1709000164044800389070015045400c8165181d443c440106034a10804017407030b4515021510b0352034188208001c4070103404c4600080c1c03250403141d00f031005401c0b1039541440301040030705d81d0692450088040e59400240005001e01d0840107240c00c1241441615110341c5140c82003105003500314892130340081d0070408060301c95485260503454950100c040c9074041c201a02401c04101000132800c0c4a035028000d11310b150340f2003003000d9007039074428000c0520307051084040060b18241680880c10000714a4a15507826580704040f890051007550911014601880148240f04090003443c1c0c1015201000704901e80703560721105030928481281d041c0303507502e80c0710b0410414800c01c00117001c290001c00e841c030700c2e007000110702c002580012030880310741a542d40010b402d080c101303015000112401c4c040600c10102a03404482400c8013503104c031580c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 108905449 1250 108904199 108904277
    0xc010c0e0f01030c0c0b012c040506010b0d09020613230a06110106090c110607051606110d060f1404063005030a020a0b0109230604020d091109010b0a 66
    0x6c83c11074180d080c000c044c80e118038030121040140c4c2c004a420700780c100e07030100b0300e0100c103000004030002603081c111100d602041c0d85650280352184052701c008034019600c61008900b402c40344000c01002e80c1150302c3c800ba00e003000f0029480c58641c0100070300705560302c4000c41000700103440c020203203042c0d2100603600001d54262076620402c110745265200f400002d00807500082c4403c020001c030f40d0402c171142070060805038080c0c034040780c200c00250010a2241c46000200101d800700e02134950340002103405111094403440c4000051480d4419585801c404c42008111410f00d441000c040d14400302848034410004450302d002800d1082900c09202840308400c1c1c0450001e01c060208488958068034010b80c0c00e042a049a04044c0c0014070014034103400200f0404070350809031150425483d01074001c0d6203003000600280249000b0030f03405d505006100c010406c1d0f10b045c0503560f02c8120780040e09640c039080d02030b003036009084455011403144019001035007101080c02d039501f55145c000f0031507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 108906699 1250 108905449 108905453
    0x40b04090f05010c08130c03080901030e010e0a020f100504090207050307080415030c0e030d08040c08030a0c020301051005090112020a05040207050a02010e0303030907230d05030c010c0e0f01030c0c 87
    0x81c1c40c03420000e03985039654128080b04582d010701455004070584000090304001900c4031100169540b00042660000284039406a4029045044c43c0c9144100030011044400d80180c1c54000c0c0383e03c200e21425400809860340e180500f40d0050b4010155145401c1c1382c02c10a81c10001e50005406035600e210510044001510075001803025040c0c411000d00c0c2c1c80d0f1602c50181c140e0718114078503c00d10403d0061001c46840009000c60f030000c05160079038090300c85040c030070361000c030a401450301e6000004032040070541284040120314800d50007013102d0384d03d12404212030a994010310b94801c400350010000c0d03401e01c10340b41d82d8031382c0001e02c04860107a03514000341c01c1340d200780c004a0302900305096034400d56030404419001c0e01d0080c1c1c051407440ca000c0c0c1000762240389900030840041c5050000454415003240f0b8400105d07400380120744846111300b0700c02d940b60081140d218082d0f00f41030045510521451780b0032040c68000c0c2c04c40c200c8000202c0158007a00ca80849941040800224040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 108907949 1250 108906699 108906713
    0x6040506130906050307032406170c01091d07050a02010209030105070c0501291e120105091903121a041401061116120f080a030506010f02011a040b0409 67
    0x1d8040c500050070061500c0c02e41c075141554181d504c0244645c00244c000c00102d1303d110035083d45103210f000e03041010036105c6052402024541c00c01041102d4205641c040e004002803031303040d24070003600c6041800b59120f0104031004540144072001941d00004201006c2c000c5000c0d007050801c6000140c240701111000c01e013100c504503900c00009040c1004075043c408217105008844004030b5614000140907035401c8100c00b9040605400341881003648800071001c2107125041400c001d000b80100a02da1a086003c0c140a4440e0384090040555161524014408460106525440d00200c0890002034070300101610b040c452840c1c100b81c0c0414055603214491003421002a5880300340079410014004e050034010411300c01c440c3c4c0040c0600ca508101400c070002150282c06108500c00321300c0c079260482d4914250020002000031441418494240d00050721648003a605d01015508583c1d08900b40c1d10300f4242070510042d20520a900342c14076801561000f000680042802d003040e642e0b0503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 108909199 1250 108907949 108907957
    0x7030c1704170a0b1815010e070809070e010504090602041509170d081918120e06040302090a0506041b0c020a0e0c030c0304111f090503011104060c0206040506 70
    0x220040c030000d01031002c91001421040d002a41200908629003540d49261400e40702800c0b516141c0300c030321002650980c0030404003443c9901901404015691103407204001c0b181603600d040031505007000502100000549107003162904d1410100c10f034688818031001700492034054074403e07020000070500148120160815074180e036a0468060324040380403070040a10f030fa01149581205052085403540072001075007181c04010301072032042e01c0c454424024a40c004080da2034407134149000084c031541400000800680341c85465001c200c03441009040e110b04c1c04000d5011241101103120400300740e00040d0f0101003d0f100203031711a21107040d41032041a07010100e00040c4a00c01240442c1000f1340c00c1e1004010341a411055410040300d03012040c08000d00c41c0c64035150103c00107040c031000700410142c03100c015003040b02c20414085130070414413a80010401044551b8400141410140702e00c4400d01c0d0400340044c20282025011603200340301302c138241c0e40040d040c4404605075682030014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 108910449 1250 108909199 108909233
    0x180a0c0305030304051b0102071703130f0816051302160c0f0f050603010602031b070b130608130c14030f060c091002030705060105040902012303180307051207030c 72
    0x2d5440745000d142840ca41207405038a014014903060103040c203640c0004424040d0f46000440207490b04c1c0c00d046140c0f840c001c0080c50f542803866a1000207000340c4811000b0180c85a610980c0d20020315008044546002440b8507904094111903c4100f60200d038060034901300c2c030402da9a00140640c6801580c000c840d0070511000341c040d0010400030340e114240c0401400181d90443c1198940107019480c0e01444c0504602e1902c5500c030f411142400b802848050302100f000f040c0c403801d0005184207a0800c070301032a4089028040802c06022a955108a8440d408400030700d00da800d2441e10303450062501c2c61950103104056962500080c180100f0348580d814003010b0f502d43c4d00b640200100c560403c00f03100c040d07400c100400c101107100400e41c41d040d600e00b520085501c8025200480710203d54507004480b038028400c555500703807a20801140a00f103008103030f9250301b40c00d42455460741f0490000610590143c03031600c040d62020406401894000e041c03041d00071005442c0d4003045d0402c81c9807 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 108911699 1250 108910449 108910453
    0x30302160b190f050f0610050d02070305070c090b0a14010e090f0a1b0c0605070e040e15011d0609070201020c0304060c020a0b04080c0d050f151b030609180a0c0305 72
    0x1a2480521161140103601ca00341c00084c8020b0030304152100040c60060012405124803d20400f10360b4003030701c100d40d1100c7c0c008408640d41d282c1811f0003845d42d00000004c403002d5250710320010b80a2401d0042d40c2091a0003001d0b0540c05140440146a003c03a481009041c0400b0428400031030303403400d2030640b14a02c400d007640d07400c1c0785c0100c0c6102110b000c039a04d54600c54442400103034459001b130107015401e80c0224001107c1d201c642041e91000310800280790302c00e00304284045003d00215400030140606420000c069884a4005050151910303001001038000000122640390010354503408c40d020740001403400003548022030550380140c1280c8040307003000701c03040d007103041c03500420000b000741e5508142004d007010310064484031a60700c1188241ca2800900c41401001d00081140d03015032000c4031207407800c003045c191155504848100f40e03202c1c11211a40c1411120048034850300c4e00070000c07a803556462420300b220b02a105071b504681d114102c8210700182d002580003001e14020f0340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 108912949 1250 108911699 108911731
    0x31806020c0c0402030f0c031012050307050c0109080a0201050d02040504020708181903020d11100906030e0c06160804032004050603010e0d0e01030f18020a15020604030302160b 78
    0x50740a20303100004001d80d0146104104025003c03025000164010741000801952921082480002c070f40c1142c000d5004504041050020000008020481184540c0a030b5010005080040d41c290019116800b81034101004210041d803080009028070508540014200394a590108080381c205420841e062440020007a010764150308016120f50801c5840071004004d074500c0081d0b4803410b201c02800388000c04e0070301c410040f04402c000324000d0f000d0071110b08800558001440141244602e80c082840c00700d00080b0b0850201e0442940800500302900d0002c01000c2407020080080083d50304050034032010000680d05000c0240300b1040e4001041c07000071081c100011240f018022074403d0b0700d0000e000d1a200d1004c91011180e011500304400922080350041c0d010b8121002c401291301c3c54a070a090302c203403040909e030354464000c1d0b500041c027585510303800088400040041d00036902c00000030340080e2094009040c5a0b0500501241c240030580c0c0d00c03078602c2c0d0142d6100070b88a450701 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 108914199 1250 108912949 108912967
    0x190c080d031d030403020f090606071506090606050405090408030709090c090e06040e0c01050c030f0304060e0d180e13060203072703030801152c01031109030c1003180602 75
    0xd5244000c014442c0196103003030f20710790002c0c00071140d00800c9406111000d0010b1816a25803082d00d400b19040740c404598001080e40701c1006204500071600d60b14900400803c11a00ca00309507000d941c4040c1c95500b85450fa80c407000c81a4000806000812450040114170340e82e450050607244c062030b40710301072418141703110f070002c0c20030081a10b8080c41c608016088404400111110364500c20308065070303182c514811442c11071048008001d0500400410701042010a07840300c1100ca2040007590315541015100311850b030b000b08180c545403901c070601404045110846a900800c1e1402214200b400e16611101030780c000301c4010b40440c4103400a83c007011181d8502c104050890124107143c94116a000740c0000d206006410500034860021410036028426800c41e1a405030440a820944010021114007510a034140043d0a06c0120404250200c050300c94542000340038022a07100782c01409602c1111a480c0c07001c254540740c54803112510390f030001c0d000d1401140c025940b50541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 108915449 1250 108914199 108914231
    0x1201060305070b0408061b19051b10050703020702240702041407020106050f0a18060902040b18030304050d030c17030c0a0201111305010513030501110306040b0909190c080d03 77
    0x2810f614400c10031444072050481181c088030210000c440c503019280ca60300100311a10f000310302b2503a41c0c1c9031404043e900c01480c00034080c8080c000384201400a0f039101c0200b1001da00420307100a4024204a01400006a8081241040041803003001d03042c03001070b80026081d140200d143c0095242c03c0c205100d40141d0a0003440060001600c0c0440700c441840301250f40e00525100e9100d8026218440580307664042e00108002d1001348070554540741c84100a00995000e4070740120611312400501c00c0c14100401590304844000f41400b132803521584042d034400100d510200c451100c08400a8190182c0c2000355010746c100700e4460fa11508248400b03800c580003111864042a818080018411110b04405040d1071003032a1240e2100d05007603001c0c0885116400050640d42000c800b0721904401e94040c41c41101c040303909120402c4120b0034000121404da424120765007108603038120000500045400301885900256100d50342d03007410a0800801c040361343c0000351280a03e409035444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 108916699 1250 108915449 108915451
    0x506071d01020a0c090f0b0301060f08160b030105090916080d090f180c05070804030609030905060909010b0901020a02040608030403030f11100911040f14010b0c0303061201060305070b040806 84
    0x1e000400314240305490310304080d101480b450941715118040000015a02d0708a0302c0190b4018009000b46a199220b11034591080e02600c18a48126504e2409840440ca1400101e54900d800300d032459007042c3c140801600018082c000c1d600c00c08244116950303910383c0c0000107284040c050290600541c50041c528041c0b0351210b1211505c206040c45074580001011914045074040000c90340c040c0b440513282800303070b42000f50503403002041c00018400c158000481032407080e50f038500d403a0348480402113a8000e03410030903001200075005000755015513005083c5000c0500485004611640c0080c040d01c00d660050101070300f01080420801d80c0201c1003c0d404492400d06030f94880c80c400c800c541c0c610110828002c110f4550102d002844004210a007280f0380c0a04142b059601c40396592000e0518408403000403480c0600014001a1001c1a079103200a03450181d17240da00c0741000c200c1c105989041c01c000e42d542c0e80340000000f410802a00d00109412868142c68903c0c0a21050074900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 108917949 1250 108916699 108916757
    0xd0c03060b1909090218010603060501020c061207031a06040803070203010f020a020a0809010306420c0803100905190c03060308030610030e120c060a020703050301030b0a09050607 79
    0x89040c9902c1c060000c0ca090ba0310507100c0c00c04001541c0c02007400014400880b0901101c40c00c5840030010503070030750540211042c2c0c0e1080e001c413416071083d501030141d03921400320440c880e803604601045245200350813480400d0058030080c0d0200c000c240019a680d8455803218101d0380c400203103082141428050141c00720364060703045040c8040840065150f070303140c0e080100300410006041c1c0c4541c2c007075401040584400d0700d02441d420100d0210840c01c14100d040b100c001d001494007001141607003070411890700c046076a05000c481c03d503901c1292039000a4201016042c900c00040349852061040358070a0a40c501200030101c0c0101c003a80490304026401001c040c2411002d001140f0701004498020b40d058600020351603204104a0081c4104d40e02d03408140070f10301c10548003800801c0941041c86510041c1da5040d04c80a803030303404a1058000007008120305100400c0401d40d40310401798040d100031004076001b0803542d0f0b460f0902c03008035a040003003007006200c0d400803240041004020a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 108919199 1250 108917949 108917959
    0x110301030206030606030702010f0606090611120a0507030e0d230c0d110d060908190315030602090a0806011d0123280e0106110703030f08040309050d0c03060b 70
    0x9415a00850030b140300040610740220000004155018800d50008001030030140c410450192601001465003d29104240001e00400e01c0c11000100100304401e5004112020318908194814240c500e900f280005a042c441001894061a190140700c00015803040b454880c3c401000152400680301c00a803190082c3c0c0710300350141d03481d101d01d502000d90ada0030602d00c8000c05103c000090f0300841d6050018011410725a00c0810860004090000109074059882c044c80e46611f044040703030302111800c1d80401c805001000440c0c090781c020100010007408510071907448801840c54203c0c00c2e81b00244004000c940e11490b40c0301605100d014001103000100d00040300c1460f0304408030410303e52881031031100807240360000f1311380030b048084240c165000c0805030764003000e000c040001d10904c00426001c44226001c410045144815690325484260705180080b0085504040060044050080041c000300d107607603903003044a02040c400d18203607105038154985030b81a1084262124000e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 108920449 1250 108919199 108919201
    0x409110a050406230a02060402011b03091206021e03090d080f0601080a06050a1202040e070806130312050415060501031107020607050102120c070b0105060a0c110307030818041103 79
    0xa81c04000c4804440803407500c540b410340302c40050315110301204114203440a00040ca19038064012845600c80e6000b40c9031041c01083c0c02c0c4c0a05c0340410441c0008001544804080c444414100c58600009003e04001801c1c800500010300018800304a0041412008000c00158060030030090f642105c0514000388a41410100d03240d41d101c000d880300d8107024a150000785082c400f40c0c01400100402802800f407103640e032020701560041800264000c42c240304c451181c02000040000c105d0701c041d0010310305543d8064405004100030b4008500b000a20003603181000d030980120350003203008600c0d036925101000c2e4001c0032107203150706c00c1c2d0506040c00c6c504511b111074002511442901070780c42658807406440c10b240244201000c1d20701c201030000501c00320b00122009000550301c030b1107124015903250340030050140940c0080d0360004405003c5040040c8401860124541c00501100e807116101e03a1040718a4001407854840030b29000001006840d080c0100310442c507003200803030b140d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108921699 1250 108920449 108920467
    0x11090f0405070b1e0903010b150a0e0301090f02010f050904060f050112060506040909050312010b031f0302090601030b010c120201020a09050906060706020309031c0b1e01020c121e0102040911 84
    0xc1c00c200780421009000c0410380c4131803911b0a4101050a4000800140203080708100000244c0c01ca200d60744000358002010f01e045003014468078950580102501ca0f18600c10740c01101c02c070404100350403c120701031010034103e440310f0250601410031840c0c014451410074000524030141035121442450400034200129103e04007218103a81d010799012400c0c9000d420407d2840c0301d80751740111305142100000031040307000b101860065070b4001caa0054105646401042c0c00103a000c00f96000400c60042481c541c0280e100741c0c0011010705092080d11272985901c045140a1000c036000350350001000050715620503511009000c0882e541c054905041020594502039050000d0007942d0001c082444001c00f00240c07034580c1d10540d4010041d01030460300030050300c100d12400c2d006800492064100d80c0c0080400c1c04222810b81c0100740c040b10450030040403103513504d10404d83d401000b20515060b95088200070f21009103100240c1d0703d601d03180302ea404464000408a0103160305002582c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 108922949 1250 108921699 108921727
    0x2010c02090a06030503030a0207020114180405060f030105091f0e0601120611070c0302041b050904050c09060720060c070303050a030b0a0608070201111e0711090f0405070b 76
    0x145501a100c072076403039440100c1e61004015540025010340700200411000303e80a4006114544c400e80e5060b007a00c040c074603441c485004148003200111b44e0703900c0040c9141401d0303015581c030003c000d041030121154040443d08454050b00c090100c1d80181040319500c130800a81c000300002591300030818000120035250f02c0d00010701030941c0030b1584824030001d01455420210707041040b041015940e1040c1e182c10f42c0414058401280203504101000c101c2d001d42c2d1250b44500892910740d903183c50343c0081088010a030003030060000c0c44090041d0502912810041c000e030034401d01ca0300c054014070352a1100c0b40c04002c03e0701d510500081103078211207080070903060110381c1e140c00c1c81c41c0c9940c080a001c0e000307446038200882e00441d03030b107000141403688001a035000b4500d5070001c12078222011740e00191441030903401c900c0d450070000704a14124081700100030860041400c052094100030004047e42c609031002a80000c026082c0070902c481441003100410130030850624102000b94441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 108924199 1250 108922949 108922967
    0xb100e0415030215030708010b1314030106030c0902070c0e0411060a09030209040c0303032901140906120115020607120c210507030b060906090d030903080301121703040201 76
    0x10340280d07101c00706040e010001c5041e40c4003841e40100b00681d0850071150740501600111881800100c00c08000103210300d40034116843d4140702c05c142c411072130a000140710303042c144403283d0f40c144d0350f260000004900d05058060107003085007405aa40c4c00c0c02d0400c01c8003040d882e040552180401005c0c400040e000712400c2660000645600f41c540440b0001554491071550010390042c04400070401000210184131081d00d00ca61802c201c000700000c41e0b81180c8030309174800c04045001284060b240e40c05040a0030528081c0d4041504c5d2660078404504260000303090342c240c040d10040144814101003040e1105040c040c0b005010b03034640020001c1401c810246503074405a5075804038042d0910030440308002110311040390000c2000c054401008007030807640c01c00001d1608405404526048089034542d08000b40720604016508081025403000706200f00c0c284120000000000b42c0440f0280d4020719116030512080042411b1500200708142d0000440300c0c000c008000050303070000060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 108925449 1250 108924199 108924227
    0x23061602010c02120105010902130806280f02040f05010e0102030a0806091008060403020a02121f0b06070c06020f0607030e03030f180f071d010f0909050118030804060b10 75
    0x1c2d0700c03101c0c1c0d50700109801401c144030003000c0d542040004902c2c0025a001000e51195890b00c400c105540d420362640c44100c26640c9000c40e0b0551a038408500603250a44134004c05818030001e0880c1d0720581d014200d0341f00f54012000505d00d0001000150303080f03400c0f021034023400e002561911001030002421441e00504403031144003040d0100c0c00d01c000c01007810015042400850b1018140b03030401079500d100a00c0c003203200386c2c084e954081541c000403810165843c4415110180b000d000182d8601800d0074082c10303900a00280101c0c4081803001800320010400c0f5005080468024900d203420304400901e1401414180034094280340070020840f81c1c4003a0032040c0c50504c0d15141c2c0405a0103000d420212850310800003445620079000c20603074125030a404064060390310303001d80000004024841c5580814451404100c81c81c21074011081c140e10034000000d50490b4404013501900c003002041d80094200020041001060710076540845011590525562140f250040040c816420380c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 108926699 1250 108925449 108925457
    0x2030a030f0605090a09150c05070308131b060e04020301050616050a02040e010204090b031504031422050f153403050703120902100f050c01062306160201 68
    0x1e010a919140d4490409800d0041c0010321034203084207028041c280c80c4005580780244040704003070b9a176481c0b0440780d60030902c2c6c40e4641024480c0d2030030345102000401c800d5461034010480f00010f03031810550002e0440031000400d050342011002000e81030f21a020500036841040140b01ca0780e00c003010f40c0c007542d1044044100321549882c1c00350808480e200000d41160a15850044620b0190090002c2d952416001c000303034913451007050303910500403550101c0200402c02007004644100720344049001d440440030f18180102010010b85031140704d001000712100d000502c05441c040c141c0030012001202c0482d114010362052404034401c0c4601c1c20304c10901c680305403510ba00280c46203202d2607100611400010207501b0054102c0e4420942100007555500d05680100e09130310504214a40103000d4640f906a01c11050f200994255010320a0080604c084141c2c0202400350788060080cac440e2a00744c0b4403e0807290a00c3c98207984a240c4030b28418045004529480301000c0507050702464 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 108927949 1250 108926699 108926711
    0x306010e09030903010c050d0c0306032001050403080a030606030e241b040314011d0a0b07050913091b080c040903030e0d180509010e0f0402060c071e080303010602030a03 75
    0x180342d8401c51079020f8142d42007180f10b1303043c183c000c0040c10014803101d005000c4000b030f01000310103e407036a001c01000000c541240307454144010400000750201070401c1072803d80c0380d0b02c4a40285d00b1001d50361001940b1148280f1006903d80148400c1030900c8001703259a0480a6261101c800d40103280210100650001062410000d0000d0080c1c2001c14290390f0b1035486e0308050903c2e6503454440340070340d03082c40c806203803d4245c03552a8150b407400d28050026546070340e80e0509842d1001c2d1a42042040c01d102c013100a03581d03450000c00c41140b501000902020780c0c50301801d500b01200ba6000701402c042c1c0304004030003000c24070141041c8100d40002c1c824200e407501f5401481002031145047c4a60144914a540c01100d004225030380112900d500300e07036480410000507001d005400c0e1220004000c02e00b00a000401940c12510017400700c0d080403441c031062868000903607c0440045501e0800030758001114006e03601804210340a54619030401c68081d607a8894030031007008040d030b6a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 108929199 1250 108927949 108927961
    0x3140f100b0415181205010e0606030a02010207060f02010227011106060a091d120301080f070308090d0212010c050a081302030604031202070c090203040213091106220617010f050306010e 82
    0x40c02c4001070640c084d1384e2004a01e1031b04000f402090701f00100d9000703100781300104074540b070000341c0e10705502d034140c0c010300001d8213041044654022614402082d903401340103108207800a184444220205001c1030040c0c07017014800100198101c1280c43c2c8140c0040d000c4c4241c0303841b81c9201d02c068074801040801d2a510100c5e40d81c80000c902440603102d801144002224640900c00860480d10003c0458078024010000652a10414132004211180c10004980c40b420841e513600003050000381030350114092003141e1401d4410312400980040c000180380100c440c0c015401c01d400c21404005001d00460300d80c04642d0340d013800780001e4103211005e101e002128107590111012a68071034404038140b580d0314020b03406900709a5089100352098a0400340c09003140c402c108940d5009450b07004003602b82e005004880e8031001200004019849607040c1c041c003040400c2c402004035981e110011100c1c84030190500300306070041e200014034081d041100c0da400141050540c3c007643c495813080c0d1510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 108930449 1250 108929199 108929237
    0x81803030c03070506040318260a0c08010507021513030c02030a060906051905040b0705030c040f1404051e012309040f0302070614030a0c03140f100b0415 68
    0x40798400601c8005200070410002280c054002c80c07007a280c428603980410000c01d40c80c0304501442d4028104036115404008840c907110070303440e2103441a104180d61a0322108900d00494015640131b039128001d20009590411424803048912001650103017030060002140582043c03000e41080b100c26141d4003036690600c4189440e41d0301580410000320185428405002c0c1250722100b2002d82d10f0a100b1a00014060070344510b5000c0c042c1e1003190f40d4604e0540d0b05420260005104a00500010610740b8848a4070b00142407065441414490800c003000706540d00100865110005440c8603e5040c0000c4482415602c140e10500c0e0641d1003110305c0121040346400e0940c0c0310043d1001d00c03050141c2c5d03c00d0300c1e100c21f0280c0d0954100340c0d1140803d5400403c40542003040300020030002e05110035561041301c80b600c2a20b07000c10f103241c501d03841c044440720660f6400c1c2c1c0c500e1440c05202e80740703030440b10560003410f004d60b00314200343c60403c841d00c40101c018580e0b8103015141004103800001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 108931699 1250 108930449 108930457
    0xa0201020f030f010806010e090307122102130f0302030304030b06190e071d0d030e03010e010c2615060304060902041b02010b0306280e0d0509180408180303 69
    0x400440c2ca9141c060098801290280302d0781002d0700070138002045d20307a0702d2410305100d0480c2e00300643c0b81c51104e80d19006a20b900042043c104459204000410b001c04101c20108400c05a00540c1314042c403502e5120070042075000c03541c0c00500c640c0800040c0c8001c001d48040b2a00301000015582c0d0703000214400340303518411a03080540c041c0000c5489002c40390064041c030700a0f910b926183c2540100c03140b006402c038050035885018650028006403040b10b224440d584050b0020403001c501d81001030030748001811000100c0c1d20006224058a0056030074001031400014103c061f04144c60580c003840750340a07080380908400030024090020a81018800641c0548204110b100c00c88a10803005d45100b0b841c801542411501c3c0f0951600058481c050440c08010b450b400c601d01c1400d11608594592a5071041e4417031a2602c660201804a0107000c400741c2c42d40e030f94945581e010440f14030940d010852520b400c0c00d0038040840c0e00ea4041d03503004204902d9034902980f07460b0019103503000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 108932949 1250 108931699 108931717
    0x10e10050409030f02060609010f09020702061209010504050f07030b0f0901020909040309090f091e1b06020a020108010b030f04080a2109121d04051003210207080c060f0a020102 78
    0x81002c112070105903100390740ca1000300c055401c0c0e43d43c644440040110041c000c0c441c4081549001c0b109010590003540208142c40c0700912080c941900443e10b48081c40c0d040340c60f501240d540c2c20400003407000a01c01640449070810240086a003940d5a42211942c041e0004158001d1103001660480d4258125032907008000c00503034080c0b42920f0014000015070050400c81e0f4181103825140d816540288241c495011041136200521076003500baa2950401c4240c07003407803402036031f18042e024a44a00b00030780b01d181e01900c1352501500001d0170103407042c0d004807113015040041004407007404101d1a0010b1740556035543d91407500300119000501c3e94034002d214250480303410700034145980a4030290748155a1750205200707450f004d44d400840c442e0481f01d80e601114820b00386140952115610040988012582688903140d84904280b41e118210406d070310070b84030030110740e01000880d0040c034545000300071450018012279028003e44c4a00c091030903000c10210090381c000c0d015035805030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 108934199 1250 108932949 108932951
    0x6060b0c0114040b0a18060915180f0204050709030803190b010f0c03140c030406052503021e1c050c0601051f03111603120e0105061c02150c07030b0c0c06010e100504 73
    0x24403d042c4142d640c000141d00126a510b00300f0304511208003180d0ac0c540441e005801040354010b40d40a01024000c0100030f1402c0096400307020000903486000745000c3c1110040d070410140c16812a2401c403607a01140c00c0c1801207022a5005003580b152001d010f203981460990341408112046401d10b000d0031440c00c08600020038085640d6500c18041c0040c00b510000c1c4c0780c0e085d804840c54460010100700042d005070015503ca0419010703001c1d18007100814002203ea1070925450080b900449040b80040024400030380741e40c84c15410051540501800c4408500505e07041c010852000b10a185d40020300d13480b070811030345200d541e1007610980070b40d40075244041c02c000e03c1d000f06000d05403903070308951030701d460b4025a01d040c051044500c10400035003a03401c015083c220f01d01001c448400102e86c81162950001d844540202c0500021000c04005005407801c600d0b01001c40320008008000785002840f00e4a0300b01c40c0002e25604480e49110341e2021a10707690b1010100f6141504015002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 108935449 1250 108934199 108934211
    0x180603090a0c090c050901050310080114070806030c060406031505090c03040c0608010501120209040f090c300803100b030903070b010603020a0c02061606060b0c0114040b0a1806 78
    0x940049080807145210700c1d0005540d5885900c1d10084807040304d0345100240c014022440d865004a0041d6003000806427951a0543e0307800300242541c41da9a09100c03484010000d1000460308000031541108041f0041c0c0b00c0da420200108150f402103205031005c150f00c890240f404443d80c0c4103c14043c0c00064241c580c0b46c54041c0c4e003070055502c2518200d5010308030380070004481d4420721035107040e0f94050707407004201840641040044d4110605096000d40e5414090f00303404028400e8803e264801d00e0819002485c00e8480f0001c0b03110000001c2665a00c8219031441c0c4d421642200001e07544a45d600d40c41ea21a4207440d014004250404540c003000003007030106245001010b403070654071484440c0c032180e07242d0400721301381e0180e01c01600c0480d603174160250051401c6005040d2001c1401d50100000e03a494860740e0507545a0f074040c0c102c4400c000341c0012003617420700070384003514000390000c1014101039490084284000702100d006503a81d400d8010b40740054041700030700c190015414000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 108936699 1250 108935449 108935461
    0x17040308070903020901080a140312060d06111b0d05040b0d09050f0706020115060c0f0f0305091905030c031501030b0a0204150e0405010509090d08060a030f0c030b061c0305180603 79
    0xc1c5d1010410180da552703c210320903079561ba00000c2250380110104031207080a4560314203101ca4a415000101c07000c0c0d894106800880c01050090101c0c2d4007001c0c0b49104841c5d9050040d07050650038814001000401c210034000d03c103c00040350103040903000001441c00f11418404e082c540c01845464441c050140001aa1681500101c952003c4610f0307138402240e482000b501c050034043c5000300001420380455000c56884400707010b056000c0c7c1040c9243c1a80b54000a0804040d5401440305042c01c0c4018800350404000b5900072003007e5000f0000c5d2081c481182e002d102c8144801031503e2403603800100904c0301d03501910020080c1c4552001c06005000303002d440e191a08103500c0c001d03031502000280360f2400c1c80c85140500b00f00e00c00b4249903a69404d0480b0b00020041c51181c026800750b400000042c410360900070041c2c000d288040400d41107240032b4545c1c0e4800380149210383c1040200010100852803050842c990500300740390384030f42d291000c035130340c61000c103080d90311690110030400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 108937949 1250 108936699 108936703
    0x60207120503180106031505130506010602070807150e0d0c080102030f0412080411040c11060702070e0c040501200a0609060b042004050409050a05120a030501061704030807090302090108 82
    0x10064111011803405522410f0302c540c225226032201500780e012000344c81103141c143d5800503810003c1c3c1d481e416203040c0280c5940745020800c0c1d0003080103a00200c820400310f501405888040d0014a00c104101945040000c000c0044148a64407511300c03106003d0030400c80c505054000e00c0818020b5440340b03070099030943c0ba12011241a1511034211403902c003818815080130740b0841e4006511459803269100b40030043c406a41e04405111120480c20000340302000118869900c1d03500030f206607030801418070044080908600c41910041c0410300c40b6131b0f000748800c600001c01008403e201500e04050510301841644050700091510b41114107008450300820b85d203c80c29502031003250400b04078141c8080340d200300c8008d200014071082c017503417070b1070741008281900800c210313040408185c96a504001c1e0ba02c2141030040b03000035680700400d4050240c0e80c010034241c20071060740c2c15403072905082d4110080c00101044078441c000b4101c1ca004452001c041c43c0c0282c1183c01c15030f11074040c40d1b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 108939199 1250 108937949 108937951
    0x60510090b03030304020306180304050603040b07090807181e02030907080d090506040b09031c110705010804020d0b07020319091805250c02040e0c0a15020c0d060207120503 76
    0x10303100301d04014a407101030400000b01c1e4010366020700200116076440c01c4c00c0640c40c0b006c05498010380010400007405030741360301c0550f00550291100c4041400d041902030145d80300c5522098003604040307020041c80014a042c02e000c0c0c1c5a110b00400c0e28007039290911203107000c07140b04040d031a2021050121110b00011400c1c00d490035801190381c0c6481e5038409540c1c1030703040d102d001d43c8100100024848144884003800d115040a001c4607203101561003c201a200d444c0089800101e090500314100401000340710001e1400f0300340400241004d4000c0780b600e142c01c0601402851a41001c00d824500c20030440355a180c0f4500107072040b40000c01d005040170854464004d43d01a05c50f01030800400ca8402d036030090f0000340058400d680c681e00000c00307500030024440d040c05031041c803240250f03c0e030f4007030190380302c440c0740240840f90194070402c0220308003500040010304100d50601d0125070000f800c13920701d210840e0341000f010200e240a03000ba2280301802420303500c0d00400340e04401c0d0454069 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 108940449 1250 108939199 108939209
    0x114071b1226060307060c020315040b0a0c0507080d05040317010603060305120f040e0709090612060e06070e12100609020a0801122111120d0b09040c031e060510 71
    0x1a004010102c00406400c5a0503591142e240e0001c03042001024003408901d140d0a10107400e076121104945558520f070f00c0126401c0d03074442189010490200c02c207105503008e04005041c0030742404e006480350b0401d4007031202407004599860002ca414940210900e03150000419810a50343d0784804e001409001144412a01407007900b800d99000c52240303041c3d6015960b48032107141002e00c2e03d1541360840030090054018070000c40c02c08a000c0c9440d026440107020100411820b600f40da20b0075404031407215100103400d411110078811050742c801c3e0355a01d010000c0701c20f400c14400e80c400c11030528036031040e14401186406000281614180c0143c1000002c5880340801c1c3c0c1e0b40c0e00c19800c54000e2508004040c503400644d0040c0706495030701000d0714001d030741c0380c0540000c86044036540b421552003030b440e440f0b0002042c0c803600f21002c2d001e5000c1c0c0440646c2c28a000c0d081581c3c1d914810b682d140002003076003080740340c2602802180606a0b90117904410180200c0c24200007043c92005076000d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 108941699 1250 108940449 108940487
    0xe04140a061a04090b0c0a1103070f030e030a020f04021c0e060601031d0d08070e060c0606100507021e010c050709090c06050f0a0807031b050301050906030114071b12 73
    0x60201c1c924003842000229034003c2d05901c0705e69242450f901c140d41c00189441d0500181c0c8080d011154001c00c00740c032866209103000c0411891a042c050701448241407020f100b6400100302c0001030700d81d80003509019209440143e1101c0d01c2c0050a07851030002c81d2100310992600111010700500091a103009032002e807400c2100d2440c02c400c07000b01c01d86c83c8161030482e40c490600300300032a11402c0d0042d07000d5250b14000000304c441c1d00000b8401c2c1d00c031294003011076000005221103442c0c405c075585c42843c41030401615218855010602c4400405041c09003030b544000c4a25190340607513032416035a40d010041d240c0d07039511450540c00800780c0a000356080f0780004800b203250341c0907208660000c000c020402d418030500d918201d4000314002c00c0c80d03041648544510354124405400031014100e1601ea42d5101d49c10001400020070b00244058440e81c1000c50141600015900c0c094020055281070502003a285c40420701c0c5003030700000100b01c080324484042c0040d03806040c202c107100350313112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 108942949 1250 108941699 108941741
    0x21002071d0a0b0a03030c1b03020a0b0d0f050601020a06020309070306090506090118080301090e0f1606080a1a0d0f02100806030d030e0706050901020106030c06091a07030206010e04140a06 83
    0x42800f0100c1d0303145c08001c0105000580c17007000306611401c10403030b074028546108001a03c9034003181c60080694481d0720f4010340414540320036841406849020250240200f007280350450000390f4034201c1e00f80143c031499001000c43c41500c4280709150180d500000e09011140d11483c1140e5901c0301161306003419460524031220116041c501640303a0754011007040c0c01d513420b260a6400030b142c0794018600600c900d500400d0100e4003032114035114070b0141003240e030302854420042d2044074002e29403050145015544005802007858803001c001050b21008004021403429240010110304060740c44001f040b00454020f40c442c403203a12810058080e540d4034052b04a064058a8020500d0003031074001110500441e4880d0002c1c2c00d03684030510001c40d2095036030729200005045600400700040c52618184004c40c9100540351520048042c2c8914102d03140e10300948079803040c010400480b0016021805108995031880b00c003c00c0901601c440c0911032800c040106441c020648422401003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 108944199 1250 108942949 108942971
    0x10504091e05070f060c0b010e07020c091f060e06040b09150c0601060f170403030203060303090a1e0812160204020408030a02010504060b030705030a080a03180c180b010c021002071d0a 81
    0x250070745051f60060081c00740d1303405c0000c20600381000500c2541144240030946006940c2c0c000d41900800e1411a08407000100000e41c0c0307a480030680000c810302c8086135000c0ba03140ca03540116403c5403d201c0e283da0b102c08001d030000d0240b182c1001c15840e0200042000100007502145080c121003c80e01c0c1c03c0701100070b40d44203450010140b6440a100d000b00300c001004a03010f50011503000030000c059a28260601d8006103102107144c1140440202041c145000500c40c4200240505030110050044410b05141c400e070782d100d25a507440691440744116400c54a490f01594081c044200c2900d46560100000038008e10080301e0640741e503414403080e220355080c08200881512800703800740101e944652200703569503100c0c140f000101030703031594444004515282d0459a551148001500c100e103030803d034a159181c180f103044161840c0c900103060a03a000f039815280309505aa50745840b54034910b09a080c5034060384890719440314031280300360031840355a0b00c510a80010408001030003560b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 108945449 1250 108944199 108944207
    0x50301060201060918020f15160b0c0f04032012030d060510050a1407050d020d02010c0806012115080c01091202030303010302060d150603090b0601080f010504091e05070f06 76
    0x10317a80300304144136518008409810720f1055501d42c0800503152043d00c55116500d5169503008030314440381050b07029848420040d0082165400036610840c09081c030400c034007200060320840c40028040500e843c0007041070603007083c5050407060024406081e0b0400200f44507101d50158006480180c503041d00465185400102c0080c00c006070341e039982c2007505802c415140f2500700350b01c03402150424008180040c20811008149510760343c09424809480e07540682550503200805081c484000c0401140e030340e11503000c54406400e424441c0812480440c500020840e0210303120342061880c602180011000851001c142402c2c1e844400032980c84000c0c008034110303004000d605410400040000d841c05402500c00141d07081c80001e040c8440328105150074045c0e6008801182e242c280c0c01e42800010346074a030380480d007824100322510b403034404000d0340001401100d00c43e99035207c1c49005d0201e400124000d04444901040340d50402c1c1c1444c1d0343d5400315103da00070381c811800d000300b4040c1c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 108946699 1250 108945449 108945461
    0xf120c010e0718020901020111070501060f0b03160c0f0c06021b06040e0105060f1c0605130903080406020d0f180b071821020301050a06030b01050a0308031302010219030503010602010609 82
    0x122444000d010a150842c201a5005c0e030900c5045640b203038855003c0300064002050543d12410000a45528004440142080a07840441901e1081c406c104c0b03071900c0484201c030b01c030100c0e15103500455501d00d4070540d440702e04503000d05140d04200b008500d0940000301000307060f6084102038402842d170006c0040b184158000c000b620240c0d00010481d504044014102c4840d5450b25a428a4411640c100950441300c071a01c035519182d03c0104907509043c0059100002028014800107860b52000750501e04060402017581c1c0d0f000944503100000e039403100a0b84681c80c2c0702840b02c3c150304c50464481c00c84000d0f080e81c4541c5480040340e0310320b0045a0080c1c8502840d540405640c0c5024960140081c910140c11b0014282c9030183c001a5401c0c0720320780c413178501c100001501500b90708100e421054160803181c0204408441400451442e0080c1ca0f0f122012071132000c0b80d0038061004134240340c91642e102001f4180801d295040641190285041e074034668000c02a26659034036550035104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 108947949 1250 108946699 108946709
    0x31e0b01170c0d0c0812180109030f030f120e01090506180a080706021209100606050307270906030b071106060d020910080601090c0809070302150307020f120c010e07 73
    0x40645500011800d203c844143d4040c010710031824510f0342c4038640d5041410184a84e0030826002a4900b107407480071031000720750002031800501c600d0456980d00d035038100886e03026042c841d0b0340a000003100c1c0f0419482030014203041c0305000e03914980603490f01910080300111403d018400004180c4038514001180711029a0010044081903442d090b48a40c400c40702070303840e82d40800c660000307a241021441d024501c0c0c80010b00c500b083c446210710840d18150407500401204006200440d54000440a00d0400a401095020000d0600c8443c4609647c0c00484000d0815000006220a40004c644034018036120604806040c1580ca03860f45030482d45c55900c0403c9404203009402c180b840d1706c0c3e00a1141c0301d40026940ca40d01094a4078800760301100000e900c0e00220200c0e00e60003040203410200c16401881c030f0b04e04580c00a140d59244940d52410440e011000030718062003005074440810801d0141c500101d0ba1400f0310240d680040e01e840019824003c050710080b00014080c41259 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 108949199 1250 108947949 108947953
    0xf020c030403030f0309020301330b030c0c010b03100b0108090d1b02040b0411040501110c030709020f0f0f040e010503060411040c1403010801020a030b0603150402070c031e0b0117 79
    0x1d811076070141d802c0d1106803150400c041e030b07400e2003c005840901c51208060614207040024101346450382101040c0e58810310120201140b04200700508030080ea9040540c0442e20f0740c8030318001c0c124500508018411941c54812280a50b90000c0607510a200108003a40c9806550f5903011400d40c1d98011f811854001501054400c0403803580000c854039810710013000440d051002400082c2500c100e51880f2100480c0050100025a0452400f8400c0842000078248281f88080080d4884100744103581000ea00060f00c0070b86001c00c64112500b07164640c4850b0384981484079411420b41144c021101c560ad01c1030004100c0d80b600180484c0710b10343c04000f0138025108042800040d020b50031984080c0300c441d4803000c550441980113107002c0c044000005858200413400102070b20280d02995018904c20410300101e00d0800201d442542820b842c051703076800b224a003c1c012030100d40c0c000b805040503010701008600c83c1c03081e004c500500801301007100b40d8a0710b49070040030340c3c403003040e258507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 108950449 1250 108949199 108949207
    0x110f130638031902070309090e0114010b0c0313080609070b040305101d0d0e09070c0201050a11191211070b180a08030703080103051507050403060513020a06030f0f020c03 75
    0x440c1c4030750003168045403000401814961003141c01d0140e07042007400b240440c24000c02841003651610445245aa00000a104005881d01c61803c0d500d0180100c21209030b00040a083c2030004008a90344180c1d0031540c641199640e0040944501c400e461032a8070b8080c090700011b85100312010744064940000c0034122442c55400010000c203244030f02c5903c10b03403441e8001016032030140920700c01d0000750b80b01c82e5059800d910800c00741200003080001030180d07a104401c05030760720034240c800400d05800d0030111400910702c014a4610350303e80c0c0014a4501c0b5031800200088100007500203649030701e5a2041210b82041d42e03480e45403a010b18107905e40240086941c2c90540c402240d00d601c00641091b80e45500c40c00f000f419035004060680200341010b004004119040100b41c0840540c20082221828481402080c1d0700c56844054825030311000480c0d0114448481c944810303500a12070001990741c0d4070043d014000908400410340c1c0342c10108200300e540c0b0300031242c00000e048091850 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 108951699 1250 108950449 108950549
    0x301150e0409030f1b15020406110304030f0b0c0c0a0c0314012d0609052a0c1203090f0609060108010b1e010507080d05040b04150c0c110f1306 63
    0x203004441703140310fa2000d203880780c1c08000c215000d0000d01d203070b0300030500540d4550405201404c100e06c54450101c05134000c20080010680c0144051610360340201c3c40c002ca030b200d41040c01e8050068a50400352f0740a0321800d80100844221424116442250414100d4031140e2003a401c0324088500100481840c2d2545038030341c0481d160524100220850010f200c98403608143d0841d0310417100c5a15848881c100511060743c020301c3d113220520403d6140703143c0702240080944034099000e84180119000c00401e0f460315050040075082c51040f001c0320418074040280b141d48200a1240c05581d500c1c00c04000360700d05003103404400c01e500350550000710f100c0c084c004580303d500c680d0065603d0403040c002003000c28054050749009a000b0303200354480341040e090909202d820b4520035507015140c01e0034a40201c0e08485441143c1d60015011a80305ca000d80c0030480b0000c4454034264000095808101d6040031039111000303450007844c0c88145080c07030b009074820111000d0100342d9122000124504 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 108952949 1250 108951699 108951707
    0x18060127030308072d031415150415080408160303051602070f05060c0c0604030609060b09040209060409150c0302071101020304030b0f070e060a080f0c031504051b0301150e0409030f 80
    0x1e190b03c21740c540003440c0c426800321041d00b0310064034880155040a400751026180c9901580603111110745070610b428544020140c68201d5070a04100f4886e0b441d001902340480358042d240520209050b079012104103241c000c000348401c40c0c1c1814580071044403200d07120703c002030200035030380d06210300c9441c1c1741050100044c94014280e4000c0d14403901a41000302c0c2c44460281001b90f1142401040340e921514007403040c1c400c50000b0b00d016a60100c00c002c05a41c42c010016000a410b89000520880c58180701031802c0d2aa00d010401c1418a00f0045000d54075034020078086000741e210007802e01d40c00004985a128901c005003400701c035540494a100c0c0c048010035003010440c18110411801800861100c0d000001054007080c9941c080006005031031140952103a403a80d200c40c42c5251407401849115200440c45005950320030004048615643d500400000c440e01c500340c50350f82d02e9a601c0222403692448038001007901d203090302e5500303050140e2a0031070390540399216010340c000d508407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 108954199 1250 108952949 108953027
    0x40504060e010903020d020d0f08010302120109050105010f030b0a020901140307020703020a0f08060604090314070206091305071709070614071403040f0803091806012703030807 78
    0xa18035940e1807040712500301e400d200e0005003510a802400710f5003131421001e410144c4100001090101202810440319841000c10341540c0c0e040f00c5100702c48004c0d0318401d00400403000020320035842e01e00042000741c0240a51411a0320540381881e51351342e03100ca518241c2c022000b8050115445c0c5035011285049400907503804203c030300c100c48105070380e07400188560145178030481210b03041c20b106211088062090f5a0b00840940c0c041c0300d001803d6a000741403100d00d4200050041c03002c2441800c558071a021503400e81801800080400b16050440c07005140c10764000010407211100e003d010261101024841d51280b0041c0c00d4942c41c11324141c0d5001540300c1818100401040444000352400110240d6900010002d54845d0308100f1103800c10310960300450820340c82032291031400c1e5030300503001000000d43e03d003209654444c50f0042e01c03154440c400d4410000c48091a21008125041040003101d000c1d584540303140e1100e00e4280d401c0d0440c1541300c03500d04560746200c0340c51040206a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 108955449 1250 108954199 108954203
    0xc09090a0b0408070209060108070f0f0207080f010c0e01180302090601030204081510080309091503010204050303070305070c050111190215210609090607030b01050706091b0e060a05040504 83
    0xa00c0316605660754501100008550407a2a6000818241e0a50404201c22030b0300100a0800341040d0409800280a4801e0030f241b070003c011002c01d003580e001d0310030312000c070007441c4c0a402c999202c0180c0d0050340c082e15088920800041340178a008903190700c5409a01007020316408021819400d580a200302004014585818140c00f00300c000381c10f0b401008a5100400706da28800c18609241c0014806441107900000b095402800042619502c804100c0d8101c48502d82101401c51594003007806030085501041d8180400318900c0c083c1900100100361140c82240c110740440d85a000655200e89074003d0b10010758000d501c0c1d4450001000a0407200d94001490360742144090003c0500c1c07503100c6209040f084212500c1c3c2c3c062100441d030110341200007250880d0179840c042104940d1510014280800c15450b810750300007507402003080f120001c3d00468140309540c901e040c01c02c80c0f6424403080b08160b203292400000e9004034500034030701802d001810710030024984020000078200241003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 108956699 1250 108955449 108955453
    0x91403031c090507090519090606050303030702101407050702040c0e04050910050a0207020306070c140a060e06150303090609060d0606030b130603031b030201021201140f0a080c0909 80
    0xe004119032400712214600d40d41807001144400242c90701c5400c0021a5010b801001d0070001440301e060544000418000c0c0281c100140c480110706040000e0880ca078021909400000103002a0039404100c1400c400c8200300244615505c4a03560080080101c032903800040d0284840d00c01071620703030070060b021031640c540300100d808900c002500311802036480c0600d541c0036000b498131400b094007035107602c0296224110704155154000c213460b003034010144010024500328650400c4802200c240307061203400c0442e04108540e1411a00828190242c020075106e0079000071400e5411038001d0b4044600078010314141146d150501c051600070013038559210b00c0510019001c1d4196104a200a212961740030442414070030510a04803010902090b50504103c401d20100303410060228041000c3c1e120045c1170041800d0403402801400d01c15003141d101440009441e1601e9001151041021516503115010040402100c40b07040c0c07050b00d450380c02c003400d03510a40c5080390100d0380c440c80e0501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 108957949 1250 108956699 108956707
    0x1b0307650c060a0618091a06010203040e040303050f0121060f111611060f040e060d060e070512030703080f040503090310020304170a051606020d0903080901050a06050109140303 78
    0x285a420001c0460303803240f03e282e45040c100b0008450704050f180091500c0c004202d24801ca0300c0310807844032000fa0b44031a0012a07404680940d100b001140d00508a902e0819071501740303803400a0190406581003980b0040e80d000201c0c210340b1130304071121000640240c0c004d0104682da10280940101d54281074229079950095507030114980042a16801084054614800c1c1e454071b1501031900d4006c59014800c24454042060406c0c03003100c0545242043c200759940e00c400c00118901d00e0148024074282c280340555650340d00005010342035681c200c2c0c0c00c2020301d0342c420b0030940e24020494003500281c03124001c50180c28072600c0d5150024014001e4034540f24100020a2526020601c3c62680f01d600100300310500103034601d074481800316510642d2800200840081990240030719070780d0081000c3d031441c02000325560460703441340003a41041c000003040d4100941040320403140040e082d420080040c00c0c1401603c9140213a450584a0700d1200307062220905407000b03581382d02509440700308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 108959199 1250 108957949 108957967
    0x501210b0d0c030b0a050405031c0b04090501020d05010b09011d0303040b1306020706140901080a0e0f0102041a07170708070503040f0321021b030765 66
    0x140742070304690050280341c0c1400e2451402c00c1950300001c140300c2642e4500300a1200240b808012140c0800304050200a540144403182d001822256440380c1d1151030001400c0070850f06401400c80c0e2210440108400c0c2e0743d900901e01584030301d94485001402c1c110f9951303000d00548110030f0030303041c0140451b41001e49998000510751711500c400d00d481c81c3c580c5001c1182c07603410482400900000c7c585103540890340700b02161903005078001c8034180314030000090f0400006034855a1071400b90b10490780c0b00700c0b0141c0d10318000e5005000b0860219030440d00112080c0301c90044075a6560710004521480700d406003410030b1030300304110803107000d0b10801074040840c3c01003002c1c001600e003c9890050032450340c03416054100004c1010340c0440b42c1c5401c400b200c0344e00420401c004000c81c03414994481c84041c006810440c158001c104c17000400d01c0740401000010005d40c0d41e080c1c0c07603840c10701c1050340080031284a01600c5c240b04a00803040c210030a0b4101c00c41112002451244850341c20030842c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 108960449 1250 108959199 108959209
    0x403060507030204030507080312070e0105071703060a24051e040603140a0e0c10090504060902040f0f0803031302010c12020c030d0318020f010c020d03270501210b 72
    0x10707128503002a801050600074007a05000b4034005102000040d032800b15404040200250001c04000c180040c00010b4842640034000300c3e8907160b804030945042c1c8003202011030750382c2c00680340d05000f000c031001c01280165484e601c0c003480804004024a00009481d0204c03180d502c4516000c00e805100301141c005010200060030203062140c8002c0b0310030b041851407001d9990300400a4000c01c1c103200160408600100d0310180001040e224801c4d51035540000b60345100f03e0303071310080d0003916081c80058110910741c058800e6400b02e13024035204030380c0d80300030050400380d901a519290700104041040310042811107104544107041a600ca1441a2200030802c0706200c901070250300f00811018092400340019802c1d544141020030108130414640c810807840380e00024000d80081c01c5618090f03025922903030490364010064150f0f565241303401003000a034404900c04642c0c840b83c2c503c05901d4452410000c1c1c803010380d0384141501c55100c0283ca8502c03004070302c01001d9641c00a43c1d05940312 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 108961699 1250 108960449 108960451
    0x4230105070c0f0503120a050a0c020109051908010b040e03121f030b0915160e0d05061003140d0e01120f0e1605040507050307050c030c100b091311041104030605 71
    0x240f00d104409442c100c14182041000d607284134200750704010720b06c649a00402507034054100e628010f200050f007880140c80070305d4150049a404185500c0602c18440175440d40d0050310ba01500030300070003070000d00303010550301800c2181540f6042404510408035103d84540e80c080950070314dc1001030a6808030700168905d03604242d8580c0700310810401014000c0015880d6440ca0416040701e614124241c0c40c0c1d03000c0361080030000c0001001a1201e241d54103003842c005036400c0000c0e5841420b200c0300099a0000920080714200c200244080030030502103000b07240000381b6225444610400801110540c42d41400207105a940b4041803104000a11966090303210807070003800d2a00000c01c26034603441d03031540314611450030301c0700b000182603214060f0780e0490102c4c213006d0340b201102d815042c1540103401c51a0314500c59031381d108490510a401040c41414140c0c0c004101c1c3e10389000e04d030146680c13a04054800a444003c1c1c003070f203041076400000c6c100800c01d801c1d03003440d48030760b0b40200350740c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 108962949 1250 108961699 108961709
    0x804030f0303140603060c0c030d0501120507060302180103020a020a05011b0e040207020a030206070203030c0619060b0a0c140705030a060e070b041505031b0a09030c080304230105070c 81
    0x54031440340010140c240c4201004691800c20503065403900d040080d07503d40d0020200d403070089020443c4d10307000300b00700152000c0d103144481c01d200ca0341e1600013132038403041e0305641612103205801000030240d0083c4200c80f21010403c1a0a4030200c045d00194003950210b0301c0c00e01180304007030303040d80070031402c3c0b080a155100c2d4200310b40b60a0143c0d5001881540c50891040c800d910420903e8016690007101c082125415200b840c2c80720000c1c00042d09600800f903800d41e0f1070098004222070b00a50f07200c06400100d5010b410030004c4e03250000f01801d0701803c1d10603000303d60100001004558010282d84640c543c1d8800c82d501c05803100007081c00c080e030010f0116103451711b40345d60760760800f824007a14024140d03000440b8103080c5042c0310208184084c0c10a0350907c02d0010104080e1440c07500c0d480f480e4a8228005542ca480c031034230045c102e8800e0322043d51100c22801001c548200c01008032401c4604844044000300355041103041c3c14220001918140203040112000259110050b02c0041c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 108964199 1250 108962949 108962963
    0x70e13050f060f090118110a0c06150e040b0c0c0d05180d08181302040b090306010504050106170903300705070305041401200f0111030c04030b0a09080403 68
    0x400c0090700c0e90404040980118030404141c0b480159548800054604541c403054240b1508024060f900c0c000b0540300004c00700e20340780040c124114a400215040b082c501c510700400104202940006118995008080940741c42001003400300350b15030300383c9800040c403402040c40e0460328400305180151000d908408500e0225480003404401c17410711810b00740c00d440e0740c0c40d003501940d034140c0030b441100b1800081c00080034280317001e0f0300e422207841002070131604110f503201e40b202440030f001c0d0010407c0c603109209440000c03655081c54006c25040308c080b519143c607610307141c0c0f0303009040c048028204034540c03106106041c41005c0314900c1001c60744425541d080641c18806001540400003856141400010895940000e03800307811601180d83c001480000102c0540048981e001d0b04d10707400c2450308001c000014100ca01285c0748122a4964008101007000508901203602040750100c0e85040d082c0000c01c085800c120800b644840c40c03100016000c54940e840f82c0039604542c01c20f031600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 108965449 1250 108964199 108964201
    0xf0607020a02030c15041809050a0b061e010807030905030c0106120201022104050d020402090a14030d090311060306010c050609010903080f060a0605090f0604120c0608070f0305070e1305 82
    0x90f0074240300c101d003620b2040d20042c1444840030b41c80c011603c11031289402080c00b0041c2440184429400f100c10a640101a01c00d181e0943c10000d0004400f0780e503080c8114200d03100d646400035220ba4103a0408410303103d1407139039524081c0030390082940c040b040c0c0d03050204010f005100c0d1404c0c850300024160703807070300141980b580703000080c0340c0448e0440c620080420f060709148942c954a0585007180c500f114100d4003c2413a00c0400d020f8000d081c095600b002d0568008903840561110611100c001a4100c64112100c1c04044038001e1403072001404071011070040e5003840c1440401940d000d003041c149202c0d240d5071581c0c0c080c47c1a400303c2d840030b0345075501c0d0400300405034040c48554200846002c2c4884509103070000500c0e500040c820141840740004007145213031076020b00c1905140004250070f03101c1c1d81d1070145034031442d00c1e0002161546d50810f00401d10f00e0080d955640146440d17036400c5041040344005900800024200d00d060146100118100d81c0d68030609000300341a4442c08201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 108966699 1250 108965449 108965453
    0x504050105070f05120630010f1a011b06090c03030f02071a1c0605032406010305010e15010306091b0e0a05060706150314060f1f0311030f0607020a 65
    0x1d520308030129000c01400b040000c60501d5100485038002c3d60403200b01900d401c0f903031f02da02c0d00070481c41c00e480040d240e002020410300c8819403158846526612040c814441c03905040141c0100748a556808156078a408141a05991006a1040b4030411002400620130f88840845a032140d2007180042c4004451050840e0705000304030080205903079480c14946560910036242c0a5101245904d041c00120344559071069081078009241c003500b80c803083c0d0034501e018038400c0300700181440d071603030384401040070b0354424402c107412161a00b0050345e050301c4d41e00c2c148080d100c0300301c85141050348800b40456407200600c1140b2000f201929080140c3d5240c403005045480b44044c1d4074858108050304000e04d8688200310355800390b00180028100c41148900380c494000c0b0f41001e0300310a40701403403188000001034205d010709107806520b0003940d654220343e0459562000d04030b403e1894010104000391034040498100070004060f02e1041108003606460300104a5221006920041d10101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 108967949 1250 108966699 108966707
    0x409151d07110a150905071707091a090408071106030a020301080105060a06050a050c16030b01180902150f12040501050a0c050f03010302090c070c0b03010e011e150e04050405010507 80
    0x4144202c15000d400c42e45199110a10002c05010b02022a640c40d034445100b00300c0103100e010081c20501d0300500c80449a010419540c0040f80541c1119604c4d1006802840c406c0958400315943c00030071080b1956202e5940030360540103048125150101c1911888079940e896010354413458052400503181d61620b040301382910000f074000d9028644a601c18032090b07500804813540603646041c4a41d035541c800004518000180b18035000c007481c8144044104106800494101c403400030702e180d9015034494200701105c54850b0000e42c00b08400c00709015041d804405020200c01c94005a42400b0701502c8403841d04404980031140c07030755640d0030044410040c0c480d08020403038030324285040c10403000c00000c0d18801800040d1003002001c0000f102c1d5200c1d40b08031010705a0001c00441000d60390400405550828000c00e10110304450000ca01b240f0382d1548018404420300440d4920303850000f0100360401000451410420400c01c101071715140c600469004170320800c00010b881c0f0f00f2040044c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 108969199 1250 108967949 108967967
    0xa03030f02090307050103150302030f0109110a0b16031b060b040e031606020c030f13030b16120e01020c0703110f180114030a020d0f03081b0409151d07 67
    0x2030129481809200a10386000902105483d070030f08000030b0100c45190207134038802c0282d01c0258103109182c001c1d4142003040d08291406880382c2004030a1301c0c03030141007000550450040a509020078401070101e425012010b8948074001d007800a8200c1250040d00448503a00009403016600c1c0c5502c04a54149445001c4003050b500e00030b1810f20415000d00040d55500c00303405850143c01150007080b800041c012540403040c00c0722025034503c00540b0440c0e0051041c07000382d0b030485842c00010100d894454010200d019141d948245868641c022140209540b50f540016594240f0549035041000c00119015601910315907149040100c00c00030a00c2000040a018550804544101501089100f410f4071a01c08100001c8170356140031030f00d00029000041d40c0320b540301404406001649000050241c001d41c2d50307500c55590f85508404e240c050991002d00f8220400c402c00014a0680c8a100d940d421000c40000480d981c40ca40099009203100c40c010a4000313005000e14031741c0003820300d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 108970449 1250 108969199 108969221
    0x110d0503070905010507060609020319050105060301030b160e21010b0402070c170c18040210020105040506070f050405090c0306120d05041202010509040e1b06070519170a020a0303 79
    0x240c0c030350714109000512846007071080906020f008610300c003c2180c543c001c94050b03c0103041c1191070746001c0b041003200300c81c03101501d091075242c030f000803605007010400c4a0503a43c20000445094440b03001215042d02266454410401216003040071540c3c0c044920045948030000509070200480100d030841d60a80a030b64481c40c4100003a07070010352141c503400c049034070040c01040c2001a181c0700034209451004c0301e41d440101423915900f10305038500040d005e64000d643e01c0d0440340c10900e069003207031401e03503001e07085900081c000760707a0505c1032882039003603140ca1612a00381551100850b445040948100044203404000c001050030f00095080d0340a190100414418007088070151251240780100d12003070003100c01400659000300120703049441c020704100051400c82c803656803215060030b081c202c59005441078543c580b4009058851440d00207000c0c240c0303000c242181c0c0c04000038018040310b501c0c102600303e001d200401400b0b401d14460341e8000c1c01d281d00c060715008045440e84c40304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 108971699 1250 108970449 108970457
    0x9040605032808040b0a03021801030903171503010504110301050c070c030314190905010315050f0609030a050a05070305070e0405031602040e010906061e0506070b0709090c110d 78
    0x1190804100c03035080750345200c1d164402c0024007601d0600740983d100381c0e0005101c81c1000541e20420591680c001e21242440300c1c014480c40c1c201d90300441c19aa108680980084c12801408030042113074800c1da9040710700740a800b2880741044021900b502c100700c400303480d134468805d01502d84c0d00b020f015250b80407840d003804910f03000d2071790350303a4101c00f031203000280403c0f10303a103800e14071281da91040350b03105240b1511800d0030b04048500207048040d01c1c0034541c0000d0a000c21a0a407041118412042ea080244804000a45201845269000b0085803907040c800d4800a034041a03081c4200c110643c0200f014040d950b095060a030701d042c0702c07a400707007214401645c10040420404015503062011a480380f0558040c2c1d400040c020b008a00440c8200c1d52801c2021000c00580b540024101e840c1c500207131a4034140742d000c00d045005148580c3c0d030009020041c481c001030400641c030b64004141d00306410815140c4062204071340d4951a8003002c20300c0c2440180301c0da8010803060004900d03900e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 108972949 1250 108971699 108971713
    0x81e060703060b22180203150306060d060e012c0705010e0d030c051c0905010305061215340e04050405250e0a09020a0e0105031905030d050702030904060503 69
    0x440c648a10038015080301950b1524481075014144411301c42c02000e115011064540340008042d00952041c0c54244464080fa0600303060380c10042243d0748141c000900e0b2039030700005078850340c3c05040020882e8946540e2040d052000102c064040050940308003030b103001e44880c0c0b060803490300c8210b400c51414800d0701901c80045a4a004680500580c545404c1242c0ca0036071504a00d07050056003074125800303c80d800400340c0c55100e20302200316002640c090109499000c280841c0c8080401224a00c0c0c00071315890000140100305c2c150007078400d0341d140442011514201d91307a000c1c030300c149030f8054080300b50b00e80496a004880c812500d0080b24100403509160f502c0076521507901603140e203510b50850b03d0110813265503401000511000403024038600c2d2009001e802001104030803072240d01c241001150341c51811040c5410781b40040c0040112103241e800004020030000b40881e03130303131208100010075140c0900403103000300042e0b0020340c1c0721005641000151002c030703000310340039511081c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 108974199 1250 108972949 108972959
    0x170a06050619020c030d050a090e090703080c070305012904021c050618040501090218190207080c031602040f1404080304060207170a09090501060507020f0a081e06070306 75
    0x4400c07250b100780c10040112442140c480c007a0304003840340004035858040c0e085020a015044802045c81c020641d403180d005c6d03600c81d082c207102e0b0701c0151082c80565001c01003c0c00003a050600070403907950420b0031a00c6040e601d82d00d480c25949071076041d18035811a0500d600500d80605580344400f203046505500f030030043c581105c55901004407445401d42c4030030100741d90b0b45500480504e440e80d0170010a0540c80c142c144503020740b40c1c00702c0480c01503140c61a140da540c0e2841400c1c0c1d0180c03c42561003064110840c0c038030000794100300410707100301004014501d00d0401c02c1000740045262205801d00603076541c0104011681c44084641d80f543c20325000c0c1e00e2810307000c0d015507400307036001042640b0790700d80b82825030090103040402003030070814034050003209001c840940f06801c0b0b10b59400c0c419540b185403040a60748284504001b03d0024050b10780103240034550054039220180144141c0ea07500e01606140400960b0030001500c4540d040c1402114280066030b40300440342001e125451802e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 108975449 1250 108974199 108974209
    0x1060e01080402130e0303061e0a0303081504060e060f030708150408040330021603030c1b12020307080706270305010c030506130603020f04090507080d170a0605 71
    0x4225414100306030300002070110f6551300d401212025500800b040a07010703014449036654801e8550910580d08c0a01d02211450b41c00181c106188000e005480385c140b4590341a140050003601c2c049441c81024448540c0303498038410340c0018008028854410309081c801d0002c0a0aa000c100303001e030708001024007019500040c4e0f48589110301600c040f280e602c1e824410f4590050382c2009101f01384800303000e00b10308214a04d00008607400d0450416a2503408070603a40c4154a55200e84443d001080c01c10100e40225000d044c0140103660003558001c010075910484402a0050020580c2c4180141e055080400c484000b410045008002c03035405d2000180c009006484031050f01a000c200b13041412244911803802160321400a02040da004107018000e004d00301d0308180a0034004e4000c0e03040380302500446e001c0300e0300900b000c0c7c5201d11010510018222506c030079a5a445003240c009130820f810030064105203410fa03190310307500c040d04e540040510409001c40c0d05003030030071905006030390b030b9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 108976699 1250 108975449 108975467
    0x140402100207240903050706020a0c0b0414010c080919060f03020c07051c050703030e01122003101e030201080c0309030307120e060a0603020307080d020a120201110c0102120705030106 81
    0xf0038441ea080031101e00c20886400d0074503000201a070241d010005074940d000203446200c00c1c8202d01001040e512041da04045000b01c0c420400009264524541194028042000210b000b030a03038901c0c10700280041200000c181080200d001010b00c8104180c55108100610016891506501c1d104c07d03502010342e110f2190050070f1045080c88069004441c0c0c207204040c12a50207c1605d000c6a0b4030705020300300c50025039129002c1029010442d0810380c03184520000b21600f404805040300c594511040350b42c000502807141401401d0000c00c0301018040d900028940d00b181005a6a08510004000c1c42e80030302000f41d41101031003840100712001c0f050704d510650624103444400814041200584400d41000426004100500c5140001e40e08440c1c1581c0c02501200c070750b2a610144c0966170b40582402c0001a0445201c10000030b400001c0044c000710507100101e4000408215584268422504c03c1016980050440f210010411105a1013022410304e5800e561410102600c8404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 108977949 1250 108976699 108976739
    0x12050d0e03012f040e180c06070803042006040807050312040303081303210f0c0203090a0302060906040807080307120905090a0e0f19050105010f0501170415140402100207 75
    0x65041c905451060701a050301c00a1a090001035a02d0900303418400c46ca641d064500c00c801c0c0110138189030780f800c01908480070f4947c8010100d103982d445449012070704501030010000d03c41c1e050001c0300c6e19510103001d400079151080c06001c4461511040618100380759030f02000340c50701440100042900f04150a5129030440d40c500c0500e80189005c03184041c1300c1c4200031007140c00f080b80d00c40c0703403200358482441c002242c80300304a041782a0380d0503641c0f40603040300f460b400b141d504d13018001800c01b40003500469001512041c1001d071640d4400b424410590442c00080d400031698006001e4071840c58100300d00300781004101c0e03c0c10a0003003148850018903200303000740c9542d003000460794100800d043c0811000c042c1c0d00e0142610070503840380c0901c2002922107600f400004941c0c2040400804200c6105842e07810100c0b48040c10074407200d20080c02590700c03010860400403504c1c03080c06210720715800320400e03603060300d0b1603c1080f0340405500504011580031030818410a0b142d0702d02c80519103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 108979199 1250 108977949 108978011
    0x703050f090301050f0103020f011d011b060203090102030403080114060304060903021024060504080d0f11060f0a180302100b030111120f070f0203040311040612050d0e0301 76
    0x140340000340c0e400303120756216039425610301410892958802480c840c141d902c2203950890f4042114011250340403001820f81c00703081c4d029600c00c0e540d80a00e0401702c1c980324000c130192648000d034039034034103c0e00201d81841c401e940000401007015070003074040d4003505650227040b20981c900d001007010b03800300070801001c05607500b0404041c10300800c0642c21105002c03406001c0d0300300244450b01074a0005002082081400401040090041c41518269009003005001d25204840101c4420089c2c2c0e041c101441444400340d200000c0034807107503100390300e00703040303a0082d06000c4075a00c1207401e4402c1c040c002d41d03104441d1000003039001c200c40d80e000710a05008101240b140c1300007070041603800d21580030550000303200301030811401080ca105044122210380307079035505c10080e034103500800c00003801a007003000203200003036032308041200e600c60241000403500d803180b031580c8440701b24032001c0d120f91380609032131540c1a5002445000ca840c09800a1041404001c0e0b007205508884107240609 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 108980449 1250 108979199 108979207
    0x152106012c04020d140106031e03020a0210171303090501050901021518030a0201090b0a0506030a0b0a02120106110d02071a0903120a0801030507060c0308072709020904140c070305 79
    0x756680311a104d0750710790844008519003101c050518000d0585e032008031140c030201c19800c0c1062a030000341c4050f20b90942c0140407805416401c109036000d060314400306200483d5130781500c00d9039a0710b51500c1950100c0b0060413100351030402402c401c500750320080c1045000c00c80c85203980da000c241102c0c0c03120f4030058404541c80702141c42d032000c1c1d0142400d0340e1600c00070495455140d41508503023291401218402065203800002406403071085480c0c1d0b81517030009010600182d11918240d902c0451700b60b0040c200030021040c40c04028080e400000001e14408001002d180188400c00d41d03820580010040326140424804604e803001c008040642d102140602c4191400d00c0341100301c126600b01190b40d084090400f4048034402c0c0000e8616201d0048040b99081c0180d861004541e0541c0b02c241c07a55441d0b14084400b0384004040540203c001e00341c1810381c407800c6200da4047c1014240150f110b041d51000e01003103c3c1440018480c415640042c040003500c6041244c243e5901460f0855035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 108981699 1250 108980449 108980453
    0x120801050312120925050f0a0501080c0c03090d0f061a1f050403051608060a0c140a1808030d0b0a03080909130b01090f0f0911010305152106012c04 65
    0x7014000182d40f101c18142000b05c0c18100c0740d104110741903600499001001207540c40c10b020302100c96000700303800701e48824040317070041007403902602240c1c103880b0032240b51580c94400318030b06407541c0d20122402c1d0b010702d0b000360410505009601340b400c5c10080040007001114000764030702d5500085480d501c0c040e0501e02d083c6c684030348111800303150000b0482d0b0b280010190074542c0701c043d40c40383d038510307006050200b008610b46000c3d01c40d0320001541c4a10680b010841c140340e85521112054080c0840403d070f20708a0403846001790300500c0e0b0200a180c42d4180010514203441000990b148944507080c42032002404a600703541c0c11403015200c070002c9a80c0c44104001107050844050a800c20b00d200000d225200c0b500008060560300300148449000e1084002c241c1d4401e040042c41001c00d10402d03886544227070710040d0700054580b91345445103c0c0c140403072644c1403040d40345071040c160b4650380c0601c000108440c2e40144031081c035541c42c80088465030990090080c07140d1450380011008101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 108982949 1250 108981699 108981703
    0x90a0803061201060f0303090501020303010305030d02030a02040e090a210804140f1b0a09061d19020705100b0607030203030c130f06031a010809071a070803041208010503121209 78
    0x1401e40b85080003000000e490b911300c2d40003011103120803000280c2c0000301003529440882a00d0489501400550904008000c103d02941006015500c2d03550b090000190070803011080c00c0c09001c1c1e9001501400c0748504141010924041841140000c209403038001e0662220010b0ba000f9001000c0008003808c02144905180103548031000320702c030303050400c00d1104102c1c0380b01007010011652403541036519402a030a8803c50310404a00e03214090400c0600008042403607880380c540d980d0007030b00c1045074454030100d8101903426078850380000304040341c1ca181d034441c0032802c400407644c1e00d090030600c0e54000e60701c2c03100428102083d41c0100d406405100589007000150130005144484a6111301d0028010090307000f80359020314804010fa031055006006c50f80c0038065900c054000c0c82e082452510ba0300410031081010f02508000c5030010403110310182d80594070481c0e84c44081840e500b0001e12400044e0440d601c00c0c1c02080c100409011400c040b5402e00d001c20030310a0b1182c1c1d4202001d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 108984199 1250 108982949 108982969
    0x621020903070602100c170601050a18090207140a020f010c0302070812070506070903032a080c0303010e251d040510050307091107060b0d080406031a010206090a080306 74
    0x64042c4036107400480d50300d4011848815490740d60300100b260a0034520200d80c100c85003144515101c0c400c10105900b9403040b0000c00c040f41441c2441640b0b0b42e52142400907030300c2d156016040c0703503a012603c03104001d95801841d9080b682c400003008000340d0b58001855003180164258184400c000894081600038004280100b00c5078090b80c9400c000c07403030282d0480d031080c00b08464502400c400118913a018000c1c50050342e40540d41e15000300030071044050b036000310500c249803621040e20900005000f40b001000d010700407102854480d40b40404203c2400000703480480c030a20709514810b03c0a000800c152501d201d5803030100205003890010300d05074003080762001d41041c18002001004000c00c4032040407228250121260207503111554000c541200340005040c50f420801007005c500715070094421103a004083e1a01d5442c9552601c20592159000c0c0c800300c1d4440c001c400030300f1298001c0701d584900a001070700180c84c000f4049511110b0b12000103202c03200200c041011511424946 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 108985449 1250 108984199 108984217
    0x10140c0d20040e060109090903021f020d020f1306080f060d020a0305010213080606240c010b120d0206010909120c1502070f021005040b030a02070218010312031401062102 75
    0x1907840c0e0f15100032441580c811a95103010800e500c000045400c40341c407608440582607405021440c0924580c10b191901c02150510415001d1051210000162000341a58401c030003815583e521140000700c026100c41d0311140521005808000703c0041401e42c140e400102207d1900c03040c0c102e03100050a140850b0006440c0b5840418503014079140c410020702030300d0840048030460b955070303810800d91040034026101000c040070460803107c1c0382c2101400444182d10000f11344030a0803404190450030300c0200100e540d0010001d004030741c1d0180b0840e070161040001c00d002d2403a241d00c0e14034407490b021402c801040ba40035021010300c8401058500d60484460080d540c0d129207060640d20344802c0301050388120349003400c0c441044d01801c1203800f00d56408185605565440e500d0b000250482c2d00140e8001d0031024020030034801403404c040c0a03512500d800b0b41d030503007080001821108003c880041400201c00148002500420841c180740850030b1840c2c059600b0403c290013900980b866 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 108986699 1250 108985449 108985511
    0x30907120507030c12050f0102090114161e06060506090a060c1a1017030304210c05010903110f01151a09031207021002060115050a05190210140c0d 65
    0x101e2850b0584e401c55405c20302840488044207100c2c0c206170708034481c03005081c0c0820b484220140001c110b1070050710107100c5c01c03100124164003540360148485044c0c45190a0500d00008200c01c0021503c00d6030083c020680e081ca00b000b40100204801f44414000d260601c842c0800680412508800040f031100802030340e01914203144036a5800d1030301c0c900910b0f20700c0401d00c0761003140c120004240c80c45150803003010360400407074201c2c402e50341d07441c0010042048200e10303401c808035009001e41c882d1607200f139840103807803084260107c0c14202040684082d40e41884811082c2e40b5a01c0c00b42815540c8844041000340e003d40c801032410f104601c3c0c10358050144e48042541c4e54a20000351442c14001e8500b4030320a03510100407030302d0310402d020361304203564505130a00c242c0784140d01030501039042e81405881c1101018181414001c2404240c0050b400210781406100060140e2908508403580c407806a003899100803110b4014a418407078440d0f620a400100c0c801540c4200c9103000c04010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 108987949 1250 108986699 108986723
    0x601090320030f0c0109050d0c0905250801091803020d08070302040314032203051b04140f010f08010e1b0103020f030411010e060702060a080405030c070807030606080303090712050703 81
    0x381054071080c000504d10f01180010200040c10f0030030709615a081544901e81c240881c2c20b2052240092002034500c1083d0340f04403115007460003001d00c0041804c01d0035101c0ba0b16942c07400c5100002d41e21000d0403031030124a4201c03d05d0000f0307000600180358880c00d003800e21072683c400e08210001d010302c1d4400303400c00c0c440c9040c4127101d00d000310042803200203071410000034800034404103001c0c00c440d2000130401c0d84040d0824204504101400da034041e4010004500a03420009105001d0015100894030158050040100711038020444004105940090103100341030f0b40016150100d410b103900c0c1c440020000c20700d90382c1c443d5044420b907203144641c49489003407504000c1ca089180c8402c8502081000205404a10340001034030425036008110b14500600111300310780320500600100c0d0144014402c8501c44803013801003802818442005103412861070a0a00c00d0350031950042070070b90030070014000640000714540099464036555060b41c081030303180013454020036a001800c01a9105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 108989199 1250 108987949 108987973
    0x209071e08090115050310020c01060f030b0f16020304051c0b040b161707120b030d0203070512030f01060c051c0908160608060d060e0105010b031905060109032003 72
    0x40c4060b00400c4090003c1140c2003d1920308861030000d401940d51643c0980c000318445504c42d0000c1001180120000c140150f035951000001c49907a00f0856400403902c04010310032041e80400d0313903c400800d0347c1011480000314040d4581c8110700495001341e5100004120400c5900c010403691544809003043c2ca1034036052054001e9401c0d90000000c0300c4412440c4442442101700c00000c06180c0c0d003921003900d8400c0c042c2c1c0e004004541c00c43e82c46032100a443c10550b8240041c80c0d00c01c1081c1c001c0c3d6541d2080380f514905001c8081c1034204110410300904c01c3c00003001d6000c505440042c200f2054203851401c05500e048813240700c042118402940a14009600010301000c80751850111694041c40440400c1c452030a4040c0700001119100064558648040090070050007035078009003a0503101c0c00c00e400e64034240c0010184410000500042410510103600841c10b080020000c500300b1500091a041d21413001911454404443c3c0501660446207211114402001c803010441d41c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 108990449 1250 108989199 108989207
    0xb01170405030712050c03031504090f05070f0b0c03070b0c0d020a170108060411040f0b06070c030b010518040308071101050f0703200403021e06040909021c030203070209071e 77
    0x4110488404600204c02d8803001d0007402070310340030005100910f045a9500d440311803101c1c0c0500007241c2c420b44138091003010402d4040003294003070203a805403d0071410a400802e41c81001e0b4011021904200020200700f00044155117400f6800781100805454604c650700b9140241e15140e00d18510014900c0d11440e003043d10340c5c901100110075940981e036102e1a51f0b84840c02244c002d40f050348548d80300c0c1c2c00c4d440c02d035000301281d1210000001c3d022030030102081da070b0780121104490b40860f0304014401c1c84000c0110718010b0404541080060b40c00512000340d1480180009051058083c081850341d406010061315100404008000d01e00d49240140150a800d85c1c5000100e464000444420505055081c44405080821a15040c82d41d4240320b002144007081d0b03250300e81c0da50301403180c554803200100010071141002061003400343c01000030030b5100703a100141c940b0303a409031100001c0e0088160390300c55404403041d2016945040054035410340321540d0b401440202032143c250f50b504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 108991699 1250 108990449 108990457
    0x1203061908010c08060915040b1f0305011701061512110f030619050102210c011b0e010201050f01170c0405070f030605090105030c120304090c090510090b0301090b0117040503 77
    0xf083d07a03020020340b14070003800007807035003035a110400034500c8828080508103034100764158240905045a00d00007100e04186440815940f030700002d460b4001003200b440300315405510400034100810045292090445103c07a54269201c1842120300f200301c00d102d41036001100348070040c0380e00b0f503580d601d405128800394021900d06204900948503103802c880107009080c05d80b40103030000c01c00001d80582740130719050315084030f941c101010040d201941b4020b000b13507114504400e44002c1020140300001d071503a83c1800c80c0b04c2c110380c900030401545012603a4114111a40b50460780c001010780b000a9007031420035a1a50380042c100428401855808030034078a41e480305603410041c00361504200544d003d001c0c81255416445080c02c40030382c0c42d1620300d8204c02c040b03040899207055603580859003640c0b03448201d24042044010300b0003080c1440d40940810b9100b601d01020403c4c2843c501c40030340e00060080500042d504c1403464003036401421049110a1030a441131101d150615100e0ba413584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 108992805 1106 108991699 108991721
    0x60123041406090d050a0b0a020a230904141503011104050f0303120106090510030c0815120303040c030c06050309120a1407060c11030408120306190801 67
    0x51920300411150348184040c6c00f4840a50a0076586c021008040c1e82907240108284580160310450505121600302ea4070011604414018205c900603d00c806400628240c90300e00104010481c5503c10744040800480d8405120f0526080e130312100301c1c541e40700308180001d100e50b00d0403079152054808050704680c104401c800c030380c0190000030fa0080700412603054003400030f0308040540e05002c25007410140300f10007146900030149600280703891221040c0b880c0b40049035070b80502000068206004407502c03030030700b410302c089400894030007140e07225240040003854038041d50a4034840c0303a92201030046c502022505038015404000300f41e00f00804a1400c02e1241210000b170075469005400001c0c11000c280b4002c1c0c10844002c59030320403540306000400045900080705010f42c94002082600d03903c0e0280030580d603101d4138100a51041c107101000c150140e0551000120007 = true := by decide +kernel

theorem cover : BRFrame.Cov 108812949 108992805 := by
  have h0 := BRFrame.cov_init 108812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 108812949 ≤ n) (h2 : n < 108992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
