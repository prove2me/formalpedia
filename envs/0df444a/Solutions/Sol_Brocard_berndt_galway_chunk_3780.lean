-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3780
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:02.401791+00:00
-- url     : https://prove2.me/submissions/cb36860b-76e0-4ac1-84fe-df7e0206d5a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 679676258 ≤ n < 679856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 679677508 1250 679676258 679676279
    0x1020901080718120807021f020f0708030318031b030a030501210b1906030b010306060e07020703030e04090602041827020108040f02060703020f0105010608040c050603190e0318031204 81
    0x1c4e036015604c1149010702c140c1c00303d64040d0040d0850044a01301c41250710040d541071089014804000b401401c450b410301301c030191244000b03007403644403480200700460500c02c14400d5410140042d54500282c3d0751705840c1a403a988140c04c5140002d00c2c00d000824071110042e8002440310b04400ca84c29412510b41e51000c40305c2c005444e148a0421030f16515110400e140204c00142d8070480000401394910714260342691031301e0f0405103149442074104440301d90700043c00360403603400d454040c1543e003030344000c02c00400000c20b0161400d400090f01064124600c0ca5152410641100c10844904682c50601d40c60100200080c602c0c01002c2558025610482005800c640038042c488120034603540094100c1c0d20100c000c03405604031041da044418170a00c00c0f580100f0303041c07d11a482d8501b42d41c0300ca400076441d0107003a02c01c0801201140501025103170606600e030700d03050100020300315103011540e40e801c61501941189240800c22540781400f03e4001d45244040302e2075410700d8201001c2c0c61 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 679678758 1250 679677508 679677539
    0x1121509020109030501110a02010f09050c19032001020d0c030e011107080105041b090605060f0d020c01090302030904061202060d090203030d090b010509131a09070807030501020901080718 83
    0xb41000040340c40030020034000e100e50001020701011040d03a6100c078000103804e54150541c0310300680e00c0d00452130b01060000c140c460380c4001c1150001c0c4010350709511148a4200c0342c0015100d602e607490010190f0801d5030300c402007800701b6002c540103030148070720844420005140080005030311a08010b82c55000307066040461554105844050340c40d02000e40c21918211426103548008080000a800b141d0b404e03400039065101003800f40a0405010034030034495205201d02c0341c6400a035020074103c070f0760306803010b022440b4000d1000d0035650400039900c4c0c000181d4507100b03078603110303001420108501c081c603400340e40603001d2400c20350403015800003001403031800c1e60103001c2000030f488031084034030680b05014401c0b5005000d83d41001b00340000000000c0145c4055203100c112200031841c1c01074000c5041d40d03100403204295071124030203802c01440783c0c0b02001034440c0c1c1c0c501004022042d009803401080c01e9980584030790b204541282d400c011030308190020070000c1403c0c071500304200c000c1c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 679680008 1250 679678758 679678763
    0xc090612020315061308030c070603200f37031a0a03120c02032b0c0218040c0f030303091704030f03140906031302090a150909020f030304031a01121509 67
    0x1101d03421b65680e6203608641c8211222241500414010322420f81c051083d182c6108800c80ca00c5e025516039030b81c151041c400c2c1c603c80700318050040b8071842005484180680c200c0c40c901c00c0301c001501d48540390381a10401d8890702010a061444000c020041201d205110714401000c1c502450b1442d124400001000d0100c01c08201c2e03c0000c10015841c20003062005040000442028041b07604000301c0184e06003005108000f2150310307030000350b5601c2001d502c1c1c0520180d0700200584803440c10129661260703021001604089800109040d0160301070822140140b01040a0100c00d6120b4032407403089000c018911654681c01e440420320443c0344440071001080000d1a100e555000540b0030342048851110303140200080d001141407400b0042c3d00703c04039400070311019950016150800f005800b40c21090350b5110041c006544d0365030980c0b01c5040c805410b8130f80e260b4803030034071610342c010000389484035425050000030f4a2001c0412102c501d508980c1c02010070100e400308001401880105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 679681258 1250 679680008 679680037
    0x31211010e1b01051e0c0a061404030801050f040902130b120f030415270302040f0c0806060705030906030a0203040c06180603021c1b140412030c02030f010c09061202031506 76
    0x170300c61404424005020f001c1580004040c1d106151400c8000c1e030381d00800c0260751030401c07001d20000a1704100c40b503041d90002c407a9903d10b46c04441c003050080c00c100c0030180d40403400c240617071140201a401902003480a90b0752003a001401c01c0e50079503030582c2d2520b8940315801001b0421441c189450800300504003845c014441061410565110151903092403400e07c40c40b20302001146418400d029240e03c140e4014420352128100181242c1c0f40181014060307200050050300304001441220607010000b422540c69040c214404030094200325003c8982c40b40864011800501904150342c460030441c020103003007400c0060031070194104824010060206403558070002600d40600c1d8120042c05041014101c02c0b210020f00f140c0c1e00c3c03d841da0104d08200f109010040c1124031003500648c160402d40304c106054800f280ca084241203490805528001c01100d00d01c0d480301e440c00031200c1b44d540f002660f41402425004038801942c0688040d1000340748407104e828440c0140c0360403001c2e02780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 679682508 1250 679681258 679681297
    0xc0315031c0e131b08070f1d0121060302090c0c03090616120c0302010605040c020c091e040b10090e03030417040503030c0102090a1703030a020310031211010e1b0105 73
    0xa0b0b0780d050b01c204500303108080303031322504107141c050344215559400951898400324000c081c01002d4411808030172800e6080c100d014000c4007690052440a0901c0742e00368092221840341c0c10960010070345404103c0c400c0c15a50042018400c43c41c0a540c84200742201945c07801e40300c40104045130b40200050382084c1c00f013030101c601158489114003030080c9251684c9050f5840c0b4a0000d084611304e80159100780c0c45c0144103448180c0c0000d203908500d1054542060507111000c500c225101c52100803401d400b5400100401c20400c012028095038009100f2295240c03540c1d801e005079007820060001c42e41c400d000142c08128468240703102d00000d020114602525000420301b1a40300e241d0002c0140c3d000184400b20b41804c0003140001d20300003041c41c80071814640c0141d240e10001d801c94940c0e98000c00440e025806568208000f15484007200c036104410000c0a0042481001c100e0f00795443c121075003820920106202041f13207080694002410140740065a03e03800242d030740c0b0322903400d490 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 679683758 1250 679682508 679682539
    0x204180605090d1805222a03020a05030f06150309010c08010803070c062709060311010819091505040c030506010b07030210050601020f060c0315031c0e 67
    0x22018400a401103401181d1071410702002868800e00c1101d10080081d070400e060081025004c80c80c054880c100c40801452441d03c1810318200c50102d46000d181d8070b49468a05010500202d030b600495109420796001e0481c184150124003503034141c00003040c0c041002800b00d03e44004200e50059005003483e10f1214003982d4924140c10480e00d182060795900c0304040d4007604041054010403e00e0300a62078403041d6610942200c0b200d00c1258140541f045409856615412142c035a482409040c040b6030b640e14ac511901801c00303448203035800720583e801005c95501c5851031030b104007820122140f548903d41080c20090222040590b0308d45e01400381c10703060000380e0094901590041d14904035103411802c0c41401c010040e0b00003005002c04000711000250081085000d5070444900020141e07240790050313003040070680d5407402c02d01a2400b000034051a03500614050310304803681c05041c0004005055841c202c11655100e12500714000500c540d11542e65000b40080141c1908101102e0341e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 679685008 1250 679683758 679683791
    0x30412031205010b04170307200315130605061009051903060e0a060b090906010603050c09042f0a0507060203130813140406030b13050f150a0b010302040807120204 72
    0x70381000b84c682d0030004080095082d40e00150384600010b2015504e4149070790394151040b10308442d1203a000c1461007001e00613503400d100d18203079811002405030b0141b8007025034040c00459400222800c0c1e2030072010603181d04040005182d00c0d0019102c00c1c03550307030603c000c00441d00c00941a903c041c00322030b640031000800c0d031b003d209044030401005018001d12440c02c00d00f50f810046150340592140400c1140c8440c00244050443d44142000140c42d20790000d160000c1c800e501d000c07a007203410070255611042258807514604800b6a030003003403010418440381c5c681c0c80348514400c005a0244000d901180c080e900540c0c200b03401041c0101e5048090fa0384c28031503004a42c42a07842800200d081100c03401c07600601800c04002c44081202500310b40d07442001400c043c1ca0b20a28018a0902c081080010072031a0a0301c203003041220034000c00b80181d04030303c540840b241d560f03480c14240315070303d1540a402582c0c10742c2c8030403028298150504c0f2107044c4c2545107507803d0b644030340c8540081015101c034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 679686258 1250 679685008 679685011
    0x170406050c0904150e09030702010c0b090304150507020102010e0d2c04060b180f060d0e01141005030c0406030b181213030b091b01031e0507020609060708010602030412031205 77
    0x2180c13076001040c0d160020780300d0700c214020010321040e0410080600143e0f80030000c04451580079600c140c951302c450701300c2e1386140141d0304030811700b855900417115040e400c00041c0c100203201760300901c449880c030f40206803102060802e940216030301090700c2103c2c10039052845450903c20328200c41d10140300e000a01a81c4850b4480e0720b0800001611024824145000041070201a81c2081141410401059080c41780c070011a80c0b8543d18030800d60a5182074010b44001d5400c03010708071a50a01c001d40c8800c0d090b180c072955100e8031901a05211900b8140a40411240c0080016415550712147c41503c0d03d140880308506001da40116181d0010007400741c04001c03890b4500000050540c030307100b000b69801078100101580641903801040c018002a42002c1ca420701c0c01080c0d123806203d03c0221899030b880005242d50070581002341413076000640711301c24000d00080f1900c58564040c1074a064400307014080058104100900c200d100c034618508805219142160300d200c003102065048800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 679687508 1250 679686258 679686281
    0xf06060f0e12030d1d06070f0f05090d0c080114091c021207050d11160b0a0e0306011d1609050d08041d0411010e01120e010209090f070807170406050c0904 68
    0x16240c034030305800505e02007080e4000d480000101507a0800c0c90001d002d10300f106001c1402c0000343c0310004850380c46501900c1c003168010388944180802494014034041881c05410b80940c40d00003500280244000380b80e02a6841e83c001e4001f40c0c22800d0301c03d021121002e4250150b00c0341644030f02c840d074401d800074244e00707000d0406030207001f10850009084100f885440052940488043d4444020034422101100d41404c0741035a01ca01c0040241c81401c101d440c8598140640c0c000055807504071200c41c50001003101000540303a94000c0f11603000c3c0707a000300000004002200501203810104e0070a280180918519410f00796076800040d148540d078000c5840c1c0003401030034041000310060008510500c02d0071321b5201e44881000081281c4c40034034048440d1a15242890701002c1c00b981240e04036a1301401a160034600329031928a01e080a0b20b0803000235400c2800560114803c1c8100304860950900b0081036490310703100c1c3c2e00038060103880c0019410007000110f4040d50f483c40f41905040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 679688758 1250 679687508 679687511
    0x60b0a030f03090302150a02030d0507110709050a0c08100e131401240b0d09020a0509070f14030103110105070c080d020c0301200304080f040801060b0d0f06060f0e12030d 75
    0x13400c500c14801e660320091941e01102c4014440c014015401105403a101c1225000002e40d555403040121050141045958520b0056079004980480d05410543c0f1480002c1c0080c413901038903001c11204014105c406c043c9030000380d5070901c003101f407403500288c1152503100e098404007d02c5d00c03580c840729090a50365400c0d80d5522075011960f1260441070740101e104c0c103080d08502c0d18100120700c1500c41c52400340740c126039414a8004540c0e82e5104000a041b000e428030185281544001d400c64840018560102c2d008040750010482140300300c90681e60f1140e02c030000003446000548154000d1081110810794254021480c0314081001c00d00b101c02c140d0040030f0384072504040c0b508550105507105040031030030030540d03942c400480c1201d030400d9109201c242c3e2101c845991002500607a00082c0e001d5080460005c0c0080c4040041c02d0004009082005408152030301c22041f15402d103c0c03d80401d000b00d020350b00701400349590707081c3e004001c0e284001c9005950301d01c60856010444015115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 679690008 1250 679688758 679688777
    0xc05120301090c0e0d05060105012f03030105010801090204060e0d0f1b051507051c05040e0a0914010912030e01061a0c01051303080c0d06150237060b0a030f03 70
    0x3181c4c440c03c1c01543d200c0a0b158400050105d49845440ea04c1c140922070500c00c14160f62820112907007411014007100c50601d8410000008115803298801e202d142d00040c9160004918113440e03208450032200300741c07107550341903402c0c2062040000424070241c1c4d00041030110f0348081064070355801c40b0b480700e09070900500b600b40400c1000240324074641c0d0442d43c2040c005e4000103880000c840000e05158000154102c90200342120b007407040c1d8000442c140750032810310912900c00d0f080070309142c0c450900700301e0058001013500e0807130703683da00050b0004804403e509407140c02a80200c034031030810800410010703141c0c03044112079064002c03804841c200000d002c0149510a00c40d90750408a81c49041c80b441800f52801800705501800440e284000003900384915405a0f20030350003031400f1818104000e4602e540691100b4400c041104610601038490418409481400c06a044c031540c211112003030340e0300da20340141800000307103070401e51551020001c944428107040755903210350795440c0403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 679691258 1250 679690008 679690031
    0x31e04050d0b010e0a020f0d02180604060207030506010510020d030c0e12071a0309070b0d0b0d14060a0c120e0c090f04050c0d020d0209061503070906140f09010c0512030109 76
    0x42d404c000c1c00c080000f441409103050020060003241c01c0401440c0c00941c850426240241480006405155205800040015445401042c0d80048900400541d5190781e0b0351028060380d0100c4002450068128426500d2158080da0000b0500001c606d009501d090014010a0403032507840000d001c0d50740b010703008001ca4544012000000c0344400d04035811800c00281455441e01c550003002400c640202d203030361902174030398000f02181000400802422500d030070040424807400d1b10310b000c9402100c1c0019100d180e07602400d900c0c1c401c1503890000040300d17043d924006004030722114a40d0300a908109500703544803010340307000c0d640c032210001c1030b4200340c038215160052110310240a06859565500565a07003080c00c039041e601501d88000943e9840000b50400354803060b560140e140100a100e00180d0080c000010740e022900c44000001040020150b10300402c0600440ba913000c02201120303501c07601031000803502c2403045400303414000615022a8100741c0100d00390700d58030200d5001c0e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 679692508 1250 679691258 679691279
    0x311070312200a020306070c080c0102040b09330d06090e01020a020714010503010b070516171501051c0c15030b010e010804020f061b0610060f050c031e04050d0b01 72
    0x800c0c01400b070043c601e01000fa4007003600c46200402403c140440200b00d00244111582154104d42c0308800840d0b8894560440c10855080300032003a004005941100106803000d540a45004402c003c1c40c2401d199030a89003c0d41d030340403421002c1c019071181d50014801c2c2040c09441c080c1d2070140009600e03040e9400000b440c02455a0010b285100340301884801640c210003100c1c15140e0425803107980300c03090305009261040ca011442c0c926a5101c900294a80300131183e00b1040310b410040d5170001c450f0b0485148420000e0280c42d60043d1910081c0100458407200c210303c40c0d2240fa18010350640d01d2030014100b00c0116181c2e13010944800c0313004090f41e4046035200c025140cd082c48541c27400e01c0d0b00440c041441c0400c1090051078006501e82da0388000307290320030084200745e045075054038001d41c295030854003500c00c55012444021001d408a40208203441c00540500000c508000800d11154090340c0c00100d108918101040003003103544810303440c03404182c024120700f02594505000c410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 679693758 1250 679692508 679692557
    0x2090a030b090114040c0e160504050402031e0f070e12060109020703030b09010f03051c0f11030f0f070b07020601030b070f09031502030f09030f0d05151c031d06070311070312 77
    0x4235a001c2c104c0502e00558000c0c01340c0301a6202541e00584968401042c11040301d104004a9900c041403000c001500521504044c45030181da629415007042000c1441184003903542a040307240c10004c01171021003e81d60240030710f03500038a004600c0d01c03071a2010a031030742400e810101c10100070240a0042c09400c01c048000914982400e034141101003c000b040d50400031500d400300401e000c814107480038200191280f1082075803100b9506c448000d03190160781c1c89440103e9004080600007590140041441030480e41c000361075541c41d94500c031046500d2001030070241e0074054851300100205040c4030101a045245000060360707030410001b0241c00b25001404a0a1769004200040161745200d080c1c0e1740d0781d004064007044e076848454443c0325907086401584d40142c82d40c40b1240c1c04400401c181900e1034041d4607450442d100028030302d01d0610b022086650440010441e140010384036140525088981c4030648030916143e50300c001d20a00440254400554000f20000c9000c04111606 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 679695008 1250 679693758 679693771
    0x110c061501170601051308060a0f0f020301030f0f08070611070b1008030901030e0309040c021e0102030103020d0b0402120d02031801020601050901031e050d0f080a02090a030b090114040c0e 83
    0x9100a0b060314280018004000e149078104070011910700c0c0b4034907011008102500c401e030f050364000d02c0c0c03400c0b2240050528641d4882090b0503c041290118494400c0304d0581c1e0700540d60290b0783c05540c8544101900c2103030308560200042120a0202e44d103131040003040190a65a15500c10140c10520f46000c0e020780402c43e403a00c0000108001c07800001200c204090a0a01041c8142c181c02c2460840c02000250394000d400d1000c0180c04170f602280c2e1011511001104500300004402d4403800c0f80400d000003500402626241008102c0f90745071a64441d100a0a100c0d036020300703001e02d9052100810620025034008250312604007403410f0022441c1d5401e00c003c040d590300d003400103081e0003018070000c1c1c051036400c1c40d00700e035101070032880d4120250000e080b81d90061050304000c290014090f510000140080049645c1400354000c4490030b0200600407480d190845d00d03089601e65018040b84410b40da1042c0d200e8082142401103880f581c000c03001d0304442c2e40382100411001c00000c040c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 679696258 1250 679695008 679695017
    0x30b0406140d0201120e0f0a2303030a09020406030f0c051e06070212191514150907180b190507080316050403020612100512030913110c061501 63
    0x10001c1c140c6480880807445038091904150900003007204c14000c007510400f400c058003c4011000034981c0c00141d00c1501c91048658944040080790725001039060403404c07019a40082000c654000c041e0303000700245500080c80040c0040d503980e5040503414940307100b165440c0d041641007141c0d15103100c0b01302041d40701211014180069500058040c07156a500902c01c0882c00708481e52500100318071035550030204d209402c000b0311820450607001919500c0000c060408800c5282c650f08558180d0280d00d040c00800119410f0b0700410440403801840c00c000c00441e003203c86c1a80d40100c2d404002458400c50840d9160500c00140d07140c201c0c202410001c0c0318081000e0b8001860000460303070300065840c01d4401401507400b003100c42e0300c01c0d40d00c0a981718a01086811540340b1480c6424011501d81c41011032031552141840b2044ea040300b00440f060304180090041401c206080d8415402c605e0000a40904110080d42c1280c100c3c3d00c4148541e4000d02c10406180302015081d003100c042404c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 679697508 1250 679696258 679696289
    0x60f03060e1518060a030212070b03011707050121020a12110717070b0c161212140118020c0c040207030c05120412030e060c0f01051b0705030a050c0307060606030b0406 74
    0x49817000e01d0511000303014500720b141e03c0341042c0052200b80b0143c54020352007a42e07548e451a080790030b1041031b40000c82038000e014000406601596014503080000002c0c040b040c4001d41c503100094016640303d5090102482c0300d5440000035210785400400d071019203903141c130881e00380800180041b89059505038401c004600226100c841d10a0f84944001d4903d0b80d2102e0340d400c9000050a1a01e00400310403990060030000764000800103264036104070200300c100500c00300702105d080300f0300c0707607000e030a604441c0602a8203c0380c00800340008564215124421040d002c14105d900c4007806800113841007600303104000341400141e040c8003400282a0505013810700b40540103000b01001418402c403202040c1503910f83c48192803000d0403070b070261002a500904030b6800382c101111100241d0f01c1141024402d0b2240e90150381d8001e402000450800009104c240d5060384500302d034805603c800c0c445000040c2d0b2601541000d0714041c3d4011a80c04520340a11090b22815008440310200d04007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 679698758 1250 679697508 679697521
    0x3070906050f09060a1418090c07030f1107050a09090c0e01180917130e06101b020d05030a0207150318020f01051303060b090a060f060f03060e1518 65
    0x383c4039a004210351a694805043c04250b508001304283c20400441c0403d0a0810030030b0f105e141401c03070b031080e078510304656201c1038507503501d1068940041c0030520880c03041c5141403040c00306140609c03402040340c0100b911280091000c600980c803900e030742602d40401004028815421400a18030590b444a865052440084804050841d45c40c03849940b100800c06104280b230180c2c42c51281e50606c650707940b042d00c0d0280d034042990302901300003600b444042226820301c10206525030560785c0d59014498000d401004130320701c980c481681d100319040c007140042a818030042460603025002825000d1802648245410b164030028082c54902410564110380103288032510540c111041454021880010388550081035a5500c0e2652410000720812180b81e11009a152341150503850382c0c0d40705071071041034600c14000d1030307212142c1c104208072090290070300c844a044a8200030503000d817251003a42d140c29080341d014815403105200118a0304040707215922081c800d074111862032401c02c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 679700008 1250 679698758 679698787
    0x170f1009021305041a0c0d0e03040605090613082a0f0a0e0601030f0f090506011202060f031e040b06091b0318100504030c14030c0601050f0f150307090605 68
    0x42c041c107445449000140c1003002c58016a4544c0001300c50b542d0003030600f0f42d40822590000c41075040e0140c82c26007030824005000003600c2c1110f0156030340d24908000a42409842d8000c4004010001c04103040415500340a1010003c203400008824451605000740140444020300314903001c0c00ba40020b5048689541e0b5180e400d844c0c40204100e45e90721002c004030300a03c0100040c050b0303070f03152800e042010395198100d02030312405101242c5040c0d813a01c1c1c07070a003000c0f81888003e510070300410416801c0607000000d55070006000900d030000c140c0900c1d030540ba143c0700700ea00302c50800300d810410500346010440507802036588030195000049010307260759244406407009510880001041850311020805010501211102800141007a02e00075203403000c0c00004581780940940103031160303040001a200c2d040c44040c02001d0316440e280c1444404600c000740c00723800c94000d01090030140c640c2c22045503100000102d06549207460fa0004001c2c07402078001108010b0704001d282d90b029841d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 679701258 1250 679700008 679700029
    0x110702090a0c171f03060515030609030405310b100c0c05011809140601020c0303070b0103060203130506091b0d0222150906090c03050c0a18170f100902 67
    0x45404942250301d40040b404c44000c10130341c0c61280502001400300410515406c050700640e0407081e003103503141200c0209a2150400c58001800d640180720400c907601c0c2c242d0000c0303800300a0511528000c440005c7d9071903002a4246036000054170b843c241d0300700f4103001850000003d2189429104c440c0b071660340040342406031013103504100c0c81da000403218441c507001d01c000a1019800400040c2d00410884004520032a5100c2c0503010b03915011819040102c111071440b58071840c0e00071b0980c25680c07880000d41001c0c1080c05560544016200041e40401c111401442044020a10200c69144404e005c0755400780060092010b0707a90900162503805885e000c006900c1014481010701c1412040202518000c041844c5680303200018410196070040060741c0d0414030500070903040c000141c090703c400f9101c2c84c2010000704003c444881c45a02e28008001d01d42c401004002c0c1d50360f40c0040704110b400305000381c1e500001b454040105080104000039501d040051040c81070356000258120300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 679702508 1250 679701258 679701287
    0xb070b06040c03020c011802030706081612060b04060c0b010506040b0a080a0b03032a010504031209060b0a0f09060f031101110322031209080c040f0f110702090a0c 72
    0x101c4880c2c0d100c496020390180d80c00d82d03400304001c00c01180c40c0d03e0005007aa40b5100242d0090103100000301d06540719103100d80c424510130a080005e0383d0400d4048844491402010b40710315603624001c11680710102c000c0008003020f5440c0788801e1210b0400540021069000d41c0c441c0304100405c000c880224803d494081038103040120a03a0303910b0407818054480c1c0f5803825030600000038920058104d12844480304495403044200403101c20724501e0803a14107a90280108000380c0e01d00c2c41081c0590080c1c04803034414007001c14001c05100c082058880907410401c10482c1900043c0a09904c1e485000000c0400c10f80003241d040c0356403204c02c604000309100342e040060a40341e01c4600e074420800c45049180c3d4480e03020100c0741c0029105d41e5407032503000440342925100d1880f04007500c213644000680b00350b180030344410144e140801001b0800d00310702e81d41c00ca440c2d082c0080020b60340d10442c888a041003401030b07501c80030362041164007100202502620362070140c801040591100131403100c1e0a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 679703758 1250 679702508 679702511
    0x3030914030a020d0b011829030a02091501030c050918060a08030a0203070b0f070807050c071e050f0108070c03080604020415020f0d0e090f040c0e041b0b070b0604 72
    0x54240301090802c01c0d00c49001c2e40201302004000108280c0910050407104040183d00d484007441e00c0210a5500407003642d03949000c00f9480c80347c41040708104c084540d0008040355000d00715030307001c5480ac09007144c000b035903c20700392003d90582d6090300425241484610706503107010f0306840040c03003c01c000024041032105c560001403241d00d596106802400c00c030700c00c90761078001c8010025aa1351203e0700071114440e440703000c540d41d5400d81c0191405a42d80741c403a44016524004122078a41101040c0c01141c0309a007000550160358031106206645610188000f244c241000c0c0100081022002410070031880d040042e4158800e060318a42503051505c051280c6039400017902030b004640099107510483c2c264440c84030303000034a000440005a00380e8454100a19080e682449515070080c1c2048001c00059201d48200d114164014461105a501951200d40740d450011007120f0840300310191000c0101324015044002009218082c0e080f03240604c10380c0c03046100c000c0908028002ca = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 679705008 1250 679703758 679703789
    0x170f060d02030a08071209260c1905090f0903040605070302030702100c0c05030f032b05010b0a0324050d02030a05060a1a0405060105160f08071208070801030309 71
    0x280d440d0092031040c560002c048407050401d0341414076081c0d02580702110a20b4110411298150040110400321a4041180c201c40c18442c410030508400c10300b540580381c01468a0004255100c2c40c00a19a4883c03194041c041c508002c184807000b03602500540515400c00300b0440110000405c032800d0315002d203001511070b011442c00364594011440c0003940314860341c46040050390b00481c41100c0070301031440d0b5508656900f043c1a2100c80c80b250003005c6810070854007251403a5090400c42950890320000b84864203c030104085036405c0e0800d410080000855041d400c0c5d042c09088541204000b04081500d9007000310040300d2450701c680c60180703215540e060250743e0244405800c040d002829600035103003404c08003004181b04070180d9542042000f50300d425041620500b41309403411b8465518040d0309101c6282803a4800000300c0d610b00d448400c0d0400a8119400b50451a03c120301e1300000107099940584400b90041c00b0004002081d401000403d03800074038401140c1903007070640c0d00d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 679706258 1250 679705008 679705021
    0x2090412090504050c0a1d0a2105030403030302041508090d110a1703061e030a06020f0403050a150608150402061c0501080f060105010206010e16120e07080706170f 72
    0x7021041c0e8003003a0312524140811100c8040303040103001104295660000340410b0003480340c09121800c80b0180c2001c4285001e02074142070841d005400c204400301d5030030340c1144e59034040c0745503c246c104034000b0b50003150030050745540c1d41c10002003207258204105a8a02821000d5031244002220010030541c0035820740d40103000c2c03000410382e030340140581c90041c14509283e803107940241d03212802010a001c0307603400c2039410742c0350b251101002809003800b00c04544410003c0d42014003000b00d008000c1000100088041000c603006c10320880710620440c25009030b01003200d00075403105529030131088070f2404019141000aa0255046415988030522041c0c10039442200394880c0048030300d4480081501040090101c0109443c030044a026a88600049854860030300c1a40e5542804070045110b000c01e46c109803e0101c120305d040301d003001880a5810a88010303496113120384c2c11021003401080424400c0501800c0d1608103a5800820040020180c441c010500144242c140303010803407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 679707508 1250 679706258 679706267
    0x2502010e0409060506010e040915050603070f030507030614041e050106091505130e121e0d1506030c051206030c0918063601062d08010902090412 64
    0x900090240040181c080c0358904030000300703130582e10140440c0803c80840351a203454058101d40d039902c07500c00420305481c107039440083c000c080c00c0c2c143d160107154004034104040340d820301f00450107000107089180c95401c18200312000c0c4240d520419901c0c1c0f00f0800403920f06580405850f5080c2c1e00d00c20714509609045005008179004004654180071030040381950241081c8155a000c0340c0f1009a2044001810f0480d6240700b6800c080d03412403814260001003042c0503000c0c01048603020396114a040f401d8a46503482148201c03412a610b8403070540e000304542c1e0385000703044c80307040c1004102072140001e0120b0003807040c255141c42c803802c0000d105844c240400e007401c5c440034110468900b0401052003001613a044404424400c079030000d200c41a0000103403245140950209149603a055080c5210718503103440030341c00359200c00d030001c0c45c030503c919412209014545e090200e42d40b02042200440107581c041200c43c0c0c101310300c3c100503a03210b008098119500c10800e178099800400b0655 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 679708758 1250 679707508 679707527
    0x5120a110a0c0611032503020706110705010b010806220207050d030b030f06160c05010e1006050a0519090506010219110103051e150111011b0e06250201 67
    0x40c03400300105a444000340c029010145103031080d0000d11982d0200ca5070b0b0f001c2404101e0754200c00c040701c401d5651017018030f90f20f0401c0004003484c0140c50207850741c07100740581c3c05400350352a003114001059414094284110f06020200340307820702081c20000001160101090908282807100c000c01c6a0602210341c11605690750000580700b039503070758940c050000c004c0525201c0c001d000711640d0107903890011a09030b118000c0c2c05015403c5680c845030484030008150000ca8a40d941c41781034080701c510402c800540c881883d80c010822509140038450000104c1d03002c4d2340510b02000c6000080e403152031a031019680d0352800084c28ad0b59040040f031804c8110540c04a401c440d0710000c9040c4442410000303507c2c04281c0f01800240c980c5281d0b511891b083d0030080c0d001a2844d0040b17448c040c85201080c08442051507d225025000c41007a070031540c0c03051a543d000207d0f0512060560b4010b006680c02101c221031807400c245c101c126031080015007029805c0c0c442000d4084004680c010715460 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 679710008 1250 679708758 679708781
    0x290402281703071410050912030708150d151b120908040b0301170c010905030c09040302070519031e0201021209041e090b010929030708030a09210305120a 68
    0x3041441c1c401c24007586403c041020380710700d5030030701c00003440342100007523030220000e002d0345068555904c41c81c08803000f1002030404000e524110f0300801c043e65554846042040c013600956100400080d04d04003216100d01b041c21030740e03805040c480320392500221000541005208081420b810034500041c091045820a8468850100c0045145044168150840120070701200d031940040401036408423558410241c0c140e0215000d6a000d0a0403181c482d0050701c00e00441c0c8001d91140c0001309500183d55a4a550701100401003060046042c424450f59800c05810810041d0a8000075222401c5005000048400141c0b180b080c0d00c4950114509180416070f8010300681c541d040e8000d82003031401914074500640022031201014031506882007540680003012640403208030390b02000e600358403903040c002d80700000b40c100c00510003000040840d07601c0040e103d080000690281d00000c101c91002e81c150511880041c0c4c110007111041c000603d00c0007030310703901c00c07030400701429001190 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 679711258 1250 679710008 679710023
    0x807020c1507080d05010b0301030c0e010b0904022d07020102010612051207080c070f0e16051b0c15030f09070602071406070c060201151d010b030429040228170307 72
    0x1100c40d850303005107040cac87c884c2c111710140f03d55849030513580b0a02070080c0c1c41300803000c2000d003101d0700c4c00754000d0420104107010800408254829400e80c00c5500b94028510303140042c03143c045680c2807180001038017521490701c040d5100c0d5100c55070748401c0b803c04401d040000160020a0192103801d642110003042e08903a2000d842d0b40011006d01518810400c42d00c013003102042c400002c4074940c036540c6640d66038581c189054100f50004201415050b46d1390380c0151000d10b0040e484800942e454030030200e0101d540d03420094220384400c0c90007001c405d0320b6040040c0070f021513540410010203c0301010f0192030f0000b02000058158856000b00070004803162000081d40d58040d040101911144441100e80d0f41e65a90b19a104806c036088424036120880010701140440002450f001405408071046c5450381241016821070403001c0e950900120b4400c000441c6404e5401080703040100d030080c000600c850000d8070754008607006010f03806502200c0c00410260410a0b0760215402411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 679712508 1250 679711258 679711261
    0xd080409061203081e1513021201050f0901120609230f0c0406050303070b0a021b0c030c040b01080a0905160618050609011409040f020a030b010807020c1507080d05 72
    0x35030000d001c01c40c00b00f14042442e000026042140c1e6407000740069541080081c51a5151042d003c0800102c04100d640480c0310030a805c7d042d01d0f140701415042d60030345182d08065042000304001c04940404481c0f246950740f0051004208042010840c05e6100380c02090701290391a00001da0221a60440e0040110703200b80e015400b0000b8442c800319110310180c5061408940500040d61454050650560b00800242c030000316070075005948032052090050520320034041109450300d40440c595500d51062201c40c25a290900c03e080d880c035021902000000e050744006401d6200051040c50f00c40e47d035001481c01c0c0101846921414042c002c03400c6043c0342c542402400c00e07944801102c078140c880c210085031600300041115039070801612038030a00703488000f4122013507000c180441c0e00642c0320880511904800c0c005412000b145840c0842d0f041c40501c0010907828008011104541c48504401481d443d40a0824960410303502c00641da03040d41d060071440c9108640909882d20b25100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 679713758 1250 679712508 679712519
    0xb04110f030f070305060307050112021603020d02010501060201020304020d12030b031914070506071e1b05032416020f0d170a0c020c0105090d050f0c01180308090d08040906 76
    0x20055100321410342c465005034a44020413411038800b180c0c9180c05900c032000a114560203032410003071100945402520b07101d0104403400742c200748114100c0240e0b012401001410350203001e150301400300d0b44000c5080d458140c00152040c0f401d884003808061244004001d483c0c4203811145d00c1c0707140a411226807400d00303402c000d80100142015104036001002c1c0743c00464000c9115412a03030300511203802c2c00200d485900d049095001075080041541d1400400140b000c0000c1044002034030040405901e44802c0c142000f4103c0c103a030210040710312112150f800311030f9500381c110700382c03075824442080881d100760701c0c1c245064100c8500b880344641c000d030020b0744070b2020b140c2190141c00102840e01c820310706100b03440a903160040940c22050000c017465100e0030241c801c2c402e00429102c80c103452a12070a003040b240a1103da104e4000b00200c20399543c02004114405540401c98078a82e441d585545001d4040c0f48111131103aa4810084014400c0141c180c0707000d4503188100300309007a500c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 679715008 1250 679713758 679713787
    0xc0509090c090a0b12040327090203071719050601021f06050102120c0d18030204050a0b12070e01031b03020a09050402011206050f0f1201020409150f030201120b0411 73
    0x40304183c8540b100d10000300300d800000f8159550590302d804224030759241d50f074081c1d400c10000780218011040d028110000f000300903558000600b07540e00c3c01681e90030300d540c00802d11882800140c1141e0400c41c10320048410300500101509400400041c02d42c40d0240102e0900d0715540590001c20391a0f0000e0600740e0442c0e00c40c0301140c0c0c0907021141c5e400700038544031040e030003050764000130307500840800c2904900a5030407280780c036051961703010b08645a070700040440c3c0040c0da8540007a41d60b410b40c0c40b4507051183c800158210807100a04485160615038000700005000007030500c010003072154011241110b0032400b6582c01000c4c40e00b1036440d610408001c210849040c1e000132000d007103c52440d0b81307521450042c0c8201425034104000c0d5401070015000b0100000b64200147c0e01c00700c5041030b002c1c805400580150701c0b0101c0d003040900c0119004181d641c00100382072600b14030070001070384c0101d100310143d0300d06038011401d0705a040c0080d00500124080d460168000600c03030207201d04a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 679716258 1250 679715008 679715017
    0x15032d020405040c020619090c090507020a060b090907170a081204030f0c08250210020f0f01020310170c031005010905250e1207030b01051e0f01030c0509090c 70
    0x1d540410403202c60b09000c0b40c0d580d00585081040002017807d108643e0380540011440c140107400b2088800c0d0744548107021a2421683c0c0401600f140700010f04000d194001c400350300100b1a94590300d400d1a4442d507484600c2031003408840c01c0c500c0841419a5003e000070030304140c01ca0a43ca80b980a01000380c00781c00d60484007180081c40d050303180300c002e0f406490b40d0b40e80c2a8001c0d03042c0c0d06148044503040000305c51108010140c8441c032055000503942ea64000080d16440e43c050856003984007801d5140210403140d510702c0c1d034010f1080003a4460300102940440340313030441d030854903001c1556580c14580c1f0340e602543c00d802503690804101017146c200741e04030340007404104450350320b081403814244210f442a00e804604007017081034042c492880b0b0126114010400c0c9103400b5030403141440c028455000711090403646004200300d142c0303601c04208d42c0c161410010548041140041c184801c1800a2414180e03503424a011192084083c1c42c000c0d203000d01380103d03500b46100480d01030f411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 679717508 1250 679716258 679716269
    0x723040303080106230a080a0209040f1b030b1c0201090e011e08030a020703030f090e0a0e0f03070f02062803240810020706110304030512010f15032d0204 68
    0x125485d052130940861161000d407041c85915a5041c4407031800201c54400c000361480700e07860b40078001000e05170f669108008040e4242d600000d005003030807070010b0030310301001844018103242007120041500c4071403060310380e450501d0080742c50095a1006843c5190180c1249644404441c0046103804030320042d4844071100d038510840c1d0603901e41643e9920300c51704400d240140c0200c4020800a4000c1030700c100340b01d0301400c00801198803801002c2e00c80c0310071580340d500711303440703030300c01d0072842c0e814480314100800d03407001345203010322070b0722600c102801c8080300a004940c002031052120081003001001501d540c030205d00070308003140c0000c000d00798240702080714603031803000514030f094080300301c0003120250b40140c0350183d00144c1036002500909015540aa1101c1c10703040d01092100085105074803940b00e194036610603481400c090b0005802c0381d88040070340a42400788000b081080101510300345404200705084042d121120440b8002c84425000104424690078049801401c203880 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 679718758 1250 679717508 679717517
    0xf0201110405060d05070516060501091a1005030705070c06030c18060f08090304080304060807090803130e091e070305150c090d1e031d0109060203030723040303080106 74
    0x44105500c91062003035104880c2d0210b003c025038043d0320784603000560300005506010b41008884000004c04a450400485070b440e0740380018410784480f481a0801c5002c025001c5110040201c08210180c006030203140a000c000700004003454851000c4440b4160f0020f4085010b81d51018081c01501506000307c0100356001280800e601c0d0b940c1c00b207811078030260b40e204200b1000540640d00084041c1c444401404200808140c0190801c024401402156510006842c0c04040102000e1454000d816981c00410104502011105425059074841920801903848200130305292492410110361003141103007031612a00c001007a00300490b4029010b441940e404591108107054045440d410078039001c0c440014107041120700300e40c51134421520807280c01c0429050b24642d82040358210001341c2da40c400b11080c10741000c0014018402030030322010391410114040e4403400010852001c200c80819407100d041a50361b4030904501c03001e0b0840e0354650700c03810001d0004809009220126 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 679720008 1250 679718758 679718771
    0x8100213210f1202063108041a03010501080108030403020906040b04090213061a191b08030c04030c05180f090309061602040501050907052a0f0f0d050708030c1b0303070f0201 77
    0x40c00c0d9806c0d001c80c0300b40e007076041c90024040000b00c01611540c120081e5034000040c403011072009025170a4840c0011074460140d01c80d890703e0001082680305800c40380e2150418403080005844c3c403039003543c1003001114085021204400860000c002c103600203035001041c1d070800c05a4400e582c1c484030a58080b0704a040c60000901782000d90b0384540907114180380002002c0603d09031040780355a0706681d8000000203840416101c10a1070b030416200e54044040000d010000c0090032031204008043c291501d0081250290320302030b13044001441d4800141d4581c0018156103414001c6842d80c01c4000d20141c2c030b030060001c00081035401c1d0482240140d281c030740040f13414a41110705c47d22072503050b43d96518010046080114840b10a00e11605002403400d03203101001c02801402c1414410b6402080010290701c0300d80c0c50001c1400410341405000c102072004204228205c0c0d5125607044074069a41041001304c501c01550580c0419a40c00f012090040c2154881400e521070001d80d402030060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 679721258 1250 679720008 679720021
    0x30312022106090711100b030a1a010e0109050103050319050408010f0f05010905250c0b010602061906120f02030f030a08091605060706090f12020708100213210f120206 74
    0x4845c2c45480203009038003030490200120240e030003621200e00007405a8200350015035580100b008a607184004000b0b500d4014412100a601c556005010f01e0303409002551454441903105d1141095441c0d61805042c0d070200001d000740202c0b401040e102c4020001035a04003003541c000d208510441500d241000c000061614440c0100fa00401c00103a2070190010502040034800607001e00c4031003480094584000401c4008444600801040e00a007c00b07162412200048a004c0d60001c15a070b8038008051010200030002403240c80c0d4044440c5103640c105000003482e019001d0f000032801c4c807002a40c840582e6004a40301d0040b05d8100841d19943c0c4010074014212106029160308500180150000706203941c100340b9009010f075504020200c0c264440b2003c95501c0d000c075101590041e80108440c0d042046480c10f843e06107041103040100c4000268400c0d603480c4501c0312841c002c80c01c01401e0746200015004401d0380a0600c56128000c1e1410781e01603000c0d000d4a101600500000030340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 679722508 1250 679721258 679721267
    0x16020607540e16080118060e01030803070f031a0f0a080304061107060f020c0906040b121608060126030c010e01060e060103090b061512040b0402040506120303010303120221060907 79
    0x1005032032502c0b2284c3c03581c03d00300c4580c018400c0810380000652900000a441c03806071100901079400b81c13114a56902c1c05d00700107002510140b500b1000c1514220a155441c0312140c0c2074080f4113030464a02000344900d400143c0c0380210380d00001c5060000050000e10380d5003086550b81484000c206445010747c1d01c64007520340549c2d4001103405a0007a40500c422441c1c120206a44860002c00020380405180041307000780c2d508802034103a95200c982e020500c0601c0d04403c10081c15050700800b815030401088090060b0741440601c00c0035401c48015005000510030f450f84070f490b05c002080039480811006010305407500c1902c00300e05906002c20140c0d44280503008000350400c0050180e0b80318802409440c1d128400400060302060211314030303090813401e03094000c50094968038018103090040000321000074000905c0303407040c84481c0310114000b10036641101c0e01424001090070010418202a00c54807e54498a0101e00f40c5141e24003060000b05004100c10b941000f425900d03043c0544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 679723758 1250 679722508 679722541
    0x7090602060702150703061e06082802030c040e16081503030304110118060c1b0602061302180c030a0606050c15061816020607540e 58
    0x1038001c401803840c8603184c0c00c0042d400c0752040c5030000701b040d964034500fa6010300f41110304100f948251000c000f01daa1025010341c2182d140d0350500d100c2e0400c01c04161600c00c4540326441c1d81900480000d007101c1d80d0400b610b00070004821648072078908a05060025000c280600c1d01044507c004110860020201d0340d59100010340150700d0340c1c445845140340480c0c500070036810040d94102c000d14401141e110f0303c005028540314210b10078018a002d01e052140c040f0011540d5003402c0042040c294001002600001001d01112502c40310740003003820340c041c0c0410114500e140f10300b400410101c1000452181880c001c00300702c0f2035101c0030111418890103203440060f40c8070180410303055a112090540000300200b6044e003104001f0001011000200c44000d618000d400e000c198403a01448101e50181240c0f0307203c4001e00000e104416502d59556030301c460382940110050314040394001d45608821285603158100364160844030b400e203003e004001c00c3c1c0c43c840e07020608034500080e006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 679725008 1250 679723758 679723771
    0x80711070e0c03060d0c0b0c190305040e100321020609010c0203040603020d20040806010b12010b161506080115121103101a0406050906130507050c03030108060709060206 75
    0x10403254450b0009040d441e08080c0c600350740804080304010014108108220080200710540d84d2203441040b00a810402000e40d81011742240b10084000a0740c450115001c1c0c0f16420140c242a84072401c1000030241142c00c001d203044581110440c03440d08045000e10001126821102141d680c1100d02d400d842d00c0491132800369109101c240a00c60081c2c01405440201602c0024603000c0e594034909400d0314545c0b01001c440002400344407601060084501414901170f01a01d80220690802e280c6401441500014080894002103c503140e40340c0c554003941105501d01102c5503403054000404451241c1c0516601e080d66000340c4551911101080388e901d0f81c1e80c2444d400300c5490b085819400491082e84c503020711034a018940300c0c0ca200e80d010a02150f0261620900d80d0030038001216240e400c10340c41140a10204403651b40c0c1c61200680702030300e440300401e10340c581000a82d010301031048091002e000100010410340d60000700d0350704c41c880c15034034921800e030342d4139060380c650009a552 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 679726258 1250 679725008 679725029
    0x1703041a073011030c06040c0602070b03070801060c110316080709060b270a03081908190c031104080109050111090a03030c05030708040e09011512030309020604030b0708071107 78
    0xb01c1090b005003603525034403142030103481c035141d402605642803280c204c404031780b60a10840300f44441c0d80d041003050301400e2034100241c0b82d4181460040c0c1045414821401086800b00044003088a200d101100420010f4220740d50303450056802c9082c15175034050b6041c240301d0a00b000410003001e004640c22a09460160b920700407610b030180130640300c0a490018201c01840b116115501c400f030701c00c801035000b9442c0d40c0d2100410a00c40404d6010751800d0b03400c000b2050188030700c1c502d039800c48000c4500841c00001c0e0f0f90300c0629090b4090589141c0d5902c7c1d001c0085070004100e0f00c19085000364520400003000b03c524070485070700040c0103011240b81c1212118009000203400341c00b100442d2809501128104951aa290011588250003070b803016101d00c0b0522502da602402940d00c20002414000505403d00004548030211a03c0150801d51200780354001d5440342c00490340619041308a40d9107903d45800c020713028440560780b45c40020825048000f0709480454003805899007060f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 679727508 1250 679726258 679726343
    0xc010c1502040b1209100506090a020a090b0c0d090506030c070f030201020d091a0f040819050409060902041d040503180f031006150314011703041a07 66
    0x11008000003010290201681d420030000c0743d002d01c180040e0005099201d0252141c1c50001c002c01c1c104507034a00c403007038490b0618060041903980d0030805a03016682c084010b07200d071030031201201e070052654002c845001d00021240005480810542c0e401134003a10307004031050341c844c00e1258071b00c42140c44404910081c840744000400d0310700c00e050303a103002c8e100260400701e101030300008442244408803600391420043c000b44400a48010b5400000c1180780480e501d05900e9400c464032940203c0055400c07103003240001c4501420540d0082c009040d03003005950340b80c14110000354410300071040c18052040b0303a440c036102c1480c06141b08941c8000910b080c00e00c0b0b01c1900b4201e140c0032840580c06001d00c088051680c03400c00c00000d81c00d040740804500b040c0b8106200e0b1a07520641840410141015000c0b03c654401f50500313030460341c0c01c080300e06001e00c1d1110141d043d030059401500c018108404070a600c00c1c2500080c0102074050f8444100e2600591070080703000c120481c607100003d20540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 679728758 1250 679727508 679727513
    0x6031203100314033006101d180a050a05060d0c031e0f05070512010b06250b09060a0c0c120c14030a05032715040213060e06030f0c010c 60
    0x140f848925071100c0304503030a011907143e0030f00d15507145a10b56041581c080141c030b4000051400b49540001041d44c0c40000080a400002d040c800354503102c0ca841c81150b01440340c0350304d8a210030b51503000380f10015009401d08031140400381c0415a072035039125003003001042c01494840b54900d50070b644540c952001c0e52559581000c41c0d90b20340c842003588000103402402148400e0030050350b440c800c00283ca200ca05003010480382440c2010060b481e60b25141c5034200c40c1d1035000440d10500d40011881142040350004c0801000c1c00d10002000380d1782c05000d110082400089043c096454654140314400c0c549100f1904e0914082018000d00300b1500400c010500400304010703058011550129920b00e99040f82d45075902c5604400d0008030700104221441500402d5030031030a1003440c11034a0384100640a07643d5412507500d40120300c0760f01c0b0210381150744810800e0b40346100558240443d9a17a9441500c802d1003c5504030b00a000e0b216200a01c020040f6060804a07016100d00b0501d030010f4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 679730008 1250 679728758 679728773
    0x8042604031502040509010311030709060f170c18040c08210a020f1b0102150103020612070519030b1906021b0f04020304111314010b07050a0f0b060312031003 70
    0x300920b080d80ca030308000c0802c0945410655a01850080c845c60300400242c2050502d4507510380e02010f5014036201080c4582c13610020400304450780d1100c9001c1e028409014a407d2404c0d0350480e81d44074605024055103070000700a69846907014003031100c1040d90314401580c41d168002c070b10000d5501c0032114910f8103682038010f0b1401d00502e09c1101c81d11108003a003245400003420070401561450442d0191940c0d04000c0c54018000c0704814003181c0d451640881c0c41406060170aa80d5400f10000080c00148a04240c5102c2208130801540704007201d00003070014810111200e000d194010028900e8071884065542143c1d0f2650040112441d0110000d20000c5c5080b040350303201000605041e10f03940c81f07001070740c09240103c0382001040c50890400c5120808014000c1030f0314146440741030042a040034035411509505105580d4034650302d055824800c400100070090700158030404280030fa1210751510070401503040b02c071100310081d000c011750b02040340e070118107203141c620610007e03019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 679731258 1250 679730008 679730033
    0xe13050f13030c050d111621080d060f09060e0402090a0c050d05010b09100c03020c0d020402071505060f040e1207030201090506250503010b0d0509100207030804260403 74
    0x40c1c07600580d4a2040e07500e0f24102503017904404000740c42085044006c140030300010200410004092150b14540300d804000c05502c4d8030b6008003204407107514424080c3d16000c070381d61042c0c000c40402015071150122a071107541c9001e16a2070a20381240801d0000f40b80d00068045e580041140a0940d03640d070159000d03080b19400407042140a2100344964441401182c2c00f038109569056255545a410b20040f807129811354000c20000b4150807002c0b80e00814a01c0040b0419036001b07015000c5030011030068400e03214003c1c0404250b1424000046081d40202e00441007110244100d901b43c000700000c1d0b0340128030141e0942c000300c84448001080383d000300040d5109000121781181c11b61220760a2240495100d101c00d0100d4803800c40302e811252050984040e94280701c0c2c00c55060044134420b6000e0a41480340803640c0310081000700320b080000002c0c5200380d4500b5076450000c0c2c58018480f85060b02c041381c000e100326096418074608041002002c044900c5000e06061039501c60401b816039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 679732508 1250 679731258 679731263
    0x204120f0809060c0609062a0a0e0a0e041203050c1c1121071412060406090c09030309080f030702060318010614190e01140105040503030301060e13050f13 68
    0x10704010000c4a502c80b02c002e040c601c10610301904580c42c01000190070410001c180c003115413954201580c07946140d039940c941000445191a131a000c642d6000c0d10035040d0341000c141c1c05500c41500040246d000700c0000d105504c10ba00e200c80a401810003a8160b900680e6000d81c404401c0c811440364107010f01c500982c201311440b0200d94111104c06e803001a9020307034072101c85007402400c130758100200d804049401c0481441c10790001812070002d804540200c000c15000c545025020840580c1e45400a801030b1880752800c00038000e1b00a0050b00c01e00442c0f00880104e0b80c8071034000b40190010a07c1d140d102c118101440c90308c20507a0800c00958801450100000c0d600740e03d28001c3d000900c00c1e03a004c0c290180d58a10809040010009030720440003000e003600031194018007100074245a1a03046071500c0010400b441005401030301c460080d6000b031901484048000186568400e04440c0800e4098406110300e041040c921021780d10102d5442e41c1e0b8070820004203040006d10b420420901b030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 679733758 1250 679732508 679732523
    0x90201020a0b09160b03042609090a060501020c0a0f0b030403110d0806090f060d031b2a0f29090310050f15210f0a030f020c040204120f 60
    0x1c29030358030310481000036034824646a1010402d6504601c2e81d10f181c40191540030f00342421440c01e0341d6028030103101042c600d040b035200701210030f002030080e400381e440c40d480041c1000054509540c0d01170040c15503101d054014841c003003070722106040c00c3c18132800b0f0f00d080910b841319150030701401c1c020a500103001102002461a0168400c00c4180700c200c1039030303403503a6980780681031100c01c04c8900d4001900400304011120113002607640d501601320300e02c580c181040c1c1005443c410013038801405208000d00483d004c0824159801c05444c08404900d401c88914a01c17107031a0501c41d040c80c81d003802200b10b0082540c0203440c8143c2e081c1402d2802c0e55481c00001e02d000c1c0c1c004046810200d180c0850000e00da2070301c05000604070001c2c011580300b2240d800703840c91140a080020103103d003d0307212038401031014419445842e4148040041c92180710120794012102d403074000c0081c200380007440d00502500c3c003a90840d190900840341214a0101d10034240c5195443d48a03004050050442d00e04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 679735008 1250 679733758 679733773
    0xe09241504030627080c0d110a0f140f0a02090108030c030d0207020415260127060e0607050304060f050606071217130c080109081b0f0610081009021309020102 70
    0x1900c03210201c070200e1046405c02c0c0c40f010a4581c0629240003108041d00307000300300c182198821030018801145a4014189101151590505500e80f41801a4803d414040e90092004c15800040c81c0705c41584291034000c0c0c0c03a0f03a26001d440e203a004401c1d1010755504200212000c9400c2030300076062240c0010310000c0c640a1040c00c4105000d01913014540180c04212400e150b4170307503040f0703400b041300040009100131018040381889004502d10483e10320340d45080d401040c088503902030441240c201c000c480f950b0a000c100a4070a400c02c076022500c0c5410920f2103500680c490140700d01909002d49401d0070419596210014074001180c20070070000c500b2540c0880141090b0302d00d01542403c860000705d5866801c0c03020840d1a590410601a8103081c08100010001e0040701c20a201003031007110342c0f098454000c0c2c1041b4008131b82480520030101409050560760320b40408456170041100e010000c02440705c82520035458003e0b6004c2c200344c04540940d0311541294803120300c14410348052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 679736258 1250 679735008 679735061
    0x90d0816140315120d0e0402070314070f02130c020703081c0c0e04180804050402071e05010b0406090c0906050a050d020d090c0602070b16030e092415040306 69
    0x1190011207440c40c015031240f41c5900341e402d00410702e13120100088054802e1100b586000740c00d2860740e40025020741d500290106c103251040001504680e8810b504541d0b034440b50a2016102c0c1c01c51005034407036006542c0301c0d20015a00d20039400015440d40140c00c00a02d591602046034105088121070b1450854006007042114404e410288031207483da001095041c3d000e100c100c0f80c013003074104803055038402e040000c103041005681c00c8a10444001d40e50390001c4c9050b0070000602d00d002d844442e801c2c0700c90810010190481c0720071020036141084219074940c1e01c07e00740c0f20854585004194210001d200003481035005250f405094240796190000c441c100104036402600c80c40d81d404c0d601d100d44002c12500600403030041465100400044d4141100c103081440f0710a44045101c031488004020140202c1c0c4c804100503005095008034604504291207040b081c011480c80c0071601301c004070143c41c02d60701c1d601ca0b0460740341125003094290f54034040140508000041c40949040e000e41e47e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 679737508 1250 679736258 679736297
    0x81009030309120c0506011e1208040b0a03020a18030b060103050c13031b06090b1606090b040f05060609150f0d0503041205120403080a180b040b040e090d0816 70
    0x6040ca001c0c1c4d0341c102a07a1880c102582080010380103000070503d00103010136504540c2c1c1010041e68441102000502a2407904040074416984818001f8601051020700c03a501580944030808040c0c03030f9081480c000b00d2280c526401301d03005c020096107071480480d80c15482503000c2030780b0510080080749844101070340c10000001541c41110902003203900c4559103004805d80e0001440759082030f052190030000e022615010300400000804000106501445041d80064401c0394019288807400d0806041442c8600010320064805100c1c0d1804141203041401c4440d10580800748200a07542c520300412004c10841c00e1500ea0207002d0382c10701008500144010002400d0b800640c025130040c52404070308114103001d02c85a0200e0134003040020500c0c3c88121102d03010305141c21030999400900030a07031046681c1201d107510b0400710b008580d0001d100000c3c800d03600000307450b00041e0344001147ea5119281c422080010b00900007056901d1032000051001c42d000c0d0400400340541e0424691 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 679738758 1250 679737508 679737533
    0x80a030f050c07060f020c07212319021c0f170703110d08010302090c120a0e0c0d08090918010c0e040c0c0f0b060316080604030306050901081009030309 67
    0x442222001594030f00700030f03140c850b030b011401d00130f042542856143d6030070340e40b40d40591140d443c4502e107445500c01f495140034550005143d01601da20705070000d01c071a0401d044130301001403100b803056501006610740d030342140310702842e401070801d03c000500d9443c400102800070b00860f0011041d194020005000d5009664240d504201c03494841e07070b003420014020800005005a250828050408095404401d40d4151380e01030b00c4804058590b1500700c201441110b10400304548a0301c18040c91350074541000707110389500c1044071041c1c880c50080107044060b10400070841e40040005900350300b05640000e1f44010240c243d500d6424440301c1c41406d40e400305c05094001100840402010718082c0300704102d449051401d4540c41010b59501d200c1350024810140c000c80d00e1400254041d50104030f240810b0032603044002d010741e55001d500c0d0b601c10082d1812400710381000030100d0941002c506017070490703120000900d070408201c0305100041ca0408425000c01d51540d4100c00820041185031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 679740008 1250 679738758 679738771
    0xf21020c0c091302040b1e06070311010c12050a0c08010302130209190503060106090e07030504260c0114060a170c15120606090307060e0307080f0706110118080a030f05 74
    0x5036114010300c100400c503241008418403030841d02c1c2a4604490405400e682c06c2c0605440c8c05641c3d084a08054441d0407080c50190055820414480322096100040010020644406100540f50380d0400002d8400c045e00550001c0d070b0210041005d8600f00310490125002c412005190861400c00700d00c440040ca520200c00464100082185080820185004002034541170300d849080805c90303407030764034090007120070151030b100801c05002c07011a589811000312001c40c10301e10f154a80e10480c540080700110441d51030b0010258450220032116880b820000702080c00941c1001a810b6400d51881c000e91024842d51041c048c840d2120494010f031001d0401216461395420b0000c07085061004003c2400f5600900480e601d41d207001804105690b480d040510303c4501e030002107480d020706584042294417071391520035800400400d041054802d155103420700c44840341c2d901e170300b81c600340303d10f1000401c82100c0510100740c000e4080d010000301460081840c1401e0f1010301d00351034041d40d16 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 679741258 1250 679740008 679740031
    0xc04061d06190f144618050a060e16020f0303040609060b0f130b060904020a030914031c050702010902182703070204020906190e010f21020c0c09 64
    0x5110110610f40601e84c4101c0c201d0b1082600080040b030640b60891200c0701111046103102d001074000c4042c048507010380462401494410303a130301558142c42589828801e400d52801e00440c031040c209018000940d03124170620740d056194641c490117082012080d40007103001e079048514403a1014002140103501070080840d5904050070404100d031141e0100c075214024041426180c1d80340c2d425824100103440c03400003142208080030448900c07070254040d80c0907200190220b200c1d0740503070190080c940603403540d4103140440c8018541e03a03c40e1000007020000c5242c480c0c0c004650300d1300308503031040551001094445c225400301d5090010032000803802e82004ec100b00c82200044428030000c407402926284d01d80c03041400780e44034420341070041d000c1c81d00007445100c203469030400c540b40b00d0481040d07074101040c43c1d400100910a080c8100380000d5110384108641c0703214101680e0180003410a41003900e0309010b80c04002e5006046030340c01c40c040c608640c101c5669021a580c86141075000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 679742508 1250 679741258 679741289
    0x2100f111c080106022a03030405210d0801031e061107121407080f0d06030c080a02010f030b031005071b150e01020f030a1802060403140c04061d0619 66
    0x8000c1c1201e10140c004404550240c0c220b5a201101070a000e088100e01b40401612413101002013070451040e1f0304680d07044101c405940c0701f824520214a440c000c41c100948512085052048410720020310004d03002e0b0090406800d810310f940344c81000054403601d800100c0b895401d2100c80242c0018400b65a000e1144820300346a03900f00d40c01701010488605039526210b82555404003901510300300c5056218003080740c004400c513903488031024642082c4600980d41c0d55031140380e0380701c0b04044101e0002d200751400c9072405001e80100a8580303001800341410400300c0100000811000b02444104140c4c800207074241400040b1420405000e02c20188007044400d80744030035551000500c018980c0b0420250a05510710342c1500e410078150400440e070503c940c121041a0100b150300a0352100300000c00204005030440d492601c030041c841a50185007070030080204a61092003400100203a1a004021266081c0d810580c091401000d1100040545500324020030041d0080d2080c516680e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 679743758 1250 679742508 679742563
    0x3060307050102070b0d021c06030c140d1709011e09030c0e0f0f070509100507020301141b09011707080403110f07141f0201200702100f11 61
    0x8440c0024107400c1c0020f0000c18602075041c2d280b0b104100004881d42c0d8045030445180980c6140384c0081500c19006100c22070f00c0341040c03920aa05446010b5020201c40a1060103041c0b00c000740c01015000140940d240e0004200701101d1b51202144074100400382c6110003450740e030f91a0020510129035141c00e809401c5191240b1240c0d6690422642d13101760801700016511500c0c00b00781d102c122010100350948030780c1030030b6a1900951032029880307521813140c2c1442551242c05402d416000f24028000740b85500050074145900351880c2d020300c82c00c030103d241a003035184010440210189030010070302d00c140d003c00b1614a1f0070b0740c08100155002c1e0901050540c08201d4204c800c5032400600740701d0240480c0d40350b9a09540c03286007005084804d5049240c0c0e51420100e200c03016504004900101c4420000c0c000c00012030104010070b012103030f400168a190080d0303007032594041c0010380b40440d16078055900f8044001038a0400c0f4800e112504402010702030300e0300c04001041090032500d21034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 679745008 1250 679743758 679743763
    0x80309070605180607140303010b030a06060e0d1b0e0a09050f1606030b1507210912080d27021503090a110a15080a11090a2d0308030603 60
    0x1540714008000003801040040b00080960b11014101100d5042e92292140b40011290556130350340440d50001000014190700c030440110320030000300d03104004043e200d290581e4541528034000d9001508015810009942120300b050780c5150300003580901590703015003104251081719600d0b420340c2c0342e0801000b01b060030410504101d40740406001c03030307051101d601814060584586000c00d0744400321036496468400c4400c00088118184954a0700346003810817a8000807030b04001a04294680803a41e14800c07041c20703059032122101c4520f410780507140c0300c1aa8008040e134001c2247c0d520f616540007800349072609900000e0901784402c54426004120380690000c4001c00820000c0041043c90000816503039441a407040d5910181600d1b500032428485494000800401c000200f1a02450700a85841c0c0700740c841ca08280030103210622651a14000c011030039400010110050111280350b0b164080e421340507552030109012103003092000101c00781e00c1035030420340000c00e026050030709 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 679746258 1250 679745008 679745023
    0x21308032d030a0f061a09030606100906140c01020c0f010c030203060906120115060e120703030807051e0a0e01030f11091c050609030c07080106080c010f030b040504080309 76
    0x2140c25100c5168500c620501c0319110082444075001c1e603541c91030707995144c81c1d489400a4007102d2010390400e201140b00390456407100b844284680325040c00a010762520002c6a40006256034412040714030307080d03043c0c500ba003041e084144609002c1c0503c401180092020b040f1141135080145110902c113a031181c2101c0303110220004043c0108200207054076502e20b440d0b0083d40c1603880141c80c60366030b200c0c41d00400c00c14030340f0307280c10321a030000240c0319034400140050328008403010700c240b8220300003841d030f0380b415440010041007207000003401e00d5002d034001d003810b904110f41074a03040012040c0048658000d40741d00010500c044829407055906204000d01c0c61070721b0504101030010f800c070031340307841c014403c4941c03160000e01d01340340c06260706890843c045d55201c000c80e15035080860071207440e81c001000b070446600c642c1100107070b60300c01406250200c1c0c080070040c0140035591401141c82c1d602d84400c4009054403400e45160503280d0780302d0a0300c41c9009516a41c1c503401c240c1c8585041522 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 679747508 1250 679746258 679746307
    0x1090b280c110f030c09101706090706110f0a0602030f060d0302060a02210a0504020103050c0a08040b07110d090303030f060b040509150306010305011406010906020c09090102130803 80
    0x5000380107800500c24511000392200110b4458481010450010740340110301c111603904803903d41d0074000003904107221541070307895070700c4111100c0303d440c649269900400c40314002247d10000302042918003405ca001c501105403000e6071602c0c450341d941186008a401c500303c7c8e20603800004c2048450314440c2c059003180303044451150340000b9490007555000082c081810540d40007800086044406821500110344404103894511300310540100a090890301680401e044c01d00048000c4105406c68140c1c10903500c589405071503a4652b210b49620041c12041849505400420003c0d420003103007080d03480690750003c2d568107510b002819680d0a51301c04660906154042c0643e00e00c3c4d0060b542641d070b041c1e0b0b901361980c2c1d581a14540d5514150341b6250180079400012050004c113421001d54070302d400e1000221740e22a003004444000c018818480140c10400041c200c510340b83d00c86c0c0e0380000a100001d8109440542c4840850141e03502140d456400061003030100702e6060b0100c1c15200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 679748758 1250 679747508 679747517
    0xa06050603190e250e130b04121205090d0e030607050a1d060301060c1a1012020d020405090a0501050c04080a080a0909051005030f010c02190201090b28 67
    0x2000c4000c0c010b00480c442da01060780c0e4960340c0074a9040020406124403681c10001908124614080743c4421080c0717001d403680c0d0900d2040010b120f582401880726000d5403020003458240d07565160103900e0b0303a0420048040207400f00001524144030300a49000e9100342020b041a0701e04084042c0c004014000700600980002c0208030800e9005000c1c4c1c0c004006c541000e0700806131b1f10500c26100305040e0181c80e8032000100020458640c0020000d80a52046500800016507241018600c81c0c044074a009a405004801d100c04503a8032020208217101034080402c0da130342680010300f92102200c3e005541c0d03000400320002d04c04240246608002c4c0124000d240c98140b170341c55600e98181004c0035064000002d2110b810380e119403001002807901f18000c21150501d001c01980c00100761048520034821290704006031041881a003040f010a82c008210b6810594202070280802c0c501c10ba0501014010010701c520000d401403c1c40c134400003152000800d103070000f9001c900c28400590030072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 679750008 1250 679748758 679748761
    0x803070e01080f15030a12050c06070509060913021306031e051e130c0e061017010501030b22021b1203040f1112010b01020c011b1209050303070302060a06050603 71
    0xd4203a503141500b0056080800c2c10130102803020901c0c0074100b04004200f040c010710300344c40e4a9400b0707014100302120f0b40c042d103440d41c4440004940900441c50340ca0360290080103a0784852804c00d0452486900e102e00140c00c00313144070182303110764440d030f03100102181e220b07410035054101e0603844904200410100b000541010481c1940012030492070182099070f02005c10a00981d0441505035113511080666042d03031694000e610540c8160b44090150020382d580300340ca103002e01010445480c90014001c0b85038a08030044001c0d00d0140c50b41c54001b480c0b205001105040307052030151030030031a0009651415032130089170a0348500c860802d85a000301c0988400308203803004598006805c00f0203082d41030010308118105414462040d5800410906404201c5e041900841c119a8003602070b40c0405c00325000648079008034a200c00c0123100031504205c002100e0030a00d42c0c0c060b5442c070340342c0007403038668000c41d1131948009425400360340200100816880e0600894010340002d0314400d0a5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 679751258 1250 679750008 679750021
    0x111040803040b0306030a0210020a0c0b0a0e010c080f0406051206030102070309120309051c0512040f0b181503010905010803070b0601110c030d1206091a1203040504090803070e0108 80
    0x781d0059029a01d0f0b00540000070a655541c1000b6040303515030010311203031008140b650040d60b034103081d49044031071031038006000a410849030250350351050aa102c2106003500140115a0403d40f50011140000c0901002c1303280603a60014001805c959100c1c583d0341c840106c21480c0c182401004188243c0c01000720380300182d4400385010440e41c90f6200050194402c0c5401e0b00c000483d9003060b50001d4600484c003038104244468100040c1c001c4041c0c0c2c3c10052196240d1801d0b10890140001c4515030f03040802c44800000014006081c5103d00b03d0085680e01c80040c82c142503800441c40302c0c0300040014481c2c030900d44145030042004000a40c604101c2d540c13050305ea6100140300a05100d8940120b940c040818440540804001010385004a1072964003500c0404d030f00d00c1902c6600d20704040403a44601710722801c40c0c100c861441c1e0740421880241008001c03401c80900c0409400207000024054a81d8046d102c1e10f90301c201220b5807245001c0e1801440c020b10900220304204d62036050100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 679752508 1250 679751258 679751263
    0xf1915110f1912030b0d080d0b0d0b0c0d090516030203070608070f031e0906151a030424020a0906120507210902030a0c0609050105070b0f150607030903030201110408 73
    0x41043d80408003102c0d030540c00e8801d0307000f4624900707010b070490700c141401d00411407090010030340003022120410072021408180082c501030740d103008008500100110784040402e40240c180400d07100030120b6000050b0365002e0030039000544c104ec948038401d20034001c51505208210103018039250128523840d0598005014100310050314007419034032058040d1925803d1440221085807003410300010b010b45c40d040000700003040d4001c4011103401c001191103810010540120301619010f6411074503103854041ca560b4070701c51400d404005071841d52110b00d0302c40c000307403500004588401102524182c00500002c04000d05409060303c0c0c8000c10111a1300503005100e0540214403820b6494460b00032480201061540690301d445040d0004007040b1000e0120001d40e482980c41c00712551b541c40066849003d000001029240340d40c3c0001c40c038154054040d50f000030b09400c4003038240d01e6000401c0c096404110260f0000e01098418014140c0901400c21150031504030245401c2c9482c403081d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 679753758 1250 679752508 679752553
    0x240412050d1815050702030f0a20010e04020d06030209010305030a0206010605090d1407090f1a040e1002030601020106170604060b010503070c080903010f02130e0a0b0f1915110f 78
    0x114038810840d240d901d40e48203405031031105e68080e0494107a40c5641e07031400d0307440d440518222044200340304414460421702405a0015506071104080f54119104000c041c0d0492421002c2c4696100380c00400b581da440100b0b40203601072800b556540e88000c40083c1003480582204080c0941081a0900b40d2140102d1280785600110a07406a030300c0c082c0ca060901c8070543c00025494100801c41300300d40d08507400304640c6903100c004540800148014042076400291074071409412002c0f14944810668004513807000051000181e155101c003428181888006008119a409501004108002ca100b02480700500f42044c5d421494a0f09005203040c4407200028031000d004034100c0c030700d82c4094002942200c05540300b0354907a4080004900c40406510444045448680104695071f100b4410030201c150054007410b484805c2c101030004184c00e041c1e0218900700c40013000694041c5001c44141d2500791070b640d520a124500080c03a18000780301e1807405050304020b4138168212034030078062 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 679755008 1250 679753758 679753769
    0x10e0f13080703170a0f0e06090a0b1008100b091305030d020a050c030d09151a0f01020319030e0106050613030b06150a05040f090203040c05240412050d18 68
    0x10307030b0311000e40c80d040b1007500402ca0104041c41c1031206202e00c440c1150405000c00c10124002c208080600c01d010b42d0369001914441d40d20b801000703810000c91a1080503c3e8401824100d1000700c6507540890742c50174440c000c044014555030358510400c1e260851142d90041060200320845000d01d8071465201c0c403600070648452035000450b441c20b41c1c0100305441a4050201c20741e6118903010344150082d080180c07045a24503182000072100c02d54030f204184101c080035000d01215841710317007400300710444101d299042d4030091110f140009012402040c1d42c0c401aa4041900502c0e00600c070300351004d5820551080b5800d00072210564980191241105d0b0098040c5481341c44220114039020401140801e40100000d0f41c400b40341c1d04400140121094271042e800310030faa40514908034042580c00500b560f9445108108521b01980d1081d60811003c0740c103040000c449401e0701c5030382d000750b2101c540d05601035008800d001090001c09600f03903a5040940d504c03140244550040341250207403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 679756258 1250 679755008 679755023
    0x5040e1602070611010b15030702011508030405060a03091218050f0f0621040302061e0903090f010905061218150414030f1c050612030a0c0f020315010e0f13 69
    0x8140011030b09400100d103046000e800900044002946547e590744100c1d440070143d802c1605e071518041d0005040012500403102542c20036040c5000c0101e01c0c0e0103015514200350300c542003940499003070800e84440e40000d44602e59061400845c80300301000070b43c001d80c03058003100052262511000408401e0301c000b2201c00d580d5038501984241c015411010706015004103004000c00c242c0c000642d14014403902c030700c103c5c00702e900800e400090001116110310542051201070000d0034030055004104005040140a0035140c0b004154250011072142d207080c000304050102c50003008071311108146c0f05001508840c542480001012000644000d11801080d102080362040c113206a0710a5607049107856601d0034124040b41a060026103aa0385861403c40412100c0c44c185081c8207904201102550801096500540742d0015000064500d007a16440b9013005076014000440a000006a0489154108541b00c0d005031401070051500100c503600340914140f6061444250b184d10401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 679757508 1250 679756258 679756277
    0x31e010f0e0408070f0b09061f050405090c100f08060306060603040b090a0204050f070810060f0e190f180b06090f010c0609060e150126070e010605040e16020706 71
    0x900c40e540b40b0134400050101072070140391800300008050840e0040040904440319074031403035100980107071005000030325040c0303414041210741069000a40d00507811002c0e0f030741800548002c69540f0941101050004555a00f0922210742043c1810303000310080d07000740814680382000c549240701c013410103017550721450005412a0000c110341c0034015800350062180d4241000740c00080d00043c0c034800d0210f45c000c1d002800103a0615855012114550f842d0400e485800c038045d80c00500c0c80400d15002148031075060700c6145030b03080d148010125024000007817450319802c481d80d0025400700c40006400c218800300303551f9480041d0346c01c00000720b840010116030000145d4001100c80801440641020000420720000d9400900b0022000058403005001c0001c0042c14800900400149541e0003270b504d400c81001800b0282103441c41021110368a855000d21041e6503402d0740b041c000a9800170381409900c010440349a0010b104c100c118481c0f040000d8040d4660410f0f01540040095110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 679758758 1250 679757508 679757513
    0x32106030d0e12100504150509060609060409050f0d030e0f030a121d0105090105010909021c0215030c13230f06040906060507050c0604030b04151401060203031e010f0e04 75
    0x44140c9400c0c620400c8800d105804c00d190b6010703000c1100c1c2524424226404615110703054000c29118541c5000038104a0f6507040c2000030510019203040e810980d0345240c00c1c0040c90030484c00030002e050030001c11a0450244005040e101503042581e030780c0c2c00020b05942c80e014000165080b41c4a039003007600175030141c2520f200050507844006580b4540740030b040442d001040d4000c5000e014502e000f44050b83e2103042d0704d015500c042c14007e40100a9081b2480d021075616403101c0c90901c01405150007030030101c040081034100b82c41805070603400088918030340d0491440c0030001c0820b1080e44031014141d10b03071258901c0c41c05ea40240181282810070300b641ea182c6007240d015080304081000780c10b445204c02881d6421002003151a445859055a160b1800c0f400351801c0380e40c07102250040341d560303070745000300b01d0b0505100e00440d903102e844030320000e44003520450280041d5070045440345007583c201d101c6901c000716480b0100400100510250040b07090810685407079803440d04403500d803403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 679760008 1250 679758758 679758769
    0x5010b04060e0c18060316030c050301050f0603130b0f0f06030c0a09020d0605030102190e06070c120f050106140f040e190c0308030408091f020a230f032106030d0e 72
    0x1c00650340c800340000420051103091f00c60074010004170394040000390180d031015140342c442030007000c6c1e1101c840d100300c201614001c0011988148034081a202c00328180c1d591030f280c80825140071145503010004c1265010312402842d03440b407801c0b0000d144a40c0a280410341005e0103000d207014940c0c0002c1c4803c20541d00340c108ae0003e242c080c0c021592510f01c00100d2070100e642d409640009680c40e1010007051400782c00750395046810000081d601850080788000321036070303d40101c030601500070601d0003042c030a202d00d4000702942402c0300480e400ca2030070006103407101110140b25503c0d00200b1080828001050312f40c6100e40101c01011035641c0c10241d182c490568401031900c000042080104144040684030070401500e018083d8180d9544441168500d14020313030069101400d40004a003217014960112032214201010040c46017269505001c1e2040440341e00e40d03c0060302806242500140c04184c000b4a402e1003d1410500000303519100b202500c20200254214212525a40d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 679761258 1250 679760008 679760047
    0x3060103140a0c03061215051b0d05060a05060307020a030e01050705010f06140105071212060b16021504030201090510050c100501060e0108010308090904050c13020705010b04060e0c 80
    0x2044440700042c41d0902040e0054030901c500340f400242030010000b148455202c55121b8290301401c40303d1104d00c4802418000d16000b4841c2c50718000e042088100080c00e10018044152440ca012810b490020b0a002100036030798045401408100f042000242d40840e000044907818980f0400c0d1500910040701c66001e000c10180855203042d10040e040000c0394803400c226219108108541883c00d401910a070084410241c010111511104040c03889641044088041101c0c0091503e480314003181d101c0d000754103507800d0740d0000c003202c00540c5054550b00640c1240c0c80c3c80a8902400d55000a210010f01e1149501071201c01d401c40e840e2a004809442c07440405c9030807030b81c00c060031500070005404203104820200f406503c4003251075205280c42070507683c00c812524501210a414130160b8680107005480718021030352010310a0391070300783c1c440c82091461005600d5125a0601f103084402d64513074140300b9803600c2d0040048040102e41c00d5480301c0b130400c4079030301c0e141e09901d090800d888 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 679762508 1250 679761258 679761281
    0x31a06070f050718090b0705090603011e030f050a060f051504020c0c0d03092c01060c050f03031905011e2309070521060319030216030f0203060c04150503060103 71
    0x11030040300c03104c4100d64480451940900c11510341c5464114051329507115100d04940c1000081005004c400f0b42e2106110880502114100c9140e90b603448402016458150450b000d030011021142404000c0c01401201c9100314800c2195080180034540c65404068409000da40c0100340e2000034281402610b02001c0702511241c1c020a07640f4000b404001c4a000e038001c406401145120b20f54298400130207401a040340304541c90342401019600c1e552401e0041321382d44506600001e1480044c000f4600a00c40003158440c94290b07004094142c9105811403240d0f09022117408043c50180002a01150010100000c0784014075140c850b039805500802c3d40c1144244003031002e040e0b4048006c10182455580540074150341010615941030145c0750300381c1c95406100da141031100803240d000320b4180310340110350107010002000840343d0f10681c415950041050946001d6040600409600c1159480004d182904181400c50814043c03c008010030802100140959000743c0c0080c84030795 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 679763758 1250 679762508 679762529
    0xd0c0f0803011712090112050619030b1008031303080a09080102040303080a05070309051b121b01110303191104050405180f010b130903140d0b01031a06070f0507 71
    0x1a1500e01d024101001c0b040041d04901c504c22000e040b000c004ca0075143d055070140d4640c01c0c04001c1d620917001401c0c024013201d5010485000c802400c00d100c11002e8002c0d4811071403003c4a00e03207550410f00b030005980c040b2100b50410440400b00782c0641c4003500940e81d0058095803941c03004030b400c4400f03080c1c2c3c1c1c201481a600c0000c4c044140764006c0c0180344600541c13501882103680d070805c00c80c00e5070781000004001c0d0f0300208a4600e1100400843c2070710400140600880000004a941c94080d02d6841018001002c440315625564060700034200407030464011440d40c10b248940c04200d400e6030040c036584030b6484c60800030304400d0804171802820014001d2245040c40d003003403200503905d619039010511a1440514030a0410f0007198074031400200002c0c60500c0e0401c400d03002e8800c03034004604010560641001c004041000b40c0f61120003004001003021655001408035450302000310b86000442010003800c0d0b41c2c6200320340000e035003d000108000c0c00fa14000f4038000d9a0780001a115 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 679765008 1250 679763758 679763761
    0x1205070219050606041503120e031204060c0b012c0c130305100b031204051c050703030c03032d090c0f09020904110901020c21060c0c0c01030e0d0c0f0803 68
    0x50300040190180e00d04803010071405c41c00000a06c0b6440041c81700800c101101380e4031006880c0140d201c402c0c20304016050380d04a241800c0c403142264844e400041c04101e03001e49810034450454030f000e014061202400d400421f039201c9035020b0625006840511100c04030014299008000030755965914076049201ca82c0d0b02d03031030b00d41e80340c00052100069031841d200c06001c1c18600002c00c101d41512040840e460f00d403c00042c000588041d078152030040000415900c0005c2040041c0070085000f80d41e2400c1d0103078103280007429111009140c181c2011a045049008407403100c00f10901c8080030000100c042d018609035074904071991102c454100b440c0380000b126402c0d500140b035541811a01044119480d6400030390f00e0081605480c010f03030000180a440741003e0040000c030801d42418000300d0a440c4030154a001c1c804c0b18858580400807801140035802048104403901c02400d0502c04980d510000640e90740c10300c01030004100c45103420400340460301240000058204032526601d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 679766258 1250 679765008 679765013
    0x40c12060b0906010e0a05010f030b131409010c09050904062d0c03021c090f050304030503180103200f0906070c0f120804030204050612030d09020405010f061205070219 74
    0x141107200704039004811090000c2c00300e42c4100c01e8400541402407070400c80c141824011140e681c1007500c5030040c0340e540c844e036800b240c0c1c2c0c00d0640002c1c4165039030081501c421100303007003031001c07405095044c0c0c070f07030500b00b41115031a00039503210107446c400d840080f502d9072181081005070a5081400d020301200b200ca80f0440d842120340c4260007900030405003c201d1007034104400324030603100b045814503e1910b11500c0740030346410809016004040e646107010036504c17075904650041c0e00858203580002140d5040840310503981d800b40009090400c4501e10103407200c101c0c1a04041c0300c2d03e403c640081c2440205020400f0344a6841d000382c02c1f10b49449003858541421041070103100c0b10b2400c0d20300c0008500703010644014016610040642c2080c0c69279080c440944805400f00354080703092050410664010406059104409c600103d201c045c0e070300521080301c9041c1c108089140b0f0718801400025000003112076004001c000020380f940d40c981c000c034203010750440c01c16140281100768205 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 679767508 1250 679766258 679766261
    0x60c060105220e0c10020703030e060310180501140d030503040b10091a0909060c160c0e040308061e030a150b06131802090a0e09070302040513230c09040c1206 70
    0x4213081c161001d01c2c8408820109903500c0750b02e07200c014001030390524840241e041c60405150404c2d9041244000941c80d2020b00c0340201d41c3d0200310b00c1842d540c40040002000b0021003080820f019a0a5407400380180c40040c6984030040c80600784040100200d02060441a154401880c011108100b04510160003940c0040001441ca129003842d00100d00e0800b004104a07000d0b0005a803254504418250000407082014106440c0809412800035852000c0703800a0700c69480795581d56030a1510604001c6024030201d06c80c0104580d9040020050700c0c00104000980d4000924100781140c80b202440a02a0180c66a401610204070b0f4041c0030a62540307002500c24800c8001c514140f640100340c00c80c012410480d52008840500b00042c40c000094680c014504e10140c98104d900c9801240954000b035804c012081061240e10017405080b503d1064100e4003280b80c0c0c1c840003001e100c0700d5580c1c11444030b07036441400c50101250400200c105030800828902810840d011242d040c103c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 679768758 1250 679767508 679767523
    0x1315060504050a2a120f230103050d140c01090b04210818010e0703030207060e1503310606050907080702070b0c01020f0f0a0e060c060105220e 63
    0x9000d5400d10011404081460007100041c10040e0403c400404a030030f03100b241c0790b070304058480521152140640c0345900602501090a491000c0410201c1c07e005c442018095500b003140020f45804005000041c004100d00d090501280781c4442420400d0266003880d10515624848030f600e45000c09041000c01c0d4500da00c00c038003903120a043d164080318043c9400c03641003480d1000480300c10014902d0401c048440e801c06414800001d40c0b170480407003103854862941c0041d00940d202d032008002c0260300c40c0c0100087e001c04d8401e070160300114000c00f0503074080070380592000141d4450884040200c02013005003141912400c0e00b004c0182d080c41002003950f4001e460142840000050703020340034001080c00750b24940d0090041d80d01d0119a8011600100103200c242d5400b0022403c0004039000030340001e0070300f448015640e211301c0c00007405010051b04201d00440c804d01103a007910002040f01411980191070250324540800c12210b214021100e000c03161a2624102c42c1141e980001d02c0e9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 679770008 1250 679768758 679768769
    0x170703021207030f030315212d1218180b0402030c031f05100801180b031e0705090a020c010614061608040509041b0527131506 56
    0xa84500e850024059207500b201c2c0005094040122100400603200c1c1d4050711514440c100c1e00c0b982c040c2c4400f195040d1042c80d40c1d4020b850141e80054a041c0290040005034079220307600c060320454402c203201ca02c401403500c0098841e1900c24a440d03003a0303020390b040c6044080314000030824a070715160002d0b02c0c0c070048c90001c1f11180c9800040d20f044c1c145403080701d00a4184903812801c1d5629180e50b0480780d4086080e9082c040c80f0031000048035100d2890f4014010203944071040e543d0704210521800361803245c54641c4c03031810021003036500e40780840e0301c14084031552290803c110040380c2080c5415041e600840d0007010501c2040294091540a8594842c8000003031014603501c5070920001100d01c054941c0c4404200500306080d5404244401d0b02c51003070040a040580e00c4000450088085500f40c403485298007416088000c420040f03c080e0004441c11403a886850140d0070001800043d0183d850101002244101d2503800400d14003961000c00c0c15031000c03085002d8000b801b000e2041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 679771258 1250 679770008 679770019
    0x90c0b030711070b0d022a010914010b100507030201140c04081c0503061c14160806011203120921090609080c0d02010507060c0e18040b1f17070302 65
    0x426000c800070941204694110220314107014450529400a5100c0030244191500e0407071550007c2100f1000c2c6401d0f61001c100000faa6007890400c510903070180811603406034502062615a540c60403030545000b140d43c40c006403607001501d0203900600e4501c03001105910a0b40c204216080ca440c010815114500299a001c5078425100b002c403018044064020680034000030769281480805202c2d038100440c021008200c0640f1090300f02241001d0252054001c80221486111505510401007101000514242d8540003196004103000c4000404200b811840019403035034035004030b124203411040b00d100b22000c92041c002c410056400510204101200010311180254121404c40329010041c03c0b25402d241c0c104101c4404140d0304a051010501401003c5211031042e011411020785490401943d18410044826080c1c024210004045000c220000e86c54500301c5410020441c240e01540d42c00e00c1d1882d111201035040031b411072407001d070000101580081c00d402164020fa52 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 679772508 1250 679771258 679771277
    0x515041a1b0706110c0a051212072a030807020d030306080d020708010b0f010207030609060908120a0506060a0e01030c0207080f0328090b070c030f11012a0213090c0b0307 75
    0x140540c407944102c28039a8003029543d1b04102505011000c18034802180d025100300c02441d10071a1000c2d004100140ca0ba80034150b2800c64000e01d0460090340c0080011014580c1c40c615a5004a1403150040c000d0040412110280802d400782d040300d005000e60100759200c1400c2d8540003507030380100341b00e4403002c2d60810000c40d2203402e054140080201040e8040d0560f40c2c10354880a0140004443c1290440d540700e100001080460015149003014045071401074141141000b085c1e8001410341441b801003040103610003078020600310000d100a08000c00c1c01d0340219001da08220031540464401c0c0074403d4102440d501c084000d04400c44810760802c0309010011900111100102050020440d440e200b400b980c00c1036070261071000e104455003100180c5030341d44c0400a0200c0002141c600b207000480e03c01d190307004444042180e490701c8036410b060504861034482c0c2041046d02074014146610b5001d1101c92503041044840d41051240b0070003036481c0b1148030903500c00c03111040003039500e41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 679773758 1250 679772508 679772537
    0x18180c06110106140f0420040303050d0b1c0f050c131d06060607080d091b06021b030d0e01030219273f05070504060515041a1b0706 58
    0x4442601c2c0c15030280401c07404d0717034007842444002c04010740d00c1d031030701a9150000c0303822040c000c008002079072099481e03036140c0b040700302a40203a500140c810b5100b0851210303440700d0540601300781d8018075000b0024102c0b000b900d0804604000302c0e1b01510380c100a10a40c209030f070300d246402103491090303c2100b0400f030219141840d500c800041e641154004400c029030404a160b000290074019140d000005215185030b840000b10300081242070020407160604100c2560140481810244071210480c0c120754600000380c0ca9107082090141801f200c03c0d408811b60344680c1c15584500c00150308654440f442c56400303030201841c42444084110310f81c40850705c071209071140d80704642880149210142c94980d1809a1026801808148400c030209510026841180c8488402d004201a2800dd401c0c4000c0c00103603030103a04200d004050418605000c07070329900880e021907040044940840360444015002c500c0361102d600d400020b030140c112101800403800004884854950341c05130348816 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 679775008 1250 679773758 679773779
    0x204050f04050105090a0b0a0f0f03030906030c270f03080304022b02150f0d050f0a091e1e05010f05070804120f030e0706021605060418180c06110106 66
    0x3406165040310201c8049600c0121a812881c001c89009000710a01070700d5150b09d001d04c00d400d51081c0c82d6040e01070f40c200300381034002a02401405075803409200c41c00c05813001400400c0d15001e0030800b904502c045d003000c50990500c0d400a0700301c4410f00c41000e03580b070408121581090710281d00c1018500210340d5031007102030311006034002003100150a164590200002605122014840880200040044120400020017429080ca4400981810241800c05d21620010201d8074030034600001e002c04201424400300341c203460229025589c11007403506001c0007916086007400b10f420a0180800c01ca01900329081141500200700321a80e03d107481102c80c80c0c4140d03405030042c2000d081020403903103d003086200f030503801e040101c0c08000340246a8985003142e400341005070030100d00e440181c1810300c103480c010f22085401a0606003031070020f06080940850b0104026982c10403010030305c0a807000c110f101c6400034003040b04a55074940142c21202c0d40c0354940e159500c0c00c0e07004a011241c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 679776258 1250 679775008 679775011
    0xf05010206060d060b1804050a03030b01080702100f0b03120a030507030204050d02010804051c110f0d0207051212120712090312020c010e1b03060f01121e02130204050f0405 76
    0x80902c14a410684ca0319002414150724150300a2548441c44100200c56480503002e64421401820703965000c1c10b006086a4011b4000c50402131000180034000e580003e50186d1400000320000d200040650b10400070103182040c80d4142c0202c402c9080a10002c1c406014818009d8509001070b0342c815600302c00b01e20450298542c1311401d05581405940b082d0601ca0703001e4801ca00b140c1c00e01c2c150b00c19244001070200c1034003002401001e50003400000510180300e03580110030040c4644009560003a49818050080901030414480c1c94446203108004003000034038140c42d030b03d64546001030641d0074540120f035034201040944440302840076841c4510210700c2c0c0c09d640c1e20041ca010821284020754040700003004650740ba00881843ca04060000865401d040310351000c940400f081030604140000b080542410185001048000c16060910fa00d0aa001c000c1842002e0a0740c2c42565030001900040c2d08482c0c49081014801c1c8150300820a40f6000c490140d28400d1715010803064490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 679777508 1250 679776258 679776271
    0x212070207120609081c150e09030d0c12060f0510020f0c0603060f0402030f04060b0909061303030e1f0e0a150e010204120b04020f33040b070c0f05010206 68
    0x3a82d030007800c00300e0759940c00f150300c04d44a9031801e403424840401d03900c2c004c40340309011107245540310250b07880340f0780c4400094020403446000980e0303840d1101c0c600741c80e80144010300c0051501e03040c040c20700c20b114003058265248800004c05c081912004640d19010550007014052516200d0f0500768a0000444200d03c01d03038000100500c001c0d0034188400d580015200540190040c54001000da0300d07400510303c60091140b61031000c3c40c09040440565800c0d14000340207012038170038080d10600200d48107500c4240e1003c038010405080c581203005259401000050340218000c08407100b43d0102c1e030061603000e82405000101030351000d5915548000801450680074001054000216403c04100e446100300018145503480d00203d42c000c50703080303084810b403010001704011440c0030001145003034410742d102803d01c0340c0911440b54200301161260480050141c50003c01010b8038111805040340080c0075484071032516000d100404540102d4041d500c0e0f9250100340d0754400507140f403150a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 679778758 1250 679777508 679777529
    0x106031703162007031a0a02040b0307081e0406050403020c010504140415030b0408070b010e060d0609020d17070b18060c07060605060708040e0a42090212070207 71
    0x650382d02c001e0300c405460108001810010070301c0142003000600480d401103002c0c0000c604403402c1801019038a540041004828a1041c4000d000b041060000d4a502821600f40f0003999110f00503e040c407030028491180740507100f941003104000d62a003055006502c40c2d02150056114140191502c2c0164004d4101c0043d11100014091134180c10140301d00c0f0324092009000c0d034498544461b5400c040b2015620f030840010090200808210b074140104516050502c00c1c0c100309000032a8005240c9000d0101da03101d015103815952081403035940e0320b0740b001000400c1d00c0030b481c522406401046080d00c80d14901000502d03c0d10081c042e44210314002000b601c1940e0307800018880c9908030000c15a6010b44d1035030042030035144c15004151890040700d1181d1102e1508000220b040030082c0300008540c203000382010507a000424000c54244540803031112200c0300c2001c2c1601e20102044048400f181c0400005d0050055000b80484584030b0b07100011561440c0e4141c7e510221441403500c00d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 679780008 1250 679778758 679778791
    0x150515010e0f030303100e10240314010609081009021f020f07180e030705100b06090303040308090f030703051c0e03010e0c04050108070b030a0c02031b0106031703 72
    0x940c82007801e54403a480090404480c40c0320b01010a14640080b107504d50080352030302080c0403c20034603e1080d80b012810103200d100c68280100003070701e2120181e10900342c94560f5440d0340c1041c040c1d002000e40d0520750030030525a603074555008100c0c0c0c0592144820501031a0106030303000a040c040c42c0441b0760060000d00c0300c80081583e00140000e0480c4800071409980802000c0180500040f401403c0c0d80309003112800203844040125040503100210303641c41008082d0008401044151821090400010318140d003600486c070f040c443c8656444e070501000402004000209004d0188a01d00b070381d0300b0017819003030001c1c1540e030f000c10300010b0700aa004840944a14003072440d031140340380c1340c1c1c50036140c1540d24001086c00d481c00850340c00419041000001f44600f40741c441d480c01003440c4001411100d152000c00c080702c0c80003615101c0c1e080c1e124000e00c40194005c00c00c07220061880340c1d112110012040000e4000d20950004584404c0140940e02c400c0e00031400b5a8002d010b03901141303100307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 679781258 1250 679780008 679780051
    0x40803070f020f030d02010506010e040501061e090f0b1b01111b0102042102040f0c0507030315080a0b0a15060509010f0c05030307020a0c080303010b1204030e0603040804031505 78
    0x6480c08001c003242c2c803050000708207100e41c8042c03140001c0c40c040d640000c1031505040703001410b0b10b80c1501700540260b00d8503004020080d40901c5282c503051800280c643d0403070a13114116040c10481d04401200680c807000051a1117485000f0828a0103890082c1080c011910542d82030b1241901840a035010a00c003019182c00100090710000703044200051505507908407040d40302940110b83c0700401d1404222006500b00342c061142c41c0d0115110030848030615a1001c1c2050148203005010560f0311500c00001406421668000c2c0100c41d0446540b0720703082c03030803c0d12204212450482c0e03506103999070340810100c4030380b041992065141d4500300742e020720044601f410040c40c101c08102441440c0c0000c614284025801002681e01500c40c2548600b0409541034140c3e0103003899600c02c1004100d420b0242d0280c5110290f144e4a21240c1d4445007400c4415092040e4010713440b000000a000401440380014411a0310030552a40032100440641c2e0407107104407203403200580c8581d120001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 679782508 1250 679781258 679781273
    0x1514090f220908070302010506010f080c0903070f081e03030609010603090203010906060305030c1b030c06130807080a03090501080f060f060f070b04021503090307060f02090d051f0204080307 84
    0x411408254440c8407061581140a068075070400095036500c41c00101c0038280350b828095203910441c2802c219140d00702d1100c00400701704000300030310001d800c007240313030384103660b040c00400020308a01c110301140300d896588640d261202c0c0b400c160103242181c440c00d0000d030744c08400e80b4810341000340303008038070381c60b0040c141d02604408000f268155a80d0104000041140c0b0441300510f0040c0000c540754040107076002d11f081414202c1c07264010304103440c0701c0150780004170140800019100c0c161617240c1c40c40c5060200c0100c0d0009182030203401c44c04a8003000c0007444000d0f039030080d515403503150b50316030045d070b4061820384541c0e9190003900b00061150a040415054801c0058402d80c905a01c81c0c0180c0882c2d0028001192525850800d200c00d500e00200050010303010070440901d10f040a8076051b52320321411200400c0076845000e00c144c4984d00d039050ba00000000b605460030340c8542c0c0340858540c5c0c0c1c0c0c0c40e111030180700445403814149442d48217407825201080d0046113807811a4481d5103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 679783758 1250 679782508 679782529
    0x8040501140c060f061203040e01092703021615020d030c050c070e16020f100905160905071701060f0e0a0f081507020a020a0504091109011514090f 65
    0x42620740c1c20080c070b041812041240c5403058902242101d52820f2610801080665825007802103900500041c00321094139440581140c4006000280c070748054140c3d184e80d01e20001c0d04102012242000300d0500d03401007140411445c3c080390b403240551b1075107003002c001c0070b0000c401001a07009451441440740258000440e80c105030030400d08004040100301c0c50080d4940040b000280d400084c801010743d10102e030b607400b8016001904280e000d00030025910729404010740442c5455042600c05e02c0003c0c819100d0004502900d4021151a0070361040501000c0e11000000f0711155034600c401c00400c00e03c076060398882c1d40c540c480d02e40f1700b1400f1070303045a904807015442010310030700017904121149140c0051142501804070010a084c1c8100210402046102550041a500c0c030060fa61144d080c02030362021680010070641500b4004801350b41e00700d03c9604240c000c4004100c50031112880301034070b043c1d030761148c3d10407207a0030344420b180c01610700075038100800701d89042c2545031402511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 679785008 1250 679783758 679783787
    0xa0603121206180204050a1508130f0506040614150a180605060703020c01110c0906040504150c02070f0512030f0903160b2a0d0509030f031b070e0408040501 69
    0x120702e180d21480105400100c503818034a055a0004040109040c94401c01c0020002c0c03050000c00c2440703161000d030203154020a807076280c0351050101401c10040500c00c1c040d0582000c02c94600303141a2811030000c160428420000084c500300007000442c09101000e0200d034060305903468145406003045c00741584046084401c0c0d01c58030081015201c10b4054a130b805c0c06035005243d90384a08001410104800001ea0740300e41001c1e0f41c030315a036141c03441c0701d0340c1240e03003520b00142c1503495041401d0a00300b00d40480320f88504120f40f440704a82d0000d1800195491021a840d520703944004200c036052800c01d51440b030b90014004101d824203060040e082c000800b07000c3c0c443c0e941c000465580600c45982241c00c241070041814030f0a242d444a050704182c40c003130040603c0500c40402d0303a81d00c042091850b01007000004120045071002d0202c81b52540741c0c41c084030748510501320f00684140030070188001520640c2030024000d00c070241024019500b00440925040c10030004488111000185 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 679786258 1250 679785008 679785011
    0x150f0f0108060d14030706050907120215071b15020703050a0b1806010f0e0a0203070509130b0415170c180c040f060206181f0b12030a050d050a06031212 67
    0x3c0e9804908100f404803d401c0c090f401440d500c0d003441c5007110440c0c2015200e564035501080d4184054845104449110380c0c04a0b905d1700454143c6e4100d801030310032150010000311490f41d2002c00b050780c0003003a8080d940c60300700000030240901801c03641c0e80014071001d4442d40c4151580b90114009410080d040203d0030230003016001c0341d1010700c1c9070070307020380c080540320700c1c000800c0041e5070405404542141022030150700c0c50518200040c0139004410251340702c0c00c1442c803020040d51941d448189044005070043c00143c0f5544504002915148905018078001461041c82c2c3c840100b0142c42c1c60000501769020660b03181e182c1d506607071005001021080c0c4c02c1001280b103600a130f800380c0042090740e0040c0442d240148a51044030782410b8104025072201445141d0046000786480000c2c4080350000b4412a510f800600301d07140f0080a15201d0200280100030640d0050003032407105649141032281751559844001182c196100291100c81101b520b4401c503849141c40c00e20641071035a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 679787508 1250 679786258 679786279
    0x602180f0103051326041d0906040c0312021005130201091208030c07031202160212060115050d061205060412050309030a08070e0a0609051009031e030207080a0605150f0f010806 78
    0x1070f6405e0783c81504103c0b09544400c01c4810790b480c10220090b03001180e80040c0c0303840d0070240c2d602d5410380c0c410301005011411182e5038120300c40c030810402001d440350b00414040780c10300c4d0079407402403110507500f6800140190b201280c90034240050303210056120f54401d180d41d070f030902ca040440e0007030841182003001d148400405440540007400c1181c08201600310b001c0d03c1441008020500c1c203d5911440d081100100010041981c04100c204110b0511a87c1e9402c11800200200100d800000030030341c04280c0c02d0144040081c245104500c0362014042e104600380041d1807a001c21201d819691740108004180b586c41268142d8001c0c45905024402c800043d0020b000d20007180c00035800034400329003c0100b8903250146040c24055070401401c0d103411a00d072494804084205a0420706880c10308c1e00400d4400c1105400034000c2c102541c0b0548d08030700d400030280c075040e40c1e0001a0452003503c82d000e4600b41c0000c01042200038441d4009400c070100558030204010301c40e641c8500c9000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 679788758 1250 679787508 679787573
    0x203030d0204030602030a1b12020c011409011407021b010e0409021f1b1e0c050d03090807050411030a1d12041a04080a08160602180f01030513 63
    0x180c00618030135000903840c2d140c200c0d101d20444400041c002d200d82020154040e5542c0c00c9607072094000707080f5001603500c0c42d900600c00e0241200e801000b0035500d080381000b04048041d440000782c4070700c052000c28a5100c5c10400c907070f0340791150701071100503c0651034a4119802100e05010108000d000031600c40d000341c00143d4800c000c45182c0e1450170f0a84100442241d210f1407401c8007818003103201d4190007054460a24481448000340d0080398160448414802e4107850391000303000c020000c040314502446c0041c140f0082d8403401046210f0b10740301007a240341a014000760b0741c1000b404181160740d00072102001e440110b1040c0c03010b841c401c010445018092000080e030198590800741d0302d62514010410b00b02c0c44040c0d025811105020a22a05001140c04101541c20404998031007010003805040c01c592040001c10203440050b035602c1d5000c0c0d608101500b00d008840c810700890283c001901a58002c48140c6a401d0b20b035a614400030b01340500c00c0a140a0b002c082e804e0441d03211 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 679790008 1250 679788758 679788761
    0x30f0f020c0309120304210f0b07050d060503122a01291903080f0903070938060706021207031514090714120c04050a061404120203030d 60
    0x2080307400074941001454103854244080240c483c1a51400194646803900101c0d6003009082d03c69481440407818054060001c90180380a103150400c107c00c020b420250340c0079010360312507050109201d0820301d001801f03107004140305c180b01c244a40c00c075140044e04c58101c818107080e84503e42d24002c04604000300b48009100f603c40c001c8202c2400c401b0109017109800301404140071540c407440615012035503d203c00981103040303d511501c040e89490741110f400701e890141003001ca0b01403080030000580705486410584400102c803220703841c080899143d440c0c03400c01c034011034070b40310f40040c2180e89642801c0005020442c0103110060400c40d107602c41104412058505100080c0c031581da0384a02000b100c40c6900404d40340c2188241c10003140c021030341d039000c02011300c01844400740d218642913071600c0460b600c03680e00c03124030509482c054848204540060042d2409075002c0b80c4041803c0d030080b100300e080046c9212807181018540941016102d07e0142d08030b0b018002030100d0b02030f28915 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 679791258 1250 679790008 679790017
    0x150e0a060c09090504020d0f0201020703150c11011407200a0605090c06070b1603060314071e08070e07020312010e091c1b0c0f0323070510030f0f02 65
    0x141402140365441d0a030000d012849079002403003e01c0c074241c00e0100594810b98080032150380718440c850154007500041c1e040009503030010349000141c2e182040c0060190b4003064007080076032200814049541695403ca6005240300c0c40b080c035450012400d86030041c00900c5c0d110450a003e4007040c008080d07000e041c40306665080f50650b44030710034030281540900c9220042107068943d01c0c2080f2007600d070f014903440d0290181c4070b001d06203411b404a141c441e41050b006190070a1083c0030032074003020102d40d02c80c024490607211034015160442c11280e8003006100721101d00b00140038281c1001120ad141c44c40140000d0298482080840c400c0e91a60032443d00070700080300410050701d000c4071380a0030141d07018090545000300d88000365030160845154070056120100b2818851424946212810f00ea42c00c0704804104020f0700108204485400c1c01d0f049180c50526800301902c102140e9031412240a15035000c140c1402422600d8070903440103604e90220036011554801c034a040404a038030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 679792508 1250 679791258 679791263
    0x80d030509060708060a0306021c090510050c0f070303050c09100206090f03030c0a080a0f110a030f06030201020c0904030306150503011e0b2706040f0f090b010c150e0a 74
    0x484408221100c0740c1030080b65800b80d801c2c20b24002074a05040000c554000790b000042c0059400305240304041a80b02d00b81001c410421400c000c544070a0a003aa900c44049040c10780f0306040400103080300041d03405841811007181c0600d410600207582c2900600300042c0000c602c50b2003070200c61030325507803000c800701d500740039030040c0c5014101510314074100000403010704400c1e8002c20034807412a807001e007241d83d04c0d0701a2034101e01d40d4071184c00c544007410100001013960703418200d80c010004d80340c100600d0b07007254986041100410341c04042003601d005200c060b000d40c10842c407029031418420680c0781d009109180000d21652105004102c4403182d00040000800201c018042000c0049002c00000c20405401114078500ba826840c10322500d00c1381d8845244990000b8095034003d00380600c000740c0204003a0712661902d008046094462240d2001005c00b20000104040a4404c01d07101e04010b0707450a181010903121001c2c03c110010031800c1c100d40e6103008000c448c0c02401041000307407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 679793758 1250 679792508 679792511
    0x40603020c0a02060d02092103071106160b150f090f071403013b010605090118080604030f08070507060504080d1a040b0103150e040816030c02041104030305180a080d03 74
    0x30301400511008c81400d0300012180301d01d80d240c00c070b4410b0000040d03c82c1c899228400c10034008620020603213a02a900f2199a041c0300174000c04100248208401e211340360f600360401762400b030441004040c80030045907540000c40d06003c030345c1444880c030b0960740c001202d0900c014100012010840309034003d9000c001071418103000746038513004200c00c0328002e0402c00c800d41d0b24118079600031019400117104038428400c000036011000d90285e05241241c0320308454040030306581e0604291142c8007207500320001080503181c2c2c640d5a0052507040c0c0a11400d42c0d134103040c8419562a50001d040142054903819418080030594800f1030196111015641204010803c0307600700740400d84000344240e605060900c0c2d031499071060658000070442e805502c1b0f4000b25195400d1091441c0b003950000d15603501056202824103801610f04440c86100f5101004001100c2e0f010324800d0103540001800581c0801c600460320364080c4c255902c20fa0700500720380d0040e5481e091a4030f031503901e451000c0480d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 679795008 1250 679793758 679793767
    0x606070f0609031112030117160b1305041e09020f0604030c030b0f070f1b170d05011a0901030f180f0b07091a0d0e0105010612050f01060507030810030203070e01031214040603020c0a02060d02 84
    0x950bc10341042c0040000756014440c0b181000c8100168940b4410452203882d9101207040c155507911001090018000c0c00b22076481e91070b41000b1299004a000c29909520800007103032148581114041c80345490b81d9440100e012a058100d420040c184144171044c07040b2500c9002143c01400510400c038601c880042e03403809800f08200a40308141d000140718001018402d01d10590a02102c01c46e000920f070001d1183c020114200061480c1f42e1145405201c1440030800c015094071103101980c0a850103007041d60302d801c0f080b00c056402d401520b410070848414030089841c084003910154410001c0450a070340c079807200307a08480090b4030541c0001c50301468000703042d0182c49040d800c02d0010203110410f605140014101c1e1040a40c014200940e5800203462065501307005005194010181c4000954423881c0305442e10086c0420780b01c02501eaa1080c180c0c60095a000b006d09080710003032030400b454400c1c02d400940286c60aa96140920818140180e03900401000e445060340e4005840c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 679796258 1250 679795008 679795027
    0x121f020c0c01020c01050315220203061206011a0307170703150e06090105060c0f060403051b0d021c230c01050c03010f0b030606070f0609031112030117160b 69
    0x10705201200450540d0090181c60001d030f680321044035031101d40d210301080b142a040780031808070b81181400700c3d4207010100c44c0740361600341794000b540501012108480040300074807946072580020701c591132034945601e0b0003600a9007000c002d140c3c00f03440740c01d10115841916202c0642c040c001ca40f8240040d070f441c110140642240402c04001e050028000c4005203044000315440690600136584203110108880000311010011443e03400e21450940d10b00f410280b40262003504503502000f10b100305150302c001300010004054440ca650b40d170003007580e42500c1b05c041c0e0f80e8030644a0340e2020444803031140510b580ca40110329034000641d40704140d64402c404a0710b401c541000c0c00d01c54604408200404c84820581c40840a07181c0d400541ea59a40b52180091524415448001d2900001005c4030081c05425030014240500035100d40c1d5813110a1036105807501c01c1d80c501101901c60920040c064801c03040448a503801080c001c48034000c0c1649207400a003140741e4400042c41d0307000114000c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 679797508 1250 679796258 679796263
    0x50613020108090d050f030a0e0a0303060e01140609010c0201051909030501060807080a080a1e080604151d041b0b03041505042102070e011d0903030f0402121f020c 72
    0x28828540ea01404042c07600d0800100540711b07024802486400c08408a980301480b0760064144007040c02c126a00207002d0b2501030b01400c0f4910030103261003412000041c01529110080c030b40900000c010a02d440607000055a103010b011100740c0c10020b05100d605805d20421003028903001c0e550b2658034080b483d40c40c0103820340c0c80c150040c000e0350300441030070407562400281920348207920030107442d10b0f1a0704045c07c80b1007080481c90f6006400004010b142c50a0300800c61034007403141604d050000c94480c541c071f085100703824854000d001c01c000e00c640104401517080f035074100d0710960248016003000c20003400380048030b8004880d1b122001090000300280c104000045c440040d8003400540f90030744425130400410303401c060210b5450700c2010041c51003070001802514540b002c01e0340c1ca50f10751130010790040c905c0301c0d000105020702001c2203910740004152442050400219000e598481d400c0c0b0101c41c00010142c180381c4241c07172411401d44078a103650702d40b1610f005c50060b1500302d00a501403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 679798758 1250 679797508 679797511
    0x290c010915020702010906050318070608070f0e060307050c070302040905010b190b04180b1f0909090f060e0312040f110d020904110607140102090a1d040618050613020108 75
    0x7401c0714810480e41c0c0060b40c10100c0392080b6052401c05640741da484d8200041000100c15900805004e130050101e901030700860341b1409401c841e44d8141000900e1340040c1c0f107640c19001c0c41c540c8260f0030300008050038810380040450021a0342600c010569a50206064545040088890342d4403089031756220b0525080d0a20302c003d141c0c0c01110440e182c0110100d151003140502c1c91b0803070410121140942c0c045e0008510b154000e040102c6104401404520004042c0300090000c2c2000340000f0740c56400d4026150070f90742050780455140b407240d0340c8100070308400740c2c01400390000340716142070941c840d000300e44240e001d440701e05101003135403030700110f84444444014401c1c20b05d00d04540241e21440c60300d540c01903010860744a00303e1000005202070050110040210600104000c01d144040d000761000034810742d003192072691901003a00c1c280141200244114403070700b00040220382940c1001300d801c10058007120781125035842d01820314000320f40a49136006003144400c21543d2007004507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 679800008 1250 679798758 679798793
    0x105070e061201060305130f0c08010f0c05030c1b060f04020901060f0206061912061a09040f06020a0e0a1d090f03270303070308090111040f290c0109 66
    0x15031812507a18030203410b012040c0100d404240c4e0340c00c0041c40e50909003003040141c0b50010080060031403245001004044180130f000d2007035090801c24846140c0d940507175100e0b250030382c541c1415035603441142c1c2a140c003e44040f440d50a2400008850300105002560080c7d1458003402c03960301d071074014003040d10010391080d0200404100c151314982d601140b03044d008002141c000c2804504140c031050005200c1d00552400040700c2c1c0d03920f04000c1694854403034880c5101c411648072400c0c00400000d16030441e000362805450004c080e000800503030060550b0904e80c10721120030951032012074aa86607541140c00ca5814031180001554800c1c103115501c541514003c0003489100d0600701c2e213034010100d6032008544180110209014400c590900004028085913110019410002c00000c401d507440c079115442c000c034801080304000e00715400c0c0c504002300b0b8041945401c901c00302d00d00b8040c41a030070f059894000103908801c940010900301c00d2960001ca50f0b10320720f040400740c4a1458804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 679801258 1250 679800008 679800019
    0x9070b03040c0e1f0815040303090501062408061804030c06020d0903030c020c0904110f03030c0d020105010509010b0a140f07020310051b03100e061915080105060a08012c090105070e 80
    0x4190300808101b10750141d403520300410f160f0268a060b03405021240c018013858240d181e032528648908400d860400580c607981c410894503140c0a0200d24000480c181042c040b412002401003400384000340c0010b17125401c010304c0d2001c0503000030304403035548000b180007c4d102c41e403c01140d5410004c0c00241d80c0100c8812115052070360783c0c1100c1c80c00311010340e405125081d5502000b907400780306446501001c40191603c07201c844070003e00a090900800307110b2050703c0000314005800ca01525800000c41d1580401210400040521070b00024501e481c500003c00c44140140c40922281c1581c1889a078003281c1800e140e820303500004c404505021846505001300004941d1064020307003214648440d80a10b6150140820310901103150700c0170300581c40e44000680500214031045c40c0c9440e030394401070b0590300e070800c014940c8035240d150b02c0042c5105006000001e1000002400000c8900c10700701c540010214101007035504917818681a55a0f4040009690304492a0200ca0904031074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 679802508 1250 679801258 679801273
    0xc0b0c0a11010218040b01090509011e0f06020c09130f0b1801021c0b18011e05010f05030a0b0307090c020304090e120301030b040f060e010b10020609070b03040c0e1f08 74
    0x18030b158140ca0204144170f00e440d20060301c240c0e4010b1146401409000e442908a51384800c800894055003101c50101003802400000762119568a040185e440d203a01410381c843c414030400108180c007600c507004040114640d0000a00603122142c0e80c0341c881c0251a2852414402e0f1080014560100e022541d004111004c511042400703100103440900c000080c100c1448008180b007540410007200341c2a98130b07000460304402d9480d0480780046042d100c0c0030201e484600445502501c1d184510200d181880030139240c2c41a81c1100d16500006021900030503130721300304801600d00c900e42d02405038000180c240401002405180394440f10140200f041068101944501307103c144405001c602d40c81b0086410400004040d207601c68104105000c103a11208900e8000d003007109100d03100e2071540b010240b025001003420380c1300c0c03c002c10190601c00e2404900941d1035000034007c80700d210b01e0311800700300d40c15994206801160443d041c1050310101c40076117070000b00d041c1c201d41100d078020107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 679803758 1250 679802508 679802527
    0x30c02030406141b030c0c0604050a030f02040912030606020705120a080a0c120e01260106030b06070203010507030e1e030301121104060b1c05040206030103080a0c0b0c0a110102 78
    0x41201c04403409403900101000904018040303901444014031010400300104051003c4000040d007000491841a101407006a004002084c4103a01c40d0700c0d04840c8541080000c0b802c401841441d01c0e00203480460550681c2d5650050460304000800109945000a201581d410061000034101c10350b03000000000300070303446507110444030000b040036000150805116104401e030004c80d0341d01031107580750207080c0c08003d000107070003000e01800a44d820345040e9044c1200e82035a542044000942700700c5909003401240079240c0816140c0d004041000082d006031000d1107003510844403641c00003034104c0c0d02c901c01030804520681c6c00203480800002d04900010101c21241109e50900310b0700e1a44c0c0369443c02c030001ca00c0e9450704a1b4001c0c9000e20001e65072074080b00400000e556080070b2400c0070011b040103c219902900d02075040741043c001400000c40740001000d2162060500405074170040e99021070000007211580b190f2507022400e1135140f5013101c07503500d42d8101d0000941c140f60021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 679805008 1250 679803758 679803763
    0x50a050a0b0909060a0c02250303140a09031b03240608030a2f0a140d020307150203070905030f0a03140405091b1e04170d050d05190e0f0c01030c02 65
    0xb815604816940d1a043c4506ea0f0007040800d0708406100c200108c14240322011b031a84001c1d511061b00812110004007c07035500e030404803200845152682e00ca0207083d031315040b00c00540c0d548102041000240c010011452048210100340070080740c4142840781c4d8950603066644690000c1d83c594414042691000e070006006100b1034040014241000d04502486440c7c00075a06a2041800303206449810301480200c072800c450b41e5003085404d0144440800c903aa44141130001d0001180a526448002026002140c00c101c103450032803012074032032000a050044032107443e801c5502a603100820550020301482000754502c0d1f40c1410145010041091018000e003501c0e40c1040054000981000ca0406d960440100301703818202641d1010000c0c60941c810f000e10b419403e988080c445170700c040043c103080226480d81c1d51a06140e00700400d08003504010300351844007400814140350020880c440e004c0da80c002c1d44028021008401c1c040c80c00d18810105a604243c2481550701ca103a400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 679806258 1250 679805008 679805011
    0xe03040f09150b0319110307080f0c04090b121207051002040510030e0a1e050f030301060e13020c0316152a0c020a0b03040c06030b13090510050a050a0b090906 70
    0x1c142041c0d40e90b910f640e85020f1040030b48070310094062a00c46c0020072404400301075803013518551900220380d155043d002005500480d610425071104100038080724640790817501a821024184954070a03598004030300f460f2038442c81541c4543c0202e220414000d0070020b6007041100904110310782400c020109109088448c4910203164031080301c410304a80c108042c0440e2034100404070f2010310304045c15580d0104194054506106803120245061030100450381201d85584071000040d48240501040325072008801e4440c99007803022100304501030000f407002c1c40010902c8280291580307080c0c0201c980002807844030310b107801003014019203845060280350020400b9040840d02180c8101d4213000d601a000303402001045000441240a80c09980139900ca00034245000303848420840498140d6410142c0c4101c040c1d8100070404540d0f4409580d15001d04151102002e515007200207440c020346441402a83c0c0c1c80c00c0081140d000e10a14040c0c42d0308461070300d1241002c01c0340d20f549810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 679807508 1250 679806258 679806269
    0x3030c080711120601051305090706270902041505091e0604170106080105180c1338100507020f04090b04050a0b0f06030a0f050708010e03040f0915 65
    0x203000600c2002e019006180b44041500104041c0d4004140f004654a9010a00c1040d01441419001103075400450052511840250006140051408204072a215035a0b0265205102081310442c60681e0505800b80034100c40c0001580e114545011130045c00b032004494020000c0600080440c0da88100260440c10b4160000c04414503003000025164803499002c04503c0040160042111740190094412181c3d00c0e00200320070f90350b0200d03180c1c001408030340ca8003154200889032403080c6454180c1500c0c1c1600f420b0001202d11070146004c4220b000110010306080c900c6a03041d40300400780030030410321717082a1039580000600210150040c0a2050000d2280d0103591a40000741c039194415001d03d50820140300050901d8108183c80346c84003c03058844455402c0000c414040c1641d106000c3d02018009160542860319140c0700111010350803103032030050143c0014000c90902403070132101c80420146a450703183c141c3d070b10010b240e29840103000c141410310054420703007114080412a00b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 679808758 1250 679807508 679807523
    0x3060f05010801030f1202070b160507211e06020c150601140f070609020303040e0403110a0308041101090e1f09050105010c12021f0905060717070c0501090b090a0b1003030c 76
    0x1c1403609904048d00e5070070211800c2e80100d54040c7c1d0404e01d510300750646001d10241c6110684810031000d000c0f560140200e18002607410b000006500c40c4810b2028141c90002c84440042035900d0b803007a1fa010002c5240e40d0350007600c2c3d03003400da40320038203680d0441c40034245008c1024032440c2d040d8090003480b40c049054003010405200b0304c505900500c00c503540c0101641c0c1d4032921a41458400c5c242a24154001401d910f0300e02d80c0904005242d012594054460352a04d07034880c2c1d01c0b40408240d8210a0341040031100000500c40c00c5400341d07a00034000e6413200a0041e2030030078601490300055018020040c2054010855039801015a0540d181c2150440c51001d40c0e10034141d18040c0e1170a00340e6114640b031400012200000d6103c010140d106105a034004d807a03030310701218480f030282c1c51403098801c0c900105004500500440c01e0407071043c400850f658070316844980e403400085428002d590001040d02081089540d01c10307901691040403003001c139003140c03002041e202c20036a00800c1c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 679810008 1250 679808758 679808783
    0x6010e01090e070504080723061b12093c010c0c06080a0e0a15150503030c0d1106090a03050d0605030105100e060409020f0d020a051003060f05010801030f 68
    0xe911031400d030800b50100d005201c42908040d00000e2a0b6885403081602c0d81c083c442001c201c106c452002c013039880c5035030400ca40d24141200100300e110f50294180401c0e098a884454800c041c061020100142131148066150080e040920541800690644d0003c3d8a101c458100c00c284507142c040d00c55030404803500c212601000103989944d00144058880301c04400c0c0010350301ea1212200348132ba15010010b000404006d0b00071551202c0042004140103107061907009a0350b107951204d241a050b81c4099019282e40e200801d045910a15a2040d0780d0002e01c15400d203550041014104a41240d0007801681b03000200b4580300e50402d14014100f003000100520b19031025080317840980001002040541408440c1c0b111001c15842629000034030340c0001001031070075124080c502034020340b20300c0080861004200d03a50144000403640202c0d5400d010800e038030792030f281041c181000d4800254440c18032009602032500380c3c0c0214100b0040600510000700c20300d0301d440c0c074690310000d9629607 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 679811258 1250 679810008 679810037
    0xc02130f02090306010f08120406120908130801022a190302150f06101e030b1302031008010509030a0512060a0b0f0a09050411090904060b04090609050606180601 71
    0xc0d210b40c0e80718941c1803149000110703640c3c24100303014040300c985c0411548211080b41d00d0b175056005078443c80d0007103500366010802c0418a5000340d881c85106542e03440c500ba016541e19551290250400740440c0c1d80800e80e10083c802c1940124003410b19034040800d00c40c0c0b40741c2c2c029031300d5004d086241c0601c20520801001c16008010654080c0c901800d0001075103006410210340c0301003220304070f01c00d892400c2e2450341503024061901c00d408181501e0740a030409150203901410030596000c1d004040e0083e00c2e41002e916102843c01504903812100c4203078030702580c20742510009420707a04c01d9081040782140752500103040745c68903a82c0141039a01a510a1b00185c1443c82d42d1b801101c01100c00254105510155002803074003800c3c0f5201d261200d40c80c3c50502088410320f8003040d039018030400c002ca8440c0303460f0075000d0303006100e01d0380802d851010340040340c01d8540d0310320200d58039520341158104002081c00220380c440f106940c031960410006017003d408900141c28603043c40011840d8299 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 679812508 1250 679811258 679811261
    0x11e05010f27140127050103021011030c06091608032d1902030a020114010e04140f0d0207090f09110907110613030f0f1403070e180906070c02130f 65
    0x107903001000440c3c0710b10742c2d6820780c032042e0285500a88181540380c1d402d280c00c041441c882e59058a401070130040c144145114243d454040360a40310a40c0d00c4180000c11944070100003d5100c1d0441101604040200c3c07110490740d0f04064101c03904581050068070350642040b001400547c1540c28441c10401e200da0050000d403080c500013502c3c02d46640c01c05100103400000820380403101c0d03402044003403441c44800e00c4100080c014880b0400c04072021901060001c00f9801c00301da1400c00381c0e5464001084001d14158803183c0700d10260f000032004005441540c4139400c40050317040d2041c00700b90b000e65909042d070080e4000302c2e8852042c0b82c000c19140c81c4034803910303420042c441080f1105030800d281880c50040c40c0800840015944455848610340310315240c0c3d00b0f0003426142c0781c3c50031028214603c410f0b00020032200c1084100d1004038130598030b6030200050340b018204031160a062982d02507040110051030708050090b01194040161111103004241d1806080e0001d941a0300f100c42c9070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 679813758 1250 679812508 679812521
    0x60702030d02031005102a02030a0f03301406090414070b180a1703070b060d1e0309050a06050f0c011103040c141c030c0f05011e05010f27 61
    0x540010a000d800b00540d034007d00c400c00c8101142410664030b22000d407070341c06c1e46401c0560080d016080244900c00240c2c6031701003040918480c1c20640c44800903160140d07161600045600010b81000d00c09001c2c05d203d510400141d0003000c52121003d19010300480e0328004054401080c420140d9258001004240009009050043c18056448843c4031084101490f001211441009600b100140410101c01ea07242c228038018051418010340791525080d00d40003e00d0315030031840c1c0350381c030000248251512440800000a5800c800445824000c1c0131381a60380200c1c1c0186051041404002d41010541d80081c01c50b102e42a540c0d1150320186024110f03001070401030034004020b1004102880008078103030340c42d050340d090b000020882040440e5503112200d04180481d0400300021901c01d0039050302e028081c07410000c200350b0541d141401c40300d441002000e603611800c4180903800c0c5601425004003508404c9910312820000d07102036038400f07150303100c6454030070b001d19041e80b030415005030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 679815008 1250 679813758 679813769
    0x3060714030910050a0f060815040807080c0d031406030604080d0218040207030c0b0903040b0403020d020111100608190503041e03060f090227060603060102010e0304080c030d02060702030d020310 86
    0x2c0c401820302c0041d250140c0204c00e0345986c030508250011549100000791020745800082e940384283e100c607102c3e82d01a501c40e05003139034004000c010000d07031400e04010a1300c04846550300040c0f01845542c0031015a0709c003920151290704180180070100c1c26100035210250030f0f200740143c1d40c2c100e580c0b0000d100c0c0c424002c0250420300101c1c0c0c1c4014035400202800344140156141c00240c0e9403c04013075182d101ea4040c0c0b941181d806e02c024005400c0ca48010160300e80b06052112062602c10101031414045203039258015803500d405003c2600e05000103050702c5050f1320210b031800010b95070343ea01c1c1c0c0503038007451104040d01c010201104000d034104400840e0060010044800340d0b0340707010098115280264014a1043c03d00c400b4034103496000c182612000805d07543c2915500108200c550015024904564840e02c42c01e80549091005200a0503440000e000d0b0360304100a16050404110b404000c1d504044108070304980c003c800c403400ea001c05e40c0016541c1e5550082d01d5490380068009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679816258 1250 679815008 679815011
    0x80604021b0d030501080d14090d15090510060b251202010203150609061c110c0318100c1103030403230f010e150c0d0216030e03060714030910 63
    0x1101c0e941080072a01d001c03141820341e014004c581c0c8070b40045690b410581d18800014803a0300000d803040d405003019202c80d5400924000460500e91240d1600410000c1c40404c0b10341d440c2505020000b041052000f00000c00300144451032070181d10004501400f2110780e151400701034400000100010015070b025408035040d0a00070543c1c3c2d00074000d402c201c40240d00382c5101c00303001034a0324280040d42c2a600c0004c00d00c0d850218441c14168100741411450300100d44c0b1094105501c466410240400b4681800150348800020072840030b420981c4507020301800164140007503540c0d00000e04110070b40c000900380d56240c24000840d141d846a54001740c072500f1802c0d0316041000c42d80740c8401518080718101e65440740c00c1c000281c2240d850002c03841c20783d0312000140840d03103403045200381d005034407603201c03418014444130f00010707a441815038540707121400c20300504043c0c00250f1015078400980c02014145012071000d040304071a01500b2925150110006e030034a03c08110440755620490380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 679817508 1250 679816258 679816297
    0x20150108031c050114041515030e0c0406031110050c01021b0115080d0f0c0204060b030717091218040c1d01020303161b080a0c0614090d08060402 64
    0x1815200c0d0000300207031548001842e400030324403a89014070b5040c1c950f824580701601ca111000c100c0140142100e000e406485c1038070001d4800c03189076100d010860030307480100307030601400d10b010700300300d8040e4020b1311641c58454240045075284000b00048082920a01181c141c4a03000340d45a009082104845600000d02041102000851420070b06811030080c4074001b49440e08550b103a0b01401420060b50000341c07140f282611652000c1e083c50074500309485140b880f900480e080d0707800c9810180000c03000109000e5003070760100c51424001d01030300b0300125605143c00311503107580007007040d00e80c60003000c51846025010311180e0382d4048002003041142c1004441c0c00340c205c540e003107198100b0030040e8084151325400401107074800c24130444502c1490301400c030180d81e00c0e8103401c0c0041280010f00350140c001803d26006000b00d0340c0c45c1c0c0f51410034840c0ea207400c0b000d840880e404140c00c640540c062120948d00011829181c0030107080c490074035514040428000c0c05980e01d00400b6034103411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 679818758 1250 679817508 679817519
    0x7080c03030421050c1203070315030f2a0e06130213031106090108011e050a03030210050709060c02010f180e09060c0c0a0f02030a0602030c130602010b01201501 71
    0x441d003c0301a04248540e440c0000e5103034064502c0d0140010b00e03e010b400034810007410401c00c00042d07501c0102070800244078540c00c0708500201c000c03900120341884288010030184118140780503c0040e02c0d242c0d010f070143c1880801c00d001c0d16a40302c3c4074400030504000c80c40ca681c132010250150485100119228081c0003c0303440320080030712058492031a00c1500d14014100b01003100c1942d03006844158140e440c010441030b03128426203a803441003414400108082d65100021001580690b000b0b003043d0b2143c81d140300441c4c90242c401e80a1010301d0340c0400ca174940113100c039403d007070302424140c5c2c030f510381181c041c0c0301c00442050060b10b04010500114400d0280c1a0701401510020f0440b40b00c0e584004400c88d03d40b003a50b00d40d100c035038010420b4100003402801440003052028003503d920130f0f90b690320301090360000d0b6008460701001151060709072618102c014002e01c49031000b407200c1d20561002800d012850a9280e4210349606400300c030b000c804200060300b40080c040ba4103030560390386 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 679820008 1250 679818758 679818773
    0x70e040503130603020f0913060302040207050703060c0c0c1e0b1b01050105040b0d2d110f01020619150e011202150301061d010c050f1e010e0c0607080c030304 70
    0x1c41c1000081c416008a0441d00c45c2c400d54802d0442d0012852810b040c3c0d00c10080305542c00243d0401c0261202030200050300c843c006440054880c00081401505500d004070580e0900e07004803040061106000010800041601d01100c9110802819158a5010240f54103100b078200c8061040c000514203280443d0100380190300c03c51900800c41a43c03200104416074091003619944406020503030008540085c800c9444000010050315100b8100000004020200c030030644090028078100c0d0700c3c6003410350810281c0e0109101034919458032290b80381140d060700e1113000f2440d5460481001d902c486000c402d01500507100041390380c1d80d64554019039001c28520403400f0326101a070321050001044c09507410303501551141c101d40f10000c01e524452480040041e07041100400401001c64818805030004c0141748020b0310450820742c451421064000d0726140140c0e240c03280c4a1032030000420f5020b06a07400301c9540d5911101420302240d43c1c02891074440550100009100400010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 679821258 1250 679820008 679820017
    0x304050a0f0c06031104050f0603062d0901091b1b0f051606050a09060c060906050711060c0a021e010632010813110604080d03150e01051f02070e040503 67
    0xf103aa0030b00481210020020081c0642e20419401c1206014407214520b011000b465002c0c802410140c100030002018035020304943c1804920128011035000c01410300074143c03805440c0148041c011140c038030b200d01c10a0f1061240c400c0402c403480d81e503c2d0f0040700e41c039a0718070103981140c581c001f580030b1401d0160721030100e01ca54200e541040c000009034130703001e01c06958420515444030f841e40f5242040549080c541e00204464869641c410603000400920640340659546c1e40c81c2c040e01d0060011043c606680a461009029024001c14800310760020300344c00422840342c2c00b000d03200d03400c00c900ca0140c11560062589c000c19400ca1130001100711003817080c504294502403c14422000066941560540d0017035200b50030380c009040800d070446d02400100d07038080c0c00b841c41e0942d12001070341001090810000041d40b035500210010400ca03241202802003e442072a4551504c4001400a8561080c80c103100501d80c840180e061300a0000000400e41c000045195182618082e6182da00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 679822508 1250 679821258 679821269
    0x6090106060e09040b0a021c0f05180712050c03010e0a0b0c19052101120b010504050705072a030c18060e1b19030b100e0904080304050a0f0c 62
    0x68010001a107502c680e0100051100103080c0c840c40341c0383d80d1100c42a500d401001d40e41e106800300310380c0341c072140b0b1254020654504614005116440c04d5080004e481026001d44000503d124201c402a003001c00d8443c01c4541514510310312813805e140c040c1c100040c5085081c1d165207080300369072000c00b001c42e103e486140f2070981110340381c2c0d89401c4403401d40100c0e0302c0107c415002100c0b00f58858064030090540c00b03402e0381e1511105a0281c1340c04040c803000d030060202424008001d00400200c8a110f82c0500421142844a0b160001c4000d145018409010b442c0c00c8001c0c0b00301c00d10014281c8494008440b40110100207504c0f0709101100f4403c46c41409484010344145140c180458400c4d282a141e016100043e9601c0d10280341840c502c1d40c503e00b0350750391400c2002c1062440d1013440031101150544003c21000411420481c9070703000142110140301c0018429071155031007a045541c0282d101c02e05079200d07184d504100c1c2c54801104801010311000358004c0c0700780710800c00c05108a41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 679823758 1250 679822508 679822511
    0x409140d02071203090501080403020f0106140109091107020405190e0c0906011805060f040f0f030302010c02031306081e0f04050105090708060a0207030201020c0d0908072111010917060901 83
    0x203645122a10340703036100f4900500051080501841158802c024041e0041e000e07104071541782c5d0200562a0071142c46a215500c68600303102015200e507000040c01c4010060700b13200300007141c007222004035148030300d24000344119600d40000d0070040710010041c10a01b41104200402c0390244207603540c580caa12202880b4602c621300048041d842040e00987c1d002054403210a228034000c1404000c0d086580413091000060001041115104400e1070042c0045c4040303423200c1e451820041d003194074110900c8115081000304400000341005c0300b1302220880c0c6005001a0707140c440513480382c40c554a615410103080014001c0c0140e00000040c0500c0c000c0d0002c0000e40c0350390072800da8440e040d1281c05000c0c1c00400014910400c10760203048c145000380001740ca041c01d42c00c040750034203903081c41c2070010506101c82071151060030044903000c0c3c8010f404500380c910f4050091b008490303d80302c0042c030b2a04d0304050007020303034800c40101005014114004d000501007240c02a00c0310070840362621290b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 679825008 1250 679823758 679823773
    0x91d070605030f240d020609060a020a0b1f060f0306030b04032607020c0118030204180b100b03040204020c120d020c011505181b040e0702010b010f050405040b0409140d02 75
    0x140f40310004183d003103507015550f462552001780103800322402800d982c8500d00380504001e03900d07540002c0441d024240d000c1d124440ca5481c1c21241050090440d1021007041410140c1c400c112000c5d0500740d82090034140020142c54008070058034030350700000d0100302d00b034050108040c0c1103442130080820b2024500b18609440c6092404c00c3e20441741e0200683c07018000300340381d50042c032882d0704100780000f50b860019140d4000c50305480c00600556880c0b10410420814000071150417508400e1084140903414074050124985000141010348200d500007000030203d2000c01003080b074403070780c41e165a86030050031880d840290040a440303003880d424568000b104000303100581040da90010320f042a0414140b1a000e850b040040138003a0828aa00c000f080d0720021001502c02841580090f102ca8a02038500a003500d85107240241481103249001c100950440107403820364805072000030b1a03c0039080020054804010041c00b000c98450180070000d00100c1c0700421341200d0b0302103a505 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 679826258 1250 679825008 679825021
    0x60504050601020d051e040e090a050d08070c03050c10060b0c1b1507080d0218010f0c020102071505090a03060b0f030610052e021b060c0601091d070605030f 69
    0x540001c061300c0000500c0c2009900b8607184465041c40741001440c1c60103080c5a21101070155100c001d90704030403030b584860700541c02c1000130003c0c400c0c003c0480ca030ac1c08136130526100141103910600c100805202003c5075804240204100030b0801d0b05140c001802040d80e02c0083d20441e41c031240c1540c07114001c94400008028030b100c9905012100a41483d60341580c8442444158100e210304071030200040003140c007d0f000c1400030709190b404a101e40b0159140180c009030460107030044181c1480b124554010140c2e0700130800c102101da1001d6401d6200400c2041200e0910840c4c59141e0b0100381280e002c01030000607442041d8030300007510ad0362001307030741b1100f00740d43c07844201c039240d0300315001d0303030b002c4c4240d003400611801c44a1800000030380e1035141642d01c2c940102031104e19030069101103543c48041c01c44017042120080203845c5c0c3c1d0f00c1c1207200c00d522625903205008400400f500c49009060f0507142c11400903135110201c00b40d078411902d928000f030103580143d4000041031000004900d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 679827508 1250 679826258 679826263
    0x11070f03080f09040902030a11010315050102060732040503100b0d03050c03041814100b0714210c0105071d0f0d0813060201140c04061d03070906050405060102 70
    0x50300c0d040100c85052210507003281d42142e0022405a42180c1c0f24001d541c0180c0742000b40d52109071040d00c030350030b1103071025000504560030304001d1020702140310000c00840c2d8000c07402d56000055031901000941902030b503000f601002d419465a8810035840e0030802070005005041900c1044007170750a480c40340c2c080b000968080000080d4489254050310b0000303409031000303000d6070516000b52802c1580d54406101b84121003500c00005503281d0b032014480c0c82c07102544070340c4900c450000d00701c02c5040503030900183c0550742009000d4604000c440d860400104684070141c1480000c61082c951940708610300c0c0c2d001409105155801d200c04505403e0081c400c5050100c003040701da100c1350480500304101c40c008001080c3c1c00c00440c0680b4404a08800c0043c0345006011003680d950510b020002401c48210951840c0d0401001d418400885c410f0030880703044402d1031400c00d03410340b04e040b500000040c00f150002d87c94440c5480001d500310f0942c11103800c03588200c400b040715130354035001680c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 679828758 1250 679827508 679827539
    0x5090a1a1824031e07030902040f06030804060509030a0b04050c030f1b01030507030f090503041e050619050c0f070914070f0807110a0b100f030507050f0103110a1107 73
    0x303150855014852290b101c4100155510030014407030101326204071100c504841e0001d4035542c0000e52504c11580c2541464000d2514a071070100c0108034075403650f00c403842d5a011340e0007408104540004c0d2a451a5004c010522159410008815407401d041c98081c0e903d070b1201e102c1d81d019004088240c40551004103120083c229000990302004101c0d0004400038000100030605040d40d4a2440f0b801c540c69110f5008d85c240703c5d40007141c0e03ca040c007607180e00002025414410700c040050083c012511420252160603808a6034081c00000004050b58903000d1002200101c0c403403104010305040c2c0029200c002c5601e0f00c032040024000c5112114034905044500c000880c2080108058462095a041c0d622200718901a060051105100b60429401e004141d44014084042c440c4c030001c4c400184004222000b140c1c1c0340309285658540d207400e0340f4401d1070300c607680b400031038501c030b900a0b0002621512100012542c0b04641d15015250a5005c100d503240e520816101142d500c0f554002b08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 679830008 1250 679828758 679828789
    0x1020102280e0d1221090507050109091512080403050303131205030f13021f031406060715090602090a030501150806190b1f080901150509060105090a1a18 68
    0x204200441c4d24261060700505250440c0d2890340c1a816082d50310610500c40c5151003a0081c002051818000401e1005607400c0700441520702403004041c40b50200d80e070811255921410780c1f80c60000c0c00e040c0118051944042e005010010030000d9901e0300714074002e04e0600c651031181a88070703090402ca420f0300003228090741c04400600418091180340402d880514801440300d4100c1c85d00390154461450041004404661900c2c22000c1b4015000d8105510500035600241003c0c80b94503a0a0400c400c0d400d170b00301807076942c51100d06002003501120141040503262180039981d80c42d01d1802040b50900e1450808034402000c10030900101e0b0981c0228001004a500c5044880c0c080d40180000103c069100d81044039518604201141300b000744c00c0d064481002070701d000c074034513800d4074914030b406850b141803140e003031002d6503c648900c0c0c1c1151082c6811511141001e0100e004040190400c400900c1c01070001d042c40590b100c010103042265070002102c0503045030501a40e140303048100d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 679831258 1250 679830008 679830023
    0x4020d300e0109050906030c100c15091e080d020f070303152d12141c020a03080703020d09060f06140d03030c0239011d0f01020102280e0d 61
    0x40004d07140640344e440e0406801000d0303408081030003000881e07003080004108041901545048203005038010603030300e06071101c0c4003402158519034034866111440c00f406042120801c844000f4440301106a44030008041800c544d00e00b610a0342c4030440e00301200171800641817030716810020454940742e00071281d03240d0000700c400c2c2e0410b8456422a4803580303a000c0c2d03951598800155004095100d00e200d5000311690448c082000f0003d5041000c100f10285002004c502002615940042c601243c1c542510340103001e5140e11204130081c4c403c41c070382c8090035402c1c08011814030120750310021410144010801c5910303696010030010158403068580e000d9007000081011034000e42003400c580e42c841c81036504003403600301000750007851010601000c0342103880003006408100501144c500090a25101c0c0c4c50f111402c04490003040070002d4005c00d841189030016074001d4051320081401c0c9500c110b03007640c18000030004500c3c00da00740000548008038220b440d0070310349900d40c03116801420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 679832508 1250 679831258 679831277
    0x326010f081605100507050102120105030111031902030402010912030234050f03190c0312051801030c11011a030706110d080601180b0904050c0309070e04020d300e01 73
    0x1004491300f080805041400710400103280014800c0c4020a0035041d01e06004810303504113000e1500b1a00429003880e098203040051040550412001c00e18118000b140940c1e40d50703031480122421005940070301d544040b0041e18100b01a0046800000044a403030420360105054400761042030190701100c0041d103904009000328144040e01080c0c010380503085414030708400c001c0301aa82c80039801501c00d0440740105104000c1c20600c5a41e02c4042480c11a01700314140a035030403000c240b0000641030681d505040e030710312400b0f00121001c0c010f045008102e600070b8288040b4030055040981c501c207001c3c00c1c10100300e182c0201d64009000301b200e0014104400c881800380d0300d55070060304035418000ca244024910000c3c0071900300103004103d03602e64803001040c06201c00e554000e03100e40324101e01401040501302000600204942d000d81c41c4c11400c0d1180d001283c039000f01204041e110381c00d084001480007955001990021070491580c06032801201e00413a031b0004141215400100c0100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 679833758 1250 679832508 679832519
    0xd17060d02131b021c02010203012103140a030b04050105030f0706080907051309150516140c06010603060501080a05041e02010512070e0423010b070326010f0816 71
    0x403512000035011000a8145540c80d840e20101810920f00001070740300d03481c0c1600c9100b15180400342210540000c4d070030365040030042e110b403188200c80d461600418040c5282411b1241c0d06482104003004251681e607008a240107024022800d40b05008a0514000044c03604002418281c0e01c48040c010b80007103810b102d021100950050030700c1c21940b00c2c1d0000400c036aa266101d007094080d00010007d00400d6038500391060b441c0d40c4502c052043e16200402030303c0c1052081030a44031100e071030040049d03030a0b42044960780c01440506119840b540300007150054040d88a2030030340e08c0c2600d8241055039034a03000000e175002214001e1001e0781c900c001d030f803e60a00a903900100e42c4141000e505000780e94030044d45841046031410002140c511440242c1d050511031721007201445104070450703030030b080202e003907604040c42a1000c02c00005409000d252042c000b60349001244011450480ca042d880707101d4090080c000c001410441c4840000d0325200002c40c0b0705038004031080030489901c3e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 679835008 1250 679833758 679833769
    0xc050414010e0d03180e090312090d090b1c02030108031305090411090c070501050703061707080c27150103050a06080d0f090f090207140712150f0204080d17060d02 72
    0x11121014180c080c17004a003d409248819100d07070400002541c070b94010f1074400d0807040e4060051400d0f50004060081060390044149050f04c1d003e0340c01c0340d0f6079494411480032911410300706042d030b94804000400d5080001c03009061948110800075642d646810420200d01c5099800400070845115000c2c03680c01e2060006602480c900c80460420000d41c484a0a403001220030000084d0b13079400c140900e8901540c2c4110f0100306070020610103003085182c0351b8030381261a00302d100f400341041e50040002c0005c0c1031046001491074100c140d041903860725603d004c44000c11404242400005962044184112001c80706c0c25001000900ea00789019030ba1018100720303001c10040104004154000484c07101c000902000c5001079681c40c284c20000e82100d41001507001c181c02840c01040030f29445042d0402d03040c0c101111101899100704900c000f071010328121a0741500104002448000c04100c20007105800c1d103541001c180303020070121004070200c65040c0c1c0110445004809800c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 679836258 1250 679835008 679835027
    0x60102010b041b140f120c0405040c0915051303080c0f0f150a09080a110106120305030601030b030c1311071b060215010f03060b130c050414010e0d03 66
    0x18000001d008000c003020406a4919011040c20840104540315010358000050418045008841c80c00c02c0a8080d42940350710881c07032241d043c01d0518010a2200410204840007031030020410400c0c0842d03180050011100c602c640315414003403e080b201464040d004403060620820b002c0d208140c1580c0e01d680c4d4075000f194064246d8420020110b5200030b01b08242e56040508030010210400500384100c00304500610b020911800c1520764400078200c03a082c1c56280c052030610480518035080c4443c01410a40e00a44020810500200505030404000c5005440a83e01805111948402d060780c540303d088105402044485421a20a000313030321814140c1c14010f4a94540040ea4447e880091406031601c4443c22249504101d1181c0402106401d10264641102c80d507140ca103a61040c1080d511000e007a45455005900040d5a00031018151825140d01041500d015045c003e01507041801017410300c8480c0c030030004d035a60103124500c5480790010000d00d5089225502212700308034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 679837508 1250 679836258 679836271
    0xa0b0c0c0a03211e0f02070c0521100203060406050f0307150507050102300702190807140a020112090506150d1203051023120f030d0e0606010206010e0a05 68
    0x42d0b20001203125050007a81907007000c40d0013048113841400c0200e4102c0329588440e14006204004007000910181c5c23811040390411500b444414503a2010001003e8079100c3c01c03483d5005001c440c42d0304002c250b01441c0500d07010755003002120349503420311060307400f062410703a0f041d400300c030040119240c2c0c0c0800700284031003860b0031800e100c0595a40390a90308072060744004a030f08030b41320300351032203c00e10380001d041883c26910045003003088029403100d0110840c05200480c00e407481e001d024081c1d08a0340c14642c48100750a0560341640340c181c40f401c0385041203000a10000d0f24041e0030450340205c001349a0440c001d410151a86110b41c0d040a5041151030f8011030880c0c041c00204008948008141c812a10081985c0c03a0100c6c8616003203c0d2600320048564240202499814044000503242c900603910307414003405031810ba03450a40e5000844100c0d100004080d041d2503030325042507611903001022641161294001aa01e48000340a03945c0345104141c00261024a1508480d070070a5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 679838758 1250 679837508 679837547
    0x3120804110d03121d0102071103010c050708070b060d020607061d070f0b07021206090d1e05040e06012307021302090121060305060f01050f0109030b06010507020f0d050a0b0c0c0a03 80
    0x70717000800600760381020500383c0c1c1c045a485000c000c00d080030301030794080107250325201c0e00d419210303920720715117004501c40901000849000900191201e07101400d016030020101920342c6450b25016029200d800c08402a10090040c251428200040c0500580301440002c4102d2410700d6007484003600046403e03644042d4401c0f056605020505c2111f00554202c000b40c0b5550b040c10001500e400e030f0031646404025103407901940a2a070190554050707a00b14890798501c0c0c1c40d2800100c59250001c200da03c40b00e0400d01405a08900e03900050200c41d10070760307003c11421400315514049014030320281d80414007021801d074900070b030070102c0c80c0044480c0c0d60001d1403e44039100e5070324080d001c1380d200e005154400c005000300e00c0c1084c1d241800c00da003440c0010806041d50340c2c10340a0100500705034103000c4c01044103011540c0f8680c1290301c404014100042c0c42010741480c0390360b412101000c1e81c0c0e0020303600c045442c20f59001d04a03103c03130a11100810840080390740480e000b0107094424020b15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 679840008 1250 679838758 679838801
    0x1d03041401120c110d1115062701090f05160c020316140f0904030221090411250c0b030408040b0a18090606080103140703120804110d0312 61
    0x1218440c140a803150341d44c032500702007103003800a0700d00030520728501e050090340d5180c0c0b560719000040d81e0402c0e0b15502c2150340651112004101000200c03000c000700c4480100c6203004040340c01e40200d0403030b4280c0764140b0280030704407111021a03009840075060b1404d00c550004003e4012851182d109102404503010301e4a001c1c14000c0c40b50303458011000c01d90900f520b039141445d00144a0b585868202e03410341c25810725560207950b4405c0c428849074089516100c0359140b815170030540380c0401d006001840524164100410b09034021030240b288610111034680e443c50100c0412a6001d07132082c06aa600d908110307035004d15810085c02160038110411002c0348011f000d00242003080603588800c0782c801c0070070300320026000705a000400518904a810003400740e00000c45811640c0056070440c10011414a050138458280c0018006064058003941c2d0598404c49044c4614051400c161050412000700700c01c2100700c00000d00000c210341c0f900300300420194061300d100041024540e008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 679841258 1250 679840008 679840037
    0x1a1320160506090d0f0504230301060f0f17060108031b07090c0e010305250c260c0601080304120b070201090c060c060b030309010507121202030412031d03041401 71
    0x1890002c4401800d02e401042c50701000325040002817400007414206070703041c607041108800c0c61400400c0411466519141c1c0c0211948080d4410805800d034408800c1849860b481c1a440013a80e521803001f52000313040300d1038810310b070100b1014165081c0b0f40286180c120001c2e80c04201c00c0d00010148420b0081c00b400264039283d501ca12482800c86845043c41c41d003283d0b0000d412904000c2c42e2141140d400c8140a1a620180c0101c0d81c001d00241480488200b00341042039805003018a0b50200f04915240149810301c204003a044c40c8048208880650f03803101e01d020748a0156229000351200003003004c100103040c60a989030300030201d2000259501483e1103008034400e59500c0840403e890600c010140203417806142035400301940210f240c09000700009201e84980300008e0701107800b6044181000344201c40b148170f2510206002d5440781014242601109448491400032a05c1c062400d10410b94500003292643c0805028505040c98083c03c03002074204020818100080d20303200004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 679842508 1250 679841258 679841263
    0xc0c030307080412020606010e0d05160801020316030605060d09060e07170d0c08070f1a0a1e1404170c060c21040b0106140d1a13201605 60
    0x2103181950340b05031440c1014100807100c060068910402c40d0460820003005981010802c10010b6041c3d458255094081c1020f5080c03141c101d4485179080c41002002130526030540103107000e0304060400040c40c1400c010194202c03110740c41455004403090241e500b220100d5485502000e028240104450f1084001182405510f40140036124840020814511400c0000c42c00c5c03480c80742080340d447c0c0c1d2981c40d0035845004840c0001c01508418400c0d400700108010801d80c42c140d030340c01403421400d05642040181c480c00486200a1240002d81805400280102501c2034a40800045540c442c3c0d2201312100c0401c240507202030f1403c20070390251490404c0380f18031502c0f00c4105144c0710302d5080e03610361113418200650310715292001705020125915210040c1100d4a40c200f00c40182500e030110b41d22030141801c2e2800440c0b80c401e80583c80c082010440103a00307011a41c01e00034042c035030580d4080304c140d00349186d04164042d43c1070040d0341e0000020043e00000d07416186040b00142d81d41d91 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 679843758 1250 679842508 679842511
    0x10e0a0b0712090512030403020607051908070218150f150f090f040203220c0302060714120408120304020f120d0e091522020a1110090f0201080c0c0303 67
    0x124410801800c042d041e590121510018003000c42c0c0d0141c00091007001c1980c1c1c0e000f03e02019208110001d41c5a04104003086024400200b0b004c140c1035120381e034102000b85d0340000340300303a005410200c0d070490001c0644140e984165030000390700d51582441d00c1841018101120071700e420004044440768100c84071030103031409201c1c002c10a176403601071100384040c00500d402d0886c09240181b0030b11055000b035108000c0360b5541d24076210020910f604042c000c25107a680087e4000c1e400060060a02003000341d002c40036491f030700c1280c03401d50760f401e14200f1522507032040741e2080c0c10082403003240340081c100540c2c006000a140e00c410590100005040850607058031050380c0c00840c440f52001d800030440c001d502c604a0740c0e070801c0c0c5403928210b8a05d076000540144070350614401e0701d04e980c1101d001e1108089031280110b4070341001c80c038040e204401410681e00a480350101f031803800348290143c660030315402090749922048981c01922122000303040d50420f81c4c801d115550041004001a5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 679845008 1250 679843758 679843763
    0x6120609020309100b0d020609060c192108010f17070e01171002070c09051315060504140c220801092609100807020a02031501060f1805010e0a0b07 65
    0x1040c1c1c14801c0c0d1320a1003141e0382448654005c8418010a00c003685d02d0000755050050140d0b41c16a9030f9002041490030011801218a101080c00303c0c403006100c4007404900ca01c102c076460030010071000650541e03c21f4000d01c6180e14088000c0424050b01480140d401007417000d0004542000351615032a58070880c00360408081390002215400c80d01d0410049103100f03441c003880c1189401540d481d51101c000340c0d03002b580c4c20140c40e24085a03110320f18440c0f140c06103401c11100d802c40c54506030200044c1000344510b601c51804c0810191419404050041c020341005c402103140882c441c4400e810900014126929010b0710100000e10f0b0380d080c06161400c034402d408403804211140416002c0107841080810506801c0c8085000340d118080e010320040342d1801c004030b484d503030b0f0b445c200e181940003a40203406000300003213515010a0241071506884098a44001c0f03807084000886131a00301c813508a8441e00043e41c1003001c0c0d40030301d100c4580410040c2c4510f00c90340c1c0f40c200b58401a40207541c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 679846258 1250 679845008 679845013
    0x1504020d0204030c0305101b0f0e0a091d06010801060509180106081e1c02030901080408090d050c18040807030c0f0b0f060a050301020c0c061b2b020c0a06120609020309 74
    0x4101541801d2250503000c00c8e41c0b04404170b8840c902d200041a28040160120901900c1c1d01c0031180c0d43c2c2c68880060003008840d009100d919900740700015540c12581c0900d42c1d80c45080700210700280180101000d80b080904040d805036180a540e80041e010000c980c0400e55a55034041550f040a010050380e10900c2840e2807100f1441440040c0b500440202c2d12040701a50040c0c11511523002c0115000060309281000e40f5803210308120f0501d03c10802d035654843c201c0c207408000c0180120b40d001882c80d046605813a103000d40f4a14000104085a008081d03c00030403111000078010016540410300800c0810200da910b0f40c2c072001e03c90720035a0305000f044444c004110403403030a07901c0340011b004203400035410080300c06c2d034090351071200c500c182e4031510700858030b40180a260307410a0f41b42c031550750888514002e03466011407404894000301200040500803924690700001d5850300661000e080740d8030061520404440851030302e4205484151203900c00101034500d4000f450003003044002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 679847508 1250 679846258 679846273
    0x60a180b0c150708060108010302100909020a0906170621010f02070c05120a0b010605090112020f090a090204030b0106050f0910030b01020f010e030f030619080102070303050a02031504020d0204030c0305 89
    0x754140c1d000e0b00030b014804000707800040089603648040c0150440b1b90550742c800300001409070544000f00546c210401c1d1034030100750501c00f1035200403400110359050f29440c5143c0d10300850520b649030100d680d1900414800c01410000c08007410340c03c0c104d64079500014071045040417460503640300040a8880c003070002d4060005242c0825080503034200c0f1001071580c5074159079640400f80c01442550b061020102310b440c016409100b6500252010794011950707814044070307a00e8940c000000190045110000105904646108903004d40b500030889107032580c41c2c41c80c11589a403082072603c021020a00003ca4541c23106001d02d0764040480c0c8000c18101c6010f000286040010140402c40b68185440e00003120008001c441d26103460001e40c6649039160300221310722074205180d488a1044140c0001880e00040d4040e084241c82a03800f8002625907041c40003e90000740e0780301900c000352541d440b255180030b174000e0105082941015043c075540351115403900c000c5a0040d60b03203401061 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 679848758 1250 679847508 679847533
    0x10120903050d0e151f1d0901060602030705030d1104030b0a0b130b1e181608062215120804080f0627120d0c02070b09060a180b0c 57
    0xa80f0841a40c9038000f0703d0f0100000500e400440070250841810f2a4400c44008105109010341c40180c0701c0c0d42d15026241e0008031800142c01c004548a50182d440e0403070100d1158804011100050b820100460800500990400080c160840d40040340355080000000061803807644610035000480300003030703142d580400d22031032801e69403651140d246018840e604607900e4000f0090040400f955080c490007190b0003084540c0c01d588881d07003007412030100300066080300c400504486201035a400c4615141e04091144548540b01d80481506903540741495198040d03001090000108041c591240e5580e0880920107090800c2a030700c9840c0058244650b8104004680d5600c0107600281081e00d0054000c41d0050000e421078154480813201c09000000304000400b0082e80b0001038546d185241200b100040c000129104098003820f54001070288628007502c4c080309026080364070b01588100300b204c0700280e000e40d005401c0d80300c1c0c4010905209150280094400c40c0008240f00316408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 679850008 1250 679848758 679848761
    0xe070321051b030910231303020d051b060a090b0306030717030702010e0a0f210b1e06041104121a01031217161b24060e01080c10120903050d 62
    0x100c210b0148551b84001071549441c000140400e0106041900c0d10f0b2600c94008240e8500c669001940c0103600d0f41c2d001060048c04525000308119009003c20040c1888003840858042c8084810104240400400050069000650388218000d0a85481c5600c0d890700070411b003080d150554a030783c40415240119600900f0303e011811003101c0c1c60234000d140180c0400156030074096955002c0364a1007114003201c5901c600998582c0c0300d00715007481d24000003158072303100c08002d9002c4a4810b0501041583c1083d10802c0d0003e0b00001c040c2d0301c2c0c542449c140f404035459160044405c4243c0c02d40c101802c0141080040c00385d032140300350b078011240710000248015a000e201e108808420028041480e0415000c00308100907800e250071300c0c8614110220b4450170041c0d02a043c800c0f03400030505c10005411200d4100c0c50303510410000591209900038800383c0074002c2d00c1741603000c546021510b243c503080811840502e071502407891001031005806885038031400303c0109801044500e0048142d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 679851258 1250 679850008 679850029
    0xb1315150905012402070b030a0b040c0e030604170d060b0a111603030c030e030a060506030d300905030a0c02180c030403030b030f1f0e070321051b0309 67
    0x401001c2c8010750411001040407088540704616180d00100c54802e039a009001c500000c12988181c240c480c900b01c80c00c140070f40a040840c5201d5071521440340f145500928001748840000740c020701c6071340d48603920421828403645824129000034000a44125098012180038103441802d035074030b4a84804028000c903170131900d0030005811159502d68507a943c414003004030f82e054a440c4104100d0313030034103481403e4070316011509030050f80d5142c2d040c01090b8000e140034810a40840395001c80322001242c0c015160040c00c1801030b0071103010404240301c2680348880010300c020008080005684a52031540300401080204a80c1003191080d45058450f0008003150403003c1e80e194600072055140c5407000410040038580d445050111503101040b200b45504420300407203082c504101d1840b2408000c00910200482c2065007500c6010380100c1c0c0001200e40c0326041020068040b01d490114a80d00d00c01342d003c03c1810701000030480c030130407882c03403203c01d00704003070360352013402d42c0c248a02c8000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 679852508 1250 679851258 679851269
    0xf09050c150309100b220c020c060903030d0f020f0c0d1707170709030602030907090605060c0703080a0c0b070807080a11091014030c0909150d0b131515 67
    0x2040c003c20101903400308005044500481c00042c56070703250000a01380d03136000b052880090b00a44849030442541c1d03440b500802801c0e408a0f40303d0b00401040041c40d1242543d01c54040c2c1080c850150248404d400202120381000d10250401c1c501c042900210b8001c020607030880da10241ca445411360f00a100407441c18480c185009940c034081c1d1014050300103c00324034801107400e1000500d40ca10920383d039005144d00010179503403420000c000b507070340b48818010000340529214001501d898508111030740138034001c0240c0f01c0079156440700300003034000c80320101c1445031280304003000a0b4401001840b400c1c1c184c0740c0381d00e03d040074180100300f000000c0442d01035500d0305a070710f85282c200200ba102e10403001c0300c0024002d110600d0880c5e1030f80105e1080038240d200407007840a0441c080010300b50038402592503501c991396188880d0002c8602440c8281c010b94011032100101725010724280d800070303d001c50038400c00742c15903500d80c001c242e41aa516407165690610512113505600380c0b130003400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 679853758 1250 679852508 679852549
    0x130e0a03080109050915060f0a060504080d020106080d0c150e01020a080c070b0c16080c0102091804110603100512060a230a24030303022101030807020d02040f09050c 73
    0x19159105680d100551250fa0103606c15410002d280795030380459865107a10007809440229941d00000f424541140c0a04021800b0b64542d400445205105607022200c0c0a00180641e40c0f41800030740c1c0c40380d400807081d10501900c500c00309010b41f4a004018520000000040c1c0d0b07031804440040c40484090031070003d03c4030070845080401c140c0c001d25904243d141c440d01d0394405028802c40061206010002c01004002c42c10391071030101076002e00910241070f44e600003400400400c900d58520120360082805030356101c0841070f41850000380d40d014129528950f080c1e0f84030b60024000100100c1c074400b05d40d209204119120b00c69024080640700c800d8071444420309146036030003070340400a240710809070340d07804104084412041d80802115660b401c4031030b21b030303202d0400a0103076111201511010841c0030204031400c125120841c101c9410a456074144030720355081003ca02079594080ea4010340310210944560601d20811500e54400c0c40205031081030002030040482d8032142000c1c429 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 679855008 1250 679853758 679853761
    0x30a08070b06010503040b150f1c0c171e0102131401030b0405060d0305030606120c03070207080c0a14030f0601170c06070b0c03040501090b0a050414010b011409130e0a0308010905 79
    0x2920b03060207980004c50000c8041c00c41a1076000720300c0d0070389c1000440703901504200480a015248402035220301d801484200b6802d9205c4121119598404080010075402641c030811001d51008001ca882681e0300300251800458003014040105107070012200076031400f60040c00c540c0c06101d24000c0c10000c2d5010b001c10f1400708002440407075540400f5060040000000d1110395030081100d2483d001400c4240c602d040413885403003150000c49054000d44034608000c201d4543c0016040520700004282c403054a050890103c442c62488001b1a01403107814003d90102405010960180c5100c00d0000c21211103403c4d0f281c42c01482e2131116010300c80c00c01130440401d200c42c2c1540e521a0070401d40907900d88035440d04600600010038050100c150740400d02c0401003140d00220b01440c00b0300f07001030080c415544d2082c22200b800c582d090109076641620854900c090300030303015400004100c10111440d0f00719403c00d80d0051200d00d14942c001c01c10075400c15800c03640c0d443c05040303540701c104000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 679856115 1107 679855008 679855013
    0x60e01030b160e0a0506210c1e0306152119050f15010807050d11070311032706040302180a11090108010311010e030a08070b0601050304 60
    0x207566a041d07000803002e031203141003400401004000a102e1840c3c07000308030f1035a201c400c80a2043e05903030700509413070141d0114584240200003020359992010000041c01c082940e0b451354054a0038424440c00d600e50704401b0500180e20801140e0750044801d0710060000c2c80255000707148403d01c08c00a100d02e0358081807400110743c103c10300007a100c80440a4408a044502483da0320800e04940f05c150f00c604400c0c0d4010342c09081c00c6250000095240080d075074901c129881380b40c00041e0031410190311200c44002100044055400c0010305d84500c4c44808500d107410001a04d5030a1003c0203a65001c03c40d00155802031102055410020002e43d0a8a00b20b4804c1d8000e450032140461100b04401202d606410594508020382c1c2182d641c0071010050524a50420034090304c04c0c015620200030720303181903000e03c041c19160701c01442c000c00602d07070043c840e03410040240b052000 = true := by decide +kernel

theorem cover : BRFrame.Cov 679676258 679856115 := by
  have h0 := BRFrame.cov_init 679676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 679676258 ≤ n) (h2 : n < 679856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
