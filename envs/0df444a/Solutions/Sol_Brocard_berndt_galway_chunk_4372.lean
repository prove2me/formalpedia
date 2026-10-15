-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4372
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:24:26.515736+00:00
-- url     : https://prove2.me/submissions/37754330-dc4a-4c3b-b5e6-24905a32f5f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 786151079 ≤ n < 786330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 786152329 1250 786151079 786151123
    0x40617120d020c03120121030c08071112030c060a0b0120010204050402070818031c030c05040e07030b03010e01150e1f06211b180e01120204140108 65
    0xd918641c0442c2e00300541401540d40300c00410721172030b030f5480081c0a03000c41150b00d903800608803040104000d41d6a074060b83c40480740c2c0010749400d410303940050420f840001070f41e404c45016807102801d01d04494904001556903524100203103041040140c40142107a06240e1502e19a070380c03080c0c00c06103401610141c164080000070340b6038021b110301c0d4042500940041a11805d100e0110003802e52402880d41051041904074105501d4154422220844051660b03802c035405119501558541805040c1140b8094595081d000105422200c820000c1d8940c0c5d001d01e41030500f0f0140344486005c40000b8040300041e0122007481d2005401013a640c00000d00000e890389845050501d038040105002c43c103400d40b00c1c0b4000742841648840500d510b40304519020701480c8a20442d40c143d50002c85a50b0500803180d030172510040079900e15000303000e50340c4001c0741440116108500030b00c03001c40501d40402003441400b0a80782071a6407400e5a441507070041010381004583c4214104400d4120380b09 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 786153579 1250 786152329 786152347
    0x60c08030a0e0f1b03060c070f1a0f220302030a030c051b0f06100b0909070e030d03150603091502030709030501050403030603140c0312130302180604061712 69
    0x402c460307081c4104a10405200400c0d0f41d074046203001051032080c4490800e0340411007810b42d203c101b600c4d002c500a00400a490103c0d001100348401e0920507110206080f00305803800820f203e040d103c800740800e0300002e000494041e120000304000c11242d41940c07420407038501030f403640a07031205041030584420303800c03c080d889801140c83c08841e0b12105012408680303280d81d601c41000355202c505104100201da4041480506602140c03902c80c0e5184c6010840d9051041c10036019001e001030180003402d50784181d60600c441e9440c1005903070001500354181c05101c000108aa100d102498946000000030940e040803c0d8034050020302c2c0581c1c0d94403895400c494814803070b80080d040c0c0d443c2c10140000c059250f00014100c0c0d0041c11701e030080c84070880b107440d1034400d960880da1f41540100340039945088180c0c060708030410a028000240c0d0303960b4010907003440075460171701100801c117420403500349031a01c10380014048007500a5201ea4070f004400303039240885ca804040300700380412511a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 786154829 1250 786153579 786153581
    0x20c04150b0d1a0607080409020d020f16031d18130f08030a06210b060a05040c03020903010c0c030f050f1b0a02150a050f0306130203180610060c08030a 67
    0x204000200d641e80c0340000c40540c0028450110103c01d003002d00c1000d00c04901c0c102082d1030307109800c00b01a601d8246032500442c001c2d0f200001c00d2016540a106003008440c4401c041d02c1d85018088540024994600e0001d118403240340341c0d5460030800c05501d8203291246c15816860801952105841351034003401c00300c0c0107080e5000240b01c04040c446010820404401a6002d031a040005000050320f6004032402104550f131083c941c20090302c5000d020900e404041a00044040c013152080f0361a60003060076512030400385808a0340005140100741404d01c950080e1f56400e10309101400c2041c0d400500a441040d540c0d4100400402c0103070a403585182101c1c0da03514010302c0090001000240701c0c0e03e5503110142a03101d0803d484003408000d40c140f0450720400fa0030366455250180601000409030800707481590011034030503170b2000842d001c1c8020350140114007032414800d0401c820030761901c10020040328006201d43c90070428242c02400e00014640d218100e15100d03510800010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 786156079 1250 786154829 786154871
    0xd0c0f090b03180d021006060903080f09010e0316030c170c130f320411040c020a021804021509090411042903070b03060a030f02030f1b10030903020c04 67
    0x200b684d0041203074009849070000350007100b02d040d006051180c80d40d41c42042d0f80e07141032844050111700301004070284103040c1c40020f01000005041448468003d6408289001500c4030004003446081c14240188622030100f98010003030307241014601c5c80000f1341c150f01c840505140500800b1013200881144016400c540705010040030200494245507082c2d801c0603d04150518018034a0b881c0e022801c090352080324400c9802c80c0b08110040c29000034000248000506642107001d003103401401a40e0302c0092a40c62400c460800c0483d00701401040086c2d404076034600300f99482040000751a450304000a40d102d0b40041003240c1e12800500414050082c6290036503400c2c2900c100750001091210b2901c00040c026400c0b2038681c0e0300d98910074100e2105442c03080d4807004c2082c0400021b07801c110700010651003c2c1c181c42840000f1400c0614040032000280f00c078100c1c459010b1802c6c108034070420f68403100e1b4503050143c408503440c065110080b582c880c9000300c2d1910792480d0880307000d031044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 786157329 1250 786156079 786156121
    0x5010c05072106110a0c030f0c0b180c010c0308010302040902010507050a05011a0604031a180d0f021005060117091c020c030601050d02150a20030d0c0f090b03 70
    0x104000c0002000402d5905541d50480e00c01d860040450400c088500a843d0008030a0710748009841944d18262010030701c1c003201008010b00e020800780041e0707142c4000c90003000942e082c0d144c0c6c0070418104500304004c4035212410080d0a01c01840403e61000680d4116074058400060304411400100c45520400c0c0c8068124420000c1e26401c2000540c400415506c0840d040405e0465150402c48588201d1201070a02e20101500340b20100405880f0307034120005459030407004990905150412107d0110280460029010380b5074660301440486c080300720340da0301008a481c00b080064815407840c001101c0000c1c191000412050040241c00c10322103045840200c84050003600954400c00c40446900a0103070400018940c100705850810780c9500038140c12082000788403403080c50b0400300300741080100900a029030048031003031014052691038003960f552001022075000342d6880c618031f10308200c41c08010890250740012560196980101d445540351968614072204001180c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 786158579 1250 786157329 786157349
    0x91e011707050a23040e0a0602300103031b20040e0723031b01051c14010509090706090501030b13020f070b011203020303060409030215010b0a111605010c0507 70
    0x4041100f6454034940400904510003641c0168104c0d0705000907209848403c1e0003642c44007010f0b50005d4541e401030800c0407110582e0303004440300000b801001d103070182c000e2225424180c0050091581c0810500034040010442c0f000403803040e6111014040c004051568aa2141c4840e0426590300e03048804140e00d940111000700743c41d040a4900c50140150501c85017203200c1800149080c042800c03018141c3c0e403402440f208058000545880d40090030403145007400d274a90b0060f0210510038040303140c2d01400c1000c001d6040000788001044050420314150340101e0341040f06981c00b85500090701d40030b1a0214500c0a0311000c128441e400d046200da00314008281415150080405044c40501551400b03020781d984003c076046010028802030f0043c0c20030400540681040d810903d1400c1c840e00c102e6580c50516251400c40580c00c0e00101c814220015040a00d598080190852088078030702408500d156082e4440007414944600303414014401d4071082807200c00c0c0480c0001b4a0341c082 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 786159829 1250 786158579 786158599
    0xa1a040906061e030203120f1611091509160c05010e012322020d0803070f0f0e06041701020f071115090904142505091e01170705 57
    0x1e0008090070a41c0280d40c00d8000d1801024545940d4280b6801241d40284c041c004242e044040700007540d01205d00000210010001b0320003140607500f100c00118001c4104181e06202042040420800079140c20120f0024038440046561404450ba030400c2400c102081014a00c09050700d02c25440b070b5019009500e042100c1503460700c1900200d100007410000705100d032621000010036000700796034011806590b0840030014070f00c0b80c10010104d50000b425080140c01503a1780300703450b42c421075402000416440c94102e200d500300d11285018005030074010300ba054414085039142c0118480c0c003007400702e01c600c00e03060080294100e82407030075101d10035070765030708203060086070850483c1666000b1204601181118004003003614841c460041c20090507483e02d4407464240e001c0804c540c10720340640f110f80510b00c50421135481c108280300c045a151103140c201044120709000780b0035098001c100070307101814502044c030b45041d207040194130781d01402d488480c64a413041c00d401480c3c01c019610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 786161079 1250 786159829 786159833
    0x1d0106030f051606140903010b0607030e0a0b04140402090406080a12080a050c030103030c020a080607090905220201050a173607050d1106040e07090803030f0a1a0409 73
    0x10030005110307030040d0100c0d016410303e40448060b0300d030a0b200351000030384202840309010510380001c0520b0b0000030004541c01840300002001603101075801c901003803070261040c00c1400c104c0d00410041100002081c00c2c00d140403280024120a241c03400c0c890766000400f800182e40d0380d40048083c0440c1012070ba011196450a882d4051102c11640b01285489000032606640c03800313550700c681c043d40c44050840e407039940d05540003000010101d80c006003030701000c100d0100c10090305102d501150307100319080d07207010300d00f00c01c0710fa0181401c200340c050014030f030b42641581c50304c4c42c3c4026030a00c0d12690701e800c101d4003200e00c0d00c0c1840c1200c1d030229400d424042c0e14001d403a500810011502c0a50b0210502c5c1402078040d020320751000369086c1c004a500700128a070a02d600e13171081c3d00a50b08444041200c1e03000907210751064118000c0ca80d001c1050048560b4410002000313082258025413640c1040e16a078488070100400c1503056640340c0c204e03400f1180310314080340381e4030310050028451000c41d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 786162329 1250 786161079 786161093
    0x90b0d0210030f0908040f08060a230a24050a0b0304021503060a030f120f02010c020a060203070e090903040609050121020a0c240e030f0d0e0f0f0c0102070e010b0a031d010603 77
    0x1c0c03081491601c03502c40420ac4488080c8510340c441501884d00400c501040d08940f01081001444c0340062540c9000e101d000d62038a4815445241e03d18516414190608080044858290300415020f51082c400c010058542034202d002020020540a45a036a000c00050061085030001020301000000c10020400444420850040c0030348030140e06540c101022401c8900c0005003200691210390010080350b03080e8003c51b001281440d003030801d00002c1c000b19880ca00107540014556000080410605601160000c0504000d107000e02d00e4540500c0200700242183c05038100d01c2382c0c0020581a40c3d07015441500001d580b08803c0700085c0c6c0ca1350041000d00039044055002c032130819a00201200c1d01204403113801d01d5400c0f8440c1444180c0000000034045444042c000e8803407030f80719004c580030420100a40020f49002044002c0d03241c400203003882c1e002c1c0d00152400700c8800c01800469010f0081d148100c0346032500085201007807800c2c0301034101a980414032075180460100a01c50a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 786163579 1250 786162329 786162359
    0x1b0201050604060506180f0604050406081c03050c0a03020d090b011202030706261803040e01030309060f0903032708031b120307110309100801090b0d0210030f090804 73
    0x400c4904003c415601c030180300d001d1054040501110700000040d1450385868a1181000c28010b450b1604051f11400030800f120341d02d400c9442c665110b41c244030030404800031440501d0320180b0703040c042418508200b840e980500c1e0031032810f0540103ea400c05601c80e9a00c0328031100c1c0c00400d00201965030303400882071801c0d414010390090154000c0414020f0195456134450849030407003421500380307070180001012003c0d140b00e441ca442c00241101074030301000a0000b502c00c181e40340310954910324010309456901c0d0301c10428415001104007010380c1005882080f40e0f0581000360700c8004a003c1c82070014042035102c24864140e04000c2520080000038003404807203040e01d800c465080480032603440c520156580b000300303410000264031034400d481c1c0310344002254044900341448140054407502c02203071031500007401c4c50700400441d80e080c00341e116190000d0b41c2a0b46011140c0c1c0100b1b440c24800c0b00340c5014581c0f95294096a005540d00514040340c0015405413603617143c010344644040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 786164829 1250 786163579 786163591
    0xe0702010b03210903071206020c1005010317210103051e0c0918030d050708070905010c030f0305100918050618061b0f071b0f0305031c1b020105 64
    0x21916090a001d41000614840450400e4541504a42184000040c00e6224480c40744d054080c2000004c0c4440f00411040141e40c0b0650000d030302c1c2e172941403429103840300b00101e4090480c1407000400c089160b0300d0b081e6010030000210f007a41c0d21080c0404548841000980b00c41203100200000280031000c80e1941e22111480501d200c2c040d0b410194960b11707803140388110b6000b11980c0c04114690001d0000c1e140c10203004003964200301520030040c0444070b04640c16404113000e42d00b00302d061644030f0501c03000741c4001d0070b1610f540c6160713440042c0300804041c030040615030b540004c160750299110900f8001c0c1002c003030501030000000d41c054104000c1e01400c58040c441d4001061103d2540b00d83c5412581004009043d150349220303070707403080450b5190001985e0b00f04005517203448408200808020b4015105041d04202076003000040c5141540b19003a80303100501c003480064400300445032414a902e6580301d04041843ca954024400440c01d00d010720704140c0480003864043d0800c0e4420301c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 786166079 1250 786164829 786164831
    0x601050702031e060c130b1803240c030f15010207171006060206090a06090201032310050909100506420405090601122c160608010b03040512040e070201 67
    0x186420381c40c04624002c40c00141400110000240640520580a0310414500b6208e00c1c80e1680004042420704042500314022132005ea1310309a002246042d107140c02000b030701c02080c42c40c0b426240201007001c02130700d00c20446289401300c102d036a02c20807481c0c01614454a40002d0100303030000d4071b035403859074240706402e1034103200c00010001d00204032030f1322554402003d0306032502150348030f40080c054010100d0501da51908901d45c2c2400880c041040712448541c10f0400e4185800301c0300340c4140603880203204503484401c201840a0110741c401185003000ca0224a68844a00080f400b15145500102ea1a07088400a0b40003400b030406181ca145006058405003544698050036440389010300c981268410700031a550354440c00002c1d2000f03150b8900001c5400800d450300b10f04104410040c50700c1d081e0a05124042c10051100c41966400011170842d000e180500180c00e00d20144100d208815002c800101489400d12000a03440c01940c40d044e6116180c0080c10381c0ba0700143c44200041d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 786167329 1250 786166079 786166081
    0x209190e030c1005040b0c0c0f0105010312030509011509090312020706050618060a0b0307110f0f0c0d02030a0609033b01021f0c0c08130306150b0a080601050702031e06 74
    0x3e60b5584c8541d50007039411040920a40d9100c00c2600708a40c0020b0a90a0318840c90903a00d0610000b8460240070f03500c03941c0c8007004040314240080c1611800382c03540c08564502401c092b4007106c101c0e240c108461090b04003150b4080181025210020305c050024140e40c00001c0040400203160b00862040c201100c80c10381410200c00010b0082c00c007242c100f0b0300140c45400c02e005c5130301d0807400b4640c0014240303810391009107907110450400d2183c04200e49568400c1c19181c000140a0080c0900c248040c0d40d10351034801c86030006680c80d03480200280111380d07038084c0c0c2030600d8801c2e644040b0520f00a03c2490210306040a0708141c2030343d80031a4150145443c000300c00395031011540340b04c06c800c4115000e10f0744c0642c000140c010300040600d502400000444240044e59074006000c00ba183e203500401054079504108080c3c0300b440945803c0a16428820300825a0200035a102c0001c14900550290346038801613446100e041d501a516100703510319002002c1201400c40001d07803480040d00d000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 786168579 1250 786167329 786167353
    0xc040c02150a0501052b06150302060d0c080c07210e09190b01050901050304060b060904090b01080d020109020a031101050412050102090316080c01050708070b071101150f030209190e030c 82
    0x2604e00f10103004031021241891b00d0011401c241c120400303103007400448608003690707680062010344c0031ba108038101580342e2416103011900100c429901020700032240e480c00c04e849d503480b0402804064401d801c10608a480360225100d091801070756000641081d420341002c02200342107002038001c9210741c40c140150b0483c203502c984251b4162401c180c5807217003552219a41c0d0000f0304468000345030400014401c9014569071400b03062142400354000b901a03504000e11242802d103c460f6141c29603040c458018016100c0f9818030b0110307a082101c2070b8030f2004042c0100d0b810b1050390301040e00142c001d59100107202040d030007804948000c07411510b1600c240541644600360721b110760440341d080a010502d00b035010348006c00106100d00c3d8482d01e411143c0d52003140d406002d0383c8500000d0050701480315072400902c03d492080c1c0075a0455609185080c1301e041c0756484d10b010003400750400001046080400c4030201e550111022000d000002220040d956030303070000050b40007540301d61440402c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 786169829 1250 786168579 786168619
    0x150906180b010512060d03210c08090304080a140a02100e030d09180911090405010b09180304091121190911060c100903020705090f090c040c02150a050105 68
    0x80f00180c0c800581e0326610541040402c403400c203030681c24007652307907451803113604016a4800180c4003420005410340ba8100010680394000b070100c6816402000188203240000032052110380d0b0200000c000c603400c06040c40d041414405c0001c0d040003a423095030281a800c03108170400d81100f581102c008481010f411035a10119105007100c030b001c0022100c03803240c1a41c010030105800b68031003d40e020318600100f084a94200c0b0103840760b0355a6001d050032460030890051708203100c2a0240500081054850749074882d0f4856411500c0e03a40c481404c85910407400c1c0c0307141d10700c0d420304040b0907400395084140300300741154120388442c92980c82c0c10050390107100c0d10400380e810108001c0310907070340000e0206035030001032091243d10402060a480101a005c1c8209070b40c4281d018200241c5010705000c5450005440c0e5a0706582e01c00412404820000b403001e001c82040340c0100d00500e007080d007a41044990000010018404010400b0b0480160003040c12150280d44841d036030300d030782e0312908 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 786171079 1250 786169829 786169837
    0x30a1202280c030605091905011b0c050616090e041505010f0e0c0304080405060c1b040e1c052a160303020a030e04140a0504020f0f06070204150906180b0105 69
    0x1000307000c0c2d802041c40890156400154080d502c00c1c00c54215502c6840c440085511784202101d45a45440307000025001425070070a030b1111509040d4601e074003e43d241512403034020200145850603036660001d0030302c034200440080810110a40d1340e8107160504c3e0440c1308401c110b0031583c6040030000102c1081e001840c00c111a840d2082100c1a1150b00403081164400350040e90030600601c00403800340da031940185880070b405001400072613041e00306c940da0781030b000c440e03144120f203800720709501d80130080f440c10003d40031860700701010700c0200020f17111802400c44c484110188500c202652001604400c5112840f036401c40c1c03500c86642c110a100030045000080043c1c2000000c00002070048042d2140c6420003040401c504410031481543c44500b01c4010f0222900c5009000660503d0481d200c8071480a0311241015070800d400709080348605140240216640d545000d10b1840e40348100d0090305030341d001030180756550b0044100004007500200d805c00d2a10040350940c1d8003a100319 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 786172329 1250 786171079 786171083
    0xa05090415050c0412080c0c0402040609030309090212040b06010c081305030708070303020705060f07150203180a050d05251a01240f0c0b10080c04060b090906030a120228 75
    0x7140c0407241c1769407144e0140e00a014411001d1241051100e180d80d20750001c1e03c098160b0b0b5490009031031450500918540d510740c02401a203204002e0410440c27001d071131703041e0303c990000c3d51041c064580100482e0440d40c4940051f040c060042801c03d50740e14000485011240b0440c111001d103038031440d0540e191003051000801507032250504205da400c0010203002d9402030303a007031182005001e444032080d0550142c071645020340e001040082c01000680707580320b81c50007036000300f20344401c650700c165a0ba034454402d001408008280b5017144080300a881c0030401c036100c201c0400c0021032501910030140d50000b54104150140040b83e07110030500e0014014180000041b58018884401e1320726180100702c3c0c40801000030007581c04504596202c030b001c1e5104402042d0345a24028003507090400b0440c03404d10650030a002000811210381c00c0c3c820112044821820300d2b20b9180009241000b061401084201c0e92280040c40540203d030885615100104c108480401580300802e001202500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 786173579 1250 786172329 786172349
    0x13092003060f0615071b150e0109030204181b090c051305060d0e0613031e08040b1003020a180c1b030324120203010c0f050f090a05090415050c04 64
    0x41503860000d1380b511003444408151441c1484c00d40350411403200c215039207515220030003800c2000060721003900304444070031320740210803040d0240028680e10702448064810f42d05d03190201c0b1404501c2600741c104c0c1d6403260301c0a002005503106500500c50a100f0b5980c400e00e440d9180c28002e004504485c042c000400c0614500ca0500040003c15008110007420103541e9242490b0132200802180f80181842410041c03100c4092900520b0040e4000a40d01010250540300d569540c2202071590425070106200c0d03540d94070200114589010741d400a50710800c0048006202c2c408034035030540910344200d0500210014030410380368074071400c40000c18000404142030119109a00101c501d064418050751070071600d41c1c01d0a00048990401d0010000001c00c1340110b2409200c2c20840b81d0081c10800441c1c01c1c03d06000d003640c01880031402e05982d0014a00e030b55035a0b0050044003a000003031524505041c42d003040c0b002d641007581d20301010b5103081301103081c0329112001d403000c407100450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 786174829 1250 786173579 786173581
    0x180507300627050606091509160e090103030305060306060103020c0705130b030616170f07050c01060906081f150519030b0c07050129120a0203070608040b0c04060c06090213092003060f 81
    0x30610010351200d410000f000702060382202b01e0340d5031000b028000c5009036004507940c2070040801d0704000c005004075050501c10040704211000100e40e08084410880d8a80c00c03000c0d41e01d2210000c2c00990a2580d4180211401c00080e18008240950184102e5449640050f1340e414034000b01c51099a0f003480c1c03828984c0006003558410030003001c0c07180300b1000101c0d21a90f50710815050320708030340201c0d0081d00000100c0c00d0302d04440900b16a00b1064100a208110140500c031200200c0b41c00350320b000303d10403400030040e40d40301003030780e4021030f071055140c0c5062070b102000d503c1680217141d007242c035942040001e00450050a505107070840480301440c021000c00c0f0708000200502c0440c08179207008c0c18901c0030240c0d400b40005802004241c1f5407141c1d40c0352625281541010040c42010030960600084c00780c2c540c010600340b00c040d40301e080007400300158000940144840d10040ca6a141408113620422030b0303551342c0c1e40b9034112860780c4610501c0c210302010788030802200c40c9024420664 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 786176079 1250 786174829 786174841
    0x4060f08070309031d240d0c050414061b030d06170c180901150b0a030c020d0527030f071721030604180507300627050606091509 57
    0x16140c5c0c0004a001403030492080c084c1e040ca583c0c007074140340322841d28140105400c01e008145008032034a5900d9803402c1840c00d0b0800f48042c00e400b07101c022442c02903170013180012002c401207a2079400000300108132503c03558541c1c1060090800b84c012030665074401400b500d901200000c400411407002000c10704c3d22800000e82d00c51598004050304029074031154007003503c2036203a0380d04014000800203241d035100658409400c0e0341d048030b002c50440d40a0740e6581c41132548041520328450031034005010110400603001e803000c032001031a56240c0a50903858a9017600040c4c0e600c201c0e011004180c241c02d003810500c5071103c1c001442011841c0c10302c1c1400c42c1c1e03040a20001d69020b04028000a0070800301e4280084503241e2541c11141584803010602c00d000e2094500c02c4800039161b00309070760084000d1200d250030b0254400900ca540c9840700710280c1c0311134a007a401012044203092440030300a041c825954001550824014100003011030900769a40c6521660108054100d010301d440b20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 786177329 1250 786176079 786176117
    0xe130c08070521030a0c05010b040f02130f080303150d0606180507080121020301060b0703050c070e0402150304050705092403070b040308031302091303020c040c02060109110c0304060f0807030903 86
    0xc10301152030b55070b09d031086261079540b8841c03480d001e1070a0b0340050f02c8141000420280d800e07940c222489140c1094003c000400001080780e6100219101c00c43d1600403510100751000e03d00080109028106840440d149807400080501c4044020381400300340caa0003016902c82c10203000c0e0032941c041c05c42a15451b122991000031003148003800004405d90f5510b0b1407603568100c1481280040d070001521040c002d0204003035009046030b01c01260305410158002035413000601c3c0b030130804cc800400050309101c1e05029050084c03c010300341d6a55817804200041200601841100c20040c2c124040341d2075003000100e600a951541d070360149000d05544a203103850304002c2502090700000000e51005855500085000ba22440ea040301880c1c3c5a10740071b8100440300705028011032801000d900038a6000076964111a01018001106c403912082c02007184107a20680714240700004000030841c2d41314000008000c559503c012494403002011411b0b260b8110029000800220110410100d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 786178579 1250 786177329 786177347
    0x11060601050a1106010602010912031a010c0204090c14101d0918030705100c020a0f0213061d06030607020609030d020d0207050d09030303150f0e130c08070521030a 72
    0x4907040111003440700390f001d03516280c0260004001030751501e41d420200003410002c2480381c1560704007404040c9200b0700300c080180e01c00c17004604014114500c030096481e560300130400301e5040103007405d61ba61601c0c001da0380d14800000f200d0150801600c8620310b144100010b00a4804901500c0e5504d00d5100c104031800002500d046001c1c80804580d00341d18800300300074000903108101030b0040e1022014807200310780600d00d004040d07405c0b40380e0030030004040072500c8aa05504030740741d40200c0c044121950048c00c107500f014803485030314140441e8186000b0340d0684110070480c2100e4455031814002c136100c010940300170f081980180024010b08000380c02401200142440060070a0800d48a80345085207106402000c90740030001442416454000e040d042007214000308100c501d4400328491a1049204240382c55247d1004078282007641c1507820407440c0c00404800207075445011181d1210780c548903091203001030309030709082c0798100341c0d07092482c8800344040c41c20040300400948030384030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 786179829 1250 786178579 786178597
    0xa17040e01030b040c060e032d010c0e100903030f08040201030b092811090405061507050313060c030c11030a0c09140c0c06060618180609071106060105 67
    0x501440081156015003440c140254040c014110f00c5041905080c0d41d40102500130004100081c1c0c90a4140d440c0081e02e902c80d034510720b0464500d6000c6c0e00c40c48801104e40d1042000650034590791700c3c9104d511030042d40081001b2076480b501400d1a050070341e040c01c0c8611006000c604e41c0c4044401c0d05001e6860a9423090040c1400b01e0b51806140008c3c0001d502100c0700301d100040c5a1080b00d50252a80d001144004086410081c1c6490009070080078014441f00e144a60380300c00c0040d985450b007194582c0c2101d00345408a4583c1c01c186003007503c80e00585501e481c1030404a50000d1014812916620841c0d010303160180024100d860305500d500300b0707084081e01032040c84100400100852800c500618500c0c07000100c008152444081c03008000e803088683d0842846031443d006e10105449030020011a04207961390f4840c442084000e40c060780c2c441d402051111000d40d01d04020140d035100781342c11122490607942d0044140c90207180403a40c0f0f405540b1035400603e01d54050801089100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 786181079 1250 786179829 786179873
    0x10917090f0114070b070f02060a0902150703020c04060b190503100b0d1e0501150903050d201209090604050f04030e1315060215190c030e06090a03200a 67
    0x70780641740c0303500c02c43c8144c43d8880090b101640c4030490b40c6e4140903154011020146c1813080906540002e101840441400c601c1700c803000035400d0826008001c040784804010300203000041d0350300100201900409400368450480300c0c030303151015100d082205d01c684000c1804004a13801d0080d10001e5800c01810a806280d840354060f00040840030701e548180b02ca59000319803036051101d00074203021003607000824840880f00502c00140d0114140d02001c2141ca020030303c8400b0b0384100452140380c0c2950003028024820340da091072190100911690300c09a49102c90b0ba26034200303010031a2000c890440d643d607000004200081d01c54039907860071201c0107100600405101d00d94008403101c0e035501c446418071801d0308114007a01406005240300c12950382550070301c0c101c080800d0242c2c940e00c000e1511542d40142414481c02980510701061000e0222609860320400c00c03030f0348620428058020507070340314802014000300c03559a41c4240140024041207115951807100c0300c002c00c800107041c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 786182329 1250 786181079 786181087
    0x3c07080904020304060902040b031516091e150c0201050711030102040902040e01090f0b0a060c020303040306050414120c07030b041e0b04110102060105090c1317010917090f0114 78
    0x30307501c0d0b00143d80224011440080d0310101441004102d0ba41c600000b030090700944018808000164400c0380e110b02c0040030210f5001c10190b0842d0810301c0da0700111070f041d03021040c4441e40380780c2ca60762409550100414284500e00354400343d4450401d000300030b0004070208041c0d00042c141854501000d600a4009410f00e0340f680b4904046e40c00c150480035042d0699001007200030482d0041060844440c0c01c1040301c94043e90100d0115101c42c05000c06001050313804404646003042200c009581040f4200654102858400c1c403203090940054400e1260310b0140c0c10401c112411988444030311401042010701c4d40d524000c0c4140014001e076031034010301d0041542000d00c18034602c0350602c6042089024602868000e0500580030310383c50465102000520490b02d45080660300099030f408500e441c0c4c031958a5002c6110303041d40012072541c00889024100c82015005241ca481c0310300002c0713200100d082c00c40d081a010304500b140d400000f010035011a03501680d108000c130f0342e03141d46440ca0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 786183579 1250 786182329 786182347
    0x60b0307271e0f18020616050a0b0a061d060a06140c0f0a020a0f080703020f040221060a24080403090305030c03040e060402070c03080c0a020a0b3c0708 67
    0x42c1c800344041100d1060303c8803c003c9258107144101520842e02e0072580040e41c14a0300814400d0103085079090442c40d651000b6802e110080015299156000810380103510388507003504080d201c5403084400c240400f281c10314001e00103400d250b00c2500c010304150526458a01c0850703c1d9407007000846026401040364000d100403d1040044100e8690001d20a040e00c17407051003020920360b4880c2c40301d407400c0031090100d0500411072000b12501201c00c01c000c0c0880d1000603000b4030070143d07000310300701c51501500621040b88140c0751050b80c0403900700141036a59096040300d01d0710404100b200104001d1030495a901508005070058001c0c40c0c102d0341c41c2c0d101d58820b440c5030f0040c400c1c1850395001007030400035180c2c0c2400c40f03540240f05480a50a04049136075200d407034480740c00005c0c007003d00401c406e1540c003410080100482d030000c1400b18115583d1540c070745541e20000048004c400300081a0a03d0920302d0000c962035001c014107000300002e121240161900510411603420200b0000204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 786184829 1250 786183579 786183611
    0x3040302102c09070f1e030b0d050d0f21020d180b09011d1e070302030f010f270f0305090a06090305010b04022b0f050703020901030606030b0d0605040f0c12060b030727 74
    0x480b501c80d2b80108035402c80405c1c05410308401a4540d410041d11402c0d82c415840b944610a4182d07489503800760322021410310b4400a0031100600700100c2da4100040d0041c449081074690003106d20b44020030140e4600d1410f0b0944801888001d00b244d80042c03200281043e55806402c50b010444060301c1580b80c0b00d5001030b0820004c2120002a6034440080d4101c2420a10030380444500c0803421904c4480e02d46c28030402e50a40c000f010f000282d01254860030305028608984184100411000c6801c1e01c40350060301c0d8003003a001c203540a618060801c04c0d281428030898040d030000c60b00540c442074a61211240d21141c04c000c00186585981018203011042e00486000b448691005030712644034500060442e00543d01130000c1500f0705403019903540741c01300604102d54003c600826255510304000d458102058001407001c0404500050340c8007107030742084920342c810071082c400780001108040e41d8201500a00c031244001002808a5050700f00344070800798200c0038040ba40d4100002040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 786186079 1250 786184829 786184849
    0x1115041e0e091b01092706090c0c26093714100801090e07030503181305010f090209030c0d0b10060305010803040302102c09070f1e030b 60
    0xe01584040e06030030a1070f1089000701d818150a05e06200340b6031808030050703014541410307007040b82e140d507982c0507503070003050340000c40a031420355410f0003d284281d0300107000042201c010b9900044031a0101d805500702038104042c00140305009045c1020b440c200714007407a82480c0e0803049900c0040034045211502d003034995801001c4802d00d8402d00e01140301d84045145040544621800d841c0026000e4100140d50b0641c1c03040100005c0b420b42d45042c0918000c010b8002a01d10320000c2183c130303049041c070308a5206900c000e5920f03941090035014503505a61080c01460146847e4034403c0c010540319601600300740728020200c0e20070040c0703030020a680020f40c0200303880701e000c07601c00c002c9940965039040005107401d02d0100220b601d003603110b588a00860100a200706000207003030b8a41032140018074084a82c80c2d94110001400e01c0019220441c92001036026500c80e90000d10050b01540d20042142e5241c0c540c8644240000b0020390340c0d02c041d00d03c000616903610040030180c3c494005003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 786187329 1250 786186079 786186091
    0x618010312080901020307320c01060f120b280c0c0210020a0f020d0602121501140c0a0b06060c120304020922030c21020a1115041e0e 59
    0x4440840d030903040100b03140d00040400703d46030b00420500098a07070000d06980c80d41c00c66286040c41c40410400b61003042183d490305021401d002c98440344850040d8460b5044441002903111020340c2c600b200c407a180c030460b40180205c0e005a000070702040d80d402c00305605401c074100c01c41007901010800e0040720031181e500d07000108008102021030518111300e800000c0c040c0020003420704155603000a240142100038041c600c001c44840407c0102e4054600005604100701a075142102c40b10403042d1030b060301e1900080500b0203441000003150212070700606030b41e014200211542d254a01098400741c005a00044104105601d001301030180b0303c0d24a1010103000e40d282818010000e049401901310410070301d032850101810b54241c041040d0180c3d140c142481c0c501000d040800ca20701401c9004c101d054080c0d0041180d0075408180e116284d84a84000d064421591007030181a0742070345a0f103058500100010b00075020122005010014008c8444a4075501c2e11210f1050741d600b9505 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 786188579 1250 786187329 786187343
    0xc06140603010606110a0f080c0f0604031e080a0c0e03030406090e06040209030c1c0b130311070503060a0914070b12090d021c110604050d09050a1404020306180103 72
    0x3408100e103028040d8100610482c80c0400c0090090550141c0301d904100c0c0c024030218842c1c0301503080000340c0c02642c0380c050b0035100f901c2170303c0000c8203e96115001101c003200040c05070541104c0040c1c010000c1c0900034000e603a030800642d01c0c0c44202009107201c80701002448101600004950350401c0107002500c0d0302d80e030715000b0343e2500824005101c0050a082c0c4900d0043c841d040306a180026510712050080790400129030049201140ca03800b40d200c00b401d0011800100042011001c206940c05031090b80ca0000030302c100410181c4400381802500d6250300f000011400c070003035982050000710b024002042c401c4031101501483c11713540b507010320010040410840903064094007110fa007d0003010180c441000c0074040252074188030403d80010007410620320035850f00c0b4280c0802c4240f010402c440c15420241803995541c1d00d004418800190b2a40740031540341001c50710341d421038071580401d0840580275020000030f500f000f030072560000e18004540d1101143d103e619030086001b100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 786189829 1250 786188579 786188581
    0x12131b05030f1f110c010e070e09150c0d27050106050a152f0105060a050f0102030f0304080f0a2102120a0c1e0503011d04020306070509010c0614 64
    0x41070604080b01e054050910b0340014110b1420300e4090540000d85004030040003403060100300f038185490040c0138a0340c00365860300280120030200003070708a096641500c40c2e8043c075503074103d07034540c2c600d4039030035642c0040e1028001c203240e001031034060905820170003000b08114808240245120076000c140150100c940080306091200a12521016200a9641011003401d1120710149491807104410411401000c1010000c61204140c02d150600c41c2004030361b511800c0b803041c00303003030b090358410310034216440005502e141100caa6003000d401030b00a1418828002616161508002d1050300d801104004102d0040b8141009203210407150301c622010760107030000d00c01c26130b51442c0c1da8418648108103002155050b8102503502682c4000d0104401d0384104040300e0b00c100b0350a18104001c0700d8940c1e43c2d901500080654107841c0c52150501d0184501c00085880c403009880294042d0000804100c0161151006055540c01070504082101c842d5071480100c44509031562aa55a004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 786191079 1250 786189829 786189839
    0x1809050a0b060f100917060103080301210206040311090f010810020d150e010e0705120c0702010c0803070e030f0a1205031513090302151b0c010b04060305010203010f08010203040812131b 82
    0x1c806d103101864000600642d07045540c2d20507141300c1801035651300c11950800f0100d10680302902c0712040ea014000d00d40381da07981d1400e00c0440110300d0259115945800004d0003001c0c2001510707040340d0b1980020a4110030140c0e50f48002d501a414054070141c5540400c081110500c0c0701100420515800c0809585460400b5001e03880182ca5802006010005003074450054040036400c1184106d00720341e1040544016151f03d0500364008203403010100c1000714854001d03001000d0500181d06032034000e50100b011a480c1c03d03508070700402106003114071002051058001c1c581c00341080045034003c12401d800111011400a103840301e032a1031700600000c042d41888042c0070308a903689040c48500b80341c2c2d2044041c840b0b02c03007034038003103100414440359081094100702d05464015108010745900c9042a0340030358003d008607002421030450000c0c1c151414400c132841035402a800b00c2c01c0a402c400e01a601080203040442c10500030301e03026000c00c01d207028400740c03d4404545100e100b4030302 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 786192329 1250 786191079 786191099
    0xd14040801020a051b03070203120a1e02010e0d14121009020c06100603051911040b0301080a020a051816050d05090c0118061d0111070608011809050a0b060f1009 71
    0x605c0d80c50070a4000780103480050b20006071502a10388401803003500d8007070307103802110420754507880401140180c0804086164066001740b4031040d26009480e15000010703401e4540280d4201d8800c46c1850400030f9800c1072486800203900301c0c540813144100d080da50003120050760040425404190840320921610700c1040030b0707043c0240300c0f40c00c1c140103038509103803190355455482280c00c068640701e1601e2121020454210303000303030071752603412526542c462845a68803800a60700320b0003003210074804034842c41e114030b0419590300204c401c036002c2e17945c11014020342200b000251043c80401c2c01420004440ba00906110b0041c3350000d011403e60440010804000e00310312202c2d020701000148402a8002d01d051008001a0513100c01800702400480c1c1ca102158a000c0f100d0042040c04101c0c4c2c0d61191342c0b58103c6d01c243d14402c01d5000f120b844001122000c1c64010501c0e446901c1d5100080d00c951112988484010318068005004101082c50514490079020000f44d9102c0709001201c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 786193579 1250 786192329 786192367
    0xe06060c06190621021905030a05030904060608190e190303020910031b0c21181e031103121803060108150718030c0b0405040c0c050d14040801020a05 66
    0xf2050048051550b0354082c404ca8040042001c4d00420322114030f12101e6041c0b481072401044060b04403140c400340c904000b500c075080800a40c1c4600d007030240000301e2a200b144901c0c0900c400003000300380c00e04110f00c0070004110f0342206030b850380103840102c0010320440f001c4088032402500e01507503400b483d00c10812442d91102004041c1403030494007039040148140300a20314071040c10180e0301d540060400d50f4544d188000c81000d03a01d10505401c003110740c40400351682c0601b100c03110350010b48891004c003803140010200c0707050400554040010070808100034000f498091b0a82c1d08152641e41403101961152007000807600788026041050f0604200c1c850040c043c8070040c14000010703403422031403404041e204a0401c01c49440d00b004252280d00e12070021940024501c4c0040e1f070f079450301c00c00c035041480707a0f612132890b000d41708407807034020414407804691060282c00085442a019100c00c605c4560580e40040d060102250825092005014503007103a101d040c2c5031a80c5003600d081e1105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 786194829 1250 786193579 786193589
    0x150d1a01180c08010e19060305030307030e060a0b0f01030f15080d090e010e0406020c070b0a030504060c050309060c0a03060902130515040810051806040303091e05070e06060c061906 80
    0xc0840c00410140d8050707100d190700480d48034441c038200442646d000f030207401d00360000b078102c3c0400405d01100c2501580288013400c41070301035031000e0755803140586c203c4604d10401c0e6001340b812521240c40d5031190780300503514040958006914156200e41c148000b00c60380000319264442c41c0d400302e84942200d1501c00811816640203403560508050f0144124090401002e00d030b0042018107603c0d40500884d070140000c030201039210780400c1c50040c054101a035041e555907103440441c0422a110b8070403240316401180042245498140041c169588060240c0042503a140c01c0414044454001081600a640040030080341040c040100e0b21030140160900c1d124108001c01c00c00740301080745020444882c0d000605580c40c10312010402400d0006c0950794012507081004054040d0b01c601d050768081c01440582e110039803044140c41c00e8114002e04141d00c481400c10055031b0403000a0780c400c2c400b03001c5505042d80c0341c400924003001620040c1805541140105101c0b40300c1c483d101c002c0ca = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 786196079 1250 786194829 786194837
    0xf1611090115140d0902100302270303070f030207050a0b1201080a1509150e0115060206070509091905040506011502011a0f040b15071a150d1a01180c 66
    0x2505140090704508408018810040d0f002c07581130320b01c000a5106502540d0003038081034070141000002402540402900070030041c0d05444e8009a01c4407411603109040081d004624021503a21040320b44400100120214403c410f0b020a43c1e490307524000000382440020580c64085d1004041e84922058015030119408400441c010a40081c1400d149516103034000a00b01c0c81801c04c00d040c0919440712690150a003a9920320b214815400a09111801d10458078901c1d1a8003049848000984003c000200240107070016850003022003604074200300c0118140f01a071098240c01d4440443e8203880c075402c41001002038800003000d2280b8915148000c200f40f20f241d49900d0340f034911048105001d150604068280340e1a558046242400014060003000c0101c0d0000015580300d200c048071550741041d100c0c600110702184040c003e2507400c640c0d006d00840141803090072128020251000c0a0428007010003a617481e01c07840c080d251000c042c030324002c0b00981003000d845402c51000c00708 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 786197329 1250 786196079 786196109
    0x509210c010e0c010c03080a0e03070305090f040915021b1b09010f03051216050703211701050603060607060c03090309081c030203060d2f120604020103020f16110901 73
    0xe40c1c5d000000240702c580c141032040c107646486110800508503d00c1441c01c1c1e1100250314014190801d015020301442183c09d444d90406040c10301c415a0718802000300302481c0091440c030303828000e4014007442220078810541c018003000b1180e02e414005103400f4199100300e1050000c904045030701c05e02404100d0070f0f10204905e150340c2d43d82d4800315440001030b111030200c0c2626407202d051101000d0305400c2800c40d1341294903400c001441c1000d42101a082020788410468010700403200b03c4900618082c3d5000300c1ea20b040180301d03682c0d200501e1a40d10407010131100300003e80e144100799101c00300f0f5500182c106e5061a000d403401c891500701c0006680101201742c0032070482c00c0c81290500241c50056280d44444010810091004000405c0740c486034041000708400c407000444c0c850a2506804001d004240038403114012821415040342c2100c400070f00036501940090596501c0301c000c05152020201740f50a0441c09040202d42e0300c0e1039604554801d01d030050740180940400715090050f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 786198579 1250 786197329 786197353
    0xb130e0f06060a030603080d05070915050d051012050706120911010c02060d1a040c050406050d0c0504050a1d0601030b1e06040e011e080a12030509210c010e 69
    0xc600d0003008544121000141055030300c4c070a411040096a00040003502d4905c007510200140c201281c0c98800240c07010310000d035101c40454581882040c680b00c180c5464142030b01c00c07001e04401400341e0344d03844c2e00040018010382011000b203980c5000b40050324004c0c0c10680020140c41d044201804c2c504e04060804020a00085e00550096000d007011440000240b0106055018800c0c1c01190a40f401d411601c2010490610811280e0111010403514501e07500030388140c0039500803003000a80a004185826181e64480d40442c03149040c52424190343d03c000601d610f10a0b004401214180603495015001031a02035422020074202806259444804551034584445a860021020b100020007030740360181144c000d40140d60a0031131030f42c0c44071740191a500804e454805101914440020610008140701e80502c1d0b21407030f1b0b07c2d061700c2d0160302240030b48409402c41c0307400e00600c2e03c4001e107510f403c8055400070f032144444130b032203011082c021821614207140c45d110603000307101e130300315 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 786199829 1250 786198579 786198601
    0x903030f090b0904090201020a0206130509011a040e13020a2c0103170d0f020301080a021311030c07021810090f0e031b150705070b0702191401150b130e 67
    0x300501e02a130780029442043d0004070316103401d041010303400003000107c403443c0a075102030360015594103441e42038441e662035582130341911044102815800c0301380000d00807002081c4010b5004045902840354220746900000d01480095102d01d030000f81d041c1010402440b040d0740c6e180c03424084500e0301880c3d80b454980104950054500700180a4006126847c9039907d0b0712144026845d008119180c0d130b10b0744035042c4d942030f0182c000c0e840381ba82c0c14548401c00c00c0b6400344a207240c61080c1503900396105e00c001640d20381c1049030200d9005005408100d005024a031295106410341108116214030b0014600221035030566040013850a00322848c428001c00000c94181440c4045100d01e1050f103000543c1c24586014100060080c40d80e060061056100340901416401251582c41702c1c0c54481050742d90b13640d1a6124510321003501080c0d00841d10b060780b000c1500c40300400110f040400411400052801600910040ca1012411400c2341ca01ca02d0030101422080d510802c0b035082803040d0070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 786201079 1250 786199829 786199837
    0xa0b0d050a020405070513140f030604030c0b180f01050a0b0a1a09040e031b0d080106020a030f121e0e12160203010f0204152307020118080d0903030f090b 68
    0x2e40600d0311080400c4099108008035600301812585d12402c142d250660041d0f881e8000055078800d41210f00b01074007070324020480c036001341c1d410740700c5440c0c0480303941d203120304c9010090421040d500c07501c1c000c940b80f41d0b0520802c0500001d03440002801d00c6d09600e200c1c01c58000b0101c0c24024030551b4414000d10081c0b80340c030040d0b40529001e550716189100009005844001c0058080b40004200701e089200700d55800001201050280d40c6a14140b01c07003190381080903c80c002c0140e011100035808a401014440700c141424a0403480000c80b08400c2001ea80324401c0d140c0380020a060f07010303080806442444103040b00340d000340c07143c2e124040080b54240243e11605c91040000d2080a0466500354005003208002da4015501d485e5554401c600c0ca0113000784940c0440c415a034941780014001036075102c54680625810705003a0150011605400d881c04c5101a1451842e80492005c40c100104040e144107951407081407415441c005100100303200a41c414803003141c20030300072294503130240c2d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 786202329 1250 786201079 786201083
    0x1b0328090f0510030b0303130e0f0f040c0605071703011205060f100e09190b06011805090106050703030617030714031207050a05121f0518150a030b0f0a0b0d050a 71
    0x1007170525210300001d066104840c500d0b12826030054001503c16140381302c15100300c400c5900c5940c2ca03a03601c0f0755004420001c460040003152650802d10146000380081c0040034080c0501044031030f21750509041c2d0758000e030003035595450ba42404504000f410440300d644090f4003c1d00c2d0003182001c0c516030031010703030a00480d28085600000505106010490703b80c1c801c1c03543c0c18454078441c080c1040c15000300f060307409900113084108000e0300070006602200031100701510740b002d16843c2000c1295240c000b440300714209600c80c100010310a00c40c00e142c81c2030303d403103070041d580e100528030344603000c03495441e12070f40d10350400d0000ea1103868032400090340c403400b80e040280ea20740400380212542d10410840c4401d0902d03000c14000381000251490030765103000e00704826616210010403031500031200c2c44c40f8090200000140d800340ea480a07424071144090003c01103140c0f030360788800e100c1004650b06815240520300300715142810b401289000340c0e0a070703840c6200345e90750b840d00c50b00c60041400c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 786203579 1250 786202329 786202331
    0x10e0d030b01120f0b010801120209060906040b0312030f06010f17040c03080c0706030c0908030405130b030a030c020f0a06020a02150c1605040605010302030c1b0328090f051003 78
    0x12420640d0103000c0714440d403080c1c0700741005400f5035551183d005212417100c5a00152441c00041001da03a44072001b984544c008200241e0b40c1c2e1401c0800912160082c204da80186d21990101180d4400700a910110450390300407035168a003000c0d40b5031a43c0c900a10140c10056400c468100168100440348004088910b0403a201d50b10f03414064020200c42e4002440f1b00360025009800b0200440d003041075805030395007480864182103044490205034052070200360400c1008025626041408c2000c4100458001c600c40080c41d000905115105000b60003003580c11035840704500d0156001d5030081070481d107081c8110308110b4029a600c06d00c000c024064030306040c1c048400400344c8107540b410780a51046441c005501c00044500366900e02c200e80c0201d08003203005c00c0540c002d00a80380316544845400303040000400d80852260309403005080c10340420800c0d400380c50010109801981c80724420000c091550b110018081c0301542c1c08201051165602805a569408171040d0f0342001460 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 786204829 1250 786203579 786203591
    0x30204052d0a180b151909051b040e100509070c11011814011701050919020405030106030803011403281e0f0512040317210a02041502010e0d03 63
    0xd42d1070014126180c44142000e0300c3d4084808000803001c00510502c0072050f0030303e0994000c2c041c4a550241c29440e05010000010103000070540e940c05154000183c1005030030744d442d8030211307114035402074003e0502007140004000c1c030303403104d204128000d040a0318440ea00745404da4009104a1440300c0c0180304a440d0303440030036660311030009500b0fa00c0c5403134500c40707074159180e10381c4170070348540e184c0700c0c1c04030794514015a0600d0041440604070340002c1c1074010f07603540d1589102d03425041a040c140000741e09000225013a2001d1060f040a14851405290b0b254100000141c50a03114000184240d01144005400e0388000940140d000c6008a400e050303841c145c5000b83c0c0b0903078010410001403504169078000e000c1001500c040c3c040c09801600c0a6003048950b0851038072444c0000740c032840300d18031030f612074010201c010642c00043c003000034007101d81c04030036071141c0c0c07030599284000a4000c20700f8400c1c0d148981729207086200c41d000030400d000cac0d203c06680d00c030320b40303102200c06042c3c0d908 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 786206079 1250 786204829 786204841
    0x80f030c1c0e0901141305041106160501021305040f05040201021002090d1707030e090f190b030d030903020106140f092701061d07020a1b0816030204052d 68
    0x202d00c801440c0c800a141ca681503840750500400007102d602c16610400508480d000002803034450782c0d000300d030070040304418100c5003814803509500440c1700c119141000d07400c03140861800c1c405030650f4003950642c2060f030f07490402040251111250052500b915041c107003c0141e0300081c0b42a085030300c4440150f121041c04001580c031b00c03541c1e81c01400a660200180003408070b0507005088092181d190047d11155282c103008401c0021685100440e282001041040c1030095094070710028003840800d480c80030501190420b0a0140390300080303a01ca2904404040d02030061030301401108659070300d41100301c000a4407101300006024090a4800049000703e01e454014280c1d1028034040350405440082805008107154401d868100340c0d20852900341d10fa024100301d004284e554010448205291504071303107161404e04040e81a91104800070307a01c14140a02d042c0c41d9450001580a41e1440c0140415110300030814007040980e03400000305100c110152001203007090960802955800b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 786207329 1250 786206079 786206087
    0x5390105030c12150d050604020910050603011a04030f21080601020d03110d0203071206060c0305030408030907050a0f0918080f0a0e1e030d020d1d0604030b010609080f030c1c 77
    0x501440e03174000c400c0c03000c00300a0080000e02c25000d00e10030740c3c030280c0740d981301542c16840707850760b000d00b44c0d008000308010420000900170640641296401240c60b1680e00e40d02d031407492400307800484101107003c0c104204d414941c040007001341e0741c0b41808012841c1c6440000d44941c9101d1854051641c0c074189450140c4400041d00d0034800c1110086540341024403000d481420329030303032030080717a82402400b0401e80d00c00c00300083c2581d49038680c9030840c1c4a940d60a11550030003042110030f0312490070001900d50307603084804000c001c107010200800d8180104030302541e0400902c0c0b8146105001c0c1c040024000c00c0131208000d0418841c00d4407a500054111400a290040300394041c50004c805c495148010140e0814035100b141100d4001c1072500e001e0361500b000054480105201004030f00541d902301070b105944c2d500042000e803400f84c4039031301d22041010030b81101000520981c0d051018034000c2003010b010288080066090100187c800c503034518103d0080c41d0500001d5086000040c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 786208579 1250 786207329 786207361
    0x9120d0e0303011707140a0e0402031903030b030c0409020d080717030c0406030b091b090103020c0114010515190f0e0409140c040e07090905390105030c12 68
    0x52020340b6941d5030b41d100302c500d510407911014040780c090014005034281122482107107142024241400d518500442c005149000400a0342c140c01001543c4052407170030305d8981c210b1171003a1000224001c440080c10b140005843c8403500943c0b828003c40c0150341c0c0c070003840c40c500d540008590b81d0b4620926202c1d14220000441ca903a841c03020060040500c8500d0181042d29181d5234108010821002040646c16064039560365290002c10f102c020141000c004201c90b24040c14051b140185540b50b10342143d41c0d040b10760441484150050250b4a4501c0c0342c00c0c0c0642d280000281020301c42203540f01500c080c070a446082c8498850340341c464078000d140e08091641c1c003c104110f0076102c0e0629210468844000c09a50300911030020712515181c4904500840341e1001004c1e070504101510000b0207040c8001c0c0c40700c1c03103a0f01030450403102d410070181003409046680303006c08a41c84400d0b4680000300b10782d141805030600802c070b42c40c81503800340c070400340c101c0c10071003c80c1c2c0381c51401d0025008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 786209829 1250 786208579 786208601
    0x7030f080a050412110103150e0a0e070b0a080f0603060405030a08040512220e0c070201050705010b040e1005010b07030518181509010b0403050c10030b03030414010f0809120d 77
    0x81c1d04c01c1650a120010f480200080030a8031b05108400e48000640c0f51006980104a90044043c003c5200f2003511b5220440b0810f0714003c59201d6134607440c00d825540c00098003407002a540c9801c01190100c14030059820074800c0d00100074506182d039415490740125580382c42003251090001e401c0c054200240302003010001c030819661300000354a54428401c400140082004020317001840800a040d058031440705e860641c0d04080d030507801101c0365070042c00c050b181c030340d00d0303081c6410103903114031405c60850400c80040808088403510758003030300c42c140e1107510000424082800841d81040c1151540c0c840402009201081e02c0000340b00c0d1010300005207412843c1d07004001c510143c841050300d2040c0100c1e000202681d0b0f5924182d05441207010082490300401c600d00828203200f00c0410100d199400e021400440000c0401c1c91a00540e00c0201c40d54074561240d00c0b40e58000e90745648407501e6123805500c9103803914041c0d42c2c86030101c1e6940700d102d000050300020021031f9401681c00d06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 786211079 1250 786209829 786209849
    0x403051c0f0e060601020c0120030d110702090a0c080109020a020a050a0b090705030c0a170a080d050109060501030902090612031201030c060f09030b0114040b06070302060f010807030f080a0504 85
    0x2100448081d00a100981c0c03680d10500c2104045003066000140c1d404003444143c1d180d0507600e0460500d903e21002c0c08455000342c0c4402e100a94114965008061600c60022501070711010580108060f070304020303080102d400e240c0384941454641c0180e4041c1074442c01c180150b5943c070349601c101c0c6401b81d01c0d50003510038007039400ca0b2010400450b0086004041c1241110142030301c0d003003010349034407802c1c0300d890340850880707420045624000c80031180110440255004145151603010142e40300701d901c0c114059407240140318201d694800d64014000a1a0802c10120640e002c101d00d00400f45c12140301c0d19441032454180b15041007103848600b1200745403641d5503583c0c500a250042e1034020100030400b908804507410b8402d040c190b049942201031901540d180002031301200000c04c100301c0c2c010703840741022082502c0303071001014114071a83c002c0203546004041e2100006040e0032142298201c40401c10114a450901208854001002640d17030351201c04c05840d148125031018940c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 786212329 1250 786211079 786211091
    0x10e01181104030b0406060503010f0e1009030306080f061608041101030f0f090c0510030902060d09050c1203120711070501030f020904050c0c0f032107020703060204090213050402070b0403051c 85
    0x104080c1c010707c0490f00c0030f80c003e00c07101c05c1201804087d1039064a481c0c0c115400180040a05281c6400c400402c40c06800d0000e0120344404003103080046c41040c102c074070f87c80314051001e090313105040b8400021042c0b0340b0441070f0510356905c0240c6c64003080e507181010b03221101c15543c4003072544140040030700b032a002c110301c80c80740c50000c994403840e219103845042e50080c0c944226000703000340b09080390b0042846262202440941004100c1d0020540c1c4902c0754550358072a0362100400c00c03961641e140300954840c514910700c181c80702001080003080007416140c114a50000041c15002e81300309090219800c060210203400038003070810301d154054140000e12841001c010024042c0e0740b4540d068075101400f10780c40554030b00c00c0c1074442da1824807251040400c20710f51581e8036082030041c410380f000c1350750702d80b00d00050f600b04e83c0203980604e41c005003204003266162100780040c4406daa0550a002c12034544045980b4000c00250521500143d86135403105800340d0350b100303050703144010071038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 786213579 1250 786212329 786212333
    0x1b050f1c08010506031302150d02070818120304170c03010c050301031a040b070e011134032001020a080a020706111902011430010e01181104030b04 65
    0x5a400192100c0022601400001c15203003049000c49206114180360360020398416828404012008680d46600c0102417200c6410000907000414449004400c2580c403a0303c1030001c1e851500b80c00749218800c0f2044134000407150b04c088165401c403800d956650790010260f0312140e052030316103141c19a0651904859818007a0040c3c043c1d0b0590b80220072680346031520f8401524142e90646004d44000010000075003c5440b5540101002806140c001c034107030030f1808005d10381213880160014000e4400c810344040480e103101035085002000b0700002e098619207400c500d03140145094100f0341210300e150142a40200660f40700540d01407001a03890f010f40c2d1000b912018240070300c1c3c0c00550158400101c40d0030008012010001f0001c45421318681a401503410341e08000b14000404800e002c0307101149118a400c640c02d43e81681605802a1240c00340c02c05008140c001c542d070b88107014014045400400c10000c40c070b441015001409004204804006004a0344000d000e60010020003003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 786214829 1250 786213579 786213613
    0x60418080f0304030810080a08070807140d0f030b13111b06012303060609100f1d06030a03093311120a02030703052503081602010b011b050f 62
    0xc810f5010343d440074565101d010010350510030038411385d4800da00c202d00903c00f15580703400a00742503100714001880c20000e503540b9004440c2c1d40c000000c1c16045100c2c00031070750313402015042400c00c40d072408001c0c41c41d502000400700030748107580820040d82c031005840100903100407110001c40860ad12407200500500d010350702d101c240101c1c4244c07405080440c59016540d14002d0780c007440100900b0700c03580c5200c10311002100040502d44a9a0b0550340040c17880e4210040c0d00280001d482c5c001081d000d0040421900c1070080c08050180d88129140004a54010100c1c41906d035200d542540307022500d000140031507494011041244860078404403015004240140d00c0b40d07510080d1656a503440c6144000e0f80149210a80980c204024040000c0d10480040c02c0c1010002d07841c1800104004030200b0a0201c204200d000c502848103010020f142c10303a40c00003040e003c1c40244181220100000d10b10350400e0a640b000701d0740703c141c00007003100c00d02030880418840c400710f0364015903041c04a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 786216079 1250 786214829 786214831
    0x307120b070e2e031e0b1e090f04030216150e18070c0204020705010c080f0c0403030f0c030323101d010b0c0f06010b1b0114060418080f03 61
    0x11020400740c00d0000d4a906242c0301c0c1e03040e0358204414825111a0f580a0100744244041148040594841c0c016135800404600124160f0381c0340000a40c0d015044c06003c07841c0034a14680142c10352a000002d030fa076862410043d80310385401c80070f0320191110319081e85806005526081c00d049a1080450030007020600c00070036901507036603002100a1402449080172040304120000b41c0724800241c1d1040c000d0076548c0740f1071b1014100501e030081a0300ca26007121b100604d0039000030024428480344940c150305036030300035801030035a034589851a6005410b07440030804810a0184070f805500a25001c0c0d44281010f0070701603604a10280e80f061546801101260170701c21403414110086401041900d4080c490800b00816860b07513401c1000e002c4040e007041c04032840b9441901c5445940103001d20541c2e00070803980c0000d50b00c0321020b0585840d90b075403800c0c15451a81c90720295070412441c030985a81c103c10151800500d80c0c03a04407804904204001000c1c02503200040c2c0d04034a124814011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 786217329 1250 786216079 786216091
    0x91401050a3801123207020a030e01020a080f19050c0a02090414031603030f020a0206132909070501080609190e0714040c0c030507061a120f06010b0901050d0b0307120b 74
    0x500d248960043d03280641700019600000140d000c1c0320304c240020300503256003d885c00140102c030010107403542c411000b6800449003200c1c80d080412160310007060904103090586050604a091540c0c80c0d10240c1d031500f10a2000e841032410341c0100d41444070304205c502601803103e007070b07954841c40410310000712090207100700e00192900090620f070903200c0c07080c1c8180011607405828242c84908d48161412080d00301a107502d210414002e18800005001c15043c1c0c808000c04c00a0b80b80000820b42082c1d80383c0c2c002c0381404414010828199107802007140d00c4001c0350440390701030400004903c002c1c162100100100d1164034004210040034150101018104840520100c0243e440846904200c4480140402c06c02e00420340082c807d608a1421301100c40c020203400f181c0800003400c020701c2c04103042d90a03041040b014594072418004140945405900503182228040000b4461322a40c00d080079041d86e661030041d8503550921040b030051a90766030300c0300303101554240028800b8055440b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786218579 1250 786217329 786217391
    0x7051e0f0a021209331303120201051608130b0112060f0207050309090901020910120c02070602030405041503080d051e070c02090604091401050a380112 67
    0x40035411a10460449100d664050301040554400c1082e4154840e401c181c0e41422881c07892400300b103103a08170043c09134001c02e504802c250b18954109050440e441403250b03011039052100300015000c03014640c00103900384d483c0c80d40c20f0356200140d030320350002c084c4c0303004040042d100000910002c6900c00b10b054140521020032082c201d15005ca8101d03c51454002c04680060045e0b521a240c9141812781c0300c1e0085001625060703040000402040e900602031000c1841141d0a08141c0e60b1031090f100400180d000804005042c0071000e940d0b401244103640c400c540b50140c43c90344548821000009503804101c5544844810302d03800081c14044a11100c007a2040000c00c3d103a64100007040c2c0144201d441d0411821415000e0050402008060540048c1c590401d040042c074001143c5802c0c0361001c0000445040148884040c2c64805680591203030a114280c0d03407003801102e180c1038a031880c45041004000180059401480c0c020300601c44511f8a0002d1300010700e0429039031820301d41c2d0740b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 786219829 1250 786218579 786218593
    0x8190f0201060f080a02010c2a0905130c05064e010f061211070f03020f0c180907051f03050105060f0904090203010f0906150b04080607051e0f0a02 65
    0x30040f06001164490b1401d20782c46100c503180994050786440d40c0c1c9601070894418080c3d80962801f9280c40151250298103480311001c100d241d81612803182c015010050580c201034440d00c07503004828083c00340c2403041d500001d040402074103001307012840004030340c030f800c4102100680c0d06490b21400f85110610300d082c521a0a003444018410310f05840060303503141d4046042200803524448410844401c803552801800c1300c08170014040c00d040f900ca004460280301c039614000b401c1040c0000701e030200d9440305841d01d0755582e60742c0310b20b590301e007140064540e140d803072030342d8907150652a61120341c0001401c50908182007245d50301c5500d2003103549050000d0f90341e46040c0040362241e0b146c3d0344803104041c0841011458245c00101400d4001400410b8011240d180d401c02c6a40c003040854100d0790701c4812100c80d850700e401600c01041c0c1d10030b0b0241041d02d0200156118503000f000e1104000e0006142074102c00e19403c9840001400032409807969113118110030b09500520501d005441199 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 786221079 1250 786219829 786219839
    0x1090501150e0403080a022101080c1f200c0a06020d03110405090a0902011e0507050f060601170414031b10110d020702010212130513020703020a020d08190f020106 72
    0xc182d000301c0d8135944142050b90f556130034400a4101c0c4180c00b451015441701d00b0468205184418040c0004402801e0b5240d0080c080051383c440288498887c1448280d19401e10754000201c1500c048048042d07103404602606880d00f0b291070014069485490208040380c030590008980611b400c154804018962690350517507002d01507449000d170300103645c40002e0000012900003001e05441030401c5409621420428841480e089425034001900402d103001400010401503850b407003504054005828250002003158104001240b405107200020400b0885e40d030001d08030742c0b441c540982e43c81d50f1544006403d0021800d400c0364540c0f08a5101081044591007041c4442c03904510381d51400040c1e03c07544c0065004110141d05500511007241010b8680c20000c0c010140c503001d601d084c0c00d040600f00302c00b07519960f98142c0e9480c41401040000780d000200c5207182601190540442d124074074002e04e0074070611400c822601c4414011481a54108054805031003051f00240a03454840f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 786222329 1250 786221079 786221099
    0xa1101060905061008040209220b0115022a1203040807030b040209010e070e01081008070f060206130b0a021303020607050715180b03090a05030403030c02010207050901080a0605090c030109050115 86
    0x9446c0a94440e4042c40806d0160850483d40c0140c106000c00c103084020660310b4904006009901400840e0b99194000a403140d042c401e11450455142c004849016121340006000c0c0d04401d445000c0d142c105040c41446208100703a0b40184108411240c036140ca07881c2050500c60300b91000c80c05540c070b48d0004214400904982c910480c01c0baa42e40c0148d401d054011915594041c082400300b031202040480d941d58244504c1014100300704065a00c645480402850090002d05422240e454010020300058100b0010f40d084441400090b0702d94aa080c4a11005229680000d51122001480c5002c110740031414a04862011070100d09011320500290350a801038400a841014010740501c074600c028009540c1000280045401e8280c0c9035503158034541c0b058006401007078040c0e0700f9504560f070400201001d410181c0c1c10041c40c4d45002d081c0d50369540104c4000300003a0300e44d40003540b01a0204801c900481c7c0003402807000ca02c07075040280c004c10300c02020790481c0c918030501003806858 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 786223579 1250 786222329 786222331
    0x70f081005060d0b1303030b030f0a150203070504030609060b1e0a05030c1005071b0f030b0105040b060a030b03250311060a05190e0904150e1b0103020a1101060905061008 75
    0x444c1e08000030b030751800001c4000050700b01e012824569600d03100c0c009a01c0805c40e00035181d6012008140c18140340c20f00b05a00528a4103d200341c0f4010420081099402026102180c0d80940040b900440d1741c030b801c1c13000e01014400c0310340000d805004403a0380c149034210340060366001c0c3c2c0c94030b09181d200e409041e100d81508840e5504845005032996445124030028800c1c00e00401c10120014144041031600c8180c551141141101020b02441400030841020b801441c04850800c81c03981400c02041c0f05004008845080c195128082013403500c003444405d091000c45034491803071040c1d10303081c008006407500080e81e11003000c1800e00c10314240034003207607080807003600c3d03060500c000c80301c03915082d80401c1500350400842640010300340e110071034494091407180c0041d0720052817003d212801c4500d91040320071551300030144c038030700c0c40f281480b0840380340000e203000b59851480800c1a503000e034140c40311156542ca003000020b1407012036030005020303c174119005188a01070260031101020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 786224829 1250 786223579 786223583
    0x90109080f043f0807060c03050f15090a020f2209060605130b0a0909050a090215031003200a030605012903361e120912070f081005060d 60
    0x245014044204406181c00c0c0200f0380709606040c5014030f1a41d132001502d07918072211010a450780c0600610503404002e6552107040001404030b41b168000c00100300030300143c20121032650000d00700078100d103500c088814410f10503912030300ca0711900340c1c0013008207814800c8100e058901440410080d04c54011030324080c80d1140c2038006181001744da06038a602c55040c60090010391800050f66820b517015091190020903030000d030320340090040c0400c0c4100e001072510304800400401206a02c40c2c504081030366000942c0540c2c1c40c1c074000c0504003010750390200c82c1c1e104200800010420000313420040c140c9a604044131089008408407001141410100d000100410300c00100080309a810340907041010312401c0c80c80381e40c404101c4d0342200c15520b0220359900100500303200301c0130221541101d0b1800400400c082405070b02a40f07203e0180c00c20f846d10030304110700034101c3c00c481000700c640900ba00c0e0902c540c690317586e44150b942c1d910050103054502410100002c019141182c401e0b640c0c16 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 786226079 1250 786224829 786224909
    0xa060e1006200a02121c0504080c0901061e1107080714041503170403020a120c080f15040f0b07050d0f14010302040203040c0e070203071709010c020108090109080f04 73
    0x3e0825800c11034450720498403c070b021b10540309081e1801c07070420040c8407440c00540316950395a00348501107080c41380c0907060a001d02140c40040164690052403400d20381e04503012411142d500400c21101c0201c1240c0070703045882882c7c0007281003980400c00c80111142c036000740b80541c21010900040e02c07290f031a040c0d1700c00a112001c101145284890428428002c060344d881c02d13840e940001d4424100d9049455064801400c110070031100519410260103102c0050200a03031414120b0350341e200c103455000340503c4100c00305080000303c1040c84072165105080082d1440c05040081030703038101e818805012800c00341c403180d90050034070401140e0310811400c03204036030840e000d110195001401c1110300d50241c0c00001442c489102515025110795400307036030340d0b082900780191100c0c0c1007151b0482051042009204607a00000b0b281e40d101e03420300344101c09039200300d111801040400e030041c3c000355002403021141d500540003402a51528070039410000111044035032240e041e0106200707a2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 786227329 1250 786226079 786226093
    0xf060c030c0a02010f050c091c230a022707050f0a0f0e040903020106050a050105161e050d020a0c360b130c0305060d05030a080a060e100620 62
    0x400e0310500100302d036100701c1c00041114030703044603124101e4104031468601e01c50049035100b44c9240180c90801c0200e42c1046a101001080d1151a060503c07140c0400c4024400740e800011980107204200c4d445400600c6000711541121650426240000161608007400c500191009006600307441e040ca462042050900300c40310f105482001103608010240500341c0e4514010340d40714000e01c042c65102e540003040603841d09091110701c00807030f005a41406010f001001c0026029101c60441c50381041000e501c000c150141000025041c0102411314054000c0c010b8445400140c030080700d5110340110003400341e407030381c51100202540303403402e940b488417201c61180c0203820b0358040100301c032074280007400811100000d01c110700d04004007100300744c865001c8000c40740c141c840c0544c404400c1c1c9440e1120440384d9902900da00c0b4907441c2c2c10a001c5284013203050740d980b6038001c41c0603006030703903030440c0505041e0f644603000800c9105040c000f50412207005142610002c440214685a1004000c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 786228579 1250 786227329 786227341
    0x30b04020f01030e0d030c0f03060501050d091716050705061903110903011410091b05070c0506030103050105060301050702070807051c05011b02121e0d0e0105090c030f060c03 77
    0x3801c001850814105922880011040e4105101800080186441c0050f45000f8280d001c0c2c560020b50f4016001d0515210040216903000412910350354030020f80000c0205591403c4080d022131251000e0381c00001042c20b01c248041100c983c181d690240c030446507602d5aa00c20085c0c0c520885002d00c07590003c1134060b8200c0c50094012112581420700e03568148450000820f08540303c9001e843c002001d803006009180c20054001d40140c40b0b00e61040c410002c249004a0091552040d14010800009003071800e10080c3e90208014060003482580c0e607583d03034203005010f804182e030390341e100354a400c02081d02c050000400004444d10300024000d41ca01e04002c000440c803040c0c0c003442060224184401c0042c03406e204895544e11202c3c2c0340981c403520340d64024034024501e1240c01188008000880c80a1840d50300342180e11341096007036a441c407030b4000c6007005c0c110401102c4039640c204000e03c180c0d0b80000c0f0740c4500404058045172880c2c25803800752661490140e4200c0d0b02e040041000c0340d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 786229829 1250 786228579 786228589
    0xa0f0b160e2416060b090717070504080709020301360e030706020c1e01020a08060d060b040c0206011409041109040f0506012c06131a0409060203090105060a030b0402 73
    0x7110704000780940c1c601e5003a2160b400c1071940019403048450000d030010004210b16441182c5485030f0540f100b9486151804018118032603180c004188460848000baa01c0c61054080760090802241a07420203540c500d000c0c40a50400e006416a41e0090011403043d1f01c440340c07604503020304034030046420411030700e03001340140f030701e003500c000079010030009c039408a0420b0008080c00a04c0c2c10081558143d6094032685e1ba1980302e240000c5030340104010420b6030351081d44142c1004080301c03846d081c5101894904010401e902c0a01c0c1c2040c1441d002102c160b801080305412902c2c41c1002e0326460002504222282100702d40c010000c000c007050103246030420074000342c0d020b03100d40c480c005814199100c41c0d107044d409134000d8003190401040c0d0070343c9008056146200011107800d642040c03c203540010020208102c42400c50740e03540b1508885600f6a20480480810250040004101e2410610041d44c0110b0300ca080c19806c100105e0064100800220b044a0304a45d0380c458a444179405c02c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 786231079 1250 786229829 786229849
    0x318040905070e1012080406030c0507050a110612100609091401030813080f071a0c0a020d06020d0f09140604050d03090c09020307020c0a0e072f0a0f0b160e 69
    0x301c1161131007480401e807071805418011407540944201500c56140102c010180d901550b2448200b0400b80491b10003e100012180c903020380c024941080d800440300070588e18050554108900382e80b0f0720511844101c803218200503169a940d035801c105840700200411f58000c504401000030b441401000850392040152540c1d074054030402081030747e42c2210620705101c4040c014ac1c240c000d11010040c021403550b110710b080005021640c03d00200e881d1943d00c07113400303200190040c8181d90310607082000681c100e170b04e070608090301088142e009401c9200100308110701110a4000d40510400310b035000191240b003991300c10001d00d0600d4119008801901c0701e55011aa1541e0a03040801c2c0c04006001541c8125025030080072000c101c08204000c2c2c09881c4d001d400c0e070642d040107202a0f90b0380249078445800948000c403500303020344508191240780002d408035a0f8001ca41c00501003109134694105d0741e5000d42071280d010380321110f1200102404000401c0410950300f114151800d141c0040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 786232329 1250 786231079 786231091
    0xe0a12060e2104061b020d1211030a0e0307121e061103010e0604050f070203180a030b01080d18080c1e04050403050d0e010603020f040518030c0318040905070e 70
    0x610b4840680c0000c4548040c00380c460303507003000408039040c0116540803000005403041c0c1240000c14018503000708540d202c4c40c2802602200501d07006141c0036004506100d00380d10160102ca91307854001c000104225800d8905910900410302d00042562507038051401c03864100241d81551450760004801d0f400005c00308903006900c80900760f138500300ea04090350090406c911041c0c41c9140100401c0101da000515980741e400140c0b040c403014580c00000d8a500780104243c601c0e50090b48800107820442c5903100501c3e00c04c200c0e00204440002045001119840c1c1d12403c84243c4d03890305911600d00c0701c0c0613002c8242c1c05900128540d01d0510284156940000440c6010b00d502c2004203090301c40c1120140c000c6038001400885401c0e041c481d0340c500b80c10765402081143d055900141c00c0459190105101e10786500c00708100d264800c1d458401b580910049a03503610780b040d0250340700d4020000c0c407000c104a44000d000541004c2c0100307414194003602034002142007003091450800003802c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 786233579 1250 786232329 786232333
    0x40608040218091b1f050d090f150e19030c0311161a040302090414012a1e200c10020106050307210809060909160e0a12060e 55
    0x40590003042c2c80084500075242e11000c0c21001d070006601d220350408075203585001d010301c0460307031490b0100c40d24862a1a0103500d40310355111030003202480501001b40c405441005940000003c01840010100b07104520501c10f0000c043e2681503591182d19101440c001c1072440c4e100840000d21640020600720710030304100110003031042519107000703425204004042c2007840240000201c840308e044101c0e9400030031500d003d09540c0850190341c0090002484505402c50003007841d0070a402a072100c02d1141283ca007806d0001444c1c4c00006081d40c21000420005100f140d80e0000f880403000040f080d03601c4038559145050b080001c074140402042c1c40f98004c44041c02040d0341c40400c00e61100640f5400451100d040504041c20706040d40c0c850115211580b80c01200784100280b030340c0f4056080f02c5000c1d243c1e925400400c10701c5c85101d201540c0700070f0120810248a007402c600e201080e0142d95a4103000c0c03662030500c21445440d0003081c01110009000500064541d0052240c145c10601 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 786234829 1250 786233579 786233599
    0x6010b0708042d060e12060c1c0605030d0504060801080303010302060a0f182c13080a020102040b2a060103031b021203030a092d030e0607210e150406080402 69
    0x80150946401c0d508550009800d00d1280c0781289480780d40120022146005001f007818015800e020910a00b444005503a11f14907440b00c1404e07090f803002c4010040138003561420011594001c00035401805141d000c200c4000010030500c40000070341341a0b80d8003410300f0b403901045c00c105a505850910201c1c08005030240100b03a804440e50b0300100410f007240380b0301c01180140040340000080d405c3d131442c00072105410000c481a18501d1000515007103044903075200d18450b4200d01a21407900006d51000000404d03211020001000050000064540c8010640da100500741c03921404c3c4005000507070040380c621000c0303101c075580f445c0c000d00c0280b5001c00b00441640440c1540c00c1200e00f070007038980c1c40c040b64050003041c0d000f2500015a220381103910f10504080882c0c0b0f04401741c3c002d01000f405a4481107035440b02400c480509030400e507000710701802d01e00381c041e100d644c00d07136024002000450342c03c8140c20134242080c0010320311544a814281040340c01c44400c0da000700240d91007030345a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 786236079 1250 786234829 786234899
    0x2070f080d2016060f030219080c2106040609140705091804050102070c170d200118021e0a0504020a02010603021e0a12030507110a080d03020c06010b070804 69
    0x11500006010f480801c0e00c04030320309500944055128440441810b0041141030b00500d005121840803240d07600304010030b5213510506400314000d89813842c1002d00540c01403003050710700c40c0d54a03120b0b541c119020311106031604901800d540c2400d02c150701c95140c9a000c034809500840207402804006444402a54000500031520030000e960607039442e58000f400100344901d00c81c006000e408144101d03e980b4034650315055940d4800c00082080182c144417207044030310b01600c01d080114a440090000c072011845c1149032181c0180200d224841020f082c0e0721800300b8490080400d2002006c00c86402d14100c00e1001944c0464810000c5550f907080c04401696521101110000d0407441c0c140c1c1500b10a052040703480c22900081ca004040808200000b6030101c00c403a5482d500001013201d103810a80803c007000d4594205c0460350054002007000503038158007400c00102030f50103c1c1c1d003507661b03004e03040058031627108060f1002c107042100303021000651007032400c0340c80c00220303210f0305d07848030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 786237329 1250 786236079 786236083
    0xc02010b03070308130902040e040816121101061e090e160b03090d020a020f0607170c0d14030601090608090c0a0e06010201050f10150207030c0806010602070f080d20 73
    0x140c00449204c2c0700802c0c1031102095080560002c0c040c8914114030b4541043d00b586003500c401030000b480e5400004201e100401a0094040c0280c1d00ca400740e415071000800191240c1120581142690710380310b40059502060b0f07070b507a907442c0746945543c81c0d10360401c0d0042015110341d04140d02c640c459600400b80b241081034110f001449050a00360302d900b40001100c0c10550040035030130031035200c2c150b29030140e0341d0a0307012141c015085403e10f54039083c52405080540040410704204040400c2181c14083d0103ea01c6045030340c01d6840c40c190105142d40d10625020940340c060000700440d07414050070b4040d088080d003080300b0101721069000c1c00c40000e103480035260824108401003005002c0c1550302401540d8114400f00d50240d1207103860b40341070401c0b6485103e41c0b22060364800c1e903a00c1c030a00074004013020319001240440c08644400c0700d90b9a0703100a2064000511a00c40d00040074200719280e071054801d000d000d048400d180b5407040340c05603003001c1400c1f0408640c1c1d003110868101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 786238579 1250 786237329 786237343
    0x908031603090b21040218011412060c0313031b08041d0f0f070e030613120906090b0a0e120a031b020d12030b030609060916180c02010b03 61
    0x101100c941162406280040c030b2050164894400d22506001c040d240c45a0707203852400e04941e01d4400140f545e03580c000190317441200984503000400c43c00020400054044050812103c141e4450244d000c0d24102550b07100c10403a8202000c01e014804901e0790866002240d440c0ba00910b40310032180d2019801c50784181e0314134001c4602e4100020200840140c031000019030303c080710300b251000d240451100413203410040c07000d402c0c449000002100103000c1d0100c400a20310260403600140381c030381c01d0401c0c3e880314081c040c0c074103030014504c1c454220720441544040d03c00380e654440382c152400070080c00c550032884100c401d0054242601d89251a000700000008042d00010500c00d60203040140c0600c0a4480041d080c6141d40c00110240c0c9601c1c0c080100b80b54481c01002d03202405060490045ca0601819a41405240305101c85a03c0001340b807030090b0405016107591100f030301ca140c10000c1040c41410011000200c03001c00d5281540d1001d604010b1600000c0b4605080702d002a00b0702d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 786239829 1250 786238579 786238597
    0x305070816140c040c080c031522060e130218091e0303041b15080c0f030f191401170a140f060105100813030c02090103030f030f050f0105010c03090803 67
    0x80240f0794a000d600c3d181c005d8000e0140c0f681401071540c1040781001020707100003003018180c1c0080c07643c1c0d814661101c8894401013803000c20710183c0703c000c1c548070b0b50241040744a04501c1c070b440700b00814140c44005c002d808115a0080c0400d030124458060703425841030007012110280216400643e00c000003c48011201585502a540e01d00e0300303281c503025516a40702d00021300740d0781080511110040203a09108811141070070425a5500c8044808511480c000b895130b0f50000702c20300c4040084040040d008540120894542d00e200c450382c0001c580c51002d40358040c81490004112040440c3c441d054180c4902041d40c0070300c40035480b0400f503c0c0c81614065420350003110301001507041840103e001d070034121030b0380108a0450f040204546409000c064000c102c00b00000f0405000d0b045000d1340e598080c01281c5039683d40e08010342200c1c000c00503200464101907a48807030708174620505122703809003032594045901302001106d004d00e07000022002e0205912012443c0341c3d0070006851b441d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 786241079 1250 786239829 786239833
    0x102070308041511030604111608090109060e1806010e031e12090d03030c0513091406091303210203040b042f2b0b061c030507081614 59
    0xb040030315180d08030300041100b8100161421819805001c400070880b500031304102da0206000780c01404056940c89454140d101004150450f1820000107501502e2510340036200d4256041da02d8a041d23581005e41010b45920034500802031841e603024201c80c5400480c10714102c42c84081e402d001c0703803410b5103201c3e000d881c81c09030454500b04004108000c0041290607044a030404640101284da03080e41c1c810f00070149504c8040640301c1e64440c006584000c1500080e441c0c0e2555a40c00d0b140c020f01d80d640c0185d00c107070b04042c0003450900340180380c20b0141c1cbc1401c2c84003400041d2500c082340c03810000b16546204207000c8002c00f01c2d40b151800a18065030003030060303541a00341490130405180b0381c81c0017a640c40b41d0740c0341c4040c901048001d041680c160b058500031041011800c40303400e041400c0e0382e501d43c10601d03211028144204404903511500d000d80f4042c0060203140300111031059000401400158200000c000069100001d441c0702c0720b4200d0007540f962440e541c0e0008014541003200c03516 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 786242329 1250 786241079 786241081
    0x2070203010c1701060201060b180d1205030406050601031a090c13240804021003050702150f06040b06090d110612190b09010e0115020a0c180f0c050403140f0102070308 74
    0x5110040e2045004100c0c0b1b0000300715480c41d140d006043c1e8081c0c88004407100156480202d095255558a1501d0710360011422450544c0070201501c1508299002d8030b0140c90480010140d5000e480340c00083c0600100114502d0260360402010744001020b140b00140c00b800f1101e40304031200f501d10041e21420744207000701d01100c10011651043c3d4200a010440d07804280409a142d07822840c0d80000d031440e0200c0d80b50303104a03050745012061714508905075103a4080041107103141490314000c9600b201c081c0302a040d4182082128010202c0c080d90114081c544800010071502c0c00d5240440064202d60403c0c50141e03051940c82c008449602c283c1c600342240e100100713001d20aa80c695a0101d42101155050091281044105000d056104020080c10703036002c5008004000d0754075030017042c0c1045242c9030000c10880101030101e1100060400106061841040c064402c40e00241e607515410580756407030b003a8156041c0d9052507001e0007503005401c0181d00a00042c001103000780c46407010707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 786243579 1250 786242329 786242357
    0xa03080a030e1e01051b16030903020d030509031c120e0a050106030c082a222912030d110c0a110a080d02060c0307020c0316290403060f02070203010c 66
    0x3174800060440c9001425105060291006202a01c0c44014602d91000b8154a1031030b040c0c4001c540d64201039881310301503d45000700f652200c020034842c90141d0540702001c0c3c1c00c2c581c214040102c0703820240402c1c1010045401422240c0c441c80c038581c0098122010b912480d102c007401c4541940003a905a82100014403160320104461a510900d902010b00303560345450000c21903800b203d071228810081001d000c1440d400101311048110403041c01080040f85980c080145050481c02400c407501d500402642035242400d840c2d060200504090352800882c1080f040c024111141010001401800001c008503c10020802d03801c3c032403072500c4407150a00c0c040004100c101e40c883c041030f900c00240d909140380d010455a0308104e44d441c0a980320345440106a0901c1642501c1c513070140b2036468400c0106444102d0741d4202c03400080d040e43c0c90100721980000c00c0c00c00066500e1605000c00c001c10005400b84d000d100f035140d003074000504007031a5a0009081d94404006140011400703000ba43d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 786244829 1250 786243579 786243581
    0x50c040c090e270604030c020f042301090b030a0203190f1b0905010504180b074107030c030f02031306030b01030e030307140d0204050405040f0b010807050a03080a030e1e01 76
    0x410084483c010200703072510f658024002c40804800a014403136103e140d042903115074000342d102d03d41400c0b10f085103041c0c032400d400700e205007407190454150420460b00c03401c7c1004902d0208103034024001d0000d9014074980741e04205807855086403a0301f00d01c2441e401081007040e0600c16031183e00c0c40040000e00c0c4c594484142c580c103070030051003207203418550002c2000082445844a912006588503aa0348850613210b0320300c1c420a0102641e60b156070036a001c04154149413a407481c05e090328101f5580c60b4010501c0740541580200411444400300000c24016644042120070a00c101da107400d00f580c001064060040e841040825254a100031881d81c040c061280012022401182903141500c0014269200b01e585c4d0035206000203400c0c4e04800c000d030100c80203410040c005112900701031520030031030240d410003a1403800708000080742100004c5824401c803800200503100035070035074071880c5040d07204014000505685a801401655060001040b410440c00000c08080b0005a60b14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 786246079 1250 786244829 786244891
    0x20f1f081608010b0a0807031d030d060f080a02060309011b0f1e09120201090b0313170705060f0a02120910060e090a03030c2307021507050c040c090e 66
    0x20301488030031401840b13840b00c0d820940300c020003d89014851b41d05c038020183c0c020804802c080c00c7d0751484410070400d40070004001c14280100401c10000342e6070701c00214440b1011801040c000ea0480d003c0c120161400401a54102c2e8082000040520700c59110000a0f14010070031070110300e080e5140c103002600919020b415607900e502c602000d101d0310500030312408107405003448907499140075100796480f440218001e0034800c64410760f039040800e140c620075104110129103d14003019100713032500a540c01d0310703580c0303901400a0400f512040801c01e40794100400c291651982800451400000700c0200d500448001c005480c00c100c16808050507101207401810b1075041010074406201000989103400d40d4141c5000207581c1801c2c0011501c0c8445400a6401503504001d880c1600401d400107228481c4201d50000d0001d0760107101d411079002c0c142c00500ba680180704c0782002400c103904010490701c05480c0c44100d080c4c07120014003040f181600c0d88142212086d00030000080007003028 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 786247329 1250 786246079 786246121
    0x2031f0e160e10080903090307080717070b0306060d0207062a020102121b1b010b3111040b040306020705070501090506220b041202101b020f1f08 64
    0x801c84214010034a1210403c070782c00d041180000000764141d005006882041038010291400780340d40b419929510b4265000f41103c0c460560070aa0704000005038201c1100c220601131400d5544803c1044900d401c0201e0509042c0d0f020010440050341c103104540381556000e40003964044819032903512550180d41c250150781c41004959080101d281d0000d602c820800c200102c02e100000e0b0000c0d403801004045122003030441c40003128640190000c8414403815150352000d048049602c4036080d000e00c0816426441030100c0300841c802c0f5030850144c0c8400405410b2402c0e039240442d0740243d00135401035a0050380860b100003004418440340c8001d1500f440d203d0313051820000010b48031b116100000305140c00c181303030b1003c1186240d0f9403800100301090b011070b20342e569403d102261a92040d401c0f48180ca03807612015500340544100e0841e06506040c06c06000166800c0c04a0320703c44980d41980312043d400b82c1072403a451040c808907054a00d64900e14281070403407020703800c440e0781d01c1c4c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 786248579 1250 786247329 786247337
    0x307120b03100b030c1c0b07140a030b0a03170a030e010603051f0b100c031e050a180e011706010603110d0f0b0a09020307020d020c1302031f0e16 64
    0x40d404256a000401c907025034450440001c0f81480c00300005c1c68041c3e084111600715007880505040c2c56800503429000380d006500c13034070165650b00b00407074102102d1044a4a042c07000d2064a07990780c80b2740d0001c906c419015144c168000d44a440752500036607402c500348100d035400150000300c0ba40c580122403a0200e500001d12000342542d48140d111a072103012103100041d28031860220a0b80360f00089007500c5c001d000c02c0100030700e140b401030201450340d40990108200341107a1180400e02a285000c420455843c0c03814403204c440d0849802c2540b40030312100000009011414800320700c001c0d4000c00140c00d08035400800313950706506165059101c04c00381860108051100d2004204484034000c521170005444005044c18000610107032880e260010040311006c580008150b00540c020720894003118401e031045001203903070f200d010b0105074001e400c0130344401030007503907802864001085540c11b07407a000c10000341d50311544007540300317950302001c80c01031110715480c4c28407541c42075101d443c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 786249829 1250 786248579 786248591
    0x80105011502011a27070909110306030706050d150902031008070f0e040218131b0f0308030403090b070f0c0b07032f1e010509240c04090908030712 65
    0x30900d13200480884141c050a1008100c0c045000b101e11401010390300f042001c220ba007004800105070845501036070303003411318055007460088001c0096a214100003002000c40301c2c01c0400c1100d80fa08041c0700a8080d54650305104011458820314078003519503210016100d2811692410810400da80480c1f00c903046558140041c20f40340e41030740181c1d14501c140e41d44640715031012408050246d1a0380a9040f61102885102000e01000c445164002c410400100d004105105141d0202e0f110314020840140c0e070800000740803030080c1da401030103400c24a800c26a60905900c503603100f104110b03591150014032004112090051002901e007410034039007010b040ba42d018003840d10301d000c8005612801204192180c03c1c40c100d0081c0f000a250549200ca01c0980c02801400c6600440001c7da508003070024911075400078a607203e08040050040d44242120310034014100c01500c9440e903c0010170000c0b1b0541c555000f060801c910664600d82e9900e0821030080220b121100f0840040381020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 786251079 1250 786249829 786249851
    0x180b030c1204020303250201030b03071206180b01080312011e09021315180803030c0702211203070e0f0f0103021c0f0902030d030905060f07051308010501150201 71
    0x1605584000d07640788050003403901c0300d0002920710301841003608001c000c3d0402c1c4030321411348240302c105590700c00c2e00d084c4203d05500f001c040c2c41d510ba40c0076584030200050b1010000c5a201c1d0007401d0800c00f0b90010210500d11a1140000104240c004c0001c3d03900001c1c1b0341907020304401009005001801d034841c104d50801da0f407006220f03820b100d000b9180d9008640844051001c1e9a440024120000d444182584c0c00300301074241d410000b4102210070015400203108900482224401e820405199281000907401c020618500100e10110921080c80c0e002d10404d0070003040380810f80a900040d244d18100c01c001b48240074040b460f60003030024509144091311800d9035003400141c2428050703101d0b03000490074150300404008401c030b600d003040c071043e10440a40d031010407054000d90503110504807845094040c1c91403003000a001c4c6c0c0c041000119070b0345521481d81d070400e980b454074510f020001e1912480b0748081342c000c0c00305070b551400100140031a0b65201760a488170fa00080c0281c00c100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 786252329 1250 786251079 786251101
    0x110301170d0f050c0f0f0607230a05130b22050d02010c0b19020d060614120a020714031c1b0206010b0d15090e1203160c021c03180b03 59
    0x81a00001d005011524040d1340e0800e1004001c0c078072031130044440039034080c51015540c0100342c6071803000c59003105001491040213a40800021901c0d05541e1400d55121310848496003d407440f00710001c1d103a400442c108200344010950107544080704040500c60310302401401d140e65006a20038002c03031741100c0043c2d800046080034640c00003070840555a0350100d211526403140c420055040c80040c240000302e0b256400181990f4181d1340301e90400b07042c2c0b0781ca00403610a42041481c406200c03400039152001c1e07a0000c0034000d100709030650320412a004c2c1145103400c00c0074007840b2030400d85500b185240081c8105840f007a100c400010020704100406034860106000c1c0c5801c5400000c0d04d5250480c040e0041011386001081c04d54072103a403494400003e1581845071205130280c01040d800325403c40003640d01440c243c641403840d14245003c16560015082c0301243c0040b06800011403119414055334451030013600d684c40001c0c0307a82210000b81030250031905001d031050045c40864005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 786253579 1250 786252329 786252347
    0x5040213020702180702030d11030115110a0f03021005040b1906050f130b060a0f171608060117090a0512070c120c03020409060c2606040c050904110301170d 69
    0x41418020794030341701c040c0101c0c11441004040300550b400d08000003c40c1071090000c504a034065110b810360304082040c1196000090a0400d00c2c41d03010000000200700d442000b403941600c07a0040380d810302c4030410180300b078503012078041d030318146514100034403600c1c150031941c801c1c2042d010030040e01c0d082500044414685035401c600078260100d0869061401707920180100b0b9009107501c0c1c44600c2c4136001040d08000f10b01110005446480e6511036032564000345020b400d000001501301c80740c01d1412200d00c0740013000c06041002919820500d03910494566001d011140040e02259669041c060b2070924a480d41510641301003114501084a54108034291044400c40b040701003030500340b031901504243c2000e580039141c10309060410110341d01c4000c50f02e00a480c1d00c110b07546a9107180c004007040110b000d8000060900040051909900ca400448014100a414400ca00020804032003074185481c00070400000107000c000c407500c071039079100b500e5900104040c0c106800e00805402c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 786254829 1250 786253579 786253609
    0x90906070311120a0506010f02061306390e0d020a090b150307030204050a14090a110f04030b04060b0a140105070f02040510050906010f0905130b09040605040213020702 74
    0x282c0c6211404a0001180072282468240c0e4200d0141e0308200d1301400080c0000e5a116021030300c420b14942c05c041c00800c1130761003001c0703044d4641c03091810345e195200035040440940c41d06107480c0e5060342c440d07040e42441030140d4a11041c0b4814003440c08901a201c40c0151096130b1103401b44009040050380c2d0f000f220415107507450008a18081c2250101e050522000c2d4011005d2401100300160301d41d0550291044403011941145d2080d0380306e070f8556290400154094105000000060210116400c401c081c41020b40ea214501a190380d190211a0019001202d0301400c2c2020300c020b102080c09502140320b800c42d00100968074001c510400440441d0341d03503050005c04281034090240d04e00200601a0700a003043c84145000b1200104603c2c440c02a40d101d100c00c0d401103503040d48504000c00280090f034903100b0360f080c1007608101c101c0191284009a50351180d0801800d52150407085026511421000c1070701e00b428410828a02800d504150702d03140705000380405a81d0b030380c004031501c00d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 786256079 1250 786254829 786254831
    0xf1703090607060605090f0405010c03090213151805040c08033402040203010e04030809030a051215030a1406090a0206031302010e0a0b18040501051810032f0909060703 74
    0x20340340c3c0c81e00c10040c01881e441103074010403201c204450821426401407045215500800c41070308120b8080e0201d4050410113508141075440581c0a4200c40c0e0100304800881c180b00045656500c96410860070461400744200d52207000340310801c1054804c40020f070144030040c50810a00300503060400c0d1118003040c2c0c050b02100c42041424440002d40d09038190041d0080d5603d41c0c494800e0702c80541b050300c084001038103400c006065090003200740c80000d4a940c2ea6507142c50740d604010040c004014180306915038000484c0621613034100072440107240304010750498007a00c40142820308200600c1c0c02c2041e04101001030045c1d54803000c5030b038407007d000c0c41d042d003680036400105d0b944a56032000725040003440b00c000c42c4841c070000240c241060101d07120500d2140043c280001d5030030030b2152541000c00502140387c0304040d0100d050f404034030301419043c03a0b82c1c0c3e07488030b410f000180703901c0003c1e00c0103801c3c03905280c00b00d40c50003162808003652201054201380310911354411004001030101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 786257329 1250 786256079 786256087
    0x51002010e06180d05180904031e020c0906060c0f1903080106080601141c09110406091e0506030307050d0e01090801090b0106050c070503010f05071710091505040e070f17030906 78
    0x2410341e2a00f5180446c0180c0000709074039042c40c2c090440f41d40e25020314155082e0000c0082180c1c4001040c450210014082c9e1000740c403201d044c404560881d080c90040b50041405003540004100004074480130341241e50200e074046414050138141041c1c10400c104030f07082007003240c0d0f03980143c01c1e0b411a0a1203014190f131040a02461512840180810030229060440010501142d5020803050300710444040040c6c3e40d6900c02c0c48101c1e10070045510000c8103503011182001210b0b800590b014a014040e0303031600800390b9542c1e04119580340100c022404071140c806480d44e02010b814049d0440310000c00a40034a91928030704c4800c148125010402c0009160500300000d109501c01400301400a0007002070100d040f40c041c00048a083d40010070044c03e1301015044040702c0781c01070007000c00d0014fd03a4141280700010700080a010407266005050009803525035209000030390f1340307810103004040d0070721044000301240c0341e00070403c81030140c4100e00e04403404412601280030031107420b541c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 786258579 1250 786257329 786257347
    0x60603120921060e0618010f0b1305040201180f0f0509071b050313090b030f0a0f0f0314040602010e1203283e03130201030b0a051002010e06180d05 65
    0x7400c400d1004d0f000c2030240038184800c584101c266411500807a00c000c2c8911400e015038441103071422034440740e12804950061840e48412707405a90401e0040c5000789148e02c01c03e20f038207684400c90b40002c1196001500401081d038404401c0310103040215100f030080e0a02c010000d151a81c902c4100b91081050780c10541002010801c8411040e51114590505513032881d208004102202c817407402400391920450040602092030300000c2e82c04008207032403607459211100611017810741142409181e0301d4940d2528a4440a040100960750004c54194074207141c43e420002d1a8100952800342030007400794102d09007280f2002c11036051801d50000c1a9600000058600b080c1801260326194000781003180d9007420b10f4403284014070003060709003190065003a140c8012070740c1c4858005011110801513110340c1159006d00802090103507115280c17400111074200e82003030000940e544a41a00b000801440701d10b074010100480300070741c141203d103503a031a4202d60703c02c00c0400c04001456a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 786259829 1250 786258579 786258581
    0x50304150e060a06170601030b011802130f080c010c0203341d0708010308041a091003020307090b040b03070c0c08010504080403020909010513060b0d0f06060312092106 74
    0x24450014800c070b4a0b00d0909402e0b81c0000c0403180500880800040d10500070100005810f904a80d030180b43e17403401c1da203080c80d0201020441c00e42c6403100fa4080002c0049220f07031130a0140a8021540038404003898003c40c140741036140d4404505003d42c420b90107001da0750100341900c3c6985003441420503d2001c10154220000190030714032018800c1c400442c501c4104030385003d42044d0001030100c10b03110321500f80d800c24001d00c130061408408110502c1000641e1070b480c090140e490b4410b07820010300b02c001132031950341e0300c1c03c0c000001c3d404010090443e03400050710300109040d20900d8541803c040000c0c00300d120081144040c0403100b00746604108820040c000104105c1000300050f0401d4900904240e216200c182d1080b10b0042c0400c01e02032040c0714040c01840501d0144815603401d50703d0307078040c0c15580b8025500c10b04c80e0041d00302003406000510000d510583c2c2c0060020f003140b40003a43c00b00d030001d219040240007402031180051007101000e610088981145007201c007807405070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 786261079 1250 786259829 786259841
    0x120a091a03040303050708130620180f04090f060b06040305030f091e1014190509040c0903030c080306031009030e1e030316140303010b0d06090c05030415 68
    0xc05502981050081055000d01450290384299018402da072a106001c4500d0403080d128103a901141d54107450000f41558003040040388100c42c501d81a05684c140030000760881002c90001c40350b018070345090761070541c0840680c058111010440140551543c0c2a0042d100500420443d61890810303440d6032480103860085a118003101d66508a440200941d5008a00b0709030140007030010344400308103c0040d080388242d002d1700d115142c1c1e1146204a51079010040380603040300302040501028414026103036001d00c0c0c5522016521100306091000b101c1c20666040c1c100840b401003440000e40c000c00045015420400964807611950002410440400c95925142d0b15007412281055088940c1c020f41c800b0440b1200010380046540001c18041144100e5250b0401c01242e080d080c08412400602c2d806401094205180c9110784d03440c41d4000c2e0448080440d02150108180800740201c001078018404244428941e8020150850001401c002d090801d80203c420b0980300c507038020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 786262329 1250 786261079 786261089
    0x901050a14090312060d021c0614011203050a030b0618030f01020c030a121503030c02090603060907090e071502060906091605060c03090904080315031f05130f0c06090611120a09 78
    0x881232040a20102004220140004440b12410501110540c40c0d000482c0f504a07001010300241c50300441c2c0d41200ca5602c256503030780900d580c4140c45003481c2c4841c4098030400c45254140540800468200b6160019032070100102da0300400c8030b810040404015a00a03d5207402e0088074143d0555442000d4558400d003160500c1c86040000181940b2102110009009480650240c1c8a803c14907444500440308500c681d801070508008085040d480052504401c038207841ca03c9031a103047c0c40c1840600a80070f001a444201804110201440316903049060300f001400c003486059000b005034801441840e100b1140481c03010701ea01e03405d00032070751102030007881c40d176081c5040c0c41c03c2069a041070b603000450105617a051a5103090000d03140c2c4014081d499190b00349414409942c014180c0240890b0b0106c2100004800080380410f07107c100510481c8014007290800c2001003200886030301440c2004030905a070700c1c3c014000310740c030003000d2000213100b0390f1a003105030141c41c0d040b81a400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 786263579 1250 786262329 786262339
    0xe3a0908010e010f050a0b0a14120f031b030a080601051308010e0604031e021506150c0c010e0d031209030509030d030615020c0a0909060b090901050a14090312060d02 73
    0x1c02ca0001c0d810352210000c0228098200101c2e11036000e580102d0f68103400b21500005040014051180000c10442403414002c1407480c01c42c208811441c01d01d0b442800d9200c0d2070380701058402e80c20341c40301451038044410070002c50501a00f00001481c810020745200d051110020760100900740d6108804050300c2d054000340140c00c040300701995161400c407829070014090414141103400b4180700c1040800d4264000e1018012019220841e080050409540100145188121a00000060100c07055494040d00810310300100141c1030601c2843d010384030307020b200c1c0058002500315036800c41c606103000c00011008580c2c5000d8629214500115506118180f10748020681c541c0001d403e03515038007080054034080740350a0781d4819200c400d003507000785100420f0011802c541c1c03158410500802010614210040104105181c01d40b000b211603511041000f01c211070794003a29442003070902c041295071030448515900c0380211103081c02c50412200220390155110300072030481c541c00a107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 786264829 1250 786263579 786263591
    0x2090901051518041b0c1119050603100302040905070611030901081f09060b040302030f0106060807140f1b061e0a0b0103060503070b042306040b160b0405010e3a090801 74
    0x10040c01c288a40407003180c101d14150311f010003505006221100c003071035000c44000b0240c101400c02a540d000200a0a640e4900107000009070740ea900070107101038040c0300034042c05401d269008040206000461840d948100070410550364000364883e440007421402010015550004101c2400e01d0740c41644031504110000c02c3c00c0080d5001407003182e1080b0100d8811000c461602402e0781c031079124180200e01d903040040c440358002c03c00d04a1502c0f102542a140600780343c55028580c02c540d03c6940640401c1c6682c02e4000790800000c3d400184085034454000c46012110308104030042400c44655214140ca0705aa40290008806000f00034203071100181c85600400c05604644075001008ad00303400c1c0e4424105942900e10325040c400740c0302501d05410f003210000c02c0c0e840780c040104c040840740450340200d104c1c2d01c100386c0100c0c4110700125588418022040c60100005100100d88901d404088403007090221546427414403420813129203c6125010788010a841d0301890040d400c000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 786266079 1250 786264829 786264881
    0x81014012a0c05120604050d0507050f16052e03110c0a050d03181505041401090c0806060307060504050f0609031509070b040608071218060209090105151804 69
    0x214414283d0b002911a240302d9003900500b81d035691000c1c1c41c081c009810000d60401c06510400003088118040d108540c14860324040c0c03e03141c0441003801c4d00741540e40d007a052050349041645984100106003000384074000500680e03100c821226a070030309240c1d640d1102a4540c000405460580405000761030408900b030600c0c584401212052070700082c50111001008600034000d8224240c1091244d01c81d1b540005200c40200009802a14022500340f864030f003074035090191103c4148500d04442c041450108020310300300000d42074912907040a0001e100c26507000c1e064030101c640840707034803a9103410400854600d107e49200a5014019441c5080342036805a044c940101004d20407990f841c1e03070f12000c031070087c013071400b80d140091000d00c041610140302d40d413440603000d9041c5000520010072100310080c0d5181c140201c40168000c60f08901a00c0c010101c940140010b03200700c001c90300340001140092192003441e0b03050104840203900c064445502c01c4403040c0b2200c0480640c0c403826 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 786267329 1250 786266079 786266093
    0xa0f060503180d1b05010f0e0a14030406140f1201061119020f0d030e0303031003060b0409051509070e0c03060f040b03030315130c0f081014012a 64
    0x4440042e40b807400808000541100018503400110741680d0340e11603041d00386110311480304100401e40300ba40d00c0764900c2205180511031684082a404000d01545090303280c070140302410030480e00d00a40003804100402900314540601031100300701c4241d603800c503450301842d25003d46a07444260400800000c10916003003103c0344071a1a03414201d40603541140424420300d811060001d4001d170301700f21030b441c0c641419840614268824209455002c5100020a1442e04111586d410000c40d40b001007041c000741c0d01c01c1d84440c0c0b500356814418807010b0b40700e0359035a110180540c41200d14041c0001c04190b02071200101a006100300390f0411300305502c0c6541c06400907610704c1d01c105000c0200c030b402450540700714620010b01802650642c0e481c000d11400c02c004401c8050b030480300452543c52010301d00e104204646080f6200d04e241c0744c020510050440c20000c01003201c50240c00000d005800b00c1c43c40180303144d482480e20720b80d81001200c40032103217052002c0e031207100d075103484200b0b04002c84 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 786268579 1250 786267329 786267331
    0x10912050309101a01030f0e100f060603050f0c070503041703040918020d15110f04090606020d0c110406080d020607020d1809020a0e03030c1605012c0a0f060503 71
    0x4030000c83d90301001d11010b0904a400189800d85601d02c4440e040305994000d81141c000071166079000110b6906407a101400c20407081d03d0002001d540f403a4400e0b00c00720a10503440603205901d01081140707080f02c0d91007071b012405840340518140102d249020800100100c90142c400f11224200b03024004045030381e65045400703130344401400c010a0b5000c05c241705444203041e0740c001f407016050794001e889000e82009850640003101f48c84081c07550312003c1e010000c10402c1c7d8800b40703007a55185801c5907002104c809800000454124000c00c00902c1e0b4040c065805003900610320600e90440c181c00200144071a034403a5205000703d9000d060481c0d00850a01d22507003264017900c0d03a80c000010704030b03034006a04504002d000d1640f58113110400066010b890b0082243c1420002c11402d02300007480e50300b000407551281c1d400f041c0c2c5500d002920008100081c002800c22440382d2038501c61303031401070b00300264117a9402e8000b051068076903182c540d560001d100e540302092a660700d90000903d40d40c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 786269829 1250 786268579 786268591
    0xf0a06090e01090c120c03110a090510080105060304060e010912050a0305070e030304030f02040b0d20030c060901210f0606031508030708030408040f060504082a0d050109120503 78
    0x200c020002590000900600216941340c0c0c2d10a0060f580c02e044480c02003103014850800c2681c0c0d1204200e0801c400c01c010000e0704e400351581031245103858204004140d034001c4c49801c000c0110010400b903150781c000d81c2c1e0002d41c82a00826100b079070410950040c01741000c050701161030030745600300c416080340082c4003681c0c8030b54050000380da961005072040108070340c8250305540200400c002050303940d10001c9590b44003c1020890300503000014610004d0346100340c82103e408400d0b0340d542d03c082074004090030420303405011400300e100002800b4ac01013a00e45418040312404408140842105200941c103002d4001c0000030304030801071000703080b90300800c40441d2400c2441e1a036a5150003424080394003041c000c45c40d2480325661500550800740c01107954420038080807540c2040301352001d016207103503581c090300d86c0d1500044515020340d2591084d01c04040e03440c44210039401c20342011442006680300034140e04e4901d4110f00415049001515442c400000311524651100007540200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 786271079 1250 786269829 786269849
    0x10209061803101116050709020711030d0903111e04051609080303010302241306030b0a090203040c0611030f040e0114120615040609140723070206090f0a0609 70
    0x501e45003660000c6450034503011100000034841c025132429048045d10f58075100d10141d90201b0307603c1030900c0c03d98021240849210400c407803480410304040200300804000c1c0e180001c90185140c0381c401c1440d0814901c0745c0504503001649003c2d5400c05203011503814054410051480c0c40030104401c01c4003100c2c07140028016071000141c040000003564123980e0000c0a0911880030345c50003042c1d00e021401080c01c0000103015003a0000440c0c02010001d00c41904e01280c1c004040c1d0030050200016044181c0701032060042c0b1001c00d880e03918000940e0b80301d041110507007100f00301c1246140240c41c0310184041c000100880e05a203e400200d04803105403512034094500740e82005440200c20030440e8a5621250014082c0342d689403203c44102c001400c00252262a0f4803090144d801e81c002c01c4109800399414000c5003a40001d61a504041a420080841011100f0020280714148000c1c2c032034040404c10207011b5962205010414600070020400300360303592809440c10b142407291840c030b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 786272329 1250 786271079 786271093
    0x80a1505090307030822020d08073309080d0f09050f03030f0a2f1e09030a080f0909010e01080606041406092a07052a12010209061803 59
    0xa0002c151258180e150300c07120b406540d000c0d0341c0710b000026031003c0c0300718070071210000340541c030382145c201d081c4c0c1d0084000ca6650341542c20702800d020300ba43c1101120030b60400c141010822141503651614035061404038080c800c90400340114041c1c04507517054a4503042d030030300c410700c0c665001100242c0705400740d51014501500721031702c900003142e2110b02110303404006070280038558021000410303204030b8902c074002a810000700d03030344060041000000b400101440030200308a040d01c9984034201300d452a0061010100703032500c2038131000911014000c56440c0c03c903c0550155500100d018206039010743e510120308424100a12401006000305400300754141440c1c0070703650900500d4840740580c0d440e81c0003444443d00e0010500c0c11a0002004036880010b00703200001c2c0c00d07500b060100d60f01d0310201e042c0207003801540004084205c044210000c082c8031100300b100314000c41142c0014105241301801400781c460400099400000010842500d816000310f4030300c0003000350100c400c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 786273579 1250 786272329 786272341
    0x8090f19060f1103011214030310090e0c060d0b03100c0305011d15010f0c02041d12031918050a0309030308060d17090102190b010e2202040207020a080a1505 69
    0x440740102e51800c0c2ca450104014440701c0003162001c04051f00c20f040c040b80c500b1035012100c0c00c5400903210011a40014038041010400b00c0c0a00c1e03003c0192080945591010880012058462000115074246d1548000c445d01e036401d214642c000c10700700406001481c620072004004200134001c8a032514025910a8503002c1c0820b60301c0c0c8504519120b05410311502c40054030310200403204541004145034000d0010384450180c821042c2e00c640c1b0170000700301a6a2550b0401880400c111415081402006207403800214041d410900e0031100045901500740c3c5240c02902654000c0c120b031040d50b40c00390401d43c2c00360040003142c0c0280d480e40450f4584c0c40400900d414040c10141034000ba90401280a404003001442c0c8030205004841c41085031728102d07595250242c00940d07444c1c01c040b00400441618000d50b9601984080345822120064800c011a0049040010380920380c041207100c04c40d146d8040b01c202800c0004c0469148112628107400704441c90b00340742e20110301300b20108003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 786274829 1250 786273579 786273581
    0x120c0706021608030a0309080714011b17060409050a0b0403230f121f090207060c170f0703020409050c09031608030f030903090901080a060506150a08090f19060f 71
    0x105a0344814003440c50603034180402c4007e4060240d096800040820003440004c040c20070f603d9242d00680300109002c180c401410a80d107070f0388020034040c031070002048010300303c1500c0c4140d8003d03002c850008000b121800d1036850480b0100c00100a46443e00502c000d150300101d241d40b07500050b0a03488070b1a90b01d064145014040c041c03a00030048800d2140e00080d40c1d501c030782140e0104d4420001d1400c06a0301604141000065010b103181c2980001c1c140d0500c40c95000381d240090042c2091303074800036004041800100c0041042341d08041990128400310300c290111001482d9440d400d00943c00c02000480c01e541c0540c1d80c00d13202c2c3c46083d00d00c040c1481041d50003070031a20054050341c04c0c040c0e10840c800484d40010140c01440c001044002c84070f649030081140031b845910010000a4042c0c83d004045410203000c1c203114908414401003080c0c038074811189081c20038948080c0f5616209509440d040c4e24510004032405001400100e02000d482a06c41d11270040c2c1c4103100c00783c89485410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 786276079 1250 786274829 786274873
    0x1050108070f17100c0c06141302010f0c080409050118090309090905010b1302040609080f0706030209030a0f080c1b0a0302010c020d080409020418020901021e120c070602 75
    0xd04003014194041111003c94100d50fa80c0340302c0c000a55400200f10004c0c101100c00c0100114081125981c0300e80c180002c511403810300c0c40c8074a940e060740d400d00e81c400c10700c1414400c00080c1040782c0f4178250504640710300c0c0750b0a0744a03489290035494a480f55803082c00b80400740240c0135540142401c108400142d4040c00560a03015103480000505105a03903018021141f001c2c0e40030b64985803c1c50323154076142d0503601896860080180c550b801e280380100300303010642c0504816402095492a055404103c00003250220304006980e2026400403e04203002000003070000b03d103404800c010704c001080107025100100c02610b040394070f100030f64013910740d03244290380d0003c10b901c0060005500401d40c007444140010800c0414080c140d40b100420350058020304000e64001c901084900c246807100002040300590550600b0481c5000039581c0c44050800f0001801d148420241c3d400140705842140c103d44284941d00e0f00045003403542c035009445620300600c00c03080004500c1e40350f80400c3c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 786277329 1250 786276079 786276089
    0xe160519180b040f0501030c09060509010c03030906020d0603030e0105071e0503070816020a060e0607200303280806090a090519031805030d1215030501090b0103050105010807 77
    0x10304008038000000c0315034900100007248682105000440c01400002c0548010121200c0250aaa09040004007035071a603414007018840d07644018003645030008241e400d100000c0c030f4221000d0141c0d0404070041c2421000c040c0186100052114540e40540c01080a0720300079121115814940c0d401199240300300c11000d800300c0c2d296413038040ca0604003812480f2050050341264109101da8072080107582c8400e000782c10181c88002c88004504100d50300100030101402c1c054005030004002c20110710551030010500101146c0f6140060f400014036840c0c82d00c041d04a03601e514144c0c0040d00c10000c0400c02e111010036184145075401d128500081c410f1170043d00071001c0782c82d08d40e050000350404140c00c03071701400342c80600d415042d00c542e02803002e94025550415410701c5200034003405011500418000c1d003002d424a00c40c2c1d5008200003080c03103c3d402c00021070b19812076040101c00c2007504010029400c00455405001c0701542e9941624007a000801051341c3e10305900381e44016512131 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 786278579 1250 786277329 786277357
    0x8010b040f030605090111030f01290306010503060d051002040f1a0a0f1b08090907030501062106030602040611121606020d0e062505070510150f0e1605 67
    0x60000440a804c02034005410b080081a000d000d019000a6070b0800c5a4041819000c00c00400600c803403003000040041e0540c0c0d02c00f02d845000801c0390a24403000300514144134000020984a0b203501000f1250346410800303031260728000b0803110029601911402407800042480032a401110303140211200c10303080501441e00e18120000c0c1c688407003440d000000d120003000d0b5815592800710151069900c03401189503071341d00280410011f900d02928480805183c00010310500b9080f6000c40300c15561840317001d281200f40c01c3d058024000580005003c2c600200b40020f105410110b200080c41c04441941c0460105d05c82c184154050b481424031802d5550890b0000f1a10aa004003500740200a0100d100303e40d60b01c10618011080d0340c44210345051120010408194155030962480c0500c0c2483c03501806c2e84a2540e1180f00b000615001992080200e1100c80d00c031251100410003a16003200c001d680300c074104010702c400c4940c40e840003e0904814540c51040e0100e600070002192 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 786279829 1250 786278579 786278609
    0xe010c031a010c02010516060501030614090a03080910020d053306090d050604030c050106090b01050316020304050d030c030216181d0f1e0c21031c020a08010b04 71
    0x110f415901c10741059050000401c06081102d00d49021500068007030040411594918900101101c0c1003a411900c0d80003078805002240001082106096030145050300e0181c13142000c407070901140c403028184035440054801842d0702c03260041c2d44540c5100b201d6005406010040030b410311018005007082800242588489240c5100503180030080902510454001d654a851409005980541c04034105505100c00c101c002d010300000f41142d01e1062000c15150000a4150301001d040445e03504c40a030300b02c402030341c420001da600509006009400c640900e0401620004030326509034014043c1c1000e800c03c4c03900e041c228001715100445016094000f00181c1b0000b054000401c100109000051003110982004004440320310310340500010301342d09100454401143d029290301c1d8010004032901507590721201044a40c800d5030744600840385818007800c41c8078031030f48030b81d070000c1d0030520a80d40440c65000e070031217213601d07121030a084c1d0b00da120f40d03c0745020b42c1c4100114a88080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 786281079 1250 786279829 786279881
    0x120a0c0b030c0a050726030f101404050a180b010306110406050d0c02011e15081b01121b171305070b070807020402030c37030902061c0e010c03 63
    0xc00200921802000401b0881c0720810032445445240b0410072541c00022060146000f406400745401109450021544519181d20104603641150855104a603a81e000070701c52060341e0400440e0b4450b203800403017141300d240340c0503d07071144c00e000941d440d603d040704404a001810301107906480107601e910342000c026a00030005031200341040000c40d502c13020344840c881f400b003d00075001c4c44144800305c0d850850f00c40020300701056500c101320b50b40c030842d00d00411030b1000303002c1a5210741c20320b000c1d800c1e5501019460040c2144580301c80c481d048054203176604550151450400d01503003203410f86283c4408440c40804e004240740944140c002d840300b04000b0b180080202015445480142c3c1808999000102241c108484a9203140c00014041120b45006a400082c2d85840e8000311a104a1480407003031481400c10200141a5107102600030340d500c501c20b517800016140001211040040344d81c402400d80e82c0580d09180d82480030000e00d00340a40500a84101c60581c80300b03078035000c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 786282329 1250 786281079 786281087
    0xf031318090b070504051c020f2b1a06010f0f0f0201140a0603060b01051c0c030906090302070e160c0b13050d0c03080714190e120a0c0b030c0a 63
    0x680408100e540d52405107200141c8800d254521a080b240c603290b0701da5180c003052060f00582c90411000c02c071048485040140e80701842d40c401c1c1802035419009090f1117940360034500000301c1149984002d0040b610341040040540c1048003030155023281169100c1200641e4a55603c03403040c404910451882c01c046480340c1c40711014400d040c400411ba100d405c298442e03c411060b0b401030881c64a0b01800d0052003098015101e40c5170081c078001c1c0c60500040301c1101c1032802c00009c801000d0305c03048080a010b120740c00504440350007000402070f84c000391401035610846840b400810b8048640080c601031580b844803004140303540c60394103171107441e0742d92072154142c01410207080707105035070403140421701c02c0082010b0019542c8914210510a0030040c0c0310748001020041040211140f03030703c180074614141c1d103c0c1e111511490b0b1103c9451f02c001c3e14569184440707182c22800c0100b2651024034000303064050a4064004403500c80c0c0c4030441285d06100c1242c901c0c112140400464859a02c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 786283579 1250 786282329 786282359
    0x1030f0c14090a050a150f050406060509061804141503070b160b2a271806031e0d090b090f010c051603240e060105060f0c07030807050f0313 62
    0x140000010b00100c0404d01c0f81c800c5c0c200d1f8000c20a010329001c82031020742000d11039500542000e081140c10101d000780007820720310600246000700449924505010b4449030444c4000c100e00200c034460601c0d10845030f0750001d001c1034000784280320f4082d002505e00c40103c12036001008a4990b102e03c1910b03610740800d0400007a0000d002c034814004008040e22003080d100301c0501007262800e80d01c0c044c0b40000c1d4450a02482070044540c6041d001c800c0075a94101100f54154600c0080c1003150355040009e130508006243c0c1c0b2000070340980400c00640401308050011640380d0b10f845100303544805996070340307011301e2450b9030700507080718031861003507014079484100d0303520420440700c100c5103400c64510182e0042d88100c6258440c2d030341d0b0b00c00c2d4140404440f81a607104805c10002d00c441d80445c50340e0f440d010310a05006034400213400c002001d042045520101481c070480301329640d40d14241220360301c0510203076820301071224034007011207012040303036200e14209034507200d1142000d400001d4074030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 786284829 1250 786283579 786283591
    0x6010504021b190201090f0b0909250519020105011802090303040b16170304020904080a0e0a08030408071e063902030c04200a05070203030301030f0c14090a05 70
    0x803a20b1642203000304030031103401d56980e8441d104a100d0388000b510700300990300544d0794100640e0040c460007540c40c0c25a9000c82045803400e00c0d81d00c901910f00c159071254200080704901e000a101d02042e00b060050404420b0091075111540301140c040f42241c0c8203009480d10301c1c2640000e41c8002d00550058480500001d0a0341d18260303860b440150540c0c40010310350300b035170040c03030022044c4800c041a81c1005e00c03038002c0c698510300e407560001c2c4081c840203000030030120300810324103901440f07541e80c40c26440006d801c0d400f03072503191500d03d9030700e4016200741010380c07003003182c04644101042c50350800511800c4106000c0d50030725000703031f8995902c108100c00c840d4001100314038080480b01024011400701e104180c0c001d1560041c14100507100307103c4c43c012420701948080f41c3c940c1c00100d198011107015640e4651002c160100d84511646902951503c008000403007401034180d4149182d51003101d9400b00d50741d440c41c0061030305801030441d40d0300034540c40001e95208100d400c950343c040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 786286079 1250 786284829 786284857
    0xd020903031603030b090a0c08040219050a03031718030711010c0c0e0403110c060d0504170a0518010e0a060e0d081c110c0c0112060e07110c0a03050601050402 70
    0xe0a5003085404000809030f00183d1102212019400c25070b060300c6d0402d0b40c1e0101071103024001c039030180c03150b8070140000b03000f000424244070701d1914800c09180607003801004038522540e030381002020804402040c0600c40c240d9004070380480021a51a144141c140c805582000300c2502d50507080c01c00c110f16241071010104007100010f0002c6101d00180000e42e428600364202410000c00004116121b80b040d1380c400414004c0075901c61094400074140c11101107400e40c0c491405400da00c05420440c24511400304034a01841e4201019028040500c0320f950070030a040401119940341c1010555008108501c040c0039182c86228000c503407a80c0504488501c0e0280d41e5012015132000346402d502c0901600744811012090142d030240d240c0031000c05d0f0412500100c04c60302d032100300740c0719418040d081c000b01c042407406030807220050080c04d03510b413514504034030080e0031881300030700d038074501c3c001c0142c46241c2d0318040303152a007a20b40050050141340c3c20141440000c0d8051070f01410340c9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 786287329 1250 786286079 786286087
    0x708061308091003020a030b040605090112020a08030304060b120a030801090506031f0b01120501050307060f1716080108030717030705070803190b09010b07060518010c02061006140d02090303 84
    0x161520182103c55040c00e0307800603a9049062001021107242d10121441076060101c2000385580701d008540c1581c089400001701886148005000704440340e0004880b0700001c42000140301503030784a03054a05054a8036407402c400302c10416210b0401d060000d0210b0340d8080140813824896201c0f03688002d015003100e6004003183c884102214402c10700d0202075841c0c0880c0c1c00103503030164515504000c031803020700465041a000070340710140d5019200401180c45051244184102c40c0c0b1070aa1460000703490382030504024040d40a00843c0d50207001c6140300c400003980c0c803c00000c071080079420516031480220f49800702e030015400a04400104003040c0926008940d00d4801140241c500350302e0030701d80841302c010f02810756024001861007040b03c10010402d060042c812110703126881100043c181e550110181c0e8268a101f001682561030300d42c1c80404990001a5140109801d10301540c0b066603800c811034403a01c1e00e0b154041c07800000d00000d0401d881e01d4000c0c0c1b1110100909580c20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 786288579 1250 786287329 786287347
    0x150918330c04062c0d0605100909050709090318090e1b0918030c03041e050a06080403030b06040f090506011d011409040207120f090902120114220e060105030708061308 74
    0x148a0403185c2910301d29511418007411811150054005001e862002d2000c41c1d89515050307218081d0340b0460381c0180d1600011000c142c41a100303040070100039189004520f480f884080003d14408502001c2845a001256080c406120001c05030020043c059030083e81c40b0314501e00e400803d4240215280300a005000b1040c02c28400b51000c3c00c0c039100c0c1c00c4040407480c020700e0035407200d65000b10300411001c4c4040c000242d00c40f0710a54083e40609000c42d802c607048011a51900c203a83c4000c5844407104d0300410b03e46c9990b00414001c0d07109a80c0c8980000c40f659000b0000e242000c9250301094010174001d41c4a605030000e0462050004c1c001402c0070204c1d1560114104191901800a04070101030741c005904500b000d070180c461180c0850074542c800380080c03007406043c0101d41d03a4689006602405550700b040c020240c1d20300200c40010381c40e103140ca50340640503106a002d50350003214000320b400e003000030301103048500c280010941a00c030300c11400b115004050b01078034841020450702e80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 786289829 1250 786288579 786288589
    0x60a150b0a0c150e06100f15050c0106031101080f190e0307080706091209030309060809030c0109122a03030c1215030b150918330c04062c 61
    0x100d00c1502c00c0042050f90752100c0c4c42c2e081160045c88642c0341b8500708014001581e084410005480c4a00402e005e0b04203220b900b52600e000700c14000841307608201d004010004c5603245003403c6c2d07070700fa203031004540c4502c2c01d01001d1140031503030a440044116908007160304076412103420350340d604003234074500402c9840d003200d254001801030740c00507100d41e903160402010b0304c03030403110500c5441e0104000d400e584e0001c0603540c1900c134a07002c001d0003038003284500800380126062000d44100810000d03140e031408040b0303400044071000c0814640d0016144554401000030441000405406c0028102e56000d40c001e24640b0740840401ca100d14074039524980f14810b8103000c5050120f010610761441c07500201c00100140020036101c1c03428007944603620b840c140250030000550b40242c440141c2c1848500c4d1014150154180304c019189400d11171002d000b141061310f10a14112056a89006894003036100724421707480022400110078250110314080c030382052480344107440c40d000a60380003c0e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 786291079 1250 786289829 786289853
    0xb070c0f0b070822200d0501140702031c1814150705070b07080a0e03040605040515190513051e040b0108090a0f1109070908060a150b0a0c 61
    0x40d0019003050500441540002200c1c0d130112000c030b019041e4610884e42074040c0f071081000140082404100c540c6402c038800a003008440c0064003500c403003040c90412a0290414080c20b0b60124040404100c4451001c4110b50001d1200103100b2503042d50002c050009019004805a014000916103000070ba02e4541c6a0850410701c801050703900fa0b204001269104090600d90500c00200700141c0003035144544945d000001703090900103640d500100d44e0160240c0003480039140800180468200e4101c00030b8026100300b0703030307880712681d0500d420304400d441902c0c8016035440c4101403102e4071500c40c500030310704083c18560640c4480c1d038070004203c6959030071044611410710288507215605152040c070b03841702401d00e081d0803d8280f06141c240c451759860701c0503140d890014185014000c014042040e100000f900c4100d10346000071004064500500882150b805081c01251040c002400340070345449840c034607140a1460032602d00c281e80d011443c403800740000c41081002041500307480c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 786292329 1250 786291079 786291083
    0x12050708221410200a14071409280509010c090f030308012c07080103140c060904021803060f0403120507050d1d0105010b09040b011409010509030a050616080a0504030c0b070c0f 78
    0x21b980c1c224062030607410700fa5150031003510000741e20400709040e9a00f0000f40d8001081d2248101c41004035054040f41e41c114a600c010020b08003c1400400b03c015440502d04040c03554605003110344400324220306000c2807201800040300c070360050222555124046c941c00340908100031700740a03038030180d1840303100c01c44850000c606200010401c0c42030f01e1101003200f010300344c003400200d25030b00700041850141c1c010481c080c0b64046030207a03180c444c80c210650b0100c80101250704500d054180440302c1d14088400318000752004400714201006030003500c1c0a05c00030f0301d440d41840c0c298120000200a940c10240145029211040e01d8541c203103e041d02818004009076503441340b8500303220984801c424694100a0b0460101c010070481c1001e40b408401c0c01d18120341e0301c001c484002486c001d03c042010f44603000ba5410721042d0046a071243c2c0060255480d00540c560b500c0340007100312801210060049180c40e004000059052103640e5480002400c0514a011254481d03542c000c0d030301842 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 786293579 1250 786292329 786292343
    0xc03060b040b03030a080103060c0c02041d0118030c030804020109180605100f09030b060a03120c030306050109050102061b040f06020a050c041812050708221410200a 73
    0xd100d590708260050342003484060703004510f4411180b00c01411003005110190100d55160184030b84d20340b180c3c18003103105400070414800400b542c505000c2401100500842a6213455201303d5121000c01c48480e13500d4040e15020a40790041c1c4058079010401801241040010074012504d00700c1440111480000450000380c1c1509040522840e5045100c140c014401007d03c0014440e47c050710f0701041c1c0f41d01c140031112070340315400030900d40daa0b2038200400ca003206d141d140360751681c000c2c1c4664040340603a80901100350340e48010342c0c0300c001c580a22030040c3c00580c00110755081c030311014a804c9400080641c40c00c0d68544444500828941091303006800240f004000d10404120150100364100d804100d614440d8032198009180f4500040072440902100b411050168090300c83e0303590050501035460b0304000f03910350310b6160508074000100c10300c003012405c00882005c0c240c1910f00a03014074945e08006070150360f0ba143c9400030998000c0508190164407505104004a40d441040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 786294829 1250 786293579 786293591
    0x180a080a05060105041e0b03010e0f0a060f090c060f0c0203060c0d1d03301806180d0507050a02060a03270c0612150807050f0121180c0306 61
    0x902103050140691000707126a003441d1095160003818898051010390346c0c2000a0b000c4403a070003003030240003000444c4007a4000c2c4110358150080c08100701c002d00340704240c1004420304228960084402150010309032600315201800482e0184a031816078032000c0c1042e103545004ca900003071a0020440d1107401c1080f0204941c0100c0d0620b0103502014058000c2014000640150044c0d41e40030f0201190341440c2c0030045502190550045800450400034800080389415502c603010520142e90954062042030001801807205030102440040000302078500803c2e005400c94045c1c218401c142c0b003d0280312000c500503900c4000500a4a80944001c40d40030310328403100891440140b08481401c5c40d802610000941016100c020f484003418034003807294900515200810098165015620541c400400c059a00080c0101240c5084071655a01c0182c01c0044500302d18210355042e10704445030420304e070141181c0010464808640c080c03074a0280329203a01d00c40038100d034030a6800239912070b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 786296079 1250 786294829 786294833
    0xc06090305041802091f0519180605030709030206130e0108100615140d0e03281409042a0e09010501090302010c03030509100603080306090f01030c0308180a080a 71
    0x82c1500f09402d544011800c10240c0000306000781000c03003068400205102902c2802030140003070b1001c100349403440c00075100d6030b042e010306070306c0310022100709001c11004000795080c4560200d80c8601c6850380c9451041d0300d990f0a001e000d80204039268a1608101000725500784001e140900030300d0300c100100540d96130000d0040442e03269402c00c0142c0f40f805500c0780a00b075044024080b81843d880600c941e242c01041504004080c5200c26090a000010b100054031000f00007172000040ea40e0948071881c10050310681d051043c01c03182d0380042c40c0030701050340700d460550b01003c0700a0105104540020000342301c0b85da207480c044242e00104007030496004c0b4905100c075085000d01021300b00b01d020075007960000b9000c003c4c107560040400d5286c0001418440003030000c000010b41503403051160319102d151045903034004540060080d1450000940003440c01120075048039000442180707e0b90941d2243c1e41c19902c5010803601213440e00d0180200ca465403000d841c020f143e0340014040341d440c64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 786297329 1250 786296079 786296099
    0x8010e0106090e0a1e03020a020d0807140d14070c081f0b040507050d051f260c0a05090411130c0206070e0a2d0303030b090108010e0d030209010c0609030504 69
    0xc09a00e400c0782d4000b40b010000105c01d000009030f441050302440c2c0100c500c1c1d00c1c1c2240380c00c0c1482da00a41100c000c02808040002d680080c09185200d182c000d03d400744030002c2d035644c0b202c1503111b90001980c49a0b100c240d1541520081001c00d000d40040d00e202901c860100b17150280000030303862078141d490714042255403548a4a00c441d20210780034041820008001803c81c056040200d039820354031030100d01d41261070752410603111260319074014a560350301050495400b60078021904905200688150518041a8400050740c01001c0c0c0f5426414041804407455006004513514161146020002e69a088940c101c10308180c0000c10072155801009043c80c1001e0600007e001c19110001c0703c0359074030101c020075910b9407042c00c030780b4058100c044403804400c24504645084640800b0050541c0340d0403601020406441002d8140d980360046806c903604800e01c241c2c40e410800111080910a40041051040500d043d00d900007143d10341c0012921000300c11004968000750420000441d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 786298579 1250 786297329 786297341
    0x60b03160813151b05031006030605060403030c05031e0711240901052a0105070206010e01060e0d0210080412050f040506090103020f04290f090f03010608010e010609 73
    0x901c1c00c03000c1820400b031081e2001c1100d50004200e070664410180740c00005604c014500d0040b6041500d08062880c0c0240c410391083e52005080d003c02d400100e81240680113000481e940a429540f0385071030740d01d08481f0b00c030100f101110140010401e6083e60b91950408041d607901d0140040d0303640e5011b18208008031450582640a00132107400010b160220000942400448030070784d5980e46030040048a00744588403084516120075070821040c044078500d102043e039141e034020022900c1d881000d0741e443c0c10912131481c0c00c90f1040d00500c48180300d03c400101410780980980340106040d40058280810541d511000482401c204403e01c50346030086003a485590404910300030754000642402d2040d409440e0160030001915040c5911940c101c0703020b40c0000d0000307900c5035111a1030f804041c0550b0078021407600d5400543d074250b90894121000042000c01c2185810744000a118000340007005890b80340d5a40c00000400140a0080f0507030010b40700c0001402130f003080041d41c12030325 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 786299829 1250 786298579 786298621
    0x50a080a0b01230d0c09030b5a10090b01050a0e0307030b0c0c1002030c070618060c02010c1101060b09060310030602070f291513060b03 60
    0x4242000400c2698011055164400d00b040d0003600d00412008030b9440d601c02e04d401c3c0105585040c01640c0a154050f14003800d072481028020381d2903c3d08500011b00c21808641d41510050604000004182c60442d444c0403802c2502041c4910061504140d005410114450b10b90300d41d6904018181d80350b042c4000151406403030810922988100081940c052035042100317101042a4440255504000d0340004580c0100c60500f01c3c545015480c156412032200d0006602c55212f02501c000c4043c002d887c07041c01945951400c0c00f580c2c1e03e0b828040c10a0b0850000b195a1200000d40880c000e400382e00d0144255400108110b141040c005102d40ce219183c08180e9240c400140f1004402130200e4004e0442241c0103600c0361a00c0341c000d290100c1d194401024148002480010003203081d0717010310366034014100d080c40061361080807000e1164105c01c50340c014011400013080607110031848842c456019009520203841d80401404546003501301e2400002c0102c10041c5518910740e00145801d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 786301079 1250 786299829 786299831
    0x9051903141602031914012c15090d08070e0915041b020f1605060f090a0f0e0a11190f2109020f060406080a0b060f2b060305070b0d1407050a080a 64
    0x35420300d500a03508d030080b041d000144030b0303910000005c05808000c42c51801010744108541420084503155403000000d03106008103103001d00003071210780103004e008110900500880c07019510311406c1300c800940d05918560041c0d484079001100d10903540da80c11201420740040c02820701c4c8030301c59407070000e040c4020301e407204013010144429100d000c2034410f0030101020054540f8103500010720301c40165044900c41d485110000178940100c412001c1c024003001000300030f1003d00d8882c00010f84920044862040108030390201100e104603402c90002c01c0c240b900b04242d00c40390205102d0650f429071481c99140c5c03201141800c1d440c0c900e8494003200400c41d121032400d490a0000381c84114000c080d520f0b0942c1d50f401800258030381354126043e122200c5601661756403e0b1500301c0404058200c0075a0016550340c0c0c070319400f25144905425a40c210001f001070a203443c8101c0c0325503100c10001ca4245440b880c4001079808090f04a9001d00c0c1d2548038951030b0804940d0003130014600410b018105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 786302329 1250 786301079 786301091
    0x8061003020928020901090b0309160608160c060f06080102040306050601020f06150d020607150b010201021c020f07050304030c031202010c0813030311030a0905190314160203191401 80
    0xf0700901005030b4041a5050150300c80b4a20030040c0c8000c4110f601085061034004104070360900086403024400d04e182d050140203545401084034004000c584642040b2240c1551010050056010b20800c6200f12008143d5100c0c01c040d02c0265400360384521401d03900401d0074400c00009019041e4004020320041c119807252200556554001500700b41004041c441441c5c1c42c5c0c0c541c1110042c89680180820340d580e01705141940e490780d0000361100489240c8000000b280d881802200c20f620449020b009403c1c503a0303034590f0004d62044440050005003017248000140d0140050001140200043d58400d461810a00c15141e108031b4510116403500301c5d003034007450304110402d4008c0c9611611002c0028a46400d500914203001c00724061070002c8104420711903030b90041420f652003081556950030440707840c0848440c0c0c004009000c10300024650b540d40414101a080120200702c40782c0d03138506550042030402c1c07401c0000301404480c01c4014014000c19148210004031290020446 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 786303579 1250 786302329 786302371
    0xb011e050405191a040e07020a02010f050f041d040b070306030c120503070f1211160b0c10020403060f051f2102030610050a171f06080610030209 64
    0x3040c422801220300c2075030032805060001d03a1050000000e085019400d10a641c02d580300082550010712603851456800d2000036113007032010441d4280503034182c40d400c4240009210940d600d820034903611000010900000400100b038080100b18525032000051460405003410104604000e00e4a010b160526200700000780d0206520b804940304100821f03980400d515001c3d0a503c545880502003048105607542408001001d40440c007600d0b17190921046414a41d03a0744854100000c0ba0800034124410040b410750100102104c00c0b032003066038034000314241e00c8401ca03040758200b600d500e42c0d1101444150405171181c690400f030b5010081c1c105601411a40d0013110660140e8038140024100040f00300203001521004503a00400b0740e1a00c1c503110340e004207100d6480c82090f04c1106106400940050701d00b86080000a100020340958003090b1208001d01e0652254456419a81e4038001198a01440000d029080890040040300e183d4010010111000b07882c25031002208010004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 786304829 1250 786303579 786303587
    0x30c130e15041214041d01080705011103121008030414031e06040204110c0712060b0a0e0c0309030d1103101703220f0b0d050916030807150e010b011e 66
    0x216242504c0d2003d80611220000d01d614001d40d031012188480c200c18584c90300d0038200b19107060b100420201c4114a556000441e402084070001c030215030010000d600802c07a040c0c881c075038460a400340310403950ba07940fa9410300d9903100354841102c9040442d00c0744191b20f028448104100d030074021840c503500c49190510380b10800500024455680d4200300004c9004107000d40d12100101800d0f112403070340d200034009941101c00d0701200c80c00d00c1c3c010412414030b0101001d03003d441e201034551079165a03900700d000c1c03a0360000d400d11030288000d00140305248442d000700f180600140e498a80c4a040c4001c07022540e400350380007034902d01300c20340d0801032550000040e03600c0c020381c110901d141c0c81500e11500190407545d400c101d400d0b4901400c0860031a06140003003015081c071240c04c000300da0314041e2043d01d400626010b02c180605503401040481c21100c00b4148a90180440007109030143c1826400c03101706050842c5542d458105106684d07800c12000c811840101503020481c0b203845600030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 786306079 1250 786304829 786304853
    0x30706050d0c0c0c06020d02160803070803040317011212031a1e0405101d0603060720011407090f0e0c0f1603210b0915030c130e1504 59
    0x440c42540d00c542c0c580a891140102142080d0840e20024010b83c80c0c410080d2100700c414049000b500c12481110009020103d90108490300540a981040394581c0c0b400e082c4c1e44060070960800c0002000585c20031061b400d858003c0070b43c402048004541e51402c0030160750100900d200340751070130001400780421100100c60004046510002c11000c01c00c02e40c4241e840901d802d0380180c9001c08011840116807505400c1d87c8400c0c181601030760843c0c3e05c43d0501681112010741582010b40807440682c09061829080003080a0008840d45002c00d880e0848078107106105104001000703000a0316000068200504000360364101064246186100c01c00400341ca90300307800d003000075419001480d18080e2901c40f0007907203050401800c9800e00401c0d100b250190308415203807a68908150406512a102d8200d6001c0c2c0205019900c540e100708078075108113180307501030044d03540642240d0b03901b80c074004281d0000603000508404422055107484e0105a02845003903103d01800003142100d0100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 786307329 1250 786306079 786306097
    0x50f0316090209014e050f070201060f0f0506030c0c060a05070f0207050d080c031306030204030c140f1e0d05031b070303021906060b0a03090204050606041206150e16020c03070605 79
    0x2200b1700f48500e42500482ca802484401d855203050f09001020b5540d140745c6004501c958024017503245c0343c180d07007203002a0328400c010a50981e00404c001501f00748004d994001da40329060750a000d400e41d126410301c2800c6503040261070f620b004000419800001481402c203070740c4001c190b03080c10140450004c103514400074107105004241f890400d1010000c50703041101841e4480c40c59582e89401030f0181d040f6001c1114150860407000c80d9080c0c45641702e21401800500100049443c5801d201e00c0002c2180c1c0724241c0c8407100000501c0d911411701c600800b504c2040150383d6050f01d0711440e1184e51a100c0102165000080c042001c01d03400502d070300c2e2854040d001a001e01c92a4030b44100200426031010743e50a00c04035081c9490f5401d540070906103030081c0c07024055980e5030410880340c0d00c21400f94140740c5000c8200300022034402e41c081d6182101d0110720900003a250300484519070310072903c9440c290020305094050550510078010186c1c01a0002c24000c3e08000c00030340b55008030b03055 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 786308579 1250 786307329 786307427
    0xd1d0d0807110604061112030f0c0a0903060218011707020a0314090301060e0403110c1e010e03030318070819110f0a0b03070324050f031609020901 65
    0x521424040122481c2c41188802072100e5640e07a580c1c50090500c051600c0d440503d40222071080c00119031807012a8859180d24400003080c1c0c3d200b80c26180785400049410040182c02c0740c020000502500c0282803010004400d8040800c0c03802c00141a8103c29000c80441c181100c20300404d40d0f00001c1d48000903034141810451103d202010101e08e00504d54243e90541c20003100107040d4020b0384489004034000d83c1c903031001500e0030449030364aa0818503480c2c1c0251017003400f4510410b100082d404003210515100307600c02d052500181c0b6580058442040d010602642030740082030130844071004007070020151800004140e440152100042c80107131503000740001108a55441030402c01320307242c0050942180c25101e12030902d07075405c102e0b40e1001091500349204900f910703a00300b40380d0182140c1b210100e001d00300414030926541115a003501413244400d0340303c41030320a00182d0040e0000480040c0c88841a800040044000d02000480030145006c44050200f44000b60b071001292198 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 786309829 1250 786308579 786308587
    0x50408150403180e0a0c030515280f2619020d0204050f070801050a0513110417030d0f021602040e0c030a06020324030d030b0102070b07050d1d0d08 65
    0x409950045400f164441000500640443c003051200e800c1c60003500781303150400001e10110380035070440340c083c0c4480c0041280d140403280d43d894a11229413036210805400c6100390419003d070380f07812106030840c089140310440c05000405000140c40c4480d1140443e01c5100e9a405400a40301c41c001011084030580640300e18056441d03a0011441040d070140c001c00030b500d05416410007048081e9866030001c3c50400c000036451610034441c1056840080a82050306251590440248140e00740201898814840080d4031075001c02000c40300201080a55034681403400c280c02129030759480c0500c49807042c058011502c809140c12020700b079060f63b0015450a06030042481d145400c180250325101d6800c40c1c03020400a60040c5009e0102844c1030302c91194007522501d64840b200c2e000760740650220181c030101503c00e03000240380c0001030050350308403900c03443c050300d2a52089109a526a1020f421154140d6006008450501d41080b61040742040302c800a4208510f6160182c46280049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 786311079 1250 786309829 786309833
    0xf0903040f08061f1409130c03080a140435030a09031a0f04020108070e0a090e1b0604060c02040227010207060f08130317040818010504081504 63
    0x4840103080085600c45410380e442c40a15540c402c226500c0703d410301c40a000e032181d1000c903044402940e0310303903e10011020f00d0307609004074500c00514071800e43c0b101c100e642c40880c544000c0a0060f42c051101555180ca50060142030000620f03618000e8210420040100a2102d60764000c400310600c203050b040c107541c0b51080045211034642c1e40080c000041c000018940291403c0100c0c2d204030001104640b20403004507608108803010b000e0220090f000030010741c0b25010065000e000f9040c018440074404011072943c94158000d12659130340d5284035588070a040040c50889040c910310389802d4043c090124029000e07a10420090100d20180d003811903883c1c0d0151000900300c01d00801003d42800340020402d41001d15450250042da0008520603100324400d00c4030b51000e85464080c4d80b507540c02a0442c50711240d0030707010844414010111b140350024040c0c0144d005614103515610321003060003c25030111000c0d03050080c1040100301c0c0340300209150f91000084008000ca5030b40314 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 786312329 1250 786311079 786311083
    0x11060703020f0d0504050a0503010b0306220803190501090e0c01050d0e010510090b0d080405090a180b04020102060112031409011b05030c070b090616021f0c11010c0b0f09 75
    0x1c452028200d008403d00c1c440744561080c050401c54500701c0d2035040c5c25640c2d0052500700d503810001a500764110f50f002030754440506000b2885a0314100414480441c0341d101d000594005451100c034451007000c0e00800011a070052034090444008104044141c043c15140d4405048061740d0500ca0089980b20468901d076001103071303120802000f804185005102401481e00501507d4003c6141420400b00c81c01c00c0310301c5400307250344420200c0c50181480c040015110000f015201e010303480e07002500780540b218043c0c1a07070f81c1c8512036003045400c080c80064103040c03058000390442010030400c07901103640b01d003000c8604200d44c0d0f4400c0ea680c4c0d24000480b24031200b000d501c207031003100f200e100f010003070000014503211100000703541c925a20b0308050f900c18400c24620640c132070400c3c885c0200c5810207100402c0b42c607100402d20100914504860803405071018a0030b8046500ba9040c1c406014801c8941d00154500340380a004da000360366610509004c010b4003c1021510f1700c030004500e0802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 786313579 1250 786312329 786312343
    0x180506030307200307030326010b04090b0409020a0b0c2a0105030a180503070c050402161121010603061407050a1b06022a0a0b060f01091214191106070302 68
    0xf018003901d1043c0d840b410003501c030900c00700070400c02c9200d10520070201c2e0443c40d0031906071501c00c54003501d0a450f00d61400007030a0070054903035101b80e07980c900702d0044c0c0e10078140000811a6240c2035443d030103005461410041401d841101c0c0341c000e00d1f1000343d030003c0c0446110603103100b401c0040e182c0c2c80740242e02005002e100c003c0b494a04081c25010140300001015007455440761400c0d1410b03903280c1c02444140c0c000c580c0710b00f41c1c0c94141e03001e1400140d8001420038030040042d2030341024901ba00e04001c016203c1c81070240303103650750381300910070300040b4000c1c4903040c1700c60340700010a414400c00c000c000d44216030400082001c14800c2c01c030381d0701088885c0600a90003ca0964503103280403104010b80d1200700c80c0000141816034001e00031140800c4e0800d21a0704100c490060381d41d0b005c240a4601c800f81c0c50103040000c8a0404510710707042162119225006003541210480030403c540c0ca0060f924240615040c1e4402c507010001e903801181c0318a210040d0b40d440d4403001c3c0c0e031505918000d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 786314829 1250 786313579 786313643
    0x503040f060e0a09090b1b09090406060501110c0a030f0507031209060e0d05060703110408030c030415090e1b0d0c0206100b0c120903070e04030504180506030307 71
    0x1481a800141c0d60360301941e403564a020072110081019500d0750700d801120522540104454030510000b1003481203961307000a00066104210300e0200c100e0001f0b81c40002c00c6038101c821994844003170000d035a0003105004140c60300002000304110b05400222568181d100003003036240d850050b202007000a102d0900103650004850915482d6054080d2107444580070b203200140915048800c5841d0011407903552b680c02401230803050300d440c3c10490141940e80007a00195070f041100043c581000c00041c01d442e41b2270070107561521b040c228550703841900c00e51800100900c0d0402400590003441d410340d0441401141c800021084480603011401003201d201c0a480ca0701c4a5882c005401180300d03403046c0302000004000300d40314403542c03405001e08120701d0f210340d0000041760001c840c480020401404020210f82032140d45280c0c010520900310340031000680c000c030f0200042c0311010750400e201119200305001910b03010380820b94038080d90301c0251120b0380c01d190108400014a00802c080340c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 786316079 1250 786314829 786314849
    0xe190206090319150515041d030a030609060501020c130506040b210f0102132601020415080a0c050906030a1b030c0806090f040b0c0c010f06080f01050c04060309050304 74
    0x6421032128440d441e105500c01e407455191900c8a0710484501c0c800c10b40315120f811201c4600781002002d03c0020148c00840b2070344540351400f54a0f52500400c042c0c11055a15640800c02c94200411041a10790079408a410f642c024860002c8581c0e40c502c1007901c40340c10544c0003c0c10b540d6400002d0151110904940e00b050711042030501da01468500000707109641030884844041e014965400c034400c000c1144056020704005210200c04003425002d05021480c4c81ea035200340c9100c500d42268001d078400340f019808020000381054000305a10b80c0008a15800c003c1024035800140262040600c2d00703101b03101c000300280c1d050105600401c2c006480d41d0f4241d054100c1c40f074000d40101b02072658040070404007400500e00b403500c0e41c03013144110070704091149583c0b01c956400d8003220700a4900181420203100a1502c1d100c244078880c04100210310100300245003807801400c040000d100056240d04110401c21481c49030b0040b94211141407034002410710f00ca081c19400c50150b40c111410390 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 786317329 1250 786316079 786316093
    0x13050903221a21060619020a02030f06090d08010f0e06011b080903010b060c0c0103110c0d0905010809060906150303040f030501140c0a080403200d08040b0a0e1902060903 75
    0x900498005852404100e50003400b01e6800300c0f03100c91004500319049a07014004003d0390030010b085281742a510714160045030304010440e8002800d004446510441c950720003020822014020840e03146481e40d5810309a4695040902c40441f1001030301911801940c29404280c040e44501030503003041140d0300e0410400107103803a20200507801001d080c0e20135070815036040381300c1c6001411a84462004002032443c1c035540d0300158068201012424071040041c8281115045c007803200e40c401e118a5980c15404e141800000f410f1031102a25a4115610000030040e501c8000114203030003e0f418100349600701e070fa110000e4554405c0360000840c04200380c500000300001500005d20454800202091715030321030180003118021a03103400700181d4418089004607004884c51100782c50440340d0070310403107078071884d00e8a052840b100850000d4176036000c00c820b00c01d016080581068080100340100f02c850b4851560b22044cac0c500c040071001c10522110119961902210300c500805000d4500d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 786318579 1250 786317329 786317369
    0x3091515060d1a1e1002031b0102090315190504051e0304050f030d1b060b1806010e010912080d02121003140705060f1803100b1305090322 61
    0x1610725401210fa0100450b81c0c0d01c08603103041040d01c0d4070700e030348280c8080101855004001d00d0340724080c440015400200485076806c0540300000090100640015179078072140f81c00d0514040801c4c0810721803042d0101807140c001d071800383c00300301984040300c049001c0d00e5908115040404403c04154022140c80105902c104088094800c070754003215a008022088024075444d540c01c10401e10000e0601c0e0f80c42c81140c405103003440e5109020308400130311517070b60b900410718001e2801c100c1050b1200301c00030441e51b5a8051a1040721007001c1c80c255034054540b59011441c2420380b040203250400114501005409503410355510204822841c1c0e00d0342080c500e24801c01c0864001914038030324903501d03a046c1440000344201210000b80a552400c4012007d0500a400c101c80d82508203130a540c2c51341e25642c00f0024601e4046902d90700040c0e90f55600200b01d18200707a0a00e80340e103039003008108403000001009480c0585030070a13000420001444001041c40c01c00c0d00800c41e40580d102035075903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 786319829 1250 786318579 786318581
    0x904090507320607020303042603120f07090b0306040c051309060501090f0f0611030c0d02011a15040b0c071208070c06021b01030b0406050406091b0503091515060d 72
    0x98050341c50026007802040d00c0180803d40c800e0f210007a426520411080005409071809200307010001401800c00e48005899075040da8010001e40e180c00c4a24024400c422401c44100d50b003111440c01c011079028075081128030240401010f09102d283e44040c00034016014000b11444612441400414691910f0207a4003c01e034600030140050386858002c1154840c0284000583e40c4103400080c16a150040841d005203043c610303a040c6010500c80e44400810401008441c0081900040388000c21080c44040c1407243e03078441441007000e407440802e01180e64084506603184a030f1001d550703103007181c2d0346858400b1a500c0813801900b4041c420303060110403800f410b5013611642007001c915a031000100ea43c0c034144031008a2f4011106a1001207600035405210011406072000c030b600e540d51b40000f0200e41c215803201c40700d01c2c0c449280142d8a000b012180030020a1810712034203600780f02c3e00c2599101c0034061a141a0180d9501040000ad00b0410344a180b100003001260b40c0c904581c0c20718 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 786321079 1250 786319829 786319889
    0x100e04080c07060807050409050711030726090f06090a0e010b0703030b0607030e0d02010917060916030b07050c0c0d081c050c2703061f0e010b0904090507 68
    0x41d03a00d00a031500400e00034030880140f8040c06480c4d680714209800c2004000c002c00f0040d20034000e204241c00f282041010510182c40e80b2070103600c6203132001d4000b90048203c8011011520075403201004400c00c00e0756001d40c40300c41c0c1301054808070380740d02d503010100e902e030501500310440c2c3d215108000140750080c840188078282c8203581c140090346240040c040f090144280050200f054400c0500142c200404020242c500500d0450301c0d6a0391a501d13802101500344142801e034208800b0408007600c1041850320140d21200c048040c580b9546841c044003d02820700410804000340584503035000f0000d40402090060100c03400500798540181c80d544049040c0b180580600310070081007105c0c0c400d8500c502542440c451402001404ca19591a00051a1070020407c55107000054400b003090720300c0b504c040105a059444212102d00e00c1180700c1d485a011201c2c6200140804a5080103a50200000390750103d04191580b4080d418149203802901c150204103031702900c0c1d2040a1941 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 786322329 1250 786321079 786321097
    0x140c010b0a17010b060403020a090209030a060c200a2a090609050403031521050a1208010302150307050405040b0f040c081f05152104061b0e031203100e0408 69
    0x20400c841400d8144030f041c6c09107100c0a0351214551b00704100200c4a42c0050040810082c00c0d515075440e581d580b803049403c505000c5000a07a03030441180181461040c101d041c2800200410080d103160342d810182a482c00c0c882c02c0300396a4007403c00410b0094501080c042c0c90f044034103215464544001d18020902194103030b0000c0c0c1812201c1602600e10280041070340d003a08400c5806424940c030461a8504000c42124140b1456103664003140404002a030b000140741e03640c000e55451801008220f8806032a002c2e5800420824230450b150020700719021205e003901c020511060010001c0c0b00c08818048140d00541031440c500b840d282d00100071841a944102220540d18a0100c51503481d210340c01807035000b0383c0b180d00f45640c0314280d0018044e03e44101c900d00030010890036200b050f05038287c0741103400307a0b100c0030414103504c4124036800c0380f40301c9480d1500130102201d001994460541c480301030300740c100201040340c5002034a420f5014211b42030454015050a00e0f1060341c03684001e0035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 786323579 1250 786322329 786322331
    0xe0a080601150f1112090d050102030a0903020d0512011a04090e0a20060304020906031204030f050601061707120e03071a0105010302030c1b0c040c0807080115140c010b0a1701 77
    0x41c2d20300f079019085120b40610243c006000d00d106954a030601540182c80c4146c0c000c018560200014200740001e500c02c1e601c148000c2055444c0b880c01a00e055005012541031041c144180d0701c0042d031658100d81102c0d2400c00c00101070f00d102c95413100034800d035085080c0841c10310000820510000404420052003211144591802c009800c10401c0e00802c150394040700070030105004d8070386003e60a40001005007541c0030304004030440f00b400c0c0e1142e48111030340d41007200484288030040c4050350041c907140c1040c81c10400000551040303808d004045c2c400340068001070220085491f4005044804030104890f500c030105d0403c0440c2c0c640c4500030000c01c0e44c3c28000403503254403a0091700d0189d04c940b40a14182802107032024a80100002060320314800c2c0c860840d090b507924011000281d05c191103000305424001c038024400c082c16009025420582d10000c7d4800b070340300c0039000d00102200c01c80e1342c030b0303081d242e1805025003100030800c2d03032140c103242d4041112107140501040c00f03145900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 786324829 1250 786323579 786323597
    0x501050402190f05010302070206040b0c1b040203010b04050904140706020f0106080102160201050a020a0519050d030e03030a1505030d0201230106140d0b0a0b0301090b09060904030e0a08060115 85
    0x800c125001005003d0b0080440204008101d954000d802424286100801c02c509058032103210bc250b6402590b010300103540000c03041402c440007404a42c010303620503a000d610b5503040080c02c895070b1045108103800b418803d00050b090110003080000c0442c143e0081c1c80704540d48071402075803074001d6082d8503d65440c100700001c01d400144202c41c880f90340b40e500304000d181c242d0010b40e039a400c060380c000150300840490000081c0180040b1101002600c144100000542000c0e4600404c098014092500d4014907803422500001920360001c0d00450106020402a0500d0b46d1603041c0d50107240c05102e038a41c0683e0071034064004100461802900c601c0c0890400c01c840725130310080c401d80e00410750380d02801c056084001c00901007048460310205440d42c41c4000700f41c101c060750780041c00079600030006104004ca540900c0148000444900c6c500d03041c481c00003950050040c10003002c0c45140c9444008649590b079442000380300700380583c3e20540e510780e07144420100c2d400c640070008034200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 786326079 1250 786324829 786324859
    0x1030b010804050c091f06050d060501050a021509030c0109140f19032313060f17161e0801060315030f110a050d061e0b10120f05040501050402 63
    0x800350b449550018020420b6510010a002c120701014080300e0b2402c40101b1a20000080348100030020321069039040d40e00d01d140380a40d401c840030340d0405810044104011007840c3c0e030000e21070542d442c1454245960391110103400d8950300c6001c41c07280280d420401b2440500c0b03030300000110689001c9080d6201416030a0002e07480358170701800901d0b044980a09200406e00c6500310b035961345d080c450220000e03544848080800c0d080485e020741c265220711002d010a43d0710141e01c48a032055070410031404440c08202007491000140b42d5101a0380c0310041614441c03240a0030142046412002d007103810f00400c00030a100c3d4240118400709040c0400c0c044014144880388040ba07070003001380711b0102e80303039039030101002c820305c046e01e9000f41100703004a681d03030783c0e1044c468010f403284d100058003007188200e0403001408440c1c000c60103031401e03960135644d854002d03940c0e5990550740b900032845825484d649000300060844050241d1400341044100201540801d000328000c503014001c0d04091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 786327329 1250 786326079 786326087
    0xa0806042108070309060b04090807120e060915070803180c0d030503060118080d0f020c120d11250e160221211803070210051c140601030b01 62
    0x642072100c000303941c03980022280c6200f0f03445190140d11031400400d6200203c000201503480d03042040d181d010002600b88c01b0000502c03000c540000d90b6041000b244000341c1c00140350b50150080d4503000d00c003042c0b0035035141110790088440d0283c0c045840c0b601e230309111060020b02c02200040315001d104035114134200d4540300384580b9807035606030b03a480e00d181c4c0c0b15030044a5800c01c05030000000c0340080b2001c106540c091101706040f90f19035031000341040702210000d1920088003070031750141131000011000e8000115440c041c0520a02300710789403048403000180b5008402e4400040c48040a03002c009450340001d1280032900080c1d401c01060b241c2220b5520181c0c2e044001401590140d90b6030120548486a480c00d5011403080e41c9082c003003c05200d0f925890008103400400d141401004a0240c114000700e0b0881a100025418050903070702207066100d60201d01070a021001c2810004000703d481c00c144002d103907800c10710a907452810030040c404420b6031014046030414070802003030352003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 786328579 1250 786327329 786327383
    0x603090209040602160606060806011206030f0b0711070315060e2e1208030106081b0403200d0321020705120315120601030c0906030b160e0a080604 65
    0x405012490b1215541c0340002c3d4840c2130001d25154041c1c0203240440c0c400e1081c0300003030140e40c882c4002031529400060294140c0e600c0301c03420714500720040c00841d20a81d501e44007654843e075140c60980b25610155182100c201c6070f001140b00d6010040f007000300304561225001d0ba0300390140516a2281c0440301c4134041241d5070069200ba02b0842d2841003080141d00e140f86141580a802e01c51f110900000e100180c0c101c08e1700c0803400003004000b80b5a21120391030b030080310402030000240c06032944c42c25a108522014103045214446103a20b46004404070f0b4801c0b00040c01c1451504151802400c01845803502d16425480f110981d071060605008a42890750b2020140080103001850041a90405001c140c007070000121404140d031502e500c03031810046c141c03004050320f42c9940340086080305690021100702e0f040040400005060411484d004040c9008d07a88000e1225102103c00304405d0004d82d03400b40441100003400c01e000b00d0780798040c5000714a682462683c40c0d4040c03500341c3d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 786329829 1250 786328579 786328583
    0x21612110142050402040611100506030a060b0114120411091501053f01230d15110a02010608031e1803060a0204090f0903021209040207140610060309 66
    0xc85070000700c030400030b40480d05048200d000c0105840c1c0352528045412600560480c801007561721480b000410800c22024629220090090026207440300210f07444051035a401002e02e5115410052268050b9800a040450310286e0645843c0b41c444918038004040d02d050390351000e030b2101c29001d0700f018500d6512503141e200b8803005820b140c3c0c00440d5154000709140c468580d1460704c003c42c22070140781e0a11180040c02c0c0012000581c15a07030190b4840692007141700000b4007900003a100c254603400c958511003121004207040740d90804540505202c4040400c880c40d01001c0ea81e2810090054000d10290741c0c005c00200351200e0907140d80384a6150f090328250350b04a512a40e0200000050a00406901840030401c0d03454012a01c1c0c08000d407100282e50350042000d00140c6110302c601c0303e0707000040d107003031216030b02c95200a91a40c0d4903801c603070004500003a1240141c0c4803030301160520395200040f481c0401902285030740381c107030036544403001083e01d81000030f034140310f170103038100080d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 786330935 1106 786329829 786329891
    0x415270c0915020303010608060409050c120318011103041a13080d0305240108280c080105151204030e10020c090901060b0d0216121101 60
    0x701681c00008115403085c00100045903004c0c0820350008429140010000c0c51800c0641c101041011156003010f1209002d082d0140c0c008000c200092090b1914a0030401c40c0c0f00444004140c42034180c155402031205201141c0c03080006060403604e1410140303083c00f125003003448500290301018054011040300d40089801d070055683c0f15446103014007190056411041c22070340c0d406002410040c1c501c00080410400c0f01c01d18000b110000c80d0b4088014100d41031902074900c1b0844080003c4010000065906000e80380146a401101e1200d0901100030311100c00044010000d03410031941c02c043c201c2948806001c0b00032842c07035601501080800c03006010354507402a1540e01103a140510410120401005403549a078400e8400343c1c0d1403105c0c0010b40d80903040306070f01505a64518400410380c0b90420b54011420102c1c170001d12070b100c1e80f000d08101c14910145070810b08 = true := by decide +kernel

theorem cover : BRFrame.Cov 786151079 786330935 := by
  have h0 := BRFrame.cov_init 786151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 786151079 ≤ n) (h2 : n < 786330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
