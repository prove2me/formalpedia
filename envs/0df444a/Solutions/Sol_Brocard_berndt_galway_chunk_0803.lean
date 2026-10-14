-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0803
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:53:16.892088+00:00
-- url     : https://prove2.me/submissions/514ee454-0dd9-4ae8-a0b1-21d233fbc1fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 144244604 ≤ n < 144424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 144245854 1250 144244604 144244627
    0x40f090506010e15070c1d070206010f03020a0b03090109170a090e0417090114070b060a1d06060a020c150a09050303070317060d02181918020f030106050303040902 72
    0x3200548028144551440059842c0e15040d180d20503070480801401c0e9212040c0c076005807200c0d02988056002c00d001c1d40e0310740b442c0030000c1c8014001d02030b42d03088803080c0c0d807214112544495a0300c40258456401030b010000c0a11040c05150b0103034541000265119807900c4040042d010503035005100d010010314140c0c0580c005160001800c034402450403549015910040040700710302d01d40c005907001003515081c41e8400c016590f000c1c080001043c0d02e40d90246407a140a08065508621400142c4804a440810801020a00000f00c0c0c0c0003452a00e83c0c01c180101d1303501c403562100031401103c000c207049882d4881c940c600352448041c0b00e5910761407000c0003451109940c000a21980040041c1c0010030761001c1c5080d610704e14548004113503200c05c400900d003641000c40080d040031600c0000b660402e440900c1e90710542600d15880c0104041483d55000c880c4030201610849002c2e100c0380c40075081280d050943c0b640701a00010b00c00d616000000e203544c00641c06500f07229000201940d140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 144247104 1250 144245854 144245861
    0x2105040c06021902060904020f040f091107211e11010b030f03030403050a17070f03051008120705010207170304050708120306040b04090b0702030c06010e040b0c0703050c03040f09 79
    0x1d003841d01c09881c0120111011044194042002034402c1707001069481007035885504803041d800703072004c281d90340c0d641d44c05030144245464410300c85007d10700030f80c2c44070060f4100101c405d0580d126a00c070011001c541040c18440c0074140144003000060000d8a0184100e804000c0f030b2141c20b616052154100381d5117481c251210f00c1a414020380003030740703036400320170f000401d694205616041003900d4204280088429015000207500507020701801d125100b904865200401c030510f0368280f0640c0c3c0c07407034250006543340b4802c80304c0ca503010340501141c42054501408045104000242c5412000d03100d100d940103c100425038071100000038070017040382c01c018480081c1410800b800704071404811000e0940001420a405584c8640343c1c0c042a030346d0781d03009803000313030703211450b40a83d007000310009503a5001fa200817940b5104140001c104034568102403840340f07902c01003950050340ca011007820340d40c1040000f00d0a0100c184900c105030701c001e0010704007401d15115010100340c5401e8031389065 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 144248354 1250 144247104 144247109
    0x91109060703021e0129150a030207060f020304050c01091809060e03180109080604050601050d02010c060e100608010e0a060914060106080f07081302010302090a03050105010b030906181b012105040c 87
    0xb08482220700c00c031a41b075400e0300341f241c003022441c0703d5140d04482d80150003a02c202d43c8001c10081c03400c092070102c0055075010314080d5004104072100500d01c03500558800120307010f808884241d90183d2010401503412451071140f28000c080740580780601c80394510b80014039444103855000402040315613100c000303000240307206070041c1054105516825103840040c010a030140a5070401417040da402134100407165644004104050642841c1c01d82d20b50803910350301000c003030501100003035003a014001d054110343c28002608000303d4641d203d4006007803041c07040f14100021036407040c044100b40052802040152940001341c83d100c03000c5210888000d000c4000c2c4442601480f003010b21088011358180c2e42800d0042e0f8a180510010702000c03001e62006040d036003031000214100c1d4403400a540031300300c0344040352200e441d840d0090032402141c0c910300c0c440c1e91102d070669aa0450409041090200c181401c403007092840300b504401d0000720003100c240584640034802000404a5101e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 144249604 1250 144248354 144248411
    0xa030602121617161407061b05040602060a0b010915050405010201051008060601122013050405040f1713030503091018170c0303070c0609091109060703021e01 70
    0x9800ca500f940d0000d00320703001d05034096400031040d12199a500a854a50401d209401d0098641c80e80d4a0184050155902000792603060b4140140303003e80550159010785e866600640728594410003050018102da190341070410012040c0022091201c1607410700780321441d95155a00c604180002e42075a4000c1c05d04202000b030350408100c4810080390040d0071a400b480c0100c510f00362400c0ca240074000d042d44003103e001c41c14104041d1a08140000e02090b11401120310001d9504c80800c4101d5000b00c60203044e40500344101c070002041c0c00000c0800b8500c07000d58030304200000d1020b0455034826001150301c0c0c2e0000948840300d18245052401e441071074a02070082c00302e41c94000d0107881c114410a2100d017408400c200141101744130481e500c960180442e911540f1600702960400303007034031a010210710038080c00304680050740030380d00a103400b2401a51528000409002881e4043d039410b82c00c5014880781c03150613110112030040410003241c008501c007026184003808a130615400303544c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 144250854 1250 144249604 144249617
    0x61e0f0f03030521010801090201200606220606090306180201051602060705011104051014180d0b0f06030c0604050913020a030f050307141603020405060a0306021216 73
    0x10812808440300c0055940c9450500c1c1c031603041d0700e070221030f41c00071400c00341100c2c1854001207110001540300364031840c000d0342da00c0103004891003654042000c00b081700910741c100000046280c01d0801000c000000e040d4076107139010240c520444126403003074204000240b550381c81001880124000c010359807505503007142000310a0385c00686188149401044141402c400d5103080d5074441d4103850b280c44d0410028442c0e0012000302e404180c0c05070103200d104003001144140c16031b06c20b0034400100069020238510f441503d0104018810500e0341d0355500041b80302e00900001c181d048058061821022a000103042138401c0504162030b03154014018a0144020400303035a82325a9107030441200385600d07800941c130740081080001d443e0030261008407220b418000300500000181640c5001e00740784050060701c007005a0f01d030021140320300d908442c910303014809890540e0000d40c100e94001c18545080340d40e80e4415041e0b0700706a40c2c2001d00f407200f00401038080300c2a15a20107020843c6001c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 144252104 1250 144250854 144250859
    0x30a050310080f0c01120207020a030f0303050708090613170a0f031a090a090602090d0f0b0f040209190e1e0105010801060b0d0b031e0d020705090702071802070204061e0f 75
    0xc2e03907102c0c090184c5030304200c061028110b140841d41e04564601e1b4000e45540411500c0e400c1502100408240c200c0003c1d1a240008840c584142c0c6080e0040010002030034071034032030340b00c4124040442e090950310511072941c151441d2419000506075058641c491500050010401404958041c10391140b48140e80c200c0301c80c01d50715104030705e501c0902c4020020f2166038505041c00240030383d0316041c0d0031100301041e903c14031002002d90b010803413050542c61a183e66142482c030102d00d05840094025034480d001c03a00740c5503218114529003000c10030010780880301003481807820b003040e03010000040b4590760f5408401000e005050140c03100e00d000744406403a2181c1803daa204861455101c0c036074807000f4401c04d60702482100130700c202d5200d01d81e40101d110391070b440c0c407010010355030005032040c41c1d00060b20741040348080d4881c0e036030754002d0448107142040d004d24a0110300d806421882d420420307180160382d40d00c640c0e00600054880a01e61b00c690b032140303050f5010740390020341e203860600008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 144253354 1250 144252104 144252133
    0xb12070803120c0d11030103110f010f0c020321040911030c0405060a09090207061b11032709010801050f07020106032f0901150905010507020a091d030a05031008 71
    0x2140c8200004511030b007155035a2001c224510b0141c0c440c90751800c3c0c246200105a00160b40207035050340d000c1c00c0c1c890b903412082c41c01c00003018203d4161501040d1204141c090480c001d03c15224180d00113030654900c0280020700d522280c420390001250000041420702096609100d01001541c044841905e141029202101140180c0c4039492041d0800100342c1411842103610034018880d030071055442e440c65103403807000341900780032040c4000680d98881c1c0d450b038410b0380140c103c24899000b85240400e0086014441c140c00d10000c0140400c4401882c42e54440061641c0280510000010a07081c1f1501210303030400003405040840e030402d10180086802554044c103140a002c08181d40840c0c0c3ca524002c40b404003202d06c3da0310586440000404503e001504151440d0307a0391440c41c0b1035228401940c240c003840c203010f034105075030b1007050000c002680c1c4040c9828015094031107100701070190940c034542c01801c80400141d03020040c0141d070005680c03e0380140c14460058006002814075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 144254604 1250 144253354 144253357
    0x100b040e0606100903061b1106060f120c0901030f05151e150405100305010b041107110105250309061715010e030a240204080d050c030f07060b12070803 67
    0x200744185564040041c10500603502c500017168804030130301c01d98031904030760103440186601500218038004840110000c0110f01c0034490040180006500031000b000d10165620461007802c052045d44000000383c1d60348034002e8000e51040912900b403c3c81c1d40707800313030400034041c82c0090340090700d20500100040202c07080d01509001c400d116010342d42e8262034003082e600c260b03a0b20b03003141c0740009114000300c1040840d410740340584001d000300740c0c456080c081107450300003081a498805104110014044a0a031107100005140140c00c00b059092804c1c4120714100c01c2102c09941300548404158000200e80c000b07040904011000600c003600b003041c6148028051602910042d00b90405030303008150040c1c0c06a0040c04490b0035803003500d444103a01400c14119404c040b4030708044a83c00c040ca000700c034251058080581608168520309990300d40140c50801c0d45800103015940c010b255a0010300500d40c002c501c081100714000041c0403142a60072076204a9030406c4a09200c1d0500000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 144255854 1250 144254604 144254611
    0x50d0b1311090f09191e060e180706020a060e2104030b0a020301050d02010f0201061a0406021005060102300d0903080a050405031b030706021b070801020c0d030507030e060702100b040e06 82
    0x840800d000022284114081c0082086d1725940c624052010031480d1074400f2151094610241d0220502d03c8078011070340e5100944500c0006900018110340011025040301007002c04840c12290b407103c00d100911480011240b01e900102d10214080041c040d09880480e000050000114650b5040c44c1c0801e120081c08030f006414004d18451600030a4400d500c480000c100040420200101c0802950103607400342c0300344d400620462070005e20400c0303c0d20a40d0300601050b001019000e41c40304c0040c045a007414209081c903c428064407644c298100010402461480c000061107603d42ca4040c11020f00503007d40c0003641340c80c6c00c100028600004590601801c421321510246044074407910f14495403a00508050010420031003810f901d04c031210343c4e0f4550006907001281c42c0d030045c60803800f84220b4091b4580c8010f0001007400e00a50203181c02c481c1c1c40c503010a2005200100170701d0504151100d00059000c010445031100591161501204041f94140407072141801c070140d860078082c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 144257104 1250 144255854 144255901
    0x10060b040909110405040501020a0f0e09060114042d0e0601091406040512010b0a050d030512060a09090302150a110f03090c090403020d0e0a06050d0b1311090f09 71
    0x490b81481448410040703c50181001031050055140900d000c0d8041d4010b0f46440300030600b60401d02c00b03103a0045648020525000d090505144c2d200401110080d2586030f884200001c00c11020802d841c0103090189000c1404d01200405010007a03041070805c215806010f0b242c031018180025a0392250400003140c0070b00c009080d8001138100091154440c9500c040d074000098a00500e191506420112000d44100ca8240c407081c0d0740e0050014032102584020000341040001025024403140c29035001800900a02211616940d14000321440c80d041a000360b400364100c0003e129031815519446007164006110400450002030107034021510700c440840320200025041003c00c00c500e0207a144001c0100555003024140651202e000c80000e00c002a00070014040d0381c04d10750426001c64510707960f4245403140c070b150700b803004115204a01d03920114519403044000c4050240c1400085010501ca9a03030144004222046a00030401e03030103131810104006003922198101240c19444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 144258354 1250 144257104 144257111
    0x181809030302040503030d05060a0e070f0f02070e04150b01051c09050114040b040302010506010e0a0e06010e03030d0c02010b04060608220609030c0b0901061a090a1a0304020310060b0409 82
    0x4514040c0c020f802290807040e05480003040707a08400b030303507a0042030103440103883d40e1040944411040401e41021240c941c0840c0031100708081030303032003102c501c0e10440e15072041c0c66034907884006020700084240e400382e07100000004104413040191050000c0d048003420100e1a00341c0307140d800000011900d8040364220741d03a05994041c44030a400c54920301012054000e21480c19182c800c8185006440540066181100060325940180b40360800c42a000f840800592710b8071b00c2200780420000c01c61810000c82c14625902030324100041d00035804c1c8074402040c4e80389004ea0080c2100c01c80c03940b10b0320460a045003005a40d82190705550407031f01100010b94241805400c0749099128050010112803801e080801819489011070b40401d01c200041ea101c2d854021407203007601c0c210b00510340c0184038138400b159a101444010f2140c04000b0b0500c140362950341e0082810400e10602d006d1500500108001c1140740030700810580d0301c40e0080400c249414170300c3c001907501880c0240e07000c1c80d64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 144259604 1250 144258354 144258371
    0x60302030606210d03020a0f0903080f0a0c050f0616081b0a05210402010e041a130f050906010e070c080406080c070b07030911030c0922020909030a1818 67
    0x11a1030401e080c01e18002240c0c400076131903000030001c0d40070f80041400a00c02c502c8040c01d0520034100402166004424a400d04440c40c2000d40903900c01c085900c00e000e40d2242c2900026002d000301c1c10f0030811540a0f1115282240c81800c10304081000d0740200001e480c01c0000c050726501440c5c0300181d500e15070940301e0111440542e01d52040404000220390000c201c103241198600e0850f108501c01e0f601d245070322000e4001c0c0003da40159203507406038800c1104024150800c00160443c1c2c034140341004c2005003408944004445068581143c5030b0041030050142001601d00c041d0094042e1401d030001c44526225081307a80a680501000c011428011940720180c0506491240e90071041e06002420103440180003010f056000322548a00e10003082100d160221700c03141c41c030340c0250080f10241d4039408541c0c0c98000300019000300302045020140580c81d0203881c00c0c4600b546600443c0c1e0340e82c070150054600c403521002410403015100301400380200d04004814580d0550401282054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 144260854 1250 144259604 144259639
    0x50a020312130209090706021501080a0204050405100603050a05060c0a0f0e0a090e01020a0207060201060b041820040e0f16050705070b3601050a080406090203070b07021003060302030606 82
    0x800310065480801041400000c110114030f01003101c406408850403213071050360340e009c0c5e49024810140744d50400b882190241c1419041306034400e1081d415540c012020700a00720450b21070790025541c82d4042030380340701004010800d1a03000442c14400b1741c14030000032801003000040d010340f8400c00080010072170300d50f15841c0c841006060030200500c90401c452201d03d00035009a80c90600622482c00300107500c0740103204100c281d6143c20b4270f091806050418000f1014200c0d00000c01c07030385d680c2c41c0300307004132a000480b003580b452041004c036940d42c60b1004440c0c524601a008603014110501070206d000c540791309031503607591182400d070744612050804504203180c50340001c401080000d81c040d02240361002d800442202c89805010450b1310583d00108070510003041e9000c0342c000c01403041ca0502032400a03501512840010520310081d0340440d0818a43d0b6000c2120b410010540000310725007001049542c0c031303040c0307003c0006610396000290340d10b5001c0c158502070900400e0310082d45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 144262104 1250 144260854 144260881
    0x21c020402030a0207021f02060c0c0304080d08060306180703060b130f0b12031c050402060412081803030903150705070c03110306010e0c030a0213080d120507050a020312 75
    0x45400400840d01e0f442c180e100d01c0081d61003140708034400c0080f00840120244041d0034280d002546900400711603907440001980ea5005580e44074851005200001c4ca1034403c0110f01103079119a601c002c1d490a141003414a1b00c0c101600032500b001d00013500c000c02132000120310040303981180000ca145240345003c58008210000074020f828203165044614001c1500091248503054964007921220070f6412501c9020704103042805200304691801c941c02a60840c1d504580010030f0700e0301c1c150751146180c0364800d40040440301c503500407070741c40300d01c20701e11140040b801303015000340d4607000c101c80009454000003070407405e04000303040120740b0440c0b080341681c6d0642e51200c0c452000c552282000380050342604003a40c800d124410000c2001d440741c000d070a0140340403100403415034a807244000c01030b41000c40c480043e4000d81c813000400250801044101301041c1e04c1c3c00040c916000c812400780c030402030925003405000c01503000c5556000045803032102c1a044e840c81541c540d1200100d28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 144263354 1250 144262104 144262159
    0x30f110109030b0a05060306090c0f0d03050f070b01140a030b160306091404021c1703070212030a1d01020c03071b0305010c081006020a020a0501030507020708100204140306100302 79
    0x4409204111450b1025170021b40030b1710381101111380360b550b9070044075990000c582c88241c019100c0310486a0904020180b04c0300c840c4070b03052903030804489912541c03407600310f1a4269407124810004001c03100e2012501180564255100b405043c00c41d00d0f9450303d0540a402c21498105c0d1411401000307229a01480c00b40503034035428408401c0e00100400340c590f027943c0aa10404000d06220320320903003c1100001d15a100c00303000d6103528844042405904010102825030186001096005900c100210300c0707081c080300c000a582c0820480041d12124543c02907030705a20412000c2c440300400001c1e20080e42d4045c030540020110f44160040c4511a54002441d40d800d044040078031507000710006101d00901500b15030b405035151412691413070711440213500300d001c0c120107000d903500c40c0d004980c3c07110071801100c03d0f180e80c030301c140c91808a40104c824801c1c4d078003003001e100761080001c004205050032402441282080b5050003c1c0700c20074400280300300205900042e54803008902e000c1c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 144264604 1250 144263354 144263363
    0x804170a06110903010b04200c03120703090b06040504080f09031e03221208031f0b0408160f06030e1c080415050f0a0e07030203160915030f11010903 66
    0x18a40c003070102021900244606846035090564000c1703031f4206441481c01d901c0030040804d180210081c3e48141c3c1c2d80c0082040d40d028001003040000041c480200a4007400c440c2d43c0024542c043c500b840003d004000c0c14084c0b240d814802440040717280d01094032150101203102d0b560f02e45242e80000c1c0f9255200304081101510840421a502c00100142c50304403904504241070b2804c4803039007940c514440c055070300702050b6490f0341c1d0081141c0101550303204280311100c5c0c502e820400c4485c1c51010156100941401f80042c0502c0740300414400040d9804901c5500c81c0751600300449411980c40314000c40e41090740d40d102901031290204482d4442c00c150305c0c00444441c0d2904002040d402c41141c1c01c1d00d60740900038a0b2450b40e61a4070802d445441c0c2c014449100da10b5104102015220004100c81316118040c008005030350117000c0000300c1841c1c1c8900d511010320740291141070360005500300c0c008900644003040450024400c0c0d0380c06903401072aa00001585200580d00d0f0a40da42000c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 144265854 1250 144264604 144264611
    0x30c0c05060c0c0706022407050c0a0c080d11060f0402030304030b0112020307210b04050f01020a1706090910020c10020304030323060d0227040c0618030804170a06 72
    0x1009082c0350040c240304481c4000c1d1040180c50343d0069940c2d0840820200002481c90824810001440e03190307a00200b49180652820082d801031a240442e50b210640d50350540c05820402540c007001260400d50b054209400316a46107212152950002007e04051011100000341150341c00c0c4100c1e40a150304c071441c11459619105602254604260101e00910800d81d000c1a690703469034440030b032a0340015200309041115610100e030008050821a05031080c2c40440540110a001070710000e02d06540b130f03055154503642c054503200d0002d0040f900403581602406841c000105000c10740301d419210259540340203458040c90011207081d000070306031020040c0b03c105030307060300817500350701003aa80280010940500c0009000090b00d00a81c421604804040181481001e60000b02a402003401d420140e10545a14118046400b12420103903218140100798211441040401e90840240080f9046555a823800c0c89a4010f4204481112298a0b4401070412001301e00c070b64480000e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 144267104 1250 144265854 144265861
    0x3010209180106111501051017090307170304050c061b010507080a0f111c02040e011d0106093f05010c1403090d050c071a0307030501050d0506010501030c0c0506 71
    0x6405452082c01040c0016640780792921070a100041c410a160340e01c0b81030b00a046c1d02e0701040103804000e40120200340117104002110480002c0085481644480d01030b69a031902441c2075861180c8955940c01c3c03001d814030078080401c1e00000c2e885404e41041d1981750b910300083c00703030490b4005440e0461185600704020804119403110800d40100b9103000c00780402000c14101c0c405440d0303201100b040d0900c00384652070345503241640c103e08030b0001400041c038143d25020020780b1008247c00c002c101c1e47c1200303070040080e102102400c3c010f018a16080c1743c01400e1a44581a07054084003140e0703600083c4140342d07032075401000c80200360142e05a207940300c03124524007580a0082060044c002c2001c41c020074241140f803200b183e02c10884100030b0074844000040a481170740015420071034511a01d4000b0403200c942e4503c0207941301c0600c0d546501e0380340400d80101500c4058014074003e80a481250000801c002200c0c0d055400034200490031860708602220350501e2100050480d100d80401d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 144268354 1250 144267104 144267139
    0x150503160e060637030b0d030c02090a0e0102040902070203070b1603140c1b0306090d02060415110307090e01061d09072c0f0d05150a0b130e060a0b030a060b03010209 73
    0x80082440e1783c90500c0703203540090810002e07141c0c62801501041c1802030709001032034901c41030b03540046c0c9207000140f11148810a01c4c220b03005a080030360480e03800034200c02549401c211941c014500c0640741407600141899018559046180040900c03d540c0b0b030342c601c5040328200784c1c0c02215481045502300050608000742450754441e602d406070146070301040c5002800305082070388403d0f5400514240c0c64a641e1400e100f09070103400d00d6465601c040b118000041354006500980b595540c0305030301e42c1452000e000d0358506038400303024440c02c001400080c04445506c0800c4100480d01980c044d03481440540720b041d9100711100d01c0000d5480f864400d040088032080e0080010b807584207500000e90306019000031400b42c080d040b68000d9800071038086140a11641c400554503010400720304a6001c1100d044080c01c0c107184d06c0351038000403085040c04100456014a51510a01010400601081e2600810b0001800c003d4407100c1849032038800350121500204064800d008100c902c050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 144269604 1250 144268354 144268447
    0xc0304090f020d060902180d08190c031416260f1201050301020a2c18010602010e06160302070305040f030605040201020d050307170415150503160e0606 67
    0x3d02450b1501e042404195040c452081d24040480d44405c400f82508660801c601120804402c4850450401880c4200c072600381c1ca941c00c004054035040740ca4505845c024200c0c80301c0154112540360700f40600140e205085402c22200c4d90448003414491034565648011059800385c500700010000a0580303880754094018650888926910440c0fa62603100705800d03446105c15000c00034421400d21b03035003809a043d1070102c034042c0300d1a05900d06600c00219040b502d0010541d14034502039001004126020b0081869001c0da84018007541d141060f00f19002d101240300e01c20425502081c140d0405004c0ea003200c02800131207180c104025944d140600140001302c804900601421400c00482c41c02803003a20b0060304240c42e4030402d000c4a050922101000500a80f0b80c83d010481c011070303800329407090100240101031681c40e000d00b00400d15281101c400179140d0b544402480422100c00480b907000e0b0840b0381207d1155503000115035020580004608400da1a0003d00e00e050555a0601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 144270854 1250 144269604 144269617
    0xd050120090a0f0f05061c0f0507030e0a030207151407080705070602150112032f010e160b03070905100c03090501030e0a0b07030e0114100f06140c0304090f02 70
    0x72141200141c484003c03200c4500c440c4907651610764030306001e101c80e2038604040c04c0740307458445103005040c08074040b001c140c41040500c2103000356928248000680d060140b400d44811440040c2400202941c000b13548041c507111302c04000317080c202161403d0344120421003211a4101a01d80c5810240c24030b9011a440044120f81d5885252000030306903001103210501307204005540c0801d680b82c1142c10640b2030f0700c072404400b0080c0484000700f42100c1c00c0d104170118040e0400f041c2c10401001001c0742111280035501d051075000c2a60507090048002074038090b520040030641d240d4450711f43c103a404015580000b588234054100351070030250b1020600414134000e90f034481400303a60310010342c2128003100308c1c80c04a070800c00b91100803401c0701c90b5058114000d46000100958140e90503401c5070503100304110029141028065064403c0501201402c10382b10b100c0c0241e880c19402500303184081c5181d6043c0c01c0040b55280f8124018002c0d900207041c18030007404a500d141031114002d6100e00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 144272104 1250 144270854 144270859
    0x50c1b03060106021903030e0307080301030f0204062321030406170601213903050a0b0a0e04080906120a0509070803090f061306020a0b0a09110d05012009 68
    0x50000045161000a4036007400180c80005907919117140c5045000d085501c1c007202181c807042003150001546140118021400380c0e001c82c544965600c1048145c0320183d00c482d070a050101c1030982050140c40342c01c000001c003210ba40c00560040d5504207005960300c580d14081d400701140000701540c101e24a05850f0414407c074403099a142d400654030302d2154641c0e9980500044031101c07507200550b019212202840707505000c00a015074102d41c1400c800800c15110071400100703c1d81c8075406000701c60700452501c0c0103002c41802c00f00071402484c0580318a8101600130b402044c1400280c40c00c0701c0c034603500548020340d92615070744e0040b1001006e40c4c0d900c0b8440e28103c00112007500201c1c16404ad2092400a5032070080c00b54204100c07144d000100c0d9a00100c100403411040101e40300d100000c00b070340d8000c1c01d0604550b00b009409502c0003807a03043c081d800d04008030001344980c81e0142c0005012034058403d070000e801c0107401040035030300380d807900860a070404088841c1e20024140e8603204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 144273354 1250 144272104 144272113
    0x5030304060507091a0f0a020c220e012715090b0114010c020d0308060a0b0c100c0908070b07060b090406060503190803010509130f0b06010e0a050d03080601050c1b03 73
    0x1c6000c0080d00c0303ca80602504110000d02192040c102806c004141410880c07044800000042e00011a40b09200145005084191400e03c1e60130403e4003600182421101c02009103040400300801106000f070034002c1c260017400c98007000c100241a00020b50703a8049000c1150601d5840c0a0b001100c00b070207600e0a0045901d00031146600c01c2c0c10004c00d6960250881a800c1c039035940903500d000d0050505a84211480d10105e040e00320380c005800c1c4913100308010202543c0080b07000303084079103000681d410044440014410000005848012164400c100c240c1d2040182042002040b840d40d80550044c0d14005010034400315800000c1940c0c0102c054a41d01c0c00490503400300d121400600601c40003040c8010491490041106a400400075641600001c910354412800d40740e040800c8405030000300034014256405a5000c16805050b5403048816080c2000929514000100201004240400215141d11800039a6403002404d01260104803580c04000c3c502490605068028450f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 144274604 1250 144273354 144273359
    0x5030d0603150504051f0e030703020601140604080d0c080706050108010e0d030203090d0c1110021b010903020a15030e070f1701060302150f27010e030a200d0503030406050709 77
    0x54440d5030b0113030394010000c2c8074002da8803240f00f0850500c2c1004401311960b814142c07021901c02d10051400324403940c003905a660408100e07002c803c04d020401d500520303051000780203941000031440500700140c1405229806e580c5400f880ca0301caa150020940c1d8105000041c150005420402401030204183c40c41d0029040c0d04074202c5c04211464449903024512040b803160041c004412514003c541800001420341d000c03031103103e03031900741320016848540140413405d80d040c50404064024a08515118555000680d050940f80038a42019200c02400d03008076000398441c0241080e004140c5510703a90701c401c1e0700000591881411100c1000c450903034a444018420001a00d6000b04801c0d0283d4071640f03598840c0c0c11011806c0e8448004100e480103440086010410f1801a4401c18060210003030004180161003d00c10f030007a4000d00d414400601d155503440300f10441200d0005802140d0b00029822545184014000d400008240000d001040d0003491041d64180ca81124559 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 144275854 1250 144274604 144274643
    0xf0204030b0601022b0e0306090a0309080a03140c0c030a0303050a0f1506110f10090c05030604150b03031c060501180311150d1a09070e01020c04110705030d0603 71
    0x802c2c81002c414180300000e881c1741c03600e1000440c00f02d44d50501d022104803a40c080440d19000c025142c8600326030290301008101035203c14004040c0040d20041c0c6007001d0782d03a401400c0170f0303a40079400342c200d81b02065440cbd0003881000780b140c82d038000804071641909075040c05401807409450f000403103410326040681c8403000740913445040f11002d0310365810500c1c20b1000c039140c1c0c3c10458640c509000d280100720074500d00704090314003d0b0130603400003020685442c00714100307203541e80240e010350858010403000c00c524a04ca04455003800300f010851003584e4001134110711401c03240807400c0c110030039808207403041a440030b003c1c0d502c280c0b1084074a082e14001044950020b10008200d0b90300d01354460b2981c1003c40310303100ca4449986c0e1090070400c002c8030b908280d50744010a51815909124000030525080d020260072805601700f842c051030315900002d45510f08018440d000d80e84801041042992510445528541001c183da481e034111480303210217800c05d0720066032844059000038250700d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 144277104 1250 144275854 144275863
    0x30e09130b060d1709042003011401080f06040902060f04090501090c0212160201050f12090d030b030c0105090d05010507120c090e040311070506041202091302061209100f0204030b060102 82
    0x1a070130411080c001c2e007280d9400c00701d50340105161174100d51101c410318400d0030310b90b600104910403000390380d40740c0d814558040500d20f007540c415030400c00c04d4401c2c0403804800502c92500200243c4001c5000402d0b40081009482903890f100400c0b40b00180020341c4201541c841c505a40c0400010b200b09042c004040380c0d48c210303468007a2583e100070001d000c2c40a41a2001400d89441814074508103550007002c1641a0414811501e50b0b140200030060008014003514a0b000350906003040260f1038180440c0c0c0e10041c6000490512030001861a2a81d0b10041e940280562120081c0301c54508100001c01844003103580d51703074940c105410014018041c01024054480c440b1400540e66965142180d0007140011510414050140b02140341d440e030310000d001800f60a10f006040d20107074414040980e0000f0480300920401c00d8100d40140e441e40c00301c4541c010b0b83c180902454803248030060070b060000c0b00031200245440007000500e2260f8000d441140c1c01900d1401c01a40e5800040e611b5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 144278354 1250 144277104 144277129
    0x13303140d1b050d050309070902180f0a0f05040e0f030c070f0f0b09010f1106010303090f17070b090a23040e03032a040b0d0e0c01020a1509030e09130b06 68
    0x244c12002d00c940c4e40b607101c0e2010315844524207049070320542d80c03884540c0483e03009028210803a480e140c184001818040da200070900d00559072030301c003a40341841c01c8041221130300981d03103c0c0c0c0e1552004102220304019030310520a101f015280e60b07003c458aa9a03480340301d842162280500010700155881d0000e00c0707181224102e01610740b401e4902001141c21510042e425010f01088090800b40c05034104150341c041e620030740310000c1c90f80c203003580140c800050340d00000100440081c4021855000300710307441140d030680e640640b10740d4907400258507a00e0a802020704642c00c6550f6030782244000c3c009603d41e04d019101008009060840360740c0b01c1c4001c54000c91164400c0c0d02c00301c88150224a407406c040307400807401d810f0640760012140e090340418034920a194644400c1c0c07042078003d211101014100340018403c40055035980c150b45c0c01250a1258072590303440c000000d141c011a02149041d80c0208040f16511b8845108050f6a100b0441520b075248240d0000e1081d05022481480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 144279604 1250 144278354 144278363
    0x726040b16050706090311060411010315080a060506012003030106030513020904030806010210020d200406080f10170a0b0703050112082208070603050603013303140d1b 74
    0x1070401c4130388402d405800740880840802c01500144401c4040900005001d58410241c80c1d070000a810700040c240c0f041185c5003841c4d20002c0004003c12070001a40c1d2241da5849039010600340d40e0040142c44505009021480200d00300410345242c400100065040c6d80c0d49031000c00046d00c5410f54001c0405241b44000d412240010108021900039024164452014030407180e43c0c0030f0090024017660050014a001e040e212403000f1189042040d035a15840141c010241c100b600d0100000c01d250320280182c41c120124001240c40700c030100c000c81c0d000d045064110b180070064036810546d51690a0425612030841a01180d28588603020b0a4100c5024911082d54a03459845500143d44031000051000e284200420054404203801400400549020b000141d18019014050b42e030000e05062082e49800c0025044041d103034500b404800c80c1d03c02100c6070600103940801d16801e190800340c405442145140010030b0001500c130303d420095035a106070414148148410420b95040041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 144280854 1250 144279604 144279607
    0x402090106080a1506091701020a0203190306050603100918030203030a0b01030615020312010e0106120e01230618060d080c0a1202070e0906070c0b0726040b1605 71
    0xb4466500346810520740c01001405a0f042d901d04203c030600c5500020100351250810001c03001e0700d000c8020400d2032000250307c5c140c05540000e40701e00c60302c3d121017101c10101c00015a210b1182d44842d02400d405805941d1b241014115244034694a1041009840c1810303042e142045158915500a5905400540c296240c0c0150320020b0500c40041c0c0741010307542c0d0f000003800d02d2000e00c0240e14180f15000703035641e020315940f04000381e44160000002e03100003c004000141c0e00030a0798103561041c010029058107900038180c09084050008282400e01c000401108200d03000c1d040e02078842121007000e0f1402c4010140c0e160481283c14039880144d0705048000b150b9428001c2c1841000c0d0f0054551080550350f506044d9140300b621130380180e104560a0120060030004150045c4011004090310f10300141c0c0100110081000108180107035000302d00c0980c02481414107030034041080ca91a801c000701110f428800c200c03415140ca41d21640410107902c03407000c01c25030913402e0380d5070700c2d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 144282104 1250 144280854 144280859
    0xf0b25020319231c0207080307020d0504030c1509090c1d100c11040902030f060f060d02030c130219050c0d0305061503060a090504060e12030c072312030702010c050304020901 77
    0x1810650042c5200d0790f08000c000e0800035840c05144014181180326031481501da0400309da00a25020103a11401c007404030812007130001c20481f40044088424541c9113070070715102900102e40710081580080c1480307061010b001c0c0c00d60340094a04041d0303010a008240b50800007410016500d84540280000c50340c8401a800452095018449201000f4001082c0b0700c07959804640b030244030325103c60890300b1041c18040c1c1c0c0b00402210a0300003000320b4070706a03002036540001c0d488941200c0e082e0f2003030805c03982c407091404054042d80d0a16000d010200d40000c45003002070226405400c005240d40a58240224950300070321810b4000d64010b0800c18001c40307135408041e5241d1028000d9544014281c01c001298200c0b80220b0b84254414100400c080394034601491400d00022080144014140704120000d001d91040da9072507504503401e01d58400380b2401184144030020180e0529018400404011001c03076002036002c0c109a034000c20602c15071a80c2100c882c0000c0c0e034004d60242106004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 144283354 1250 144282104 144282167
    0x30316052812021e07051e0a06060503060423070e0114040609050114060705010609020a030207020906010807021c030b09090a14060402150a03021c05070e030a0f0b25020319 76
    0x50030055114070700f107070b8080c1d59a11102a195415040c001840e50100c9403c0b400c1009c640107500003484154000c040301c0c03c01d41c0e00e503000d5001c1b040c0082c0f0407441c0d80c500750f1101720341000304a0081140d44103511095844803d03030004400c030403a0060040f41401c1b000503d45010b842102d04940300382c0910920025480300300f0025030f004000903219992500804180c80030039100400d9031140607103006a40f80c0c803e10500480c90b2004290b1814005e40d81c0c10450507680100300c000505190108200b0142083c2c00b00f1f800030300d0100c540340d810044803c1004139903d40001d100f203009020f411840b035030300701d1503881e00d80c0c0340d0040b20b000750802c414030111005041c1c80d401034105c1d03200c1401c015041001440c07580c440d0224007040b807108a1b45940c1030014036a00a20f03900900807042d40500360b00c0c070345529403869159410318003c0282020100041e400c08100c42001e0200210413030070031441070300c018025038941080a88840d0850075860307681d6028080c2d60913000400c0d52140507d180f01050782c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 144284604 1250 144283354 144283357
    0x2010e15011d1b0f030103120e0306010501030509030d0603120e0d0314180d050c0f01030603020108011a0702030322060c0203060a0b040e120315010809030316052812021e 75
    0x9a1070000c15401000d4200380c042d001d41320181400c56140d604d9414000800403c0300d4140c0c06020300300583c40c5080d240412030506450080c28049100e4030781074045880c1d03100b40e2080c078010038506880801041181d48160f900400c1943d603540f100d030f01400801c400e1401c220740003004100114081c6106028150242042040c844c0d0090911095400030900f40d0000b00c00450301d503001349100c4800d52400307250203443c8101c28030f030800c000b03070641d0f0010781503c1c03041c042d2034240800160001c800150360310031101e00941c040c0580e40c5544116211030515500044110b080c00300500c004a1075520500c10320301c000d03030000c00518058a4295003a4010304114182942054845161440000c0104608049116481d1559989241404104810481980d0075504200e4150701b807042040300041640d811103103412080700c800541907000e80d01ca102c1d6484101403a00010141c2d44c240f510300170500c06904040c0c8440b4034003114070381c40c1001c038410510207200c2c2e4282c1c104082a80c206190 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 144285854 1250 144284604 144284611
    0x201140c03070801090b0a1a0d0c0201060b041202040f0606050c01110a0c0312151e0e01050d030f020703020d0b0a0f0905061311060c0705010219080a08070e04050702010e15011d 78
    0x9110146c080e440f0304400d60001c101c184c00c041070148c00180030805001c9417003440d0f0744080030b200801005007808625803451080b445640340c0800100009002c0d0f542d594000d02802600000070421070f40d40300b40c050900d0b00100304e852000d5227020607030605802d1179022266281c0b11030350b5508034842c003990103440e03801052000d01069550703030214090180a401c0010040c5c007500c068150380e4915120001d0b1200c03541d03003000c3c1d00c50001100412046e00c42800304c48400d5414104090f1400344844200d140c0a00d81d0b0029603c404d0442070a0280022a88418080c00000c0030501001003c40703105029210600401040f41e4070500014100e026240d51444600d442900060401d00310f030f000091f503d030071910440006801c101001c002d60341e01007014141080300a01d01c114100c20350386820036140580b01805c0d0610049000081c4131505c2810541d141001c024020499824500f5000340203182c0c44200010034410805105800b40b103010040b812982c000481a0508001101c146011107018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 144287104 1250 144285854 144285859
    0xe0105030c04022503050c0c0103150e07020f0a03030b0406050102010b210c04020d0e06090703080703050a032c07061106011217040608060109051017060319030201140c03070801090b 80
    0xd40c1448800c0385810742d0300c02164061b0b52090340f01c0c1d0a52081500b4103000c11940c80c14145071621007805100c40302910b2007168441403030710394542d0302c4a030141c1c144035403201301d200140580d000c00010141c2561140046410640b0b0400100b901c4000680c200d07004c1c840425444400044031480c04082008038800001d105001c1c3c1d66903c00032000324007a03070001b1801c040c0c016119099012141410010075900054403c01000a545140c903103140e0303403140320701c080c080150000f503254409000c0d07040040d00d010030070030034140402031a01d6030001c0c0340c001190031950301460100107400e500c40e058442c1c0c0c0307811610141145900c2e0610a042c850b00d0440111207403000300c03807441c007094844000b0348014511a103412120b4502140010000030044c1c121500c6604a041350029113544440b50341501c002081d080340d49600d071303400003a01d01814130b542c8207000d9176404400300c10503906401c440c40551030708107044520384030350001449070302080350072100041780307800100300c0100710b90003031400c40801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 144288354 1250 144287104 144287137
    0x1090c08060f2d100c0b0a0b1f1e0302030105010215130b0103080d0b010807050a030e0f01050907060806060c030a14070510090b0901060302090106260901050405070e0105030c0402 79
    0xc0c00301e4805404503e2100b0b5403c1021200900050f082810003030100307800d185000a00c0c904181e031510f10b407000180840c09419035900d42920b00d500c842840f001104d03100c0d01b54908007000c4481c0144003487c0c64182d01c01c00c0e0784d8041064585070103402a00d0590301b05030050901400d030308820340e68000e002005580050119000c900104514030321860207580141202aa5150b880081c44159956000074038100300d01303d009c200c803280c0d1000a842342d1080610b00420b6050229140c07620745001d0138200351042d403900341800010700c0c00068410496829880301e11040c6e441e907003080300381d000f038540d070001c2600100706d41811144205406503245400030b00850500026445851928030036035452000c1d10398581d0000180300348900620f80c0034415a009010f11419580410300c103850600c149018400c80e1701990500f5048407241c60b0b039141e009078118a043ca0b0002506000c1e003020b8400350b65601a0741400703d0600c83c02004176058030800740050403081c90003802d0000a6000c0140c03e0a000c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 144289604 1250 144288354 144288379
    0x1603020d020d0b010215130204020c0a170406030e0708070605090a1206020301090f09020a05040b0301110d06170f0c060a03110c07031707020307030f020301020702090c03070801090c08060f 83
    0x148060318504074454000110f40199100181c13400718100448a8488207480403c80040540c48805a000d64150340250300c58101d801a185008041d910041000f40004c030003041c00407801e0003400440b85a41d0b8140003001074000f0041d110000350007a42a690410f13182400414000c0b4020403101401901e844c844135a200149889190f20f0b00049680940020041042c01c40600541d80715504444042000b45030550010b0821030451080c240611748541440043d03940030342c4010b020048d0085015511204503c02000034038207130240203141007600d440e104203500e00045020000e05600c3c000c160421a1104015075508110025400c05841304101e100398102100a46480460b060052071518114070305107035020800c914020310b24400740151030150364001401000c03039802c10b0320f6403520364490003c203004e44550040603410088450a00810700200c8000758810311140e62400c80fa81d8a4400305425034070f80d5000c0d075000808036404210b1600c0c0c103401c5000c1c240c000030b00c081c02020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 144290854 1250 144289604 144289627
    0xc1504031e030f05010e0c09040e0c2e08191815050907051c020402031503010606050406020c191412010c2c150304170301120201020f0114160302 64
    0x7100701c1507000020303884614441c5045124083e880c050205000000e101d0301c0c0c00941800300e40140e80700380b4401c07074686d03400740c440280903c04510000000350002d01100020130881c2c2c2602420496400000051a03d4040307481c0320302e096a0240740840d0001468220205010001e00410903001d4412081c40d4a240000345440c02c1748480d228000c00302254078600b0004090070708109600550007030004000d0b984040340c10001101c0f506504540050320390301c2e1080c02c01c1c003500074060f0880d0190701e041408100301d074001e07000c1c000700c0b20507038220b94003c400c0324240212400c40c462404d0310070412100602c0704d8900c02025200704080500425540500d80b000c160a50b440b0410140101d0b0390b00e00a141914070920b050040d400c0300340c8030100280c031150f0110b1a9041d0412400401c0d107030100100d07007000104003480c02ea10301c6104e50300340ca9507103c41d0f42c0206807440040803805440751441408038000180100540042d81c0c40c0741c600590b5400b17501c00e040410041c10f007010594200401c1c45440c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 144292104 1250 144290854 144290897
    0x5090a0e0307060c020d0c0203060711010603020a03060e070603020f03340f0905030a05070b160804060e0922120302040317071a010810020a050904022106060c150403 73
    0x600414020459000404000c2d04140354080c100c420040c91f2695480940c13000110070760011100d140003000c4c1495500c00078011310807900025881100514000144121038022000d500c2a001c269940c1d59545d58041d41280700307048512800d09001d0000450600600440000403030640d05ca940d810f03504900d40e510700c030100c5113603400403e0020b0304000342254020f0b04000501030590051404500d5607e440340d680600c0e208001d5084400140316200d00400130250041c103030701904a40c2c031945c03a58005410307008641407036401500740f4400161840048076001c030030b1955010441000f20419207030080003940c2c050b000c1c0c0905800700070000004543c100000c054851100c115902c50407030b0f2400e02c14644002130b42d002000306480040c4100ca501041c4031600786038007200140c1c2da100b800e070103542e14000d41025030b0380140b0200306540f1000a4007400700b82c541203c1d01703d94250703942c04104192800b031002250702c551300c00e0040003102c008480010fa081802414901503100001c83e108208 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 144293354 1250 144292104 144292117
    0x915070e040b0616060e120702012c06040e070201051b0a030c05090a09060302030f060615030406060b04060302091018030b100929040903050910120c05250b0105090a0e03 75
    0x1660700c5286281e12034082c00268420f000147d0700f940380070080d80000b0298000d50201c40349a84003024000e4030900c1080d1100030303041c4041c1401d61525075402103200c0c5c04108690032400341d400c0200142e00617041d14010498280c803020340c20308108801c001140145280701445050201c100302103a800d950340b070086c00c014071200d500811481d041d84141401c045500c0310000495102d4424004187d83e4403803007800402511042c56100d031744a061080241504d54000312501c6800500821074590580081c42c44007815988000c03220212041101d01001030400203d80480c0c401040c0001030441c01d5454105203400b41c600c403c161544c0c2c00000b29491012800407035080192400301014540c24401c100348021682048401400d40300a071607845980c0880d8482c000d040c2d21420007500504007020b80f02c0200d1410004400f40c3c6070080c110f54010403075103103220b440c050150185038200c43d0074100c0c0c80d84103403440740316403800d030900081e02006002200d02c640c83e000f05e02001ea0040005d0020f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 144294604 1250 144293354 144293363
    0x1605040b090a17070812070b0708040f12090602061008030405010f020102090616031d0d0618050d02100f0506030d030207020a0e070801030c0b0c0a020f21060915070e040b0616 77
    0x4e55803411542d0b5181c80d5507240d510441c0e100074042000801d41e1410815030020701824214295512480c00c04080f1203581c40c001c0c0380e60304c004911240035900c200d0084c10303102e2580803140035444420143c003600c100d07803064094545c0200300610055200e2204012003280900015040c0700c9a0350008031550410000e440d0058000b09001e4149640f0a44051a041242c0d1107032054500500c00b188080d1814140580031644401c2603000707503010b100240449a8100040d2840724a080754001d407500c1a900205400900b03200810342810001e100301030180200034020319041800c80c0342580690420001681e002d034428000003401000f180c0c000c2d115a0341c0d580c070078105604619000c2447c2100d9005003800740d40a11804201010009002481d15011074400c612030800a00040c00d042e4624601c0440015514249441c288001861130085240030b09036500b0100c100c02c0300359060f90440382c040000340900700040c82e504103603000329a00c15001d040d080c901500601005c0b19162824070845 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 144295854 1250 144294604 144294613
    0x103050f01061a090906010c0203010915050a1a090702011508010c090f080624030304060c21120f021207020a02010207060203041d0a020c010e151605040b090a17 71
    0x508032402807207082d028040120542c1280c0350000000e49042c050032070028040c46034100442c10716809113400300d00180e8014001d010b0301429251415511510905d117200e024101400300309a58294041d461140c0c80488016507a0040031040101181c00074042d08155540c900580120104541661020b440340c000042100100048001c0c1740c0899a44040c0710b1540f46c40c0144014080814a0f94100d100b016401150070420691340304000c450581e055450300c80014002400303a001521041d03507034002e01020079110a0800c0010001c101c001a4070005201d4100d000c08007003145d8007909071441441801814207103400480d404801c3c045d140800580d000e1a0080110b60f41080f98a015206074401303542841e2038850103c032540b41840600c003200750740000049a0366802d6040e80e06a0382d1040c0244201240710400a0716145c22500040550b82c903500014000302c00314030009850300b21036480718a09803601c43c54401607000354580310307130041000200250345985d24288941c500010005030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 144297104 1250 144295854 144295873
    0x30b130c0f0e0307060f05090117011d0109090b060d060605030114012c07050703020a020d0b0603060a02040612180b070807090602011b05030709120b071214270303010305 75
    0x80c0016050b000b15510030360040006200031179002c20514110241d5007480340c0c8500b030900060700c0403101040340c00c2d51a1484c0c00009542400443c0c03040e0a1440e0441c26507150b600ca03c1c1c5841980c2c40000041c1c11303845802c02007145810101501c042e003d000e6003001070f021352034400007030a50311180c5401062002160051002d80a08119060018850403841c055403002c09842540c940004013070000b0703c4404142081894000c1c840d55280c030740e00929a808090081c034140d10719600c10354140b0701900c01c00d4000707150b81c09144226410b881c040e45542e01c0804414800d80040c1103401c0441c0c0c1400d000070410740025104c50700381405050a034440305100d180640d4000c045e1445540071404685c10409000d003e03800100b40340c0310405441c5030503035032540c80a50030395001d60180d0041100517012000c080c02c4c000c060b40e00364050481d5940320000100403041c4030f0309aa040124964680d00d40b1008565600c590342022691002d80303007124401e50710040d06507420f50300240d206442d0fa40051510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 144298354 1250 144297104 144297107
    0x1020d02040e06030a02010206060f03010e060903041d07080a050406060302100201051501140d050703150807080601090501060516020111030c1501080613030f02010612061a0609060a030b130c0f 85
    0x210b03603004200350018000f510254000039603410024212500401c000311041040d0b4800790092030003800e004045448030b00344102032681c2c945c814415001e03c24000c8070b020709919040300c1494040c045c107603104101500c032050490020070000d0f04c100c4040342c1c2e5a0f0004016140e180905030140e0040d000081e062030715807404807154004411460421000c840c22900c842c1c0f000065a5602094000c000303440c0e03a070810203034010300007050413a6801c03004034000941a400000d010080e02c2d80003050b2007403a641e81125005880c0280106000b01e0000d0103a03558a0304c801c807401212500504d40750481e400c5000d0058195400040b03451002c2d0041e0010151680503440362900420030311004007070500c1d10315084d410303000c1001310040400c8148444281594402d4001c0806485002541a80c00c02145030200040c490785200314401413218020500b1460503005071442403501902072454240810411001030211244044d40500b020f0844240b8141501c510114242242c40e903071020300c00e2050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 144299604 1250 144298354 144298379
    0x21306030207110a05060703080a0b21070603060b0304020609030c0402040f05190b0f030a110d050f0901200d06171e060603070510110a03080610091203080c040801020d0204 76
    0x43c190300401d01580200300c5525800b04690500c0d805240c8060b81e40c659080000103841c01044d00d5074441c1c91412100201614415403407502d8003260b04895255130780307020513801d881d51441044c1c54000e0030320000b005828190000c104101c80207042d0f500b900050b60014040342c100342c01c13911070940441014030407420500070002c0d500b51030680000032a85461450221882000341b43e060254000c404200529007a400206141c0c04d00480d00c1d481d8081c1d99060001800c0840344203841501070000708000c04010320501d600158840d910303486800030141d01d20f0895002c80c0b00c0c04943c0b0358a00700010080865803c03680401d84450140861410300f1441c8407050801c040c0c0400c1d260010024000f0580e00014194121074003170303d01c0f40c0014881042aa010704120104600c0c034010200090100b50340054100e20468040300e41d00304030340d80079908036002d84c41e0780100d10b200e0106802034000309004003510341d07101041d10900c40c6400c0d15120240e0a98004480907405990046001c1c00306400015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 144300854 1250 144299604 144299633
    0x90801061a04050609060d050103030c0309120c0501030c0e0307080c0f2b030c1202060412020a0b01090b0604050a060c030206060906091810021305030c0409030203190201021306030207 81
    0x1a80704401c07034100d50304014911891040e1442028005031902143c1c0303d04003a00c03288079943c54104941c2d0303500c1c1005460100400340450005036103034000f140888810710381c0c44101d0b40215090b0261400c00e001580200103c1d01c1071020307c00416035030142d44e6410040c1d90080c117445000b524400c240382c0140300c003400002604070f1080340306c0c04141591010030081101c500701d40926240c00c0c00201e04059030030b6000b1504c003510028899a040d064030740c0006e0b12a000754860700c3c1089140d000260700300e0710b40c4981c4000a012100c22801042212881c2e00010340c800401004181ba255680c00000c200109603440318010a041a05a00c181030b010720245501003415501a5524a800070008900b242e0040c50811a07040c68000b80040503000c00100e02c01000c01e4008541d170300312080d500703015080c0c00c0c40b07190b11134828070800900c682410b003d51000154907800075400e2000f107540a01c42e10414100c61011503500748200e007110310003014003a00807c01e0b5280183d0301c12032414013294a51008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 144302104 1250 144300854 144300869
    0x8031e0c010c051b0606010c2414040b070519180b030108060403020d0201021804090501060504020f090405090c0f09071404090b0405070f0504140a080a0c0806160f050a02010e01050709080106 84
    0x5c02c1000310300d0b40c21650040c1032607030201090300b410110300d081c41200d04001941c0f0340881e1902e07a140e4242c0c1d8148103224042c9000d1148140959074040c0219164410746810350608141001e00310820b9004078030446859030000034a12001c2d442e011a02c0003a0001d031301407002d80c1d0105003400b0606405101c07005c50001644000c0d49000040850032803928442c52507103008a07506d040481c14480c0c00c0d400b031800380100030300955461030a40c4000342950458000144618a40f00c0414808240000c2c203003d480000f912049581241c2030070007805010041c030b40030503c40302c003051040c5294124003c0000d48440c01c00081c00c003040d8000e00c01200c0c0c0c010441000c3c4403581a5541185400c201a03504849402100107003042c40ca1003c1030241043d80d04c103400fa442480f04940820241518084c10740d8803030812504140d441d8040c4c00592900ca102610100320344405807442e80307100c0c900030409480240004220208074101d8203003150000c465040016120343c1013403040c2c40081c052000208000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 144303354 1250 144302104 144302113
    0x40c06090302060306060c0313091509050402090c1e070501020315181b07080711042a0e04090807060902010f0c0503030a0b0409050303070801030c0f08031e0c010c051b 74
    0x31540440d48920001c0c208612512000c81c00c031f04031a07010401c0300d803000883c01c2030314011544c0c0d032600d00250103207504810b01d4844184002c64021b6a030301c9424441c0760010190b41541d10391186140c103d911a02a02c24074442e010042001c0c018002c0041c15924410343c0010394916240c1003008000420030302c1c0ba072003501f242d0200d4000d44880041e29401ca40d143c5040000307203000c180569480d1195250007002c2c02030100f25501401480e001e00c0082460580d014031944000c4004151610226000541e440060b8550642403a2080d40c101403104009000000c4402c10ba44030280d998008841c1121400c0e1105094021940d004c0c0d032680d00322000341014425400641d0315039881380030007805030022070303924202000030350795a80043c21019048000c1c0d03503407810150707030033401d16009004c20794001160385030000e083c844002d2503100302d5610a01542c10a803191040018100d4601c481c2d1078040003d000903240f09000f031160200c0c20300191129695685200e544070001d202c00043c00c40580c03c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 144304604 1250 144303354 144303359
    0x4031b030c09090f11040e070e01030501060b0c0d0804060b040f0221071713020a03120e1804020607020f0a0b0703031103040506011203050d1103070315030809010c1109070305040c0609 81
    0xd1502c4d03002c403aa000c03282103012803185000c2002462403004444040c0314104000074220b000c01c68103816640644000d0100c16200c0041c2d00c0e0070312960f105544294081c05409403010321501410380c0061103403002003034000380040060b00344c40c1c403070401c45201a400909101003011690507450f00d6105c0b0b9030300c41694a402031025141c002010046c1d2001c4040780000341c4a103101d050903100481d8000c0160403d1034890410b0304040c5040441c601c0812a6400350702100e10b008000c814261510864000c00b594541e404d000e611780101c8400c1360400e1407c120044907944403007030180031300101c81c2d00d5500c1d0803460500405981e9002c0301d0b045502c40400170310010820204801c2c0c1511581e840400b40341010340b80480b030318030510f0f500110306894018003840200702c52000390700441c10350340c003030100e083c01c1c00714195182c140d44002888807508000c024141d5001d010399541041c081c448054030080a4008900503420845200340029560001c110400254a100784060495482c1c0501d07800d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 144305854 1250 144304604 144304613
    0x604210305010e13150c0504050a120b15030c12010c17060d02040b1201060f03210207140d0204090b0a050c0c0604020105130909050a031103160f030504031b030c0909 73
    0x64058a030740c03091340d1241000303020f11400e000c2c5007019002500c010413510b044c01c48000d0840e0028001d00d48a0515034200080144141101c10007098210b0034100e69500c03001000e140301042e0340045a05406155841142a07580340600000c07040301d07800205940c2003031400246003040c0c0140481c0440400c00c24882d05844aa051301103181c0c0c15100010184442e40002c0c00032004606c0380b240541c01c11001103480400c1d410f4403401c407032261500b00a9803d0060f03403000701c01e003880390b201c0059101d600200650188491007003071401c2c01400101c40c800d56900858141c2d20401015100084a007092003401d500c01e12645501000c1250100d0526800d05545500c402000d04085d040020115440c2100000d00c120a0700074402c1034010402c43c00d0a141046c4c8510050030140e011594984540c120a034012049400d04003014440790b018507803542d5401c241c912441020750420000b4407000c000501070206800389002445402c945281c65450308140b5030f134454100c00741c06401c0c54072440015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 144307104 1250 144305854 144305879
    0x1509170a170304020a030c030f03020c1e150c0102040803090a06020a1a100b04080a02040b0a0f061202120f0a0606050a050a0e03210702010e0306010b0f0a11060421030501 75
    0x701d01e21844541da91903e00000e203040201d038001508810001000000b000003400403d0030f0303544240c00707072003001c00c0813810440f058044007420940381c0c8031403144201c24030b0001425030110500881f02c0f42041e00c2d044900b07003243c07c15040b400076680001458160703890142410401400188028100c0036000c3d0b5944040c500300350450400d070840d1401003aa52500d50401070054051400e0107502c886d80d58000b10b03526401030000364007651410036840554204080b00c8015a0280050a000303286420011112040d022030b45441c456070038000480300013035460a1501072071005d05080c0b180d041c444080340840f0060f5020b4018840d003000880042a08203059843c1a09182040f0500c0715111002c2420480b0716800041014440310a48210001036009000004e000b0780e034510203811044185503aa00c1d081c0250042c00009201d11080c401c4600c00400102c1010300d0004841800070f50414581001610102d51079110b860000c0d01c0206540c0d0080c00c00c1d000c5180c00d0080d94500788591545 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 144308354 1250 144307104 144307133
    0xa02120c070e090c031b0112111e0c0109030f021626011d071e030c091d0d02030405090f0601141b03040e04060501060512060607020a1509170a 63
    0x20302c40c040000d81c1d80b220a0100000c0908040c055a60b210345d144541040c04548842c21070100d0b16111240074001c040348034950003d801996501e241078200014442d500401407144170203a00100044001c003002801050340861007512410300b51060f0303d00280c10040c100c441c01c851020901010414041d00f22030f44000c80d0b102401c0101040b003030b80740f02d42c090001103400e072a101708903103180302c14030314001080710484040001050b6200400d0200c40c0b01d910b0188070260003200c0c3c403041030040218982c420a000b0648981c0980750400b40307800359052810160340c00016030400700e4100184d08000030300135404072543c0034040e0603140c1200041e0881001d42d4820900160100f030010001403540600c0542441c407d08403521595504000030803a0400c6074111250350030500001603031406031042c1d40160461407946940c40c1d07290400e02045420408060b60302480d91300000030142030b0242d1070000024550f40d107850781c40c20311248a040401d000000350f000d138800769040c0089042d00000000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 144309604 1250 144308354 144308369
    0x91e140a0321140703080a1805010e0c030d03060302011e0507020307030f02040b040c0f0c020102030f040b03100801020c030a05130504050106020a140f0705090a060504110a0305090a02060714210a02120c07 90
    0x650104180d24000e223186426001050366107081d00c081125000001c6022051004400300c480b050703841541281521200d00c0b00a02192803240d005c0d03000c000500345c51080c001c682c40c1032801c2c1015500000d1424440c0d910603206821282c401405504250054202821041e80c081c466150a210f00610000302182440d08000888c4001c07811680309204440c54552040e0000b40c03601e0f15820301c408294000d803442c00450513010030004461806000395400e020fa09009541002900303e015282a48220341210500846c1000841c803070703980e4480e8074060701c043d90040a41601518000b42c8031501008040142d40c092801100380d190001208801c0e1107080d45c00f0383c000d807900224a4013408280e00100c0e0311a0030800189850900700f0003901071043e040d41c003807240d40c8498800039141c8080b908060b400c044200801c0300401c0315080b0a0700110202d000f110b00d1b01c104c0c454906075686401c8825480f414000980c168003682c100030070780005110307685152901c0500c0c41c2e9603030b69000c0c5200c0d540c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 144310854 1250 144309604 144309611
    0x11e030b07110708010605031011120a0209040501090f0f06030c051003020c010507180608010602060c09180c040f0501080906060f0d0803090d091e140a0321140703080a 74
    0x300c146104105007001c081c0c00070708441e02d06072107203805801b8110b035026190292080039250b034454000760003041100c00410f07110514018040184411030b060060a060a5980800c26451681c0b10303845907a00800b101100000c9800a0f146c46a082c0c46560300e8045200d030070007030b040c004210001d06030000c0719411030700c1046410890720190080e00401100d40f056510b020b0420203000c0e04501502c00d0002c600418130480d90311214140c5038080280034103801644088000350f40034602100a01644c2c07c020a100d03400f450340301580261110840356045001004201003109004031000d090141c002401c04401900d4162640b83e42c4038401081e05200c4e1102008440040d1201401c88a85c07540200b001560392030a4001b15036241503101100c4000f42d0b8031040010f02c4c0401d80c910041c0c1c2d991100b294074510b480c1c004032030881c05074070501a070b000146500c0000000c1000580390b202d0506140c030309400704110500504040c5e035000385402103560400001d0000790780100040d62110303c81c030001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 144312104 1250 144310854 144310861
    0x40507031a1e04020315090c030f0403121d0d0f03020a121802060301090506010f0f021e010e07030c05030706050322060b1314091911150f070605011e030b 68
    0x800d0b01c00c2c09801e419001840001404018032402ca0901c20f801020780309003aa54440280380883c5200031a282c00481e00c0764404500001d206070400d011051078820b000c035000307400c0102d08066084034150004568011000344c001030340c01010050002c50320781421410700c1c640c1c040141501ea04c1d456180c0300300c1c1d5a0121a9005139000c03405104180d0050569912581c5a44d07c210080c1001d1340c81a01154003104c00380c81061041884040c9003000c0ea0281140744090545e01d016092038510700c9400755251030712514400401c224240007140605042186d0301e19140526040c040c10360030000c2000420020003040e81080002500d20899202d5802230002c0e2504244006150001d10340b13500021400807503101401c2600800307000031005807051130035102c04000f075070f60f40c1c0e100d550117800501c100d03411004910f400c03400308a500000b42c01002000262418500d165204940c8101085000309150051208038400d060141200c080101c95410905503282c0d420005440010003940c500e4000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 144313354 1250 144312104 144312139
    0x8160513030b010617101a070c03061505150c0c10020309090106110c04050702120d09020a120c1202030a02040b0613090204091a061206010c051506040507031a 70
    0xc80c0055030414800c03401c950b120000105003a400500b441c500007480c0d0041000c2c0486000050b0444040501d00c10b04400001c41304031040c0c00c00c00c0c060300c0790100b020380080820058024210740e80724589072030017000e08107410454904459150005055010b000e07540300101c000525030704400080310068800c00020004a10307502c1030218464201c1d84220000615a810124207401c451074002900d001000324401e01c400c80e4800c54003400140e101c65a00c11082038010000e010300341d0001d002052030b40d219004500720380311652000304120031b000c00200a000c00300c00e040000d011808031440c8007012640009607115804240a4816640d50305005419524a000c42e004080400807591000366176103a588000d4006100c0c4002d014180b440306d011601d4500c07101009158002c111600f00b240c150152101e01c00000c100a050100a1100d080480d10400100d00e1135400450160385910301131090100356200508be1009260406001f5181d018004e0010040104141c62447c503203040c2400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 144314604 1250 144313354 144313387
    0xc1e03060f0603020f04020a02060103060b130504080a02060f0705031906170106140a0e01030b060301060b12070e010c021003112703010506011b060207050309060c0c10081605 77
    0x18440c034604081c1820010300c680126040341c1c000c48402c0f00030740c2c5100a00050384111404000141c1044005000242e003690206410b020050610340c18880f0400510040b074005035802d4131941e42c0420322124045d4100030321640140024130441070384c00e1406016006020207020348401d030888804508800c0c4150788000c000303046d00c01d088105e405211055900a00450003000000031503400042101c1c20305480071811204000d0815115a02c0c6071075a20b1000000f505682d4195201c42000510072548000742c03403c000040d899141d1404d200c80080d00701d0a400c0101d5040c408040044000b6a81f8440038040341504c900f00842c3c0d0301e85008060141c0d200344441401c25071074401c0c0c400103c9004c5900c400a09205400800054940c2c44c015108050407501044800d0b01504010001956640240c82090700c40c40490f802c2805071400520035404c06100820700742e000382d40b85d640354a000c10b00e01301a50418100b00001e03060102c044e0350703007104803050003050080000da4041245410301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 144315854 1250 144314604 144314609
    0x15081c030e0312070f0201050a06050a090b0d0827030705012109050601060f02010f0506030703020607060b06041202010e120d1419020102040f230d060e07090509010e0a0c1e 76
    0x2510803030b507240001c4d01800000d0040d2130700e001503113806c000900c8140c07140b00700c0d0181c3d0001081000769914000c8880d000d0030400040036000352035000110002607050019013000b911000312004a14a0b002499040b00604043e00d4401d0b070209500300240c0c1d8100c0301000c4c42e5003c8090b01c0503030105240003080070f0942414000c00c1880703418000a140703680100d9641e810a8264000c0c042138115880c40ca090f1002990b40b41e40c1604569820801403130094001c05119104103404120b000c81d990006034036030008e81c800921480241140c40c01c642e484003040003134500850b003200310003001d000040e40d24840c1840310030901600e40c0450348983c0090042e0b450b038440c0c045460f01c8010f043c0d20000e0107900300e40b0588060080b10940820000c00100081001c110300c10108131020035002c04221162030b0b0740c90113a6440341d840c002c1500a0006011030400b0300416207000c140750a0140c0050300b102e418000744406904110080070000d000b124a4804490302047d000c03607002d9501030f0114043c080f56 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 144317104 1250 144315854 144315877
    0x105040e040f0c0803030901141005060a090b070602070c05030d08010e190f020c0d020f030d05270c09010609031109070e1e010e0402070305030a09230115081c030e03 73
    0x103c005810040080110302c03581154000b07010100d117a64840c2503485040d2020010801c20034028000ca040c01e01c0035250750190303480e00d2580540da56502038270541c443c910680350190000340813410311510710034134801448180c006100004110a004081c1c400600980000010140101d15230300d542c4c00c04140c040c080158104403030848806070758001d6014814a8103d402503e1440c60401d00100c3c68503c4040a82c000d140707800b5000e6003180c000c0500409078400b4104007402c0f50929880b5a01c503460b81ca4448000305404400c2008212402e441640319a0401004480c180005503e06116007500700c4169441001074031150425078408401540054004103200041440b00c1103110b0516254002070300e0707003032420004da028801039102c0c150010740411410030100e004240d0b15409905540e0103a48807a01c00480440c41150380300040001c01c6460303468544150340c240208481200401105008060420600298141381000c001501041c03613036440018198200610403200d80380b070320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 144318354 1250 144317104 144317123
    0xf0114010e121203010e10060c0b06010c170a0915050a11070504050c18010503100608060307230103050a0b011e0504080703030914040b030c0f060d0c030b1305060105040e040f 77
    0x4000d42081c240c2091041b045010b100c43d020900c06820ba10300c00040d10065a05c40c2c1440b02c00e40c9600d6421322014000c10304000501400b04080744003540301c003c02c1c1548054050742c0d40440c200083c142c48003500485040c00c01d011035105026041411031305060000d0508a500c144000041810079079a544a6500103003070204111176190b505006102200200a081c5e4a501c01800110b030b890001300d601c1400707440c0c100014440f69005181951f4000310050840300b4158503a000048041c509031042d24414400d03429508141d80c160141540c40b403030a501c1045403600d4800000c1c41ca41180a400003080b14940c803000d003c920880c102c5019142c0340c4101d5927046d603280342c01031070001c0520444201e038111044411951905018520044a00034010414926043c01700300803003500c0460b09a100701c04012490180117a03010302300403441c00d80c400103048050310081c00031586169040e01c1a603440c101c2040300580e0014162010340704120081c00442d0b6030b9103000c095039400400c026101c1e452 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 144319604 1250 144318354 144318373
    0x301081501060203030411090a0e0a05030a020106050105070804090507110708070603051e07030c020a0209040506010510020d090b0a03020d02070f020a050d020303040306150519030303050f0114010e12 88
    0x80004088520142410800090341e0b03803414103d84901013601c00030300d042400300258559241600085412881c9414001030706410760f01081d291030302049044540e604003083c81c596058084c0301d00c00041034282429458515141d84480340b9101c0e900904114075943c90104000610601080d0011a070b004115050992225002680c0c1c0b4950f10a1a00003418200019450045c0c001601042c8000c50351034072040e120118194098040700724080c0841c81032054035000369680300243d6004a0081d00940303034550410007400440c0300c104403583d0555006940d8654020342c449103d101311201c03607004ca529071104210850185c402c8044080c1514004190710081c0002011481a11031085910034084c40d5107105100aa81c4000c0000c0d505400602040000c501d85420814801901c8400c5180c81c0b5119000218016580c031900e480e05940040306001b00b6826115098001c0c42e0031fa5000d01da9850204400110300301c1455003410803180c100c62440340d45805030303203451541c4080c0981e02800c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 144320854 1250 144319604 144319619
    0xa030807062c0a0510020708121b0d0608060f0402181f03060c1d06040509180106031212051612060f0611120f09090c0408060421020d0f0c03140301 65
    0x180e080c042915a4016410900350856141c403c40300310740e608c502d140c0d0071b00b22102c5899810601c0108141104451221a580e003c078000c0001c040e00594402c001650f641050b0680d490860024111034aa25a14051001699841910450240c0ba00010300880d0740c6000c040407821074000644000c8054440001c01088456080b40301c04800581d08c0d16104280d01e01042800310003c0345d01900007108010501c0181003503030300c159102090301d04441024241c90446801c440640c0d10a941030160211507400050703200700320004194a130345d07050210381403181c0605051121140200c2c2409510018858401510f03041100207101c1c68140d548200c1d41e90b140500540c2a141d07041c000350060b1110440c0c214104c1d410786030103c1340e8041c4181804940301c01d215920030041c0540d07500e082c0c103101c0050301d031004200240c0318a10480b0740002c1c030321035201010140800d441d03102041d90481c1800b05c03070f80d80d4860001d414440700ba00c2d00624114aa04040d80d41e1000c0e03100768428807900000108032074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 144322104 1250 144320854 144320863
    0x9081b010e0907120e0f12040602060a06140105030402131d120708031305160311090c090d03180905010f0e010b0f0a050a2c09060a030807062c 63
    0x1004281c880072800d890200c1042640b140454042001c5904201074000e501e0007070f48001c0d580d071145412030b01100d00190503186401d14640c4074001503100000c081c0510790341401541c0d0041c0000b003090010f2401d020001c43c5881780301d00a90304019001c400a025551410300f841d000d001100350821828654514404401c0400c850300000c6d40301e15181850303200140b504840035a03402c50403003810b54617020000b043e00442504286d9003480385071a03011440e040020b49100070740c400e8400e19480c505410500011010050031550f030800305010382240e0f03440700c4020100d401e6161a0241c030500c1951054220304d03e50f500f0825045140200209585081c44100c0003501e44040442d02c10341c1c1c0c3e401102d10b25114003115400010020320028100c1401003000e4004055181000400e070501d81500108220600b007020290000d840c1480c40241003503c00703550414015900a00c696045445580c00c0340b1440d00c0040010b0307550f05c15850307440b4006054440d4112180b8580842c41760300302c560b5644 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 144323354 1250 144322104 144322153
    0x8070f020f150306210d08090105011d13020a0b0c010207020310020c120706060314011d0120030c090307030312140403090303110708010f090b09070302010905060a0908 74
    0x403070380745000814a103048494640c50246a441c400d14660f181403c0c0610641155240010480c03485418040700350700348003400051009940392040d501c3d0000b060703801d588041c1d114481c41e03a0311291070780000700d04c80c00d0306c1e51003541f02d0b4080403500c06d24030100b500c5440d242d12420700848040303481c061820064008040e1140210126002250b05d80740d104200d200d02d42d220034140c0d00020700109034a00c283c014080180c0140310005500396641c4070000225102d2090012a9543e18421544225140400f06140c0040c800030001150100003101c0c01860044803c5428800440003071594011030f4210b84042c2c1000e020b5039002ca50b240ba02801c402c402d00e8111501c0e0741001c4480701504880c440c0184941e8060703545220043c555241507a0103045092003c2c0f440c058034002280c021424040e1001d148101200064000c074603040c05510307080d015012413000d4002c18010030150780d2211040041d1030301100d5990352503c3c000810b840d40812544940802e000e1a5803d058407560707850720110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 144324604 1250 144323354 144323359
    0x308040803040f090e0a1401090515011e0614070206090d060b090108150103110d06060b030613020f07020f06070b0c091509100f030b150310080304030f020d03090308070f02 76
    0x1041c1d900c4040d0002620802c00d02c511056215066a41c00b044c0b0310206146211f400c0000091540c1c100d8035901c0c107081220301c0e0002e0b8080719a00402c40000811002240e0755007280c1404112070405070018081041d14100b40765419001c0b440c10f0a65480300b04440205400400d02e881c00c010320320740304015040004035288141c3c079840000074040070200d00310000000444500c00ca603805e541c0c03030b1206d190782e0b02c18140d0070481c2400d5080010303c0c18403500000e04101c0718880d0722850440c1c100066881e400001d965443c0c0103100142c034548a0406641e80103034110703180c050308002d800100d00031f0b0280343c102604250199040c442e49103000d82c014002511705681d00395009003c581d4800c0c3c0d91040400040d040103401c044070040910501c50400002c2203440c021a0b0725202200065070141e001401102d0f0383c00020034410700840150f070700801494681c01550170145191100f525045003440040d014000150b00c2030201440b480900c030203103601030036654031846d8a041c0040d8044020000f2130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 144325854 1250 144324604 144324629
    0x1101020c0a080703030807030e060411040506030c03061b1309060617010e06040902040209040903080f07030e03070807030e0a0303021b0301021c0911120307051207021008060109030804080304 84
    0x2500707004180d10159640040208002851968100c80040000f04403004050b0f0700d940040c59640280811402180103455800125468400f0401243c4001c5c003501d00c03e91113502004040d45012500d9680158202040c2191049005803480075111f11002400c01c0c025160000c600710900d54002e90030f8511301c0d80c503800390300c03040141125900301c2030007003001da06103d07800200f99261682090301141d102174005403d25100c007010030300761402000100c0c0442c0450003040b1002d0310340104554005058942444445c2c05544546d880b40f24106000c0d01c020000540e080c241805440300b58011540640074040072962410000d4880c20b040c0e0249240e0a604544040b051405001742d0703401041e0721242d44070120403c00904000c00503540700312405040c561046805640302d10301c01d4142c000c942c000e141d030380e005854200c0c02e143c605030740d0b020065418062400561a440c5030741da84410107007060b4080346c480da001038074000785990000304061030004011900e88404000b40084440341514031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 144327104 1250 144325854 144325873
    0x212090d081e06010c060203090d110a0308011208071e060f15061119211b0204020703020a051f060e01150e011709060118020306030a02040507021504110102 69
    0x1140c0098007a00c41428051955071022562512449656008a014113107040740711011b0742c55030f05a81045038120070701e400c1101d0240c41aa00840f581040d02c001c10047c1409070581d540107003035168180aa80e280c9250070145000f0032001008841503590015004140348540f0242031000907040c00c000c603030281c2000e41c403016005850141c400f0380004020805c4c40345081400031101d00c05000600c0046228101d24114416120481c2c1800e0b14003c12501380701da640b01040c0c41c20708040404400801030304100d5011611040d4000c840306580c112400350740c8080c03500f0f04034540b8503110030142590065000d0040c28100180611810720201c8070140211595840d40c1000f842c000d10444070b210404807aa54131180c8a0700f845250084141000e05449515a1030100b000b04219108045a44241e006100017090305100c0369a4489010007586107190410100303880d015100d4009010365159008078510600a12180e101c005081c0b10845e0b40340b6047c20a03214200c0785d80711860150103240c009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 144328354 1250 144327104 144327107
    0x60c0f0212040812090d0c09020406030f150506090103060f1205160e01140406030209090c0a120201080f100e0702210f090f120f0a06050601050c030f0a1404080604060b0108190513060212090d 84
    0x10a0082cee0709c00d1031455480d600d014180800383d8810201981010360319440450a008070603410030140220748502e02400b192450102d00d4421040034880312508044400c2040d00200e24589040d0b030741841c0c141c040c42c0107403000329025200580000758002d00c0d0300e04001d01600009159517100b842190b00d107040650b81c1604034104090008043c2c000b03091407002620f0001d20b00f54060b0007081c1c004103040e20325502c0f540074071181c0050b2145001a007000a00f550105101100081c1c0c05948d5002c0915004003a10212590f11038050214002c5c0e005151381074540e50740f00e0084c030701c2a001c0c0d019100320b0200034a40c152180c2c00b8000885407245410007242855100d801611043e40601006614000c5102d51000d580d0300701d0201c02c001c1004260031100f45200003400b070002400076100070310050619207065016105004401c9040000a0042204c4449803400c0c00940448212000602d42c685030380c071740c0b4511402ca0300038102c903000248400d0740e02e5001c40e01c20320a00031801503034402c903001e807070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 144329604 1250 144328354 144328361
    0x103050c0a0203040311030a1a090d020d0905040b04060918020405090c0108042a0b030103210e040e0c150a080f07050301060318060c0f0212040812090d0c09020406030f 74
    0x240005038414132003031000039580b8020690801c0000c5c200e40f152040c0c1e680c0e00314084454089201c01100480502c00300e440b04100211000006001600c181300c0b0800000340141c40074440c0c01d104644446080180d034039198440401340c041480c06002d07522526400509411031600100e014915090010701c00e148041000301641405030760382d000c1078545403130fa009668100d024005150040040800c0300b117070340000044c02482c0c0d80d500b4036225899030904000300481c103501500e0340f0804980c540b03003040e80034401c48011001260005030000c01600183d01d007500181c0d09941208186400419868005014090314400d0355a03000040d542c00514421600003903500c1000f00d0f00500050141c5802a0800e441882d105414800200c0c0303261204004c0d5000b17032540c10f02258005120701404c50f41030140d91034126000c0d811624051034000c2d030607a99002140681203051011550402c599035050b00000282c8e0080c860b001d810352514004c4000394854401c03d00800d15000024944008600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 144330854 1250 144329604 144329617
    0x34090501031a01050c07080d1d10020d0f05040f030f140d0c020f0d020612010f0f0e1503010e1002180108010e070e040e10090506010f0b1b0114090a020103050c 70
    0x10204950b402440005407502c0d0012080e2618901400c07201244446040024070f400700e0141d640c0c03401e081c0e81000c038102d100b003100c40c0c030a0140c1541e0206041c01900090301c40031304401403500c12110f03190008121800e0190b508458540c40c884600007050210b400009200f2901940783e40c2c0c405c44a04140595038030958a0074400b2514003540d140142c646424a42c02443d030181c0b036141c004036594002151540090301002007400003900500c020840000f411011780305400116180504000c00c1640302d41c0001c0c031004040902c0350181020b40c4003034005003a10030520049400446000c02c0e000d010750480780d01e2241c5804178484031000341d84580c0001d4100e586900e001010703619071200c00c65000c018401141d80007074440160001d0750b141003000d25011000710500113142d045515009080a8040c2c4c0076a02d00b0018450903c111203000044480b50131006901c002104840102c0501400c000703e80c64600107420410840c030342c074011400c0509540300740e808121582d0350111051007801182c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 144332104 1250 144330854 144330881
    0x5010e0c010f030e010b280f050102030d020c01090507120b060301111606090803010f03021c02030601120c030222050a1a0d031e0e1008010317033409050103 69
    0xb082d114490340a58884030490841c04008075411800c180800c5400d420301c54000e01a4160880b16001180075140300300181445641e0840782914280000b07541e405110180f010181c2c2c0007411800c00282540300f8180d00760710101b5205015a541b9080c50440c00c03003002540e21021a0002402502d0180f0030545a0403007a00c000703080400c602c1c0c04a8448590b280115001ca50710007400380440e802001441c020b010b4420b05036401801e610610400f41c2640740d619403044081003080340180c5c0d000c10410b05542451500c81c0003c030490a103c04018903543c0081e4008405100f49650003d241c07003902440250041d003840103480b44161101101c0304665200700b945403184410b00d02d440c1c6603030021040340c000e290400040d009121181d000d0803034642c400340800c114500d45c0c07681b07091010007820481c4003030038400d40561458445030742003812080c4074540d001c0000b000401604a6400381e001d1800c094840151107159401c4800c824200c061160340400c1010070001a990310034044c00351415a01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 144333354 1250 144332104 144332117
    0x5010806131119050301140c0403080f1608030703051614130801021804050708090d0305070c0812010305120703090e0603010e0f07030b06040c0509010c030e030d0c05010e0c01 77
    0x1500244084118603081c100c81804001c0d500c0100c2c1c1c1e840d2002054104198a55542c40c645404109401c40b034810521041100751071040000300c005000c1610b0460303410000d00d50383d03120025048034483c4a00c00c081c1c003031910002461014040060069407080c07005807410040d54907407000e245440d44242d003d4000165488a41102c50022100175042004611480d0000c0584416186013a42c018000c1d03601219254003c6881c0361503d80212a00110103080c04c40041c20082c40c03050722840c807071a0040a2580303c002082c0b090b40700c1d2200c03424403600000031507154083d00c00c0108076006c00b88400e80d200d201c0c6290a42040f0710b000300b1548982d2307043d26030303905441c98502c180c50701c9100181203543c555610b190302c070141e11080c0001203072403480d98041d2040c9800c41c40c200d401d07410b01030050750103285072010200b450b40e00a421104602000d083c6401040c149150480f07641030740c20302164240c050b1740d10080740144c20401040707086101302c009020b028004c090040e9031780b110080060003c2c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 144334604 1250 144333354 144333361
    0x50f0a1511070503180a1203021b01090302060f0a12060e071d060d1505060309070f0603060b0d021b01020a05070312050915040c03060c080108010c08040203120f040f080102130905010806 82
    0x203400c5c810151900240400d00000d540c1c00f01040900411703003003600560010001264a031a84580ca6103014500342010b191a504540106210b401450303400304202c0c04c001150b05405019006202c44000081e006110f481d855410354a421801600c0b10404141c03644000070620560300744580756150007400041c01c1403100510100504801c4010380d500800c07550022420ba19034900642c8104083c0000f400500d00e0009188000d107500d5000320704140c50701c081800441c4000c0304850074211100c0e0096100c480c040718881410504520ba401070390310004480e0700c1940c205024184240c001d03294601c19122040c41c1e84e090760320860300640396400811030b00b20140c8125030004d8000d4040c28122900a499a69010032070b164115401d0100d1244401045291024014480c050450b440e007002e01d403c1c0b950111340c0c1c490400704400b0402034040341039a04111400250307001044508119000f155442001c0e80c001d500402ca545510201101c01092000c1503010351812904000028103140c1d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 144335854 1250 144334604 144334627
    0x1021515041112070e10020604050a0308220308100603150b0325081012150209040e1203040c1d07050706020702100f0224040f050f0a1511070503 64
    0x4402c1e1020242805010b44440183c101100d42c0c03140b03e0540701e801c000d20104040040100c2e0101700c0c00c0455021108000014078040f07080002031350700d41061421030312100e416103141d29801141d0360003c0c0241c2e40e80018186c1c030100e003502440b0f921150081e03883d1180710031002c1e5010034007642e80542c20410104804a10306000f15840b103201b0f1a203170020214a1461710300e00c2000b0400400203007800c0203101c54842c8171840302e002800d10b4a1b01240e403004959070b280880c1e8079243c025580ca079010400328040c0c0c6680d000003148441d01c000796005d500780400b031091290426201681c0d008160840401d003042c0d01041c00141c2d000d001920321060340d60f00c40443d01980200c00440307400b070302401a4001612a0a09461540301617110b1030300050310a00000d00d132840c1e00761450540c1900d900303074402c90400d41d040755421035009680e01003184100d0806034039140c0c034003281e080b641c03146440e00014854000e184000e40c0410500500c164a1490301411320b07406928405003198000300903540301407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 144337104 1250 144335854 144335861
    0x318122012071a01030c08011b0c14030f1c1a0105040e07090b030103080c060705031509060411030f070f0c0210210c0c02011101050f0c0a0306051507020102151504 72
    0x42d0f00c0b6048002e0b2541c0c00401d5100729150a80c800c07104180406401e00c0f042c5806c2c085c107850a1030a01c511502200180c0009002491481029000c503c0500c612302040b001801240c0210f5051800b140d40c0e401d840700381042420310010520ba40e18680b82e10100c0b040e113902130305850314105a4801e81003c0c2030918a8000b00805040c0340b007071001e06440083c1000400024600850250604c00d03200c9806091070760074032400500e40000c005080081020211100c0b60740c9180381000d8540d0200d6981c0e61000c1402030410031240c080c41400030040044054415840300d02c034041664400914009580341512180c00c421400be60000c040310380364104520444490032410702d110701c52010b0030040c08c2460304503194100b42000250141d401e400955811003042400b80c0440c200030442460a0382402c008000c1c003500c004083d0400141941d08a07210b41c0211001e072000411b00b1405446800080c081680b00710001c03409401002d00d8907001046603110740c4d2048815040b0400006000c90410009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 144338354 1250 144337104 144337117
    0x50102250812070b1003050304090b0f0307030c0503070e0702120d1b05030106031a03060a050414060903120f0f180f070f090b0618010309030318122012 67
    0xd00e042040006640c5000300050b001200101900750394550320f60811003090b980c0280b14100e40c1c252a40f041000500c000f04179001c542003150005500b2002c080000d22514140401c903a01d80725210000c8240100d60416208650045088070400b564514880e544000c00304d901d940960000c51100d080c0c150580010821000150400518050500c403050b81041c1c01c0402071000401c003000600c10b05070544a449071030034195644058060640002980e02c0e01d00400c101000e44d00c0d400440c0400894295000c0c2075425001600c00c68035040440581d01d0f0030040411800030141d41c042404084182e21190040050314405652582c0c0e90f80c10002140c600442c2a40602c10b070a144802100c0a110020180030326030981c00080b40b41c42c1c5c5280640742c24014091141000300320100c0207440031103001208200a00b00460800114141540103240c51145044520503045100040013a41501200c01100c0d07902c17454a007910718450b03491000e4a102c0066601e07030045000d009904080d001802d034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 144339604 1250 144338354 144338413
    0x80d0306051503151c060c11030c03030103020d0c030b150f0132040b040b0304060c0f0f080613050a0504030f1d01270f030b0a02030c09100c05160602060c04050102 72
    0x60820381030420080c480c2403c1016140155071f40359064031654130240003942c020f15103004500f001d10324140e9030344034031062000920503040409800100606503580c400115001a441c01107403a103505d50101c0076040412240c865207004204001940c00382c41d6800314100c00901c00300c05210241d5011045102690390f55074940030500000845402c0710f40144090320301000030649900307103441d1441c15104680b0108050281c01c40300602d20319030101124201c0d801380d14100c1c034103884000109104401d00d844164840e0b080004008200e405a04030b54081c03886583c541c5403040d910107046512000b101c000c0c20a003a50508402c90a610071003000820070a8144c4610f907150088010003102035943d80402454101e19004006002c005208140d00410800041d4694600303c82244680e1203078013070080c86030203074601004486129035046d1040b1640700040f1044843c03404050070b980050b80c0304580041c40781d0400120480030840984045800c180c005162030a41c0c05184a11301164050802 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 144340854 1250 144339604 144339619
    0xb03070f0e06220504020f0901050706060909060c1e0203040909060b09090c0a0803340b0403030b0301150302060a0e030f0a0c030c0501020c01020c090903090a080d030605150315 78
    0x740c803039445000405140852001061002c8501d00d0444800f40c100d80c8118880c92052001c030a40f24000030844803103107000d00c1c215503100100e00d8107500814070368000141d01ca240040050800c00c26a00902c80d006042d195071218850284a103030000348107044d042d0050f00f0600081203215900e0f0400060140709100100f001521807020688a0030115440c0e511980303c1040c080460601c41c2d1840041c14003c80030f1443c014822240090701209c0300c0807000f2401501f040075525049030114071014079030042d042c190b141440d0400402801091420a219528007604201662041001d1100300e03580601841c1c00d1012001d401d5540946200700030750140141c0f0150b003102e01c001d018000c00240b194640702442815410300d2204404a60002810341d4440311200803240c1c2c0000d40d401040c4011141030b07505030b413505041401e43c02141d4000e500549030340300200b9000008140900015007030382e03003001502e90755010005081d8622240a410a00400120f4022402040012103001000d4400d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 144342104 1250 144340854 144340877
    0x1030605030f03040504110301060903020f121516030b0a0302041d0a0807110a08030d0c020708010606050c0c01091211030102120a0b090c0316031503020604060203031b040b03070f 79
    0x10341410b051400e001c0d1a500002030074050b84c07a05215500283c842c0114142c2590704018000e814a540ca000c00b9114031000000d8809a0303a510b4094044102000145c4010390028806100d004a00751100c180c190148240e02e10480d12070310810b03040450003054080d0644c42d50b000d010051407035680800074554000d00c02c00c01c05400300403c06c2c1340340c4500d0307141d076907280e007070415030348410368802000d02c10716414800308407014001080d2988403403800400180400421801e80c0b5241e2684e00206d5203508156000410030303003180c0500082c02e28002502c0c0310212480044414051a01078003102e01220281d5001150b01e130031aa03640740002038001850120319030032280c1192002c690740003906803282924030450a0420350741e908440509482c03421402d180850051100c18200c401007007565035002d0800044007804910000c540241c8071680e11a07c401e0029202d901c00c4820881c1c480301e41488216030b810000071601140c4110040b82d0444d2101c40044034035071451410b1108016241c00c0c00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 144343354 1250 144342104 144342109
    0x207080708070c0303080a1505040b0109030204060b040315060b07031d22140103051b1801120c0602070302060d0f0207060515010f110a0f02060c030f13150906080601030605 76
    0x1002ca0700d0189080781d500e02d103986001002504014407040701c550501080448103c0340700c9114065403000c03103020803c0c0c480c1c0c2c00100c034858141e43c4044d43c82414104d0000b0052802c40040c8144c034012072203801000d401c150000280e5002c2c2c07003526040f082c1082083d010038481c038007002029542030004111a41003c0c00502a00c1e095480e4208901a07500420164030443c07207801c001103a000301450140d031658507120f17199031103e0754a04c0354617500391707072329280d81e0361004051507444800c03e0701040e650f15610407044442ca0301c4022107a01002840101d0303040e00001d503220840340d000381540d10f480e40090384103015205132030060760455000e002060000c0e42038001c10740700d1140409004a03480d62140010840c0080540b03240030b0007032290701807903120000710380d0303440071071700300c650901d90440f06d20104001c3d1080c021521031034000481e85803003178022040208402c41d417040801a106840b081c00c040c40c46074020076240440d52000c800c1211500070801c03030358004014103000030705680ea03a01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 144344604 1250 144343354 144343357
    0x308131503150e15041a031b040509071404020f0405030f0d0207090b180405030918010515090108040b150607030e09010b040f0608040203120d0504020a08030c0c01030207080708 78
    0xc40501203600d6491011400c011400c045000708030890300080f09003042e07160340c90700040511810707000f01d8680c441d69581041c481101e11800c540603040718107210200960703040f003002045046102d41d081c400032901e0118000356400070f42e490702c0c04800030050111704000081d481510340d04444c0405000009d80e59805002c1003c0e5040918050013440c075a24500a04003401c903048810310324501038015400c0c0c0c5603012070701c4c0362600d505a005482d07110703414001d14500455090907070000d55000b1201031500c0680826040f290300b80c0300359490740307040e00c6410b0b041e00604500c103001401c0c1d500000c02003400d05100340c1e0811b1290550303124100c00b51012600030780c41810300380c011400031000304015041044410b401404c0307010781c0c04d081906100c4030743d4030700b8400d10035401041000b101060555030705100580f66800d603260703d26a601c16440390080031f88002c4a003a07102c0d13100e040f80052085004000ca80d00c103947c00d8084d1a4401701c00005400a410154082e980d80805001c40b5001542580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 144345854 1250 144344604 144344639
    0x30907150215010e090a02060d021207050d060b040302090f1005060a051b0705011407030509090109090201030f090b01060f020309041a0319030e04092405010627030813 74
    0x6001d0700621006800d04814442d041c0d00961600400f60208001c0030000b00c0d81b010085c2d4122403042c1e60340100f07030307401020340504040840381c0010f010034055241d030090014250a90000c1040c080d1540e80c1c039010b002400340f844040e4101400c5c800060b0443c00305480c141d0710995a4202d030241940350030200368150000160a404180c000a61862001c80151f02e441c1d070800d150000d01c8070a081c00d0000f045802c10b00c00725030b40d0f0880890400f00b0903000f001695100000600081c1c1d00b0341c2d40d01081000303001113030400e07408203140000d8400303000e40d240201e002642d00148000300380d91070890b040f541040c4c01c40c943e4045000c02e02c03000036556281c1c05070440c0401810b0341e01141c4110f48040600385000040c0e01c210840c24454080c000940160084044a0040341e001800d182c490800006002d131040c89001c0b401c10700901c88081852980c48541079620b641e50307483c0e02c00b000219011205070420380c00c60301d0241d142070800029805400500900d82c0341900100381660f41c24150880e2034950 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 144347104 1250 144345854 144345857
    0xe1b1807030b03070e06030a121707020703060501080105071403060301020403050f060f18120307120e060106030b0604030506040f080f03070f0e010f0e1002070810061707050303030a0203090715 85
    0x294a400c0c12440c0410145020700317150f14048001d400c00314002965202d103000c004010b8042c50a840705018003d9800c0c00800d100001c0407007161a00950003501c51410380001c0390914603040012070b000070148a01c6100f4500303038442072101204568140d03803981008101c117501d903408020103c0014000e01c00f109103440501c00400346818902c56400b040352008180c514500451003119101000016141c424140c2d2600c229a480d10b07004812174418240c4e060441080303042c0310a45141c10800245e181c100d030200ea03401c1009583c40c1041210703e100354070002c0c0455001802080201754054100200b09201d083c0c41407800403000e080002e290022a0200d01103a0002d24100e4403035040100c0a1a0303141c2443c009081c1209a140038080070003000342a8040c1c0c41d031030911300c6082e008000120141000f03204861030310f02c80c0c1c40101d01400303083c011041c078145881840203440740c0005510064490090245007140e98450030200250001040002d89104402002404100d0141d240e0b542c003005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 144348354 1250 144347104 144347111
    0x809030a0f140a02060a0f0e0909061801050705070326040b041202010b100e030a150c09080d0203070308070c080a08070e0f10050c010603120903150e1b180703 70
    0x607814014500600450740d4481c0f60051401e0100581c0d8101c1191207205040c03c109001d10301c215411181c0e503190000940e000084881030007e00040001c005d40304601c4a6080d407000a20000d901e42a100150f9a240202d44184244c00c0024080c040f030f85010b0104034000e122641c444409240c0443c010788054900c1441b0505100c24440070020300c0e11010000e0000340103c0c0c217a48007044c8a1406001020100034480f50508171996044c001018129040804c50840505032002c60780106203481c50440820030b5154002000b103000308848105042e41e030041c3d41032910380d0324250744c051001002082003051489421002a5107480a03104081c0305986450140c039000741c001d07001048540205104020b00c80d0341c0401580e440d040c0754100e402901d420b50310350322401c0c0c07151b02500c2036401c01002507140302e2008500c00d600c0900072003164040c03070980d40e41740c421801c0b403070072241c0b040400611900203900e01042564403e001507501000508a00d100c01101c101ca2554080c06035460700c006034a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 144349604 1250 144348354 144348383
    0x30106050403140a0809101211090a0f05030d0807180609060305180a140c0a03120216030302070504110d0519060902090612070309050d08070206011d0a090809030a 72
    0x140600b1542c0c03000104004144e5207915490b0030070b0b94098200d107148108448010741c5140d500c11513000c03482c020101c00c240a00c3e51401e805d48981d0304422510b034000c11144d90b0000b41c024a080d07111080720300c081d0144c110b03480048800c03218048000d01190510082c001c0700b400200c2100d26010082034280d0300c81d0052414008028140c440c040d041c40102c088020034a914544080b032111421a44000344400a0f040c455003141041200750410703501c040c3c01c810000a010401502105000b1603a080d522086402280d203100c01d805404082d005030f110500601060402b03500205610b03081113107407414024240300110907600111220945850641540204044180101e0003c1c0280ba0002e41c2480125070103d0b00078001c650501403d01c20810202e00c1e018042d40c004410681c00c0800e81b0181e4500c2d00b0003409411041e03440c1401072081000010320600303001c001035840c42d540841da00031502c84000c0c0c803001c1e00080c81d00340d403020402c11010710655410403020301100e204a011281100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 144350854 1250 144349604 144349613
    0x90608060a09110906030106120b0a0e06130b1b2b060b0f07080403050d200d090302010503060a0f12030e0406060f050c120307051207030912030c1103030106050403 72
    0x340903103400c0c0c0080c180940900001c0308066026010b043c19202c0014075559200000d0241944d80d000150001c06100548144106207440c1486114804014444c91800100299039280c007100e568020011458030680081d8201c200302e60484169800081c0180c04030002003080d503c1401d035001001011058050782640800d500005414814020841e0f03d140042d240043d202d869140450b1440029100d0304000c0c0300b90550300903503002011522a01d445180180c180c510a407900b501d40309008560703011100001400e4400c4030300e42d954041c2154a10b0f401541d958101804e04d641c00603810801040001c80d030421400101000b24410000c20001c1c00d01410015250075442e0249013011030901c05690803c604000121891501e40d58502d200c1044a090028039034000341420f6000003405004c9500c140604091400095824810f40300c655007a01141c035011401421004448a007800040c0a51b1061580240d44d0034000a421001030703e241c216031098100502095002c5010302c18030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 144352104 1250 144350854 144350863
    0x30e3f0c0102060601050d0b0102030708040305060f18030403030e0f0924011403060928020409050a0203061302030a090b0103150606050c06040807020103020702033918090c0a090608 80
    0x1034000703001401075403c03d034000030103a00ca6400901e04498031203050740c0c900e034420011a101242c02131880c40c1c44684034074280342c480d001542c150f0308107220303280480c0703100d44591900c400040000d4004c0d45424510b6800360b070180c86180805a010156010140d140d4903094a00c1d840386070301203105003050308058915940b02041200c00390421a0101510101c002d0307a80440e50809000c5450040075507610003400c6802a000c0c02070b14004101062141c91154650098000e43e0302451090200381d59140c100c004901088403400d5010014a640aa56081c550300840d000200c405000c01c012089440d030910212080c1d008441c941224010110b140c003803031042d8805031000340340c201e00d000400c44c61641e4451020304040c000032000500c410445e0b001e41c0c100c078070030356010741a00d50414040b90703a000c000707044d4250044900e0007810741d140039800d90038a00317250350001488014803200c81c1c170503e0290303000104401c801348519040030b0540d0780c0d541800e0b00149481c01e40401d42d01e00700714801d400c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 144353354 1250 144352104 144352123
    0x5010801060b0a1706060c070b0307020c0d02031506011806091805040b010317120721020307020a03120609021204150605090c0304032016080703030e3f 67
    0x300c142c10300070020650741c45407103060300c40280414030615459010000b920f1b441383c184c52040c24498080300240c52036420000c0e6104184c55002c0d640080e00c11400c0c0a5410b4691800940c143c1010f2000c40a003000c81c1c1427250058418541f4a0321610700240304054481c15170480c0c00172031800c0d001084080013150040614108a0509000d1802d05645004a4440c1070100401d1810890200e00340000f4510aa5808210302d0112070310f5400d0080c40a000c0680000490510442d0301211030540c1d10070b402200d0160119500400c00f854403510102c60103000040d03c40d07a026140c0c0e000003140407050010b0410050b10203236444030b904052070112040d21402011034135003400e2400403c10351b52030805c0d140e800064854410340c0c9030381d140f4044a60707811401002c01d041d103e0512117014810001141a40c500e51200c0c0c1450b415140c00d2020769541c00d5200060010317403900300c0f07120281040003060b21050114900022004501d070080c0001da00044030510301210511580b142110f02084070701c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 144354604 1250 144353354 144353369
    0x906080705040209060a1407020a0303110d0206071d060c0a0506010626070e01030b100e130203060d021909090303020702041118010e0a0305120a081b120c0d0905010501080106 77
    0x5004d102802243d100d020307001041060010389030b07460003441d000408450140b68000c101080c442d071241340160190107000c40c240e1661099030000c84110303000107102c6000342800d440322561900c3c0c28184d12029184c40310307165040f080c2404000c030401d404102070310005111704007500056040200c001c1110082c2c2d040b2455a068a0014040c24466100000e130000314902c2c040c0519042c4900580140840040b5070303410041410500003900d0380121186100b07030040b14042c0395649079010000680c01300740c0d0f803568480c2c218400c0c00010b28240042c054800ca00c01c00016020741d850440e201100d40703158050300844c0e00014040d0451403c0e02c01d4611003902100480e081c68012200c010200c45903907885818020704030b80a80700341c0c0c3d5035001d40700159030100c1160070840b8440c8025549410002e102c10205441a002c1200c0d0381210309010420400710086c10300b000210b80c88105120360282228035a0f50080000020b07810050040d00310280c091000030409524101c80103003103c000340e02084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 144355854 1250 144354604 144354607
    0xf0c1401140d050a14070f0e030a0b13051f02130501050304050a030c050c10050c010b09010e04060f02040b16030f0e13110d09201804030813020a09060807050402 71
    0x1d00e000071050301c0307101c60201c1d80020795690340300a00008142e071840070403000510004100c0c8050380003001c8802c180341b9a560b12400c0303441d1010b0689d1070b039001030002c205001e043d00040500d101e1800300b0078445e014008540e010702c2107600141c10301402c4401d03484940d4000540c421544010725101000b86407c0c6046480d41c545605d4460301c4244421000f0204201c1b0200e41c13041c0a010441c441c0000f80051525801c3c4c035801e0406040c540c410350f0140c0642d420082d441d011840d2080501e0b0481365210030f07503107903661150b840030014002c100021440035800c1c0408603502c0140b1002d002898004400e04942c01c001d405c0182100c000841034100304007108041210300d44800400320764503140010081140000a11654014010100400b07440c13403800000c0740901c40440c55014100d803810710501041e45240e020703c80c1c0a54101501040c000b48540031800291244265a500c88000c4507040102c80d620307400034200303100035070101c41250749554050103036140138890000142412142103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 144357104 1250 144355854 144355877
    0x71e080103080a05072a060306080a02010507080c0304120803061305060112110403050102030c0712030b1503070c02030a05030a030c090f0b0a180b0d050603030909060405060d0f0c1401 81
    0x103075110f000c80003401c1100201d0b00108002c400c148048100008a9080c075031404034070b4403281056444d1054500007800d02c0e10000340e841d00410312204003a01070792200c0c5003e540380c44000990b07010b032900f260745210800c000036102403960b140d040d0403445901400d030380c3c0c100f680400c00d16903031840540c00b4480c40c0c91b0030320086a801c40c40d4014001c000407c0402d00c08807003c1036240c039004070f503c0034004d5400042044100d101c40d00040c440d2600c9449410103500000000310b08450168000903040316040c0760808022034420007441d482034052418952401143e03002c20709101100104580642c00403070220b080d07a41500a2039000b0060b403600364100c521b4411451180b407aa4415548404c1c800203000d14054803400c0502500c6100ca60f140116603510740302ea44040c1e000d485001d0303459181501040c00c0345808400c0701c21042c40289080720b5511100100300080ca406046a641b02087c800ca64000540f43d15204070054040c01c0d1113940203241c91f00201c0d6000d060001581001b038440070b031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 144358354 1250 144357104 144357113
    0x1060e0f060901170c071506060f1d04050a0605130524031c02150907050f0109050f040519091115070c090b0d060e060912130b090f0405071e080103 65
    0x1c0034249a00e03140130407898a921041c00445d101e201400f42c088a0b07030140a44020b0f40c10b130060b4040701e80e80e41d104c0c00b960010308030868154000a4900030000c0c0640d0040216140c26007040b074003c20145000102036035180b0001c0c501e145c9180801d014103032150100000b41c0019140e25564500c1481034042c9844103100198403840b0852905e111084111244c10445200b000761804d0002c115001308000e0419100d542d40d00c1e900c901c2042c0c89040d4064100d012544100c0107501100d6024105102d004543c100700f1001d00710013804c134240043d1f1314048950002c2e45002d00c400c00340c000c80c127501802c140d01d400d2100c00b58030005401c0c1c1c8020200441000a40e180d0b03c00c0c02220303255003001416100c2080090603050542c140504030fa4100700305401643d0000c241326004404003421200b04c501580d040416500880845100c0031842403420042e40600000802c1082c100a01c2400c00000f1240050111030080d688070b000a412943c8107000e6040d0034401c0340941c0c03010708101946614660342c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 144359604 1250 144358354 144358367
    0x7030c080f10272f0f09130b211b06030c07031106010b0a110a050d03020906040905010905041412070f030507170c010b1903031b050601060e0f060901 66
    0x503003100038491280390f00d01514031442c000381c80042c2110600014041c42080d08074925030300107107842c02540440c090b43c1200c8050483e55003201202c84141849083d10130031100102d0050b904802a40350140544103943c1c2401015440c03040040d00303071030300940281d01c4d440d0603403241c60750b020300440e071000c41c207195900019654841001c0c20100c1e694840d40c41c00325201c0e451071030700d0714243c030420001242d0070604401070700c0070000503079403601c0f188103080c50140e80d070781e01590203044c64110342881003000c1d00c00c0d0001c05042c1ca010703014900d059a00c1c4440d41c00c4407001d81c445aa400d6850b41804200301885194580292005004001c00010701034941d1040c0324485006210000c0f41103103404041c0603c05440d040c507003041c1c0d5210441c4d49030054032203542c4105180c0d2001d503e440c030030b00128608041444021410315140000481c02d50b50140c4504410030140a9200c400c0070f0411300046c402c020940c003a00180e907175a01000000c4013408486603089480501c00c0001f0b12030403610b43d90114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 144360854 1250 144359604 144359609
    0x50916080606040905070e09030307030f0504030c021516050708060c070b0105061308060a06050306010f030c0b0c010b030f030702090a02030402060901080414012409020408070b0304060605060307030c080f10 91
    0x48000039164403c0ca005851b040c0c50760700c0045485000b40030090304180201c091b503c2030a617501e050180c2900c007060303101242e601f214001c0100b9048240c0314003609252450000702d06000c02e80529101030700000e031045d490201c800b00c80b10b60121340103100340803061110035081224071140c103003001d04a070b841d0018002d0501400c1d0003443c021800c0300008411001300f10080c224041503907928142031400d000903101d1030041c02c3c040e21403100006454941c0c01040011aa0894040d01d0034a05004a031130565002d049140859074032490800400d580034400c004220f6100402103950b02c0051061040d9080020301100331188180b04000240e110242107840d006001d181c85442075450740f5104045038001c40c0078a105604c2c3c00000b035981c48c400003003040350a030300700e201d03908440e41d41146006905c910b00900800b13800403c810003c42401d1405181c02c80d105e2000404c01c1a201c10101e41d03560400c03a040800642c41c0c0b141601c00079080300f10203400880555400361540b5000c28600b13032442d843e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 144362104 1250 144360854 144360859
    0x1104080709150f0306020d1407170406140f0a110304020105041401020a0c12030e0328080c0312070f0f08010b0702120109080304031206060c030e03100c0201050916080606 75
    0x4098011032500b4110642014084072000852001c0d120b042c550020b42012080c00016850072155500c00300795105a184106d000d82c0c3d03000c40c401500c85400380c03400310191088074801e03120803120034080d5500b010700e44524244c0c52142001d14006040c40260745a8407070010f42c1ca6800c03c10f0001613640003040313506842e20b16103109283c54070500100c4c640112610050b208845600020402c101c1c0010410751090095540340f01d040e80306e00400da1910802610060312450840311244c511a81e000ca6900300750154142ca828004002040ca0441d4070040c8081982000b54007007000071a013264804201c50403503e0503c00c586010319001e000b5803c10700880c00700000100d00e060071543c60000d030400c00f01090b0001c1c050304040d0f02e0090015041510101d0200c0c8040c0b104070710f104487d10800c41282c0055803155241003058030203444411210f84190703003501600d241d003c030100e500e014110340c0d42c009600008176441c090300510304121182c00c2c0d0503d4480080400c00c40403400203a9142c100404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 144363354 1250 144362104 144362111
    0x501020c1510090c0905100e0904240204210807051009140a0314160602040b0a08010b0f0f030c0f070c1502010213090e010608070906031a0103031b11120a061104080709 74
    0x14074415a000c9541c0d035440c42e442020ba40c104001c110002c80482f4004001e0002041d50a481c1001c900c147c2c01240a402d1035880307401140d1020032030000d00002c880e40a08112407a200c040d45030341e0f090100700c482d04040962980b60700c508201211a1031a00103400a000e0a120300f0b25940003400c1c2001b03000c22810340400800c502080c515034a000c5180c142c4c0c021000c554840d650501100160440000c100118094000006a0081c100e0450b101440540709161411030708040c42c003d81d4201400748125024203000044800a0311401400713181d02034000110101e161030304d02e6044000d0403000e0310459006026011089240c4034040c016200000c0020130020612600540180110350015009219034440050400d080758420744c1500d0040504455005110305410a000307028480107002401443ca040060346e12aa581010544a00c00303010104203900002050649403c42d10842ca4110101140070031000f8403075120b000001c1d2038a1810189000107040d260b0f4500d100c0c0856960305d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 144364604 1250 144363354 144363379
    0x2010c030806190306060e0703050c0403240f091202010218040e0c04140906070203040308030f07090b040602030c0c12060c03040503130f1d011404090501020c1510090c0905 76
    0x89200741e8101c0080103400f8407030402ea0f2420700002034000c5100300001c0400403004120039a11a00645104041d040c2c0042d2a00f4a15610694062280d842a00e40b1015200d1819408030b000e0081141c0c4a00265003ca642c81c0241064031a4600f941d5502043d68410062660490400c40300200c06c2d6800f15030004050355038010550410030783c1908035038411300e04050181c2d02120700c00d2660081003a1011100f190b80c541100340d90364415400050614003003440041d8500c42d040195580c0095185004041d0903074501d440c0340e2580150300603a0241c0c00100c3c0b00da02c0306004100010340c031603048500401d26100e43c1c0e1055100c3c64054a0340c500d1072070005c001014840100101c5040510a00300200300c1950381800e8140309a59006a08110440d280b500c3c4d80c0f1030030345040a040e5150502050500600582000010b01d2075200c1180c042d50280440300e94520140705c40c0080600c44c4040000a2900024880c140b1b44241c200d4030031989043d4554040a50101d86002540d07010f0340c105079140d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 144365854 1250 144364604 144364609
    0x12050c0405070207030308010e04080418021b070503160b07061107140615030312011401110106030812010506040308040306050c09040516021c12110c1203061c02010c030806 76
    0x805109855800c5420142404002a400200c071300c12240240d84017503880c0d0b00c45a07420640031050f9005000f20105200500491103a03000141450100369001403405091a102d1000082c040d03503003000716044440208a1404d09000a13061081100f80d68000305050190000080c002d003007014108075030b034000380301a000c92031007103074134aa41048100701e03211542441c1d1030f80d41c64110b407955060304c0010085281410300209884500000003800516682000b1001850101ca85402c41c10000ca00c2000d14606100384103c0000c0c5000d002c0c020350300c89480f480b102c10f20406030b000794040d9104000030804220711505480940360300c0720300446d880e11016a0301e5918040d45401d01d5205180400b884403141603c42520107090303654007074810303034007210080d100e01251508180b00450800d4414244801d03560b404510600f81e140120303801d000310f0f01421031405282009041c40300380d0010a1015914100301d094a80e10314103c14410010540e900013849201040350007000e0080400210303055a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 144367104 1250 144365854 144365863
    0xf060203150a150909110306190504020c010e010b030a210903061d12130b1e040e04051c0e24030a0c0305160e12070b0a0c050c03070608011205 63
    0x70300050281c8a40c64481807401c0c005908118008081000d600c0b00082200e164010f0361240d20554010a0460340d4a41c140314401c86a00034040e80c08203150f0021810f0f80e668805010007161742c00000812a400c888a10f00710341d0840010b80c429444180e401d000645080042500b039a00042e0104902c80140001d40c0c03108520b0304014441400d01d88560f0b816050a07030818402c40504007190480700e0302e1308043c440e0380b04105c00701142e007454000c18080030042500806084031070160089800940350040c005c90303000b0b9045000d11010510600082c040100182240805105a103110b11108100060000002c00300c44034040d501064108000c140d1401c03d884406a580b01010780e01d00c0c007400f000f00200780d040c00d07400100c0c0c504070101300303041015410003101c550706e900da42c070f8809030580802c041c1d80e0510b070318801a48910315010500c4070418000e4a000340083d152070300c003080e03146010703818004c0300399601d800703540603100c1040710a51003181c140c115410500702209803a00c1d8200725003407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 144368354 1250 144367104 144367141
    0x61c020f0927071a1615090201080a061503020c0307020a0305010b1306060e151b1f05270a060903020c041b020d030c14070803060a050108090a0204020a2105090105060d0f060203 78
    0x1428800d601d042e00503500d0341003207c2c954402d90790280e980e6152040c0d4012180345000780320f443c4002c68056040ca49c0254000c01000f00c0c11070440742040602c0c0d00040140c8410340080ba000c0c4d468060f00a80d070300b0100d00031154110406010b100086c10207400401e10b90540303030303450310600c55094002d5480d55800100c4000500340c14000c3d441c1444441802d41d1215181c0c20b640741401841d5481c51142107601c20700d8002d070705210801d0000754101c4802032608070400d000c14914066290058006101482200611440707038001c0e10b03902e0141410841203654030040200100080580d0380b03a265408503640c08000614140001c1d0481c0c02d80b002c540600c525060540398040002c0d00b00180700c00c0c0d4002d1842100111a02c29402d9110401102d01c140309894500716544004c240b40010315142e0040d20301c110b214541206040c2c00318032102d8068460300459040280c5d5a802d001c61242d0a005550f07100b0b5056484055480786d40d590a40311920041e0007070040c60780400800e50324444042440341 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 144369604 1250 144368354 144368363
    0x1090803031e0105060a0c3e03060a021801230a1101061703030a05130803010303030504050601080d09061416080a020114061c020f0927071a16 63
    0x8803842c042142c00c0050288009440008000300000200c610b800c1040740c0001030180d469205a0311a651100b000e5480c5141000d0080c441d9030044a036136041007018845064082500622103151a080c541003c1001c1c1c14540380320300400c5541c40321280c600769907044210a00e8100c00220401460900483c5604c20303c8113038680c0003e42c005215800500304bd100751546000304840c0e40d844080445628600004d900a6081480003441e6500700350b03c070a6001c0348107007410040802540d80d11541b0b500982089012035a00d800740800d1100c01c005141c050704c1742500030301d40d2101d10107014160940d40e115220400400105054982e0051803d680f442d0980303080f110b401c0c0240b4509550340d42c0144207510010762a01024888000e10210a5800f4400c054060340c04020001e1946ca054a0580300c1640c201b1000705030110780340c4541c0940d40c801d10848204491580d03c0c1d080c90142a488071a0400c2103a202c840c083c80001e00700c02201c004000c3e4605044d99503280e44100708001c0d078240c40040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 144370854 1250 144369604 144369607
    0x15090b040b1314070e1602150702030708040e180105070905120c030a11130b150901030216061a01020615060307021504051b06031501030f06170a020901150e0d0201090803 75
    0x810400f0001c0c5850981d40320200d0700c3c0043c0c2ea207079210741c042200301c00fa00b40164045030384c00e81c504008461568100341c49205480c542405a00c071a9601e40c05984001110644482084800c101c2501d0410741c09407444002d02c15030402d610700404984150194034461241480b080b11507100402842c5502100542681d6082041c1d0030300c50035032030400345814004c106d42943e03090219040c4c403d00703908080091907110200030301c2914007400d800042c2c00f181459801c100081e500e001c41080c411030720307100e940701242002c44c0000b848440c080400303000e8190b51100d01400180000381156010340781094629503201c0d5a1030004034502901c2051592015290342d081c40240000480c0501208202440b054501007054007485058402280d00c90f001898402d001c081c150b01c240c2004e200b0028180f0301050240d200e00038091810700c00701d100031072544100700c410114285034110a004061220040a50204040c03025003451280606d8034032503140000d1810442e030041c4421000f6160100131607 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 144372104 1250 144370854 144370883
    0x504060801020c0105070216030b0403111902030c0d0201080a090602040515090316030b0f18010c090314010b01090e0c120c0703080907230402071a0415090b040b13 72
    0x35000303500c64000d100c055428140020b08017400022290108464800d403109800d207503480e0241c200001802c110100302407004451038588040048049090403030010740c501d501e50707204061402a18a18040c026842c014109000d40e80000320694010404074010034031003400d14240b4001d214503003141d903121181040c0e00712001c0901028020760038050302201d544254200901c4812851884010445524030000078940380c0d2000d20640c100d410f0010144501003821512429154444248000912500c2040060010315107512000c50710000080048015484c0003c2c4000c240d8011031800c0d400d8a17000c51003d00e40d40301141e40324030345403030b11115a080408440342c1d980d00c015400c1c1c0009034045c0c042800c0f00400724101048410b6104003e00e0020300d40302180528011480e00c41d032003a0309000030008608001100400030f03075081c001403440d01d030524000031880101c0c43e180250314500384800e00001d00305050a60080d8003c19402000d56a090132404000e62000000300300c001d030110351 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 144373354 1250 144372104 144372119
    0xf0f02040308031801050f07030c0c02030d0f1403010506030714090d0f02031005010b03070c051908041805060616020d0c030b01051008040507060c02010504080105150f01020309031f06050406 84
    0x55405102c1844c502400c4c0020395003030320f0a0b00ca05031030b00c0441400750008120705500981c000c080c005401d08100942455a40009040c030710f01c3e9614001145c20044001e000366440080301d032481d4101190b0a045504003004a005030000400c4801889441c3d100d22070307440e807200c05440d18011f000307003440417039aa031345425441d02d07401140c100d01a101d55403000b4400d402500031141610750027000e050455070b441c18100c440d42c400880589440c06000311807220910541d840d566843d0007008466555458840100860350040309200c00a910340000d0004965400007141c804680018850405051600004940070850034008014100700311002080211400304076040b51000c88a220203420411016255850102d03801002604485018403c441c080d1410700c59090041c94050f0030192140246402c4520989001a2629810f4850852460a00b016449420b000e2000d141415040380201e23031b503a4102d80701d09501025501c08001400401d900031401018028000c0c0003c51340c038250b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 144374604 1250 144373354 144373357
    0x6050901060f050103090f06110c15060f090702070303030906020d020a0921031e03060308160c05010e2d030a0303051b130e0a110a0806130608100f0f02040308 70
    0xd05240802c00110000b100d6000f8440c0e050010307040b10203145200e442d652540024048103030303000c01042042c003110181075030401c494506c9840c00103410905003007560405c5060701c1d00c0e510562103248098200a40c1d40d0b400f16a840880e40e2500b0003091140c0549810000ba01034802030b409040d10110b18040c0d8a58008119030850f1180b4003420144c264020318006500002c0001078040360745c80400040c00c5c40768103102c8406d03403817602d00011a249c072503a440c415076208421082d4092050714148082c000401c151000a04c070900701502c000d5603400104c0e400e500c0464804540860300d0f061600040324007242902c80d014008c0c180d40d22001e03145005401003806032421b0003030340c0c0d2408054501c0b005410841e03290810076039120740b81515001d495000b121001b89640e4040f0307100c046100c508000c030700103083d101c0745175156031004e494902d0610528401c90bc040748845800c00808201c00341001c00c036040b02c8c202c005030209e6804c4820002d0390243c9201c101c1e0010351480001d000051084400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 144375854 1250 144374604 144374609
    0x150603020a091a070c06090f05061803070314010b0315060907020a0213060611030405011407080720030c1e19030c08010e0d110d0302160c08031b0102040f03030806030a0605090106 79
    0x103525403c0701b40c9400f01155946440c1c00342204100301244e041c4441d00d04a806400c3d04400040303298112044540800c1c20180140c0c07080b19106001a4512007a4000f0b018040340c0c01016402008501c00400e00d142c1c0c0444060320950150400382d01047c01e88d4404c0c0707c088802074001d42120707540321801071042c0061015100d01d90018001c29000d80d0403207004030858045480580d1102c034410414401414182e000c4c90044414000811000780000c1c00040e4103004000a440c4116500c101d8005150801e51f0300301c000f0340301c3c4802140c20300e0706882d43c680500148105903041a0340a584441d203504500b0f450300060048101c410300000d90362415084210111020305c160f484480c1d0310041580c044680c1a07000c03c1d0b54005e0100054207900c29805880e008030503841c0c0850000e503c0e201c800c540314094001108682000800001c80c20b50340d40001c031110081002145054a40a00c03020300e980d86001c014200402c00000c20bc0c40e81c3e0070014a41c44a0704501c0821090a0900314a4001d1040340b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 144377104 1250 144375854 144375863
    0x90501060e061207080303041b170307020103050f0403080c09010201020d050a05150603090703120e06070506070207140a0902210901061505041d04080418150504150603020a091a07 79
    0x2210184011500401c504c012280c0400046045440c0e80c0d580a80c541d00e101988800600281400038009504070324a0345220b0005002d1582d0302136a000040070b07504003c14003e03005450901b80000a40d100d20016031101c10701c42c03c65298614500101c1c0a40b25030080c940d1203034100001d1101c06050b50380301c140030749410701e0840b8218440c4c40c00d2061601044030551000c0d04403107020000b248090b00f5400000702a4988070384072000860029400d50001c02c801e030b99503849042009402501000141c001c1c000504441079030380851400110302484902a41d48019000300d940c0c032980361903013400030712103105801c1c42817186044008107009001d036121300d402480c40705203c1c0704294010000c650560300e48000031110030b402d074907010301103e402070411030302d41108000c005807901d038001083d4541604100049550b42c005418500390300401e8104600c25443c0039120012691141d1a42080b0348680c100940c83e243c2d0703041d01f079a140c0c0da150f200d1b000301c102000c02c50384500700450040c82d02e00e204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 144378354 1250 144377104 144377119
    0xb0411180f040902090f0601200a0b070801080a0201110109080c030315060f07020f01020a080c0708010501090e0309100306090c080609090c0f1c080409060f1e05040906090501060e06 80
    0x7450411083c1c491100c40030350001c1800340440c651102c1060180d60082c0c06040601c082c0601101d420013070799620300584081e400100d5900c0800c0f0481c5c22480d00802145040d41d541d5050013105600c1e0015448002c0c14000e0101c000080c1d68020740012440315081070005483d0341c107821460b41c40303500840d80769000c0072810800758110f1401d1816201d0000110510a0412500b6400c1c03240096000c0303905d03415403241418000001d01c41c2e01c000d103208900394014215492500784001d0035600c042c1c2219110754208039010150003000030a850440104444c40ca401c900410415402004140c20092000b41010044503006401c8061140a060b042d20a030360039603181094a5101d40e4100016030303009440d0b10070304200f81b8010000c102803010800c19842044441e5803580159070082e445448120380707a502c10407410880c008003800418114084010f00705030740c01c8800f01d00155009280c46190307070700005820f00c0090f901460440794014002c2104503224980140018000ca664510035444c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 144379604 1250 144378354 144378379
    0x50c090708040305030a0903050c0a12030e030f0d151707030209061206060f01031d01050f011d19060302100207030209010801020f0306090c070f0f060c090501020a060b041118 77
    0x100d2049580310b650160746050443d101ca0404402904148405600b0004140140d1004160500181d1000303445480311051003803003084d000d020f444203144000441c4d0410311840c5102c0c101081114182d41d24014001380741c07251441c41580c1e0124503001007101e0354200200203400e0318000b07088004e6134001c9503414070650381c241c100010580403942c05400c58100b440805c005041c14054503210300c105040200b0001c41c205150340603410010f0000056a44820034810340580c0d0140d66405010000c40780f02514480581c40c000c48170000d481c5403090100d0b10344070001e208155003c0d03000f40da80109034200001c48054002c3d80c0d07a08a020581c402c04985000180212051003110581440d013003020f400c1d55105010421000e100600341c4041e100300f0012000000c1303000f03052136095446030450441718801c5041240484003882401c00500110503000c2c4007680c0c002900a0815a100c2804140112444041809001241d1010f6418440458a40c040d0703003a014120310740340c0081d50305a12001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 144380854 1250 144379604 144379607
    0x3020a020c1e010f022503021309020d1e0209040b100602011b0e0d080c0d021002040f170a200f0906091801060302090106051c0507020624030307050c0907 68
    0x340660704102c0d1450400044005a5009030754144c6803054038015213078007001200042002006c61052000c8060303020b0018411031405a018030303007092010700300b0003000c503050380403c0520208079400382c1842d0b00306441e41001044182c400b822181d000d4600501801d1618100c456580103540c0040c0c50756443c100410400c0c4148581103001d03441e40c0030041a00a040c00545620030800321054010f8401ca544002080c40d4100401007601c3c41001001c81c48259030000b4280840018003050241c0100020810403822510490903503206071501040241c015442034600f440150005103070640c0002a000c4d241c0361450501552801a54004411810b1404110014400300d80140c0d00c80d0448020480101103410745440c1180c1c807000014007151280c00013901180d09900c40c40000342c0006031031410002210400c45000d0314148140b2a80c208480c01079110f08004040c101c8900c148082c00c100ac00b440142030800342c101030203a80c0c0c0c03949603003030280e182c0060542031070080c041c0300089014503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 144382104 1250 144380854 144380869
    0xf07080603030301180902061207090f0503060601050a1e08060a06030603080307050c071a07150c020a060b06040519080607020303130f060f020313060f060b03040b13080a03020a020c 80
    0x10840100034516581c2407103d0300e41c0f0b010160020240c00d1b6503c016000041c0c6500004280300d0307030320010200c410b02d80340100400c00301d80c6801038143d51914aa0404c200d4400092954000c01c090800d0b03601c41c40c9401003191800c1032041e4481250401c64a080c00703150300b00030b01c5c5006070010358071988500c1d100c50041e400e03500b0f1484004c0c81240100001030300e007803080d0090a00c01b1443c20aa6600e580e44d0b0a8802d220b410300e812402c100e000001b5010100028410341c6140061540403c1c03003101480b0501a445400312030340580308a0300d0361101c22059544c0c400300d038058900200707a09111941c00011000341c4009001e156020310a05003c191541c2c0008140c07407141c81400940c46084445a80700203803203c0ca43c0040700c02e40d45560b00d40a081c2100c2c00550f100c1c0301026150302c0b410b04242852001c0e80d42c2403e0f4840140d16000080c084803010304102e0741e210b41c00040d0303c1065103641c1201c0c8400030082030044c03d503020108041d044141d040c0c00034046540d055003259401180c0c1d03003c00040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 144383354 1250 144382104 144382111
    0xc05040c030b060706091a040b01140d08030f04030306051e03150402030d0e03120c01020a0201110309120c0a05030705030705100c0c03030509100f0603031202030403140c0a0f0b0f0708 81
    0x20041c000d250004078150001b4500c94400c400342c0c07804a0300012901002681540c048540144030f00040c840505d118000703e002003012151000d980f10680c544400610010385420380e5200c00c900010700380350203500503800400c0d01034201c400d040c2c0e010070300c482001d110b14042482030189801c8030310484201702845000b40c0e0005c0207026620750701c44050781c0d0007550948264040c09035090007461114800e02400780214240c0002d0b98607890140002c0c00c6450f0f0300043c4074842001d005112904d0030020303521b503171a082c041f0507651310400c00b044d80c0d03d40310340744100900d2440001500c40410801002511520748142e04480c0030200c010b607442e017581c9a1250141c00a00d6580500c00400e01c240c200396000a00311050f1a1520b00b48442e8030244d8158000440d1100e440f030b8410002c0545c8649c80c1008100c14040841c11418540d400416120a144508a59150102d00c001ca030150901062121560050841d28991010b2801c0401080100c4000c0341100c4c1d02030000300d185004a001c0c621 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 144384604 1250 144383354 144383359
    0xb0c03030112060b03010501032a1404020706020c0a080a080a0902060a051b070816080309090105060903030408012d09050a02011803080c0f010b0a030804050409031b0c05040c030b 79
    0x250381c00c00c00e50300b00c040c0084409503101c980700c0900507040d44080c4203241c085d50180300301641140550f42d001174042003074006000701e540c6a16003080740031754400b00d0912190080b900541d032203285040030000f034080e0300c0c03d4841038041c0c10f003d80e04001c1c2c0000103158110307954a402d201503650150390310440700d8015010790418000c014030103950b032145d402841040c04903003400c00380724180a01c0da071810505070426002940140c02008451aa890a0302d00400c2244007c500e0110030102041c034140040c0b04250184030301080c881e015580034000d0f5000f600c1648020002c00010114940700e2803a5038400198600d841e1304019103803801801203100c12900403008281c3c80c07a2603401100c00c108031080da4040301941d07660100014090320000d0148004040041c03130314900c0c06024508580320810b22038410002d1000820001ba121010384044403811640001c51104500b030a444c482070640a016031400c50900881c20130403010440c070169070050714100001c1c001d4650980403211034400c0c3c1c50b07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 144385854 1250 144384604 144384607
    0x415020f160519090903020a11060a020a020d0204091e0c050d050303061315060e0a050906010f0c050102040b0d150f05130513080a05030108060c040e01060e0a0b04080307050105010b0c03 82
    0x8800c0c107100d5183c0d000c08008142840040d65524455012907940032000c400503082007000000748050a080b4a20800c0300b125070301e14026401c0c2c0b010b0f42d03171100c0420081c001d1103003440a00640d941c6a0185101c0c136081092441114203009140e0301c1c40008020480d040c0b1480d030000f140d0390401096021105a00400462075174a8070320400c240300200000c000940b68071640b980c1010120380328100c00a1807a0b40f50007044200d050100041011241c0240340202003101c1000f48581e0301c0680400399071554149840d24004900308070740603204507040036070f900f1000502e40d940460713150f0041031066840f65448810a0b16604460036912481c410180d103c0c0e00c0015800d4030800c0b03030f4403064000c0c2e0700501d4210b029003550340303a00441d00202401c0c00810008801042120000d1120035030185000c10b0280c03030319007440d03007c0080f01c03010300035181008660310910070039496034400c1101802c9007140c9561a50b0341d82c1c1d850350781c0e07a0128400322825400c2000006040d80400c1c1901c203101e07518806503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 144387104 1250 144385854 144385859
    0xc090212070c0c0305011109090a0e030f0c01061d04020909150606090117010303091e060f030209030c030601080601061106060a05041e0203040b01030303061d010501140904020415020f16 82
    0x12034040b82d04100940e00c00701d49220020003d0002d20440c070000c010040e002e07480f10448420001400002030031421a0390a10401442c2c803403000c000c56656880501e0850f440d00c000f03028441c010411508560003041e000011101410404440c0740d1065108454424456485200c0541c5407002c003104112502c4640d0041406460000040d00c00c8010603d00440e005199000640d0350400130b070f02c16800702e201400c003803100143d52100c0500018030200700e884110b103807540050881075803400e0a810503a0110307211400303650501620260358001000c803086540c50300e443c81e444017070a00ca803002080f652483c1e500000c202207200781c41443c0041c5190b115510b00014000501101285040321021070036141007502554400f9500544c000c0140e01c800703604524003e030403504603410003403500e9000c00b000f600c140060325505041d50310a1030403401e40c034a80200751150f401550440b560060002c5008525083c3c619400341c0307201400d9080740c1030060000342c1d079070310341c03001003030300e070f1014004580c00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 144388354 1250 144387104 144387107
    0x70614090d140a020a0b01120302010b06071509060902030d0e190302010801120503090901060e0907140d15170a0b01060801121403070204020a0c06050105010801050a030b04140303070c0c09021207 86
    0x1610740c003c000d0054441c0000b060f0390305c0b8070600090f04414120340c0c1c0e4503410824190709104802403214141e54042c0381c158541c56102000d610b000041340c520751200545010403009802001c2c06603800b80403640240038030070001e0000d1310031a0340395011385520006000316041040c1c441c1e0890360107031120706140e401d1001c010000009000f05a880b840104200201ca8440c44440c0d4003c2260b580c070a080440018104100000054825020020000b000b080c04d5505c0801301c4240301810381001a17405154481d481000c012075010000c0c091142c240b40c420603601003139010360107102d901500c083d0b80e2034100545a0010a00541e0308040004142d20b001612964201f00d400c2140400c40342440d030035a0005050b40d109201e40000280640f10400810265014080c00340c482407c113080b2030760612010500c0421340d88405000816540003040c00c0c03000e0301c0034917003072500440242c80d5a0318107024060032000c0c00440413906411000340016032030b0114400e4a9860b40f8511003090340340c848000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 144389604 1250 144388354 144388357
    0x6040b0402130303051b12040e0702031c0b0f031b030c0907020a020603040c030803100305010e010905030d020f0d02070615080609030901031a0414090d0509060a05070f08070614090d14 81
    0x3da8495000b60b804814001030810021425001705650546e98074103020500009c044082c00e81020345d403040c0a42c41b0344119410b007020502584000001d5800211000202030141c03018641c3d80502825017050411056034400c0c04807144254100c0703d2110301e641c24000081c008450590042c1c000035030200040c68101d0085402c54010760007006200d849813690089544251030f000c40325010110701301300b000340a004400c20002901c0081210b021030761a4582c82e8802ca816002100b40e00250000d0040c02c41c41c01e480f00607284c89011521840c4500d05a001410010310384004441d40100010718401c000822a110701c40100c0a5801c04101c1001500901544d030002511040125124000c546540c0704400000c620094990a24208002c0081c00d151f20380076064200b00c0304014100c0039445404c1126504446407404660b00c00483c1080c1c40c4110312020004c042e40130005011041c00442c0d040301c540d00c004a8544001c0752103040066541d14040d0140302c0101d2030346482e500e08001c00c0320 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 144390854 1250 144389604 144389617
    0x3090f07050d0f050a06050903070b0702010e12030c040b0304050a062f03070c050d020703020108060316031211100c020601050607110904020105160308150108010f0b03090a0b0f06040b040213030305 87
    0x113044920242c0d940e6071760015683c01b2100080660310104d011024410042e01031074012010b40000c002d0058080220340c0c40f42420302035801030190000101c0d40c10f0704240112002018014611034403410300c0e203001c580320603144105890307446c108001d01d000f180444940714854000041c00d900103108103161303140d80b904001e0183d02842036200d44000480d03030501c044110081e9503405081200d00f144001340c1010720240480c2d00a5001034101c03c1c10750301c030200c070005494000c2488030140601c80b0013212800260b503000790b01030040c22205805c0302201d0b0803134440d0017850340035a205a80c0381c41c20300c4001e004102010300030f01500e0300e2420703480c1001c9031070300d4001d401032401034513100d14041c95800300c035940394044000a04002c1044140039400d0917103c42d9400c02d207081c0b207007945401d5607003030002d003180181403401100002103081e04c4001c0181511850748041ea0f0f41c0c5900c2d2448075004001c10440f04180038a017070880781902450244200e07405158207040820243c0c2c21a2801c031070030380080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 144392104 1250 144390854 144390863
    0xf03020409052701020a140c0c0604060c1a040206090906040b1903060f0c0f260c1b010e0607030908040503120306010f030e0703110310050a0203090f07050d0f 70
    0x20840400c10600c140202c510a80030910034000c1c1e99038801d06070002082150070440c0300c0e4410b1041d45515035001610340001c003d040d00c0740d51260003200e00316082c01c800d0300e815079100b00d001400040003a0001a00e441c2a401000c240c80440c020b41842100c0d402c08030b400a511140403c2032004600c0c004555039041100074100003001c103807040c0498614550401400000141c1840400c10880c00d4090012841407844084c4020b1080b02406401080818007003400d01013004401224510540c402c4040182d03035170240f207100d0802410229240d803104036054101d4907092019003440340705001e6450b4403001c01f4020002030351032060407030062000f1074084454190401c40000c1a640401c80500d014a0038400355590341400000540030040481070035051606113403d40c40742e2b08021882e03200300e0340c0201c0501918140e1200090a003c034600b03009002a20700070a2045444569000c0e52194800804580d16405800c04141c2c1e10052840391a502030b00d012880741c009a11040c81e1120389104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 144393354 1250 144392104 144392107
    0x608040605041506090b15090a050603090322061b0f0b0601021009060204060201050f0f191103150918030d0b041503030e090f0103080d05041b080303040203071707060f0302 76
    0x80c01e5030201690901c5c0e005007101a15604500f0103860141c495602400c88602d08038079141c3c03040046200d40e4280c0c8200c510424003c170014504001c04c1c012030f28a940c071080030009100c411000282100502e010f99000602640303240300040c0e002e841078860550b086200c070008820140c3e40c90402d10030003008035045001d2602100301001317590290900b13507449154056221814680e008ac2103a000500f00d482c841402d006004000a01c0b8495039003005c100e4404410803001d1507a03480181000d41450f0806000c000100b003160303100009601d0010b1421107020400d07031502980c00501900c14564007c1c99001004030301070355040382e0b100f0080e1610141010440d803000e0701c4101c030075402c10390095004c145100351068a43c60000c41259100d400701c60b0a10155045441d501c2c03607801510001c10f60982c2c0d440100d018006034945032660b803104c10941034002925040390517241c0d001500c040b8041c2c410028003081c83d501c40480c0100d18428000245aa24a003040849080e040d03e181e51707041c580d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 144394604 1250 144393354 144393383
    0x21b01020f0d020f06070c020a030b1005120a02010305060f032802030a03090602060702070b0a03090f0203030307030b030f010b010e100908030d0204080c09010308090f0a08190318060804060504 85
    0x7003800000101000e64029180141d44400d5040c20440002c01d40000c111201c1c10160040e5140d000280c152500501180116556140c00740c4e51000c2a802c500c0d4840d0030040807501c1d01c0c10008101b00c815100ba80c0601117529100d0a1010016a00760400c0d80b50700001c520ba006001e103490a1141122046200c4000c8203803071b00442d091180194054000460b02402400303540d80400000340c0014040c0300a00c0d850740741030004039640c001c0007407000415840b010071500348501d800c0c1c650340c8643c0080c20380e42d403410054400380003040c0c810700441c024050024003075a8018180704040905a040c0c548400d078842e41810007076011005003403030080c00600030700800e81d40400c1000d80080040c0050040c1e4542c00d2000704c5242018a1074241e108466000040c00040e101d1404d61342c901c4001e4036040784100d1070304001007030168160047c81071842030346c01c0c2c409040041d00409400c14007d8036018401040040d103070002c0083d41c00b4503004a6414404240050174a0340310690080c05410191391412 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 144395854 1250 144394604 144394633
    0xa091110051e12070305040c0605040602060a0e100608010b0a09060b0a08071701060c02090108160e1005060c03131d161205160f0207120602070303060e0408041802030106021b0102 79
    0x3c0c001d03601c500010350740300c00304020024910600c0000d4012424031030b05007450501e00a50f0340500500c9101c0107074890480f00d03e24101044401c1c1c5510281d8018880f540c2c60f130405d18000d14000541512440c8a00c01c009015440b0b8400c000c141d58008190030310f0303c00c4070703041a907524030b015160b1020002034455100c1030340003403c20720380070b00342d81c1d5a9028044014010082902d1040e04134041940001100140540425058004075007503001401c4040d03a035003603602401d080f1070b4080e582106000500010005d800b1000340704c0c15900142d1411080d0b200c0b0541c030582c2c00307507110300700e00e0b07058040115480840001020f0310010042c604203c46d04a400344c00d0058890580d010410603404001d103940c800d030802e251000050840c802080c0c142e1501010032008240701d1405400c99034001540000d041c440d802030000b40c441d0200401e4181058908a04681c0c0701c0d118281075801ca33400c52049032480b03402124100e0b034040d402040b5020b003a0711800a280d40c00d160700d605502c2000c1c512600803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 144397104 1250 144395854 144395887
    0x80a06060e2d060409020304170a0c060b1504080313080703030c06020f040b0c01050a050f090a020118030c06091806050f0402130906090b011d010503010b0d02120a091110051e 77
    0x45c8140d14002d40c59091a140c04041c2d50400340010910a905124000419134000c54007070322250043c1e070110340940c5010104445007014005c520f0202c02c0090b000c03452010000c004c00c60b01003400100e110250b42d4100d19a110b1460307000c0200024903003002000800e142d0340180c0300d081a80320342e5030320345662040210f000398080c42c14804a65110301c20407210041c1032260365400582c080c6902030500d0986110f40c3c4819114600a040c0145a2101043c0d8800407400300081c66100107c655199122200030f494406644240180300c42d5800500c3c03600122400b5040868201611103c420307407811003040080c0d0400054030301c010001d03590004001105000f5407004061103940014a88080800104591440c042c1507941400454106603a42da201080341d0440d59011a21a03c4440b0240311001a1240701d0015000802804c1840b04100095000c804c0d1b6034820501c8a14544100040c001c241d08152100400b0600500500703411856071030a039aa000d0407140c5081c9411522038042c1020b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 144398354 1250 144397104 144397109
    0xc06070c05040b010305090607030f0207020307090e2509090501020c0a03050306040605040506090112140a03090609092c0102040b071505060913110409050d080a06060e2d0604 77
    0x1110140804100342e003494440e90102e0303082840d0902407403400c071100e56a10500503040104050b40c0c0d12244510480c181d05460304158000d055924841d41c0d0443c010140c40c3c12620301d842c5004900c412803408100c0e4080340204003100b102c000c00f0314a03103410b40380104044d03081560595020850300c1c0e1144020f0291010652217038895036224244641403104a515942115000718604400e2105507603401c9a8603044480c5490b01c402c0c2c0400c0391901d41185031b1002d84401080c881d07040c1e44c600b0103400569000c151646980c27a00c948035a520300400035148031490b41c0c103014018401220303502c01c03204070440403000c0100c0050b15180d03403480c01c1009035000030380544425031921840391003540d86000f4a50030410441d4190720b5410802c0034404d07a40f03c0460010300d00560b00c1214000382c1c4031071700080d0000350414143c3ea0751118810000c0c00d880d00485402000364600b0750081210707801865800c5c0000d01c094450140301030020b0300f0300c1a604c2c0d0700450800c1c003150f0380c1e5107203810ba40720b100a001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 144399604 1250 144398354 144398363
    0x70e0a0e071106011a070f2102060a0b09070804030c23010e10060503150a0f0c0c030809061b13050a242303040c090c02030915040503120a020c0607 65
    0x1014212032091904100061700b042584000c401c5026510043d0340040c0c541c3c2503080b11a54000d20010f141502d42c100c10303500280b000320948400700d400c1d42d801060680c411045a0014024010384a0421440b00b0080b505000415002008035001c00d110b001c0640b47e10f440b90350004055504507030b4400f1782c00051940c400c4c0c80e07034540c041240c100700b0510000225400e030000510034142000e0010707448402c00c1504c1800c6503444030008010982580262040304e4040100f0010780307040280080c5070540300c18099010420590120b81c281d140020400d02c90341c0360340300d035110420540c545007119611180e596101031442810124007a61000d05070002071071b520200d8015400b000110000e142c80294150051111529070b000e2024041e040c000900c0e40000f50b120340d207035624903240c0c4040d21250420500107160004625001d90000000e10141c80d040f1501c02d0007600f01100e9603000d01c06c03405541c3d00350304000e95000c1d1205541000c0c0c050540d080c0143e540b0320006801207840703500902420364 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 144400854 1250 144399604 144399617
    0x20d06031103030a02071a0d02130509161407030e0a0605030403021b06040501200a061d03190c0c17100e03092214180c0612070e0a0e07 60
    0x2040044040c1c50200600381500a10b0401202440103920743c1018410041d44a403400841f0a0100901f411502070b81890441152120b0301181030040440c600d00506005590400200d400c00040d03400b41904c02001d03565450b6440100100307001903400c113a00440900ca06000072444c81c0e540d00051001034030b15035603015101e00d082e05000b8540325406800c039581c11403940020a0503250f14081742c007925002e080c60303031541c4103040d8070742c1a1803e000c14021450040361002001c105240c2c0100100900c01807030034a00020030011148c0724405c221123a04070b03030302190581803c81d0141c403100701c0d66401344c101644026a00d1610300702c20054200e034640503400c4130883c8500701c10184204030418504c9802541810300c540081113001801c145d45401c0600ca085d003000300b20205400440b074804c00c0c92b08d46c01d01c070300b40104130308407000c0d8488421311180104280b81005003003130010384040c080c9440140f0b0740d0b5180c0e142c3c1076a82402c6240101e801c90048840401c0c01503a00c1c1031907000d1810356603541c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 144402104 1250 144400854 144400859
    0x5070218040b070c030206070c0f05030315100f09091a1f030513050d080a020c0a0311070501021f020304020d021002030c250308030a020c150f07030506090109020307020a06020d06 79
    0x15142d4080100440c0c28004810b004401003540003485c02d61007181401c06410381402030910340000070386a03078014020710002080241d20840c1c0601080301e500c060700c40065401c1d90100558041e580580e0030000a44d01c0b01040000500c1c580001b900ca5208003510001340000201044506600076204080704010417110f00809034140705495010144a28110386203c003503031180d48aa801c0301075141080444c201003560f100301503044800003100482168286c291900d0301030002725000c00401f03e540204080001e595002041092141c0c645410703824082103815940f4000b500013070f005030303003141d0560604001600d62403409007000c041c0e40c00854a0360b0002c0600352410419908803402e600c01c5115484519084009001c250703a802001e0139141d60320304030284003d01411403002520b01c101100c4000c121165188030340a4140710221200c41d0359082019810b841094587c56001000c5100401c41d110f001e030b000c0c5400544a10590305007071469226801640c00c070700807040556a0300c032000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 144403354 1250 144402104 144402113
    0xf0c0608010807030c06080709080d02150109110f130902040f050907030e030a0e0114030a050702070608090309010503070201200c070503061302040513050709051506120105010f0507021804 83
    0x341030062030349000504980b03085a8500025208501c60305050140b05400301d80d4050107105000c000c1c19090b421074004400c00d0400035070312042580070080348070282c00042022300d2580100c0c0d62426101845602d0300d00500407410b1682d00010002e503154600b454007140104680c0000c1c001002000e0030030402074201000c01c0b100350310160400f4249480c00046c7c4840d400048142c2e0352594842c01e0448180c0040ba005030f510b458404414810280c1c0001048011a0290300241c0600b501d82d00703c458071503d440081e80c0210094800060319030052094041070342c45900290340c4240e45200115515852480c07030743d10000c000c2c1c07405908585c049800a0b06400410910340100300440062005041c49800204540d56820001e0302890b283d40024071907000181d400039482e54071a04503614281d42c1c600030343c010002581c15007a4100e100c00c41d0225450324401f03903a0703d440c95901ca50000d910380801500c0010b407039150901071000c207221807000b503544c20700149040003800c601c4042c1e5180901e003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 144404604 1250 144403354 144403367
    0x142415030a0c1103030f07051b030d050a05070807020a0602210405071505090a05040c02030c0604050a0501060b09010f0e040b030a030504080606011e050c190302010902010210020c100504020402070f0c06 89
    0x140d4038160b00900c01c00142581b1280d116410a15a04100f50307a000340c00d0b11000e00c03071008804241d85101c0040d80d0800c0c210709503c114880c03641454200603a40b52640c04964407841a200c10380140c1c484900100030035100d40c010302520701103000781c0020034519100600160740469007a581030300000c0c0100030040294991f4207041144d49041440c1094060001e80c1c42c01c800c0c0a05809150f80b02e010010850080040302e11401034502112700034a4036290555039000c2d2200b04803695400c0000016804031000e0a0b501800c0e0305844403001c002c0d44180807035000c3c5942d0207181c1d106845618101d00342d10103000a01030940280d8900f640c0c1c60810b40003500d00341020b85039078100b084041c401e498003807034640441400744c46440e205517103800b200f515600d80301000d0300340c40b01664005000341c00c041e0150320840c3c085200381c00303494400a803814a001207000f11403400d030458105600c1843e407842c440d8403081d4894030051005003806000e072184c0c030b510b05a44100701da4800b05114148241500700c07a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 144405854 1250 144404604 144404627
    0xd140607090b03010501140c07080604150c05041406070302070b2a0303010f050d060906020d0f1802031b0d06020706060609080712030804021210020d142415030a0c 72
    0x401c00c03032444d4900344c0000c00030030511003134840f42d0401240e280074035941809108003d1000c5000c0380e00e41e090508040d00300103030300503944124624150201400d98042c0b41030780c0880304171407910001c81d00490203101150f440320741c0840840c0100e040225106941700013a10007a91600c00d0709a81e4074243c10b034803c0e0008241c00442d6140d00510040000541140c0204244c8400703440c0c00466921902d07141e000761882c2180200f8560020030840b912800c5540079890100500600381b002160341e1803510840201950040d4050b008550352802c103283d04200d600b503802001d44003580c514403e807210422a00042001c4134455100c04081000f90b50000050001c0d1800340081c00720b07245065500d0f040010b02050003021f21003081c000406641e551404110f0f008540f00544080225500000c0020b61100300ca1141da18035004a0103e41d011050708503200303449090000366071249500555400030754400307080c2d82c010700c68605416608100b5001d54045e10003c03201195000217200050603a80013034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 144407104 1250 144405854 144405869
    0xa1101020d030b0d0201050f04230a0918060e2406010e010801060203030f0a060b070501060f091104030803150d05010c1b030e0d15091a160804110d14060709 69
    0xc03c1d030309029a03410610300000b603824241a96904031761501d5041e90b004603405031501e103440c603420044032584802c80b610340761070840350003003005d03100c8032580120303001d103407841d0b602c0640c0140600c00034603d0340c41060780850751411110710302241d910038a0301000c000c805042003d41602880207079608000038604086090824586540c10858001d659000040c0a0f000080b003000c00315446203696480706002c0e251525040e50f0754241400d04a010300614071440d5900c011070100020041c04605c41c0558918010209614107031540d16103c50039000a0090001210a0301039600c1a641e030009800000788600004144807081c0c1c00c014101036504141000c08003e20082d510010340e2060f03a0410050085406131800205400e10300303810012984071341590b61602c2c1c090014081c2010003160502d4540d40300b22901e98603252070a4425455034250350101d00b0a1020500154030f2a008004902c00030b040001000b0320b5480350000d219003a07000e42c0f0190007040c00d001c140740c4d00c030f10f010028000d103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 144408354 1250 144407104 144407111
    0xf0902070204060f060203030705030406060b040e09060c0f0d0b06090901290703050403031d03071e05030304030b06060f0c010603080901080a09110f010c080c01020406120c0c030c080c0a1101020d03 87
    0xa004006e504c91000030f040c9000c2020000010741044003d5100101401407210f0440c0c48540b5084d4000004405903150442880303803100013510203059200b1506180c007000c102c42d0400403045d4617040940035002c0702e40d41c440c10900c101d54060711000e00e1180200f2884903014041c205c0c0c040a1060440d0002c3c0390b0008090402c542d00100790410200c8049a030326280c100103002c003100c50060014582020b45134540503a0b2800170f0502c00c0c0c0c69054600c503140340c0c482c2c03241f181e40d03108040e80c134401ea01c4020305800380d250000398203240600240021030003810741c03585001c0c14040021700b125170f40d400c01c40e200840459080c000e540e11241c0b07039038440305c80d800c204140341036902c0c3c8240c0141c1c1d1201702841080340c1101c2c070f84940d208011031001d044e4840c004584405132290014083d400500a81c000100d01d280349041840141c000c2810b0300c83d01c2c0d1103d42d074208543d05c0848920803205010348141c2c4003007040c0008202e081010075001e5005140c00717a201c00005000a0416911803940c0007018103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 144409604 1250 144408354 144408359
    0xf02030403170f010b0331030504060212032a0d0603050d0909050f06130f0501032a03120c0311030a030504110d05060a0903021e030c0d11190c0f0902070204060f 71
    0xc2100f01c0360414106205410828040401c0f107600342c903d20b001c20b200c7e070003c500c54420160094080c20036110941c0a80d038003070410b50a0140d16010449681c00301e03848038800c0c610002101c0a000d86110680d1640a07d40902402141c09441d201d510032035607940019200c01c074455010140f0300c0585038058041c410f605040355510311008015121520581c00d407170b40314008184030f03480b42540c0854100280081d60f540c0c10203540184180300c00e14804080b4025150324007580540010a4a038041d003500c8150700c040700304683c10301300e401c022001d00100e102100b2040c80700704060302415a081c4d070041800d20b890701d4401c403240e22403091640100031040030540010000300d5859440015040002520503850030b08078500189540c00410f1141d9070b40600e40c0c00c01e004001080c1d42d1a1290071180c0350340742c0800844010b4800b40c0f1382c0c440c903006280b0030000c032400040d88084980c0107280303504802ea290410644032a889a2198a0503640021040c0441c2460b0041000800e4981030b101034852 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 144410854 1250 144409604 144409619
    0x902030109080a1809050c0919091109040b010201111e04030605011806050102010b010c02010e040f140f0f0615030a09080309241005090405010e060f180f031c0f02030403170f01 78
    0x1a242d152840342c1c4291520804904209e809800100780c002014800c2200a088984a42d0b214194681c029420902c0f0042194014050b8200030540d0446643c40d20341a14507078210728110713203116501c49030f0810000000ca070284c041d0601a20000a8032520f8000010301ca03400c5a03144d40c403403815a41014801502a80c1041004c030543d902030900c01d0801040f4000200101074400003d20014a030042811686081c1d424a511803602d19120a044c0c1c0c031140501c00030f101c1d007141d9803644100c001600c0c081e407000320700c09907420200c82a0049030940b01d5a4a1180e1a003046591580079402006484074084803055200d5907802d0f1600c00d81aa03081400032219407500600071103000d01c20003030100301006403d51200b80d0709104081580c03107505080c555100c1c40c580560350542c0d4290050007900e48684041005c18180001c0303001035207001c003d1200220000084141544c080382c1e107078406801050b9900086100d00c0c82075540042e0b034507030890ba8020700340c00680954100d0504030014400d88 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 144412104 1250 144410854 144410857
    0xb0712030b090c1215130c030b0a08030705070f230607050706080709090212060d08070501050a0b0103050108010c09050f03030c060408040302120d0c061a130515041109040902030109080a1809050c 86
    0xc1151b5008149203440300025005405000c419541040c0d9400c000224004007002030039400784200103032000d035a505c5000e403010709014042d400106050104940009101e442e50204c0500068045402d1400b0398075000c1c1408082c2d4002c80c040381c5900d0400c803600c0c0c1d1006580c00602143e1904500703010f55024205118040100702c1e90090301c0c281d9000041c80306580984d8880d40c1e2040007070009142c203907603c5001d080103071186800310742028008254080180103d540c0c1c2d40e0255500142a03207400c0c10085002c0d140040160180001c1044568858082c414140700380d00802030030366903514510600022000d0302000081d55009406c0c6492000e901c083ca079001e90780c1100c00407030382e0b081640f00024611542940158029400840e100f1055143e40141340704000c192103031241d03510a01c0520054030704010404a003c51304001c8030380b6525160b0300c45001e06d400500001034446455481020741d50000c00342e000410380004401c00b0980418817103e024180e407140c14031150900070681d2506 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 144413354 1250 144412104 144412129
    0x40506150c2b051801110f0f1c17040c05040f060314030307081803040b0412110603060d0f0501060f0b1b0118081b060a0e1203010b0712030b090c1215 66
    0x59036098a80c0c0c0c04c0c03582c40f44019000c200002000c2e5601c040c240d0545540e9210202d00042c1d4074060311215034060392140103211000101a1640320820034040d000045e1044001c1086405814400c1d000c40c00e42ca6034030070710700d060f202c043d00049d905045007400b40258140c0880390003642e000b00100459541d200780803036008807124482e4a100b0950301031460a6000b150017000c2da0a4001c0780000e203d40c3d56400e502c4040303005941c02920403c40100707020081c4012240c1641101ca080b42c0d50000403009a4407009290041000007200b54445032042000001d49c0d1003c1e04000003c61502070060b900b01d15030a400e1140c00c0200a041c80400300c1c609421241f1002815035500404d8040032804070380b490070425900f40096410b146000021200200b48814002c88180b1403800842905090141100d0580d02c09003905400c000c440e0b5102e0174420150300148003055103580c401082900c40301080c07030003480d088a803103454480704a032035400b4060003094034202590401d42c140310f5890b113178494000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 144414604 1250 144413354 144413377
    0xe070519030b13151406030604120509010c0f050105010e1003051209041508060907080c0d080a020a060c0e10030506011e09050d060501030b010506030c09040506150c2b05 75
    0x801d0f611110140c4440c406440050000e15101d5000c003c84001680182805100e03a13020000d0b9480e14010300d550b54030125001003085200301c284c04da04500030405450405070500d0038200520841d95203103c61040c0010884180e0345440050106d0207260422550001c0c3c00c91402e51064655151103503103a44402c40141c01c04000148250591140e412210021ba240c1110381000395845548668800048541006a016100300890b0500c2c5c0810804011032006207850b0320388089440b42880c076844107440805501c20915048005041401000c903041403580328001c001e20300401388101c00c041d901d10701d0109807074841048616030704280070031a410381c5401c0c2c50b011009941c1c070546210b406a040142d0140c02c0c00071400410806030406070503031b88169051546640c3c0c4006000050000343e800400e004030901c49001c650400e54007240d03002d0030042050240301419071003000c035580701411501060700414124603980042010400c0c865180c401052a1442101c40050250040e90450030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 144415854 1250 144414604 144414623
    0xa050702011b08070506010e09071d13140307020f12060406051b0d0b0f010e0a0611010b0a091d12090f040605061207030506010207060807050921010e07051903 70
    0x140030a051103460b01c18940c0540420303070b80c90b91811700740d0352204240314007003107005200c00158000001140c64800ca450f4080010820104000e40501c0b004004143e01c1809144210f00c50200b000c0c1030321f0610851b0780c0b1000e941ea42c50359006001c414040d1000c41c9010304024103400ca844400002c805038000d801550024150b183d00822003202d490702c1b50b46102120000c90401c038100031582c004494003a045880e0400c03180460b005642414842060310f520810b038590030010f0b64002d035148800d14003060300010390210b94000180140300f06800000e0410394810701425051386060072402c440c12800000c00da0407000010781140c2c0d04c102024940150300c0c0051303082442d12035810200140c82e0041245032503003030441c54404414022281c05001a0030103021801950000c25a001070f925540d460800136a42c4030800d458139030196500a030090164034500200398084a18001c0c0b04040c5000850001081d064a500c0c000d01c40d00003034418901c84051030000070219940310203c95001d0b0a40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 144417104 1250 144415854 144415877
    0x40b0103060302060f09090a150308180306040b2d0a0c0912081c0b0112021602100f030e0318090c070f050606090c2d07140d140a05070201 61
    0x12006085158402900079101003041c03001c9600c805e002e08007884050700c0d0324a159071411055400e444015098400381078503c8418000b081d03084d401002c8a4031600c0315400d400f038581002c40d1806030100c0341500c40382d680c0002d00045408009951200e0008000c14003494100c10701c801441c88006002c0d070f01003c5c5e80d01101200031b1b0180c012400248000c6400445e50030711400c20319403035030100d110b41920040a000b5128501168441d800c000e0b003041c2c0d1015021800d1311440f074000d40c4081039160f04048003045450050352440c040040804c0d182e07803244403000c00454080c081c1c50401420382030903041400070005074560b40a841032021400c49184045441e0120910010302c1018030107030049043c84000c0e414020005074503802228140d41c5102c856a0300007101a2078021103245807804c141c0c01c8000d0404c03c0495034a0302c4a01c214982d52031a00cac8240e9607080c071104541034049030a800568a03a80059004410304120103a01c0504514010414000900e0351040030002414000c144212 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 144418354 1250 144417104 144417107
    0x1f0b09040905070e0411060403262a0c1203030a0203040309080a080406020c04050606090904060f0c03050a05100501091e0b0a021b0a08030403060506040f060608011409070e040b01 79
    0x6101c2036081002d50f40100d403621108000b425003181c00790b4a40c0c1072201405040d0420f84101d90440345c0151220b00c030300d80101400843c040e114589104449002d103c050450215000040712030102108000071802446c1446420005448811032064000051000345014040f045960041415900581d2540c0701c0c07400b95480722954000c1060341c480e0200d8101040b044400401c2540c3c49a02100d4a1014180401c82a13400444d0f041c0e4205105208049807418a03e140940040c80348402298649013000e5400803600894041000244c8410078448501c0940c8601d64000032014040c403406410035001908003000c0748251042c06542d410015049007907130442c00060200d6200480e561080d0a00080d95003100c82d8140094080c44600d0420718946522100204c0714417401070340c1414510b48420b8001c010040c0825040750f02c0e25000d40c2640001d12902019114039281d201c6203505027510303206c131b01c48100e0f2018080c0d0001c105100170b654000e495000841c000329404a00360700d00000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 144419604 1250 144418354 144418361
    0x405042f0c1902060c0d020304030501060906121e083108030702060a03180807050c12100b010212040f06080f0609060d050a060c030506040c03021608070c0f0e0f1f0b0904 75
    0x6170364024003030904c00e510601c0d4088001c00072a40644000e0140745c1d19400b1b01c104844076031050140b400590350700c00c0006400b000703644080c1e01411000400a440c039880f0418254404064002200810f82e03000175042e45004282c01000b81c00300f03801c5020b506003101c45135280700d42500a44101004070304030141038031075001a1002c95044039241d8013501a864070320703042e40044100700d0f024019201c2008640c21b0010140700241c5100740180300c0a601a1240d80042c071003421110304600425000026012a040c02003000b881651a08551540b52100043c021130b406441160010300b02d01c1840385c6c3c0d0341c90310704040c0c0086045400e284003010301d1814030300c2e1540c250030040920f8104240302503034640680c0800e128200c03d941c24000d04001340c0b0f0480880c0700721203c600002140c607842c01e0104182030041c01206100d101e0741613085890340410100088240e00c40514200040100078641402680168100c00132072203500341c610314902940049401802151407070b280109415880c0e41e555003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 144420854 1250 144419604 144419617
    0x509030709060303020307021c0c0302041a03010221010b030408030f0709050319050d02070b040e0a0e0f0105010603061d060d03050d0c020a02030708120f090301020405042f0c190206 80
    0x601005243d940e0318002e51a81c0158405074800c20b00034801c21148650b85200000055000684900c99411542004004c0907035207020300030b009600016484684091000b008100b20b50703400484100035000c1c4a0503001d0050f007104c04941c0061050000040124017602d8012039003d1100405039240b01c400c44000000c0e60101e84d15210710702078800d0b0401040d10b940794a601490541e0807404418106995039680740c421501c1c441c078108020007042000000c4142c101341082004294083c450100e1403070141042c1900c401c1365521401004082e400d032003900003c100c02d070403001411030001402d420490005120a0140e1089031455007003510460480700c034a40154800c1203445100c4800a641700b0300240204e009104842001c603580310009074030b46d0f4280c4210146444c0421500c1c040c00389401c000c000d542c0647d0240302c049100d40d5580200d030a200b0040000007004039055003007071012522001c601202c03003000c100a941613600881e00d00021001c0000e80d05504c00f0b240302003800d0784180b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 144422104 1250 144420854 144420869
    0x10c09050a17011104170d050414040506030109050304030308070207090506100f0e1f0e18070c03050403060908032a0409020f070f060516030b1008190c030c110c090705090307 77
    0xd001c9034459101c000c960454460f4012240b031b92080c00800e07103007445180a00e002cac6110f150010b5407246081d420440d4005000380022617070340199925240346170000d810440200d0124020044540c0d810801d00006110144052181d402d0020102d01000030483c084020010090096070b0390500400711080502401f80c0a280a16040404010b80c0380408051000250100d00003401500c1c083d8244900b0300501c0309a4142074803100c1e000e51f0703003925100b03048052250074040000420103034403c8980b070f2401031403000e580380751500c144400181094505000105900240602d0720000c4d400d9405032401000c0042c1d948086401c251040d00803030b000101891207500441040018036003155000f1005944000e40c110310480f01501a281002121500409002c4806800742e01c9005019003081c40110f507081010240051007090b11b800701204c9010985515000d02202c0d40041c0c0307146446940405820003100c90380002c0c1000310040c09090400102048035100381d503050200500a0144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 144423354 1250 144422104 144422107
    0x50d0522080901030b0108040c050415080d02060a0c02030309070314120f04051809060a0504030c06090302070608010603020f03011401030b0303040f030b0c0306130e010605031509010c09050a170111 87
    0x591a22201c203500c0281168000b9092080c11155035000d034048070300840e8442450000d950800081c007009083c0e9547d000312a2114120009494509009403500b9003240c1d0b02500785c0f841c049040c0c00503070f00344440d000c00710f40c070400c1000342d44040844c860003560303030207410322078000991100e26180101c0404a004080e40c00030f8100002e000020003081100c009454000075143e40303c924904610003141c0c41c03a079903007001d000989903045952025078001d109040c038000c8603d15440c1c200440c1d04800341200561f0142009002041d00400002d005090b2807400f58a040300305201e0320b0340c501041c41012455005c180c4020004da000340c014040d00d40000d000c40c0e45440da45c00c0320001c0304186100c260f40b10b04180c03000c902e4100b0365004580c0705000103040b03516003d40703d48d01200100030042c1440780655803200301165680c0c050144604040e490ba00d00f441508088000a085403400200182070082120007044651070f4001c0c5d0000311a20012000000c0c0c1010490710302600c1c4454403142032020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 144424460 1106 144423354 144423421
    0x20703080d09060f0b0a0b09010203040608130f0503030703060f030b15010c170d11040e06060a0302130b030103142e0b0418050f010606050d05 63
    0x22080c000607100390980c0f580d504071188000c402c80520b4075039031511914544038041c4c2c0080c0c00c0030005286001c03401c40000c7d66902c9584100e20900081d1000500480c050401c2c070302c5241e4014907810040320f11864800c0d140e5208a4245000c20b00d000004030b42140d280c0c03900404d403a80400400c402d80c56480e0000e10f00d0107084403903410001c00c09a0400004e080c001e040c030402c40c0f85035000d0b440f1284910b408050300e403070b8101d0381940c50b400c1c0020050400740c00161074000d08191440c580d2202044001c50282c07060810440bc00050000002880c8416000840c1224003600b007070b100f12001205025103c680b0f10340314020442568504e1446081c007807958050320348a0305000a1002601c20215050760340d140d002c403510000c090804000c0c044148020781c903070100d41c0020041c00e4203000c130241160082174400c4891a03074420015901c48081c8448010050920354006035440 = true := by decide +kernel

theorem cover : BRFrame.Cov 144244604 144424460 := by
  have h0 := BRFrame.cov_init 144244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 144244604 ≤ n) (h2 : n < 144424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
