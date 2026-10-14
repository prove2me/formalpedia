-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2893
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:21.764734+00:00
-- url     : https://prove2.me/submissions/93a6abb0-2b4a-40dd-8a62-a5cd8f534956

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 520143884 ≤ n < 520323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 520145134 1250 520143884 520143887
    0x19080d080712111606420303081506120c0414012607140705070e06041e0b0f040204034b06062706081501120f0b0726010e07 55
    0x714000305540303599031482d404000005950012090555109210000d010007524002c0c006c0494001c48090341115201440002e401444040e0400c1025504048190300301001800c24890305414a001d42560028007004a0302000a0000d80701845403080a024084004484000c1c1a24003101c02c0c003103a001c400328103d103a22029801c4021480c2c602940004c4c04041425a440041d08039a6580800d03010480e01d012211030a0f0000405c860501040b503413850001a42d9202c207200d1204180d4900b81400785946040400c1e00325140a8000c0d904d4a8bda420480c2100ca2441c080c4212481003149105801c102c0580584008400c0d0860860104250a603074002c079000c004115101556800c01181c2c1c105c0008508031074108409078034a83c880d20070525004e43c0d20316444810150300048080240c600000c942c2815a03c41000719907103c081402c24096403901014054485e6649400303115000390f00160424410441200000300301803d007070681070001c03091013084424941140400c00c1d0342d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 520146384 1250 520145134 520145167
    0x1506030f0d081909050d020d020105010b19180518010302100804020a0905130c03081902010605130b06160308011401090e01171608030c07050406050303040519080d08071211 76
    0x1c03041041d00281c4d141240d51001d240480080076000540e120021189250f0740c2400b6150242100f24031441c10400d0300a42545505041139400d014058035420803e455000100380100415000b0303c03005542004911196040c0028002640500da41c921507030030f818086c92404d40299405859603030494a0213141500810018001c0d400c00104c3c500c40070041540520040e02450282d4881585c40328018030800520780301c1d400d40815a41403100421459807100c1000204190362123010408505800001c1c10310311500305400074040708110030005040d80311003254103071000d44d4041601082900d0054a0150040c030a8030300b03a80380c0000601158040809103500d100c50b80c0201d5000188100d040d9078400c50701c0d00140340b96840440e480e0084c0a017005602c006003030580d0108013050914000c2901d901c914040c40780108442072803689a840716104c06401404903c00b42c58041c0000c0600502c054400c0e640350002801c0307244079503000702040c41280c041d107089000d02c515000c1d040203495101e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 520147634 1250 520146384 520146421
    0x211401050d0c0b19030b0307152304140307090513060c200c0f090c09060a02160b0901120c020a020415050a03050303040b180d050f0c1506030f0d08 65
    0x31091002d00016154002c04080c1080c1084052100c15a1350341400040031501710f222202c0c800e0f070000c9002c000400303800c40c001c107444069240c81c0421103900c1414201001004000d0782c501c407000900022075145040c070700259070504070161820b060703a518424050741c0056036010844212009100c0006480d030740075281c0a80d035414180c0d040302002c3e844401c40d0b040814041c074560451440446035107404c118ac41c0d5015011144c0c4c180c00d050400e5100324500402507524000d40000501d954554000c01442400a8420240c06001621070000102c6078000140041c0400d070384031b60015086940e40100141104c1a50003440c0e00314444e000c00000e8012400544510002440003040584403920032102450152006554901301803070020540d2500400c1600e0240d000722100d41007200100e14920081d01d030745005900c1d54022000d80c0ea0900c0307180c0904a0912540d654401c1d11000003480d0391240d00b007141a25902202100004d4540e07000d503041000180c50a000244814000c1281c0f000c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 520148884 1250 520147634 520147643
    0x807151d010e0a0509090601050405010602010e2d0601090b0312120f070e0307030b0103300f140301080c030f030a0c080d090506040b10050d080a030f1407211401050d 73
    0x24544e40d400204401070815a0b000e680358000c60014425410b044c0200c40c010040d40c8020040360302034424140d150000c0c8042c4039032002500c0340d5603012401c84040b0708203056290080c1c51a650351504a84010f000252030140680540c40c00344080d5400b82e410307903280d600f11040040390350761036102844428000901d8035003230200340301545042e40c90800c001c8002e117101d0701000d070303403541181480d4085001c10311100066a040c10654035008414510481c0541414246801f030685841d4064901040c00b03d400705105501000010b20a840010310060a0b0000d6040c2c0311780310b02ca5040940c580c03007112002030200e03000403040703000901520001d010405001070300040c04420380c1c0c0d1b1241808420b480a8507040c00d5482480001a000381851008201c121080e00140d9010364a141d01d50043c03051800c245561000d0f4010781e22440d802031138020910340d030143d1a524007144041c0000d600740030201b0029200c0f0034148420101c900c5074256072603900303200240503842c1c0010840c041c180484120b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 520150134 1250 520148884 520148899
    0x609100804140a0c0e071218020307140609011101021c060501113d090501050402011b0b07050d0b190f091404120210020412021c020f090901150807151d010e 69
    0x190001418414001548500c50b42418548c545004062505200b50003510075a494112001810355072181220b250786800e0030300706030071803ea40c8014024081c0e0b40c1c1c1c0500c140828200c0c1d0421040741c4d84114143d61090f2a030f400c4032010418070b80c5d80d680c080e0854040303070100000070048400780011780c60040071038000040c800710024928501030b101c200c10100d4541c1e44074810700007107680150103c01e03c0c5000c0241d103542100913480302c0312200c60140004d002e1080c00034003010705100030340044150084c0600b10a00c0c006924544c032007983c82a00c680c601711401d0300782c08102184a4000c1580d01f02807040c2ea500d5586490315140220b200c24002041507110b000300250607090903001510040001c600420301020080c0140f00380b0081060381400054038542c14000180d444000401d2008002c1d1090201582d13082141401040f03a98012071030301040d14000290747c080024a00240d0341440941c01c460941414103842125010384580384844a0340312892195129881c070b01d0071000001d0419 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 520151384 1250 520150134 520150157
    0x1104050303120703050105030a0b010603090804050d1121070302060d020c1906060b090d0b04020f030a0f05011407050d0e030f030109090501060b091804020609100804140a0c0e07 78
    0x3a01d940d000d00c104080c2c45075000200000f40784c00d440707801e004200a80203010091041d6865024002c014024002899512030480c01400080350a07070f03010700800350011402d40d101d4207120441d0320000d07003568854848110082481444600310aa240041c800140b01e0305085a0030010580c10051107100d849500b0702408448030400c005030741c80d540120200c454070500b1030a01ca400d0b2401504241c1110004010b0010b41e40c45400a0070030701504041186090b4035544000368103a2020083c0310762600c40c45201c8028040b42c08041002c4a05c1000200300f5603243c004501103000c004c032a204003241040c0036409100b01d041e003044900c0c04145042e03a00d404450402c221440e00b003a080403d880b81c1c0c4110b0881005401d104000c003811003a61014104189600055128130345c40c4086010f07520401c0100301103454401c15201c2404000b8001402d4000c4a84004c2200408031003d0380c2c04a01481c4c0008504000b044100509030000480c4c0402820002400b4410300040c02d2003007000041c4c101c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 520152634 1250 520151384 520151389
    0x13060807092318151504051305030a090905100e070810031a07030e0c0a050d020409050604060225031209030c12050a0e041e0504050322090c0e13110405 67
    0x103007480340745080c810f0084030303c9800c243d5141810022011002c9101601400b5015103441e2404100e003104880115060b038a98050403d0310290740c500034001d01c4081088003c6079000070212013920300c2c2020820407951104e0a0010702d00180c8145840d030810407000c921803038414020a68071130703000311108040fa42d80f42c1d01d440d013481e40891841c01e1072a4000900c07603840da160081021100440c0000c00302001a5000508107940300e101d0648510044059142192120340001d004103400405460141c0b0f001d0928402a6200742d03040b4503d00c450f4400c1d4100e861107030b410f540c03a00da003580c1d8082c0d18800b42c41203100100f42e24035045c0c0c00e01501ca042000016070020340e0846210f090340e50642c4a4541d4074000d014460f42c89642d51155051100604400c42300000303101103400094408106522203060850561213182c00001400c180da816400d103454042d6491000c80b405103104120082010318101c0f82611381500d07071a88400040000f40641e00e694021007031002c408410185016905e100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 520153884 1250 520152634 520152701
    0x19050112181b080a050d17090705090714040801050604150308030c070f0f060c1b0f020405072304030201020d090302010c0605060a12050a02030c0d05061b040909050102091306080709 80
    0x2c2c01c44907940300d80340c06c100190b40070b40c0c9034000011070024030080d070500101d9103488400ca80180360180b02d441000400701880354040e5140c0a209141703250303440d81c6581040e8060001140c100e8003da040c0300010281143c807808050031250080921404c54441904483c1c440d80442003e9030600301100b00c04011426000030500c04600c91000000c002030001c001400001d0b40c69540c81900844107001e5010075020070080111681c100e5001803030380e1710b4013402da5254081101401c801c50388400300340541e030035500080080da030003602107500b000c40b5814125032640150000070f0010b1111404580090840c0c0c1100307810060040c8240b003440d8581500d1488401010303819203003607000803044000e504081c800030944140a071540c10383d100c030303d4855a5990001401204000418146004070140b0a60a4030040c190001083c01422514202079000c1c1d08281e08052141001c08140c215005940c0714800444d8141c43c0a4400c0c18a0003c182c070040c49074520500070004403c000d610001030094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 520155134 1250 520153884 520153903
    0x1308040320040b031204030609140708060403030e190303090201030902060a180b030402030a140a0203060408070b07031b1202090a0305010c12050c03040b0402010e19050112181b08 79
    0x80c1511070544001084103448815071070318026084007003d8401c03501100c00301c2c1c05894201e500464190010302c0c201c0c0d142d108095046210303009043c00403801c2c07035001c40e8050046001c1c0e40e050003d81e007800d490303d031500e0382168902d541c24506540d90000a010742c1004194500506002420306810303004103101d6444a500d0900149407036000014505505540c50082e00611041604525103940820390f214039460018004807090090380d00c024400704044616181e0142c161880da080600e01001c02e0f4000c0b02084034101c06010015140e1803080c072944e8428950112110b5020112000c00c1e20030038920221102d4480e001c01102903107841d90340c1008000c503c503c0c000030f04299100c01c0204214150340104a00c9828407060020b04600642903d401a4100c007041156840303510041c2c034803e0611010a070040f030311902030903248140990b035104480c0280c88055008182c4d201c0c0004884201448490489404220002040c030640003928003038a1058048003083e00e521044e0b01d801e07282c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 520156384 1250 520155134 520155173
    0x60a022a01090b2d16030509120a0201091101080f0c030a2c010c080106140a120c0c1403040b030f060a1a09030d05030603340f030c0b0304030813080403 67
    0x16a040d086600190701150994507003121405403500b00300940c400441c0388145c42c181050344030400700e101031206202c0c0030200c1888400b50b0341c1c1c40e0122000a40030b800f9049040e91201d1b20a50820459406406000e12800080544060640c0c41040f44501d540000c0c1c04c4500f01d40e92803044a98440c6200301c14a00c15480000c428100311160302da007425104800500010000240010010a1b81010368120710400f40c5212580301e0022210441e090881e0040214409007002c40c001480354111100512060145166646002481407069070341d1080f481800721801c0c04100249142c24640701c015003044005008044076aa5140d07214180c0700342c040c800130a01000559030030140741c208620001c0141e1030a180741146055000240c0324030b4424a5400e01e60140203c041d000384818010040c040403401b0881103882c1c0700c2c400002e040318940421508061940404101d203240903041d41c2c400c1c0e500d9650080660f9402082814815002400f1500640c09200c0440010301020305032081c56240c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 520157634 1250 520156384 520156411
    0x20f181b1303080d0e070b040b0c0c0a090221160c02030c0a06020708060603071212030b1c0303050c030c04031217040b150f10030b0a09050711060a022a01090b 70
    0x108100c4c8216203c50010103040ea02c031200800000c0f40c200c05030303412225240441c0342c4845075005541d027440c00303080e00301d030384124402404100300d0040c2d4042c240b100d0512064034084200d4402e0300b451040c0c103448445100100780d5441d4241445840b0040c40188041c1c2510300035000d0340701003060041c003504400c0140c3c100c1c15091004840401c5010b9001c80110001c0c84400d02c0d150454100154904025000020010315486000d00a030406645800050011240c0703824101c010010760460140031400241010040f585815000c03080c2c078081c007225030100c1c1c601460740c0d0f910484103140d81d0315001885840d884031018a0424400e02d0300c0ba80c00f5104150305803512090701600e0807405107040b8850043ca03010344100b82c4800340c1c20840c0d251541000200360f64000d0024a402c042d0b070784010b0b40341d4207200401504942c02034486018901c6002180c241d501ea80c4449016805015400812000303040741d010382c001180024694030000803000080c1c5540e440e1651503100e0421111030030314011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 520158884 1250 520157634 520157647
    0x1060803162607030f180f051005040b0f070309030b090601030303050711062823131115190f02060603010c2c03070303020a020f181b130308 62
    0x1581c109110100c06114420302c0841d5456104010750140500c003400b003040034400c0060b124040d10810808a08090302044480c0d1b4a00403c601c1e400d06000d0036010746c45441450740a1402030007614142c1d48201d0b40039040c08040030384001c95030458601901040300750800007004c11401c4009500400655000d0000c4e50706508001d4140c80010b011182041401442c0c100d0f600d2011030403a804c0f080c00b02c40c0320028040310085012000d8250152010030b803406d45038040e00100104800e24035004036520704615954001d042000d0001410080e05603032001000d0b10781841c1407007000c000d04d14254101b509100a520544010305860240c14003c100004900c44116804004495208c0802c034000d01c00c0700302c2d5510041001d01c40b424081440d080c2c8000711060340440300c0c08054000000f4089038000b5981c1d050096941d00007400030ba000d250180c0602c08503050002d00e0040c0c2d03007200740110b0629180e40300c504601080520004680600078000c140301551307180081c00046014040841d225034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 520160134 1250 520158884 520158893
    0x70215030115111c031d011a0409020d031214130209160c020f0607080a051b070509010e04030915050702030105130f0b25050315030a02010504170106080316 69
    0x2c09401c0d45400c2c49002c100e100350180d40040d90803030a400710b002c0b250b034191241805034060501c1441e2100c080301e0006203940800815484100e10466480030a2280d9400f4020300c0219401c0ea500a900046002a1140032034082c4000e1280401c42420001e008a81d0030b88600103180e040e902e460100d0100758402041d80340c90140c1c81d412500900ea80c502207480550054847c0401460081c003030007200b902e140c51503444d001660000c980017080290740c2c400d50440240242d01c00d00d0200740902c0440c6400891303900000311041078031000741c1490080e90030301c11013000c079900c024021010071182020120b143c100721107030a640100d49840703030303034480955104041c290340005025607250b408001c200310224400503054000180c11042080040d100d03095481026108440c4c40d0a00c0c1224101c0000c065920200440c0302e0790200c07030040103041d0008200740d110012084060700207201448188110b002e416600d140c0314407400c00005419036103402e440d0458118804010340400385008050502 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 520161384 1250 520160134 520160159
    0x8150a0f050f011805040b0630091c0518100206070e0108100302010e01050c0109050705090a020a091404020903011e0e070303090306090804170703050f07050a09020f0702150301 78
    0x507900342081041e4185855003400030305042c5c840c5030710030b54171008025200e803035040031100c503501c120110b06150050001c1c060040b90000020070003107201c0c28005041d856000c80c90101020a409000340c1141c0c000380d080314190019540300d03e40c8103607100d800c0e000d559040080c00040c1126005070846244c1120f001d0706401000680341e040c425154204140761040000724002d4030b60909020a950304840c0c0100e50710702404610300015840c0001d05001e0000002e00074088400851b0300d1059565030540c000701760b0040c0112480416203250007030118040c2c1034604a2562030182c4018200701d4082d00003400d44810b0700c15009808040d210300328490781c0c540101441014154000c080c0c1c00e01d5564001d107450164070000e814a50303221450403c00207640101d600808070000c0d0128840308282c1c0b419115107a91004442038400c5540061030078002055010486000802d01d9100e07904d040404c1010354448410038044440030015800140c2c1d52840d41c2ca18840d424400585942c148446500c44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 520162634 1250 520161384 520161409
    0x80406060602031c020304080f04080303010f0510021504081608090f0a06080a0923031b010c0c021306081213120f02040b031002040b07020a0e0906010608150a0f05 72
    0x3190400c000342d00e4401d88900b0700c1c151a2501c51801641c903035903408c004d9202e0040b031000700d150780d50009001800341800000b840c1a5001c00c5401c1c525542c0d10300402c402c07407000316441c6002d0b8024031040403901c002680056401401000f0440c17a0446400b8030000d490b4009000320790250012070401a00e00380b030404248504401c0c0d800424641c1055409008104020203180310b01d91108808010024172443c4c005104201c0000003030b41c83c1a54034195240d0b04840e91050459080210005001e0300c1400b900300352542036211001d00a8843c0c0038050390345502c1e400385411913102c010005915a00b00201000181c45400f282d4650091403078202800d03145a100780c1c01410340b00720342c8010a003d14005298076a045500140d0821780c030001c282403c2d01120b6401d2054400304000800c514000000c3c0040d500c212000034510303842d40d5404000301026100044c89601c21070050103031900900d44950005081d0003c1d99010300c00000140031403d494200000032207400d5030400042c1400f1000240c2c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 520163884 1250 520162634 520162637
    0x20106210b0c0c01060f03080c0c010923150705070608010e040b0610021c09210b0a051f0312080a0c080601050a03060b0d140f070503190b100804060606 67
    0x110020306444250098902500b070b1401540c0c0090040c00c43d0400358800300080c245440300358140c0c2d680303040c140701d04d401a540b4141507001d41454007040e03600c0303000d212059901c416032101400103241c1070b41100803075005009810110190840780f1182e07502c8060b010440c851401058907504100c1d000b8012081a440b40f11644905000d200c0010a00640c003940148190b5940b0300c00855280304911340908a801d052804159140043c502a4481c5483c01038070101407107903004542a040540c1809021000034202c002601c0c08540380ba07909400041c3c0109a07800c3c01c1e0f54000c0300c0410040000f032303da44102d4140140314400100d042d00a84583e900401a03503082282c800c0501016002c0c3c1401880c03141000300028032108a14003a9004174081d02c504101d59884505105070040105086c1c080740c2c5107411a400000c89c03c104810800d8411002540d400c0e06540701c040c44109907841e00045d50b060307941c560340218115111402018600c14490f543d81401d803c06040803001c550072a0010340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 520165134 1250 520163884 520163939
    0x3151513020921150c160c060801150c201309050c0a081507110708060402030111031009020c0102090d0305071109010b0405011413180c020613020405100510020106 72
    0x3054001154540d228809210800d80c035a9038140071610600c03814980c06c03c0001400c120505000010024405650454813140000c1c0d0300d9641d0b242e50a02d0301310980e000030301050b20060000703001c2c89485009140c41410300d030101d0070301c00004903503d6503002d00420441e515010350062040030030010fa400070051307815007500341c242081c087e20794061032445207540d0440e101041d00750b071080c002c0400810541083d202e602c0d1312403a0060700c0711070540d800e80c440e41c01c0451407224000101e040b28000e010f05102031b19010b2030081d000011350003020480040b0f55090124941648406641c070107030610030b588072595040c551070070426550054540398011540080103104a000c1c10b0b00319815680f003420040720b07040300c00c1ea00710a54410743c100c0046140d6600360001e400340304100c4200660660610034405e040300c20400320fa44140403610321654150207600303e005410240c5c01141c000140b110144030b642e440b1404180c11060300302900300140e648210800c266103800500c0e580140c0703075030322030b8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 520166384 1250 520165134 520165189
    0x1b081b0106050d17071506082b0e13240302120106031e1b0305070501090b0c1e0a0210090f05060301080c1917060a050114031515130209 60
    0x51141e280884185906882c00524241408130180840d0b81c003945510b8140070305922040030b691101103061040c014101c0c0c208002e109c24a40314031889140c00242d5a01c0d510125140400c4401591170301b000d42440d43d94a898000810380ca080b00050491003250710045030300d5403040c013074841d0902c400c949050349402407d200040c030b07030040c103007103020ba40000f4010761505081c000c40260101c5d61842c80000066000410040003107090b0040b24026201c5000c00c0381d032101c5840c000d02c038801c041d00d8107030030441f84504202d210b08000031034403801d101182c07419440340d0301040403a1703142042072001c12040c050402501e03003802c1d000c070044e00d010754059045500d840c900b03aa4500780600300e03d100d03c0c00030700c09203420190010400c009101c0a10214214601d1450b441c0d101d40c1d0546020f844035091034000708500d0802c440007010f1040103402401940701c5030f001400908806050b121a01c1c000702c0c40005281c2d01c451064140c20081400182d035030240da17081102c841015020144076a4516402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 520167634 1250 520166384 520166393
    0x30903020a02040519150e07020d020c061c051515040e0417070c06171b19350106210207030903060906021b030c07061b081b0106050d 59
    0x20964490350650f000704094940d00650380004050405402c1d800f80b81c50881054850822403410441c0c42c0c81c0819041521191400c0340c48200711803611015130b0000c41c0c0740b40705003004002030502420032800009507241991400c1c09a520548020f26482640c501c0d015103807800101e42e580b00d511003150f040c41d1034982403000c90303100001840682820398140004444e41c100c0011a41c07078540c0300c002d080c100d0b83c8a0401800724404508045455404100040d10085804146440310f101514a142c01c252020811034402c2462003684010803403107600103a9440380f0b00501c1700406d00c041e0f92066042d140b6084001020368142d118108000034011941c031450501d0300d1609090100351005a41c1c1d908a0400791188107442d84000c007440d25100c45141400100da0180550001440018072a2001400660359a00901000c4411a0450b100c10017540d401026224980fa42174640c0900c040c9858490f40c00039008100703003c5501985204030b1000c45828418030024100c111041d0b81b2901c0341e0384a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 520168884 1250 520167634 520167643
    0x4030f030614061605010501180509060112060209030106050907020f011b0503180a021302040e091f0b01090e0a020408120a0906030c0e2107230409150c0203120703090302 75
    0x2d00500610000643c081e601440440a02d0b00a811038024456540d44d4000d1040b86a000340b4000e23201864180070400011002c00d40c0c070304a851017440981174000c16102e101c000d40c803021701c040e0705659408000459803645910340d48625102d801a110f09040d40c24801e00791060500b10400200d0b00c1e44501280e5600310041e00e800124003003043e80010204103034146000e44804010354840e41c10190002d1048507034008000355a81c10350201c100341c989440031503840c03c2c107040b21210305078100080c210b51800c2c0d0313104c1c50400c01c052501514565917045c000d03245035002d80d090703180d8580006091140d00740c1004bc4d80761203000200303040c4c81c041d80f401000301800303c24050701c0704264030f50b060300c080644189000300e07020800034201c1c10802031445000781481c4e042d92480e4614040e11400280501d1444180f052000400341c50300302600701003080000500c03103d4130441c1d041030b2490450400850324840c80303080060b5038005554601101406402803140181642c00300b40c1003410500c0065400318 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 520170134 1250 520168884 520168919
    0x9040e0721030c0803090607120b090604020f0d0e0a020a0503070b120a0b042c01020f0712090308030408070b010e04022805031912030e0d0813020607050604030f0306 73
    0x118202500701500e0120f44103510703500c0181c8039920100138002c0284010031000d010703520340c1c5c840750f614000e03180c185010703507108a44c21a40200c0b2040010180d080c40d0300100040c000000030b492070103050050352021144a00380701c0102d903102446a1007182480348400000e0a0b046000380415803820005040342c0c407511261455501d800f5020440038070f4681c000c5483c240d0000c0080c05400c0d00441e03800c220050000740c1541d020160510105800c9040c42210a8165603011507841c044154075a0f5800306076444083c0c041000441000000c0750840303020b140164403402e8510b07a1000e060501b030210f44c006030031007000b083c40c02c0d09200059a9170f82c0c0000d1461209010300f5000e4107800311034540907a45900980d0140034001c10702012211914440c0c8045100d0310700c90818003840c841c01c030200c406800c924a243e5104d032103685d0ba01402542150391001c100100044603080c01d6000c2003680d0040801116198810703002d1104040e001010250480c0052a01300030003481d104192880c2e84000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 520171384 1250 520170134 520170179
    0x20d0b090f1503070312050c0d030216030507050709050c0d0b0603011206092103090308090c010c1e0f0c150305060303041a040b030f160f0509010807050d0507030209040e07 76
    0xb2801c1c8030064405100f0400255003200c031019a91409090182050380060510b031103a019504201c601c1034040d1003940c2c0094100c403c0c6008482e115034040c0c40c00c2d0f000400c150340d180324002002815003614002d1a219200c4244510388500442c0440c0703007030318000401d87d8890b20052006010b265041000340d2211504403070086030281d42800d0201000017000d14650400d05038620221b42035406800401e403080c801d82d00c2d10901c0d99064582c5071142c8007001c80e075000402846400011400c0885a561800c03035200c0302c604120026a9142c2c2c1c564944e103000c4408103604d2004100d007100380090464800c205007018401441c003400001d8a0b44624064000b0f0550b103901042c20040700d00c2e064a01030100340d01501da41c0d00300381d242d002c0000801c481401d07502c2180e104208409200310010705070107009485a134101303c070310700046d40c041030000c00d1041004018042180041c809024450003141c0c15100165980011000e100c02ea81c0b42d00514140c95010340030070070212010b26806010072442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 520172634 1250 520171384 520171411
    0x71e03170c0c130e1b12070807060305090304080d02160503210c0c0613081e120a1b0b010312050c0a02131103010e010602060601091d090f0709020d0b090f 68
    0x14400220300038003046030180210300c074210700341c0c007090743c41c01020203545070864601b5024100702c20310540c0c5032410b01646c2041e03040035030308004803070003a0052034008001c40c040d03900306500d4103001840c0601e9100d201d00107920803099065000c0070305c590103003d0001600582020b03443c1e00102050416120409004c4c1e00c00006e20103c00c440c24440300d66410f20003000c5555070300440c02e50034520761780e9018141150081a403c18848252010441349015510001d403070a155598031244850b003001e44914280016600c2e4240706510405c00e5820b410b206100800700c95043d400c06040315001401081c044c40010004601c160303400003030020a07568111520b4002d440c0500e81c48001d04123400d0440c031910400310000c0b1f000700320b60401c907041c0e8881d60300b160307060b545010045a4124803803040c10141c3d0000c04000b00060310a1038002c1e8080d058104036880b4001a5401615042d0554000c03d480c0d503001c1500c0300020000d004042186200b2108024141000031040c1050040545200c5030120b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 520173884 1250 520172634 520172659
    0x70e0316030c062c061905040509100303021f09080409141005181308031305010b0103140a09030c02150c0606031b1c020409110103050a050708070c05071e03170c0c 72
    0x541304101c0e10f46c4d810b000c901010300a00f014007e00030b9000340c040d59118242c007000240e0640b0a80d0b0741e42d41281c2c1c0581c010400511740130902991000c2c01c50f042401c05460304222408034050304010001881c0c88200094020282081100c02900190806200707000310f5204210380d41c0d40000d4100e007141c151003000050346a480700a020300c07a6041d80200081c00c040100305444032010100202140903c2c000d2054843c2400110100c0350030342c101418043c043c4001c01d0030950240d01000c6220312074105040500d01d1500000c40904510340c49142c008400200d01444507404d2106c550011005d4004007848050040762108145404842d54040d42d042d462805188201c445001e01c41500640b0810039507020b4242008000700d80c0500380c2c046420b201c00301e0391048062203400d124020558915415454a02048131a000c012400380e03842c2c815114003160450076040c00406c1601c55400f0680386501c0d61500c4100d45011112803030740d018040c03104180000f00403c1d84910100111100d980e00d01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 520175134 1250 520173884 520173889
    0x10816050c15010603140906040804091d010e011b1704080f07060e070302101701030303050619121e0305041509080604050a0201090f031505070e0316030c062c 70
    0x10b8008400e442c1401c03403280001075417a010303031003141c50140405000d8031999404850b82d42d41c01c3c3c05e44000304080c1080108002c0406c80381e100d4840200858607007001042c1200d195800d4440103412482240d56503850004400400202c0e1050550a410f084040c105c00c8090789440003c002c10240a86d580000c00c144551181c100b2180d002c0d40c006810003003c500e84044a82d90b13001da0004a00841090b142c0900c43d84c02a000d0303041e40d00e5086600c0a507a800c555080380a00700142000f60409814103400d04c24107200e0042901405000c02d00b1242c018245c208440702d40a00c4025031200300501030804d002c01c2c1d1000c21502600c0c60714051461840350303542c04541280e0190311a000701e0050b8000e2004024000c602090414000d0346c070019416140c0f44102075088480c0300003040c0807000e1070000884552a00070943c4000c060070a000080c5410022030301f002d172000c1009404000c409410b108000c2d402000401400c1d0529100810503610301400101c40110040400303030004404200e0000d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 520176384 1250 520175134 520175143
    0xd030c080a050c0d080103200102010605060d020d06060302091c021f03020c21180402041706010312020a03140717040603150e06010207050105030c12040b0a0506010816050c 76
    0x540d4411000c5070380304140c04000b046508000100e02140c0121a040811180f0032500c0c2c50590303401964035042d16403220007800038418108540c0d0706554a071480050780d82c1d07802015000311041130300003507034800994003444106e800640011060510520100c013403038544c0381c3c12186075034a00c9103403400440107000060405480d1160603076003c10804081a21a50540291000c0426402111788030000101c0300d401910b01072401c16510030007030044641d9400b11290700c0709929409040145400d403920b1100d0500000007110178013a81c0440e004004105c5900c0840c03048000510140491000c25640141a0028000d80342c0000c1e20200700ca000740442030b0714400d50000403e40c110354850756050301602070440c046050058940c5035000003100740c5050241841040c05034043c0c0300180c00d1a00554060700041c0142000c4141804805180c1042d094014041c9000e0030104071946828050700c4140e4800800040c10840800140051104030b8941d080030701e8480d09010f40c0b00c1c5221014240742 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 520177634 1250 520176384 520176407
    0x1115060d0f06020307090311010e03030f0f07020d0803091006050607030e0f09240307080c061e04090605040609020711091f0f0e090303011202060f070602030a061403070b090d03 78
    0x2d9620010500503070f80e400c520403c080300d11916202c4459100381c030054600d296105692501a0402c21a009022141c07000804030010b00d15022818420140c010a0105046502c2210b110f4000801e2000d400000c02140020100c042400c1c00850b08100200d0075500130b01c0c40050078858118114480359584001041c885000507100050502e0258040642001d000100f0804a030b00c008020a1701e06002c6408000c0c0c810749001060403540d4081404565440056600994101504100d8900d40408014001094062070100d00c00342401c081008542c0e4543c8000b84151040210000040d41002c080484400849003c41a03555194540d503200d131140c0a20308240c0b561600c04250a4510703486501030f1107984e410903205980305c10321070303680380710178092600514440f070b0480d8010301e4444010f10300c0e00380d81ca211134101141940c591080c0d0700240c800c0c00145071204002c1c1f03c00554451360a070480e0303045000300348007441c04031034000350300c030f0754104d03078007560700b5084990505001d004030409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 520178884 1250 520177634 520177643
    0x1a16031104091a040c050901020604020d0206070203070b040612020405220b0d05010516090f0b0906120a0e011104060c1704030b07110601081618140112031115060d0f 73
    0x40b484a036510001400f69455003070340b186250150203c03006105205030340001d00c043c0c000f0a543d89464003003203498503410310101d80c0300500b0402c00005840501803000140174280e101c0d03840d07609111014104400d4000c005640c20b10601c000c000035501c0c14803080090f80706842d14005000f10380800c501030201c1124480e000f00c03803843c011007084015802a40300340f2600c0a03c000300101e0000c101d400e001d0384d01c1040402c08900c003041c44070900e00c2009104d5004014003880c0b40c00402410300e01410403c0f600d040c40380307640d040400c907410000e004441603106918541d500e454185903014011070800c220141c503c2e050707421405411a14074040780d020303541008022803140f8102c00c00400700c3c25017482000c102d000315000041e000e0000101205ca4a48040d00090028200f04e0128034940d407034400c4180d003c0c0c40388100f8001408210309940602150a485004120541800751014007201000d05569000c40500080c061124241c80e40210045404100391041400c2071302819103071840180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 520180134 1250 520178884 520178891
    0xf070c03050304081e190e0f0d150b130c0f031e0e010e0102131e030804090504062903150115050a11060f0f0c0702210a0512071a1603110409 62
    0x4006c07080d1500003185650380e0b9a895030441d00c5807040c0080082e8000e5803542148035101642c00042001c0c01c1c02c02103d101c8100000e11650203000209010180c0d80c44401155940d0a8404c00c9a0302c64880c0021015500701807101045114040050403410f9030b40c0c05070f10759204a03032aa000b900390030403c0d00c21074090007591111030800640300d2070584c3e481256444c001d524241507501540503800d0048a411040b0a800d107864465204007404000740111040e6a94a0030f1b1100c01380c40002007410601e00c010081080309141052524106520694401001c5c810700100002007408580d1003c0400e00c0c588940c440d2034003007082e80c03001a0310003c00e0f40e03406007104002240c0d0007a03881d607204191860b500e401584540450310b00c90701c62110b005c1c0d049541c0e510a00f2800180109509e1039100c044129030b6410030984900d42480080401919100800251201031007190740b11818503079003040c0d5084003810005061380c0030380c650380e4010b004d05442e44042c034500b1420b50180c80c01481241c0050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 520181384 1250 520180134 520180147
    0x115050c0313080c1e0607061b0801081b033415030617190c0801060801020909010e0c041a0f0309010903020d0e010909050a020d020705060f070c03050304081e 70
    0x12102d480031401400c050344552030a248061404154003002c0303565034000c41032003405110500c005580300010039509207032211020296190903075814010380f100e59641000d02c0d4180340c0d0f190705100048105d000c6d0b2003510055a40580d401141140380820b5036040042d200c0c000001030140101d1030700c85881c481400300000640b01c280c0d1201c0341c000c07004a0398100810364a80e0149480401c42040c041c1a40d40000590895140100d42400c1200e0003092003900c43d40d510100395007500d03807542000000d03940100d4507200600b00748000c1030143c80c0d41c1030034010301d01d00f0043c00500350141344a0741e12450032007447c01e04802d407000c0c1112004244041c0c100d0380d0b4a000b00c02139020307001c00744003107005114a465520b45140708810f800030083e4141d541c0c1c19081d1078108814003404e0043c108429182d402c0044030394850403403005294451051014102901c0c10011102170b0000007403000003803006490461000039405000c4a62055110301c500d601c3e848820404001000307825811001c010000850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 520182634 1250 520181384 520181407
    0x8060409020a06110d0302042105010e010e0706030b0a0602330c070209250507140712020a09050c0a1d0d031e1b020f0d081602010801050102010e060115050c03 70
    0xc0032218135048116400c80e40c074003104404a200385c0c030178a1981040c1c02890b201c0c02c041c3c4a0a00d0349a4011340c004558000c04048450071141124142c401c15440900708101264050140007000c250845022114510f806006074441014144111000000c084e10315060441702580c0b030480808100346903100d01d4030840c0e00c06144d100540c01e0784600f0011002420415014070a4410301050b0780d400f2098419000c0e054483e031300105000c8801191042d041d103980c110800c444c80040100b40b0821a0b10b00781401032050300c08a54020001481c03d00041080803510b9004a40c1014468a06020f1000340031000e204282c01424201d58403e94503407420080c103912101d1003241d5401000402e4440c02e642000380c41c54520803210203404185440c40002602e4084c0784c002003140054100b90001c3c03110f54030052154082d00f5101c1400788194201c10940d60b1055401d4054002030000700614120940d20940d02c20051041066080d000e0403292034661040054641032503d200840740c40e01c14007040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 520183884 1250 520182634 520182647
    0x90b0c070501030f0932010216020a0e04030806150405060c1b040c1707090503060408071101031103280903030b030f0d12020c03041809030206010e100608060409020a06 74
    0x14090019040c403a03484c941161034403400c0c802a0b80404138203402e898552107566040316080b00510400b4041c28807034010742c42800103041040950f180e107080c1c9901c40c4104503040030303150401c1806000c01170400c00017a400c030340c00c0c9030840c1d022110b0800034800003402d20640c0c880c0ea00030581100c008562140b10990005200e0070301004024559000b00b00d01c801e100032101a000250300040d06100b13100da01038074002006800041c1c524150002c070781c4540109151810a4400710b078180400503200042c484000c5125080023024030301400404c04400c040d8113a400050003103111507444045140c001c01c2d540340c1c070854181d49640d00780015902d90402070020b01c1c0a5406600038090010140c01650300412214900c24580c0c40e184900008620b5070320003500128200d030702c03d1004000106a803039405c030000d0f600c0d40178013602040310141c5160003420004180c1c01445200b004070700340480315042c0044041920228500210b06645810005015010444002c0d4120039040e4000c68026401762 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 520185134 1250 520183884 520183889
    0x40c050901110d02030d02030c0706050108030307080901060b0f090a030519110d0807030f020c0d0b0a14070504060e01030b04141e0405190f0c0f090e010608120703090b0c07 76
    0x8030b580140b802d825240c5610341000204400c016081000481c9107404180c0c0076503005881111420304080451380c0c0e600445101707070044001a4008000c02c1409548600b271690b018464030000c0c403410b4035100d0352030401d004272401d0094900c0007050781c84960721012882801560410111081c0c044402c20902c95454500c034280c848c48004031806290f0b042c050b0700104910f0780050080d00d4550541c50455208141c1c2501400714060038040c11410394650407d40e000301d0083c8500140e60600794201e07401ca0703103201010444c020320001000107032500041030303e00700c500c281018940a40807800403001403c0321140c80d9407051405d03404000705410301044c0d6214090086030741a11a680e004c04c150a004116401070243e0f011103c1c0c0003441c03a00940007144503110b13110300b1030aa003841c0d540c41070060880c1c012001d42c544540c0c040018903c58020a81e61800c184020840d44d8101105681c5810042c6240f00700302c0000203220b01018410452040140b0740003100d03984a420751750b2243d4454400b031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 520186384 1250 520185134 520185137
    0xf070f0f080a11010809240601030b09070c0201110708030c160e13020409060b130902033a02120408010504020405220201390203120705101a040c050901 67
    0x140004141e0035400a0202031140d00480c107090480c54110046540f240010130004450040d007840c00407400e0103100c149000c00c802e440c034065a190610005048600c0f08041da441695180e0602203a00c0d08903034100c01241e02841c210155010000c0f00615040300da61007200f492100140710a0b11120200c0c24080d018013894412400d80d03034075140720b040c040c82620740310105041100c1130300040c6450fa04c070f26041c43c0315500115045444500094500d031400305c4807100a910741c0e0295045182c18409503642951101902c058401816840c0700e0380c00030010700c012210403040720b60000c0740c020024613540e0080700309459915501d6228413400313807400b0351382207000d2401c04010507282c0b544251401c044548048a01549420070b03001100e0040d100f4424030301200d2680c00080d045101328901c266101d140050b02980d2051a105041c80c11400562950b00764209214003000544007003452441307040601c0002c5088110030321860340d0995124911070b8010300d01900030103c1a000b03005440000803d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 520187634 1250 520186384 520186409
    0x1111b040609020a020715090b0414090604020a0f0c050f030f0a030509010531060608160b0910140d1a011d03030412030c021306030b0c09150a020f070f 67
    0x110482e45050303004180405000d6040b00300c0a1001001680c2c031000e04100c140f42010f0032a9403a2003410203503116411101003c0444021501c080c2400e02c0c03850b0704071000b594111302d003600f101c000a01480050059600b04200200520f050040070040d090311340030300e201501d94030f125441e03078429154001f4040401017420180010b030804010700c5000d00c0340360300c83c0d071100c0c90b070110000741100f41c2070034400480060f030003103036000104e5602d10492000e09280c0000703000d0000f61201c040d08900d00c0d6070115040318010088100d250700d4145c510303141030445083c180d00c01003003c103541400d030240b01e940e059040d10301950900803040c0f07107081c1c07407035000281c070740012002c00412203940d9410168140fa030150700c100401c00480d41c02030380d0b40c811140203280000385010642e000890b1440c00c01d0f00d89100ca43c513001c007801840000c0500725003000a01c400b44d8601110080828040340c8a501c03450060000070500e02d21030390091000110f4040740e441035039146500c41e00c40e1821480b150003030394a074402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 520188884 1250 520187634 520187639
    0x9060c15131506150809010f0608030405040b060708070b190e0a03260403050c030405180130080702150a031523060310080303070201020a080606031504090201111b0406 74
    0x2078511410f41501c1c030302e903025190000c01400a95044901508100440d0b41c1c6411010740c1580e00c3c8110406010580040c1d0740c2c441c0f4280400c41900c00ca1100719120301810084100015549000c90b880c2e2584100030050301c2e50349041d200702101c00318030040c0403103050009031300d05030501282d401c1d1168441d40300c00c0c0f48002844a50004000825841c03514045244040f8001c2030281018104111480b0f003101c2c600350b00ea4010803007804a444d403c502990000340140582014125907080f08008258440912540403014501c04200000b000d80782150000d600320941d201c400000080f40c1c40d209405988605001004000702444908025044401e000108441d41c0c5041d117140044512800320386804009070400c0081ea0003d445a0507201030580006082842070014600c00c1020b9000180c45d4001e401002d011604024041d074410748080007080300010079048644400181030345c0000b0b06810510060300c0341e030a895050409481941c0c40350b0141140f075541510750400646082c00700f0359 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 520190134 1250 520188884 520188923
    0x150e010507080f070c020301150303030501170309130216020d08070b0702120405010311090a1514040e040b040f0c08030403110d0b0c032a09010314070509060c1513 72
    0xb0070540c0c0240c00e620348030011400c180d1143c00f14a01c4a80010000a2007076811292001d001c2031507401100071070344800c0100300300e1080c0d244562142c0700140255160203545000140194001d4000c400c2103a07001c1109800b1400c44440494075590182c00e82c540c000790b03402d1464941d0804941160847c0300b01740001c55941c03000c03034001d441d009014070b6a418281444015000303400401c164424116091103940b2569440315000d000908100003d206e591403080401001c0b0380c00d803040c44421210400040007051b00950301580c0c0309400001103070032500c40307190105225a003d0700c094800fa010107070119968002000034070490f0700c16000410810414414000500c1c40354101406205001000600584034400115800103009540c00c10b8100c4040e0040b84040044405014220b0041400c03000c6580600c200750410003e05071a03140c619240c10020020b200d0298000c0c02080081043d813003401c1e042000203003c0c041c07080340c0301c190300c0c2c4a0000c0c40c0600381c1903003e82c1c0308040300c1c0503040600e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 520191384 1250 520190134 520190147
    0x8032d27180606070312020703050403050706170708150d03110c1c020f011205040615050402070b07031d0f030a081605190507020d0c0602010c022a0607150e010507 72
    0x1a088048104500d42d940010004113410201080e02480003a400c180f081c400d0520040015034440c1c1c81c0c8946507421420b22618002c1242c03c40c1e814031002e418041d107169400d50300203600420a10f0240c03c190f42d4507090240d00400c0e500f0712a0001d0300c5045607000c06030041c1070410ac46126900320b920304181c3c40d0400c040015480c0c152144a08070a04400150520111101c02104181016041035044c5243c203001c96108480a8507903641c0c074813409001e0b103880302c2c0c02001000100ca0660800020340c0b2400c035044405000c0c2424556640036440984c45052078500c05a0f404005460074009181011a103c0d40481c204100282001d40022510780f44800407022040465540f035060058400d0265080e0800c242580140841805980010f036502d080800e0107610403c0d2a0090798505130f406420b4450481501e020340d0025121006551317508082104500104040601e00c00d5240d030129903240300d055005803280907040c0c05e0051002c075035005a80c03a48002e074007c10180e80c600b141103414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 520192634 1250 520191384 520191409
    0x2030d080405101802100e0d0b0109050c0306060306010309152306060a120c1803141501062f0f06011509050d0b18060106111608032d27 60
    0x1300310489145102504025002c41926221030400490031401c2100180384098283c0c0204c500030f01c0c20006100c40711440c05455007000e100c000081c01d50030500000f501d180801000b981c1010781d60304d0170000303002c1120b07015100c59101400801400388001c0d020721024083c1ca0441c01005050400b1901c241444001c942d6402065524000b0b00c8070642114809003038450191003c01c00b0915050790341c00ca484c0e40600055104081c1440d85010f007505071030030309041844190104250000402c6066003288085c0b4943c13102100ea600c07401b02c07020700f81182c204500000040381c8540326411009850010b1001d040c0c8034500c9e10501001c000182c2143e64044500a440d004254000300c00000780d00101403030341014818002210607100100d0441c6440c109902c02800107131040b9090070744a50034004850711070454565075a400e82403101070760350f038031076841c080d242a40910185110441100382211403004c45820107030382c0e80d141030700d050450400905c1000345070025a0388150760b4900800c40380d0a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 520193884 1250 520192634 520192661
    0x80a020c0906060c071a13170105060405061f050c0d022103040c0506030702010209090a020a090906031a0705041a07061b02060a0b01020c0a0e0103210e1c02030d08040510 75
    0x4802c6c1c10f10a0f01e01c0f01d501094440401d040042c8022035902480030300c018003414408000402081c0000d58981c25034602400b900d018602e01424000700c0d4036900c5000d000380d01d880c030300d450440c0f1010b00c0441d000d01c83c148041c0c0c058050580c41c400903a6010440201c074403a40400020003580504d1015094030054a00070f00044442038100050300301000996130119050000508001c4000d0102d8a03441040750a1405c495000a0a640381608004101d0103050040700c204049421555811001c01210001c4a401e40300d01d80020101340c492170440d070203041d203a074030083c5021181030f41c04255008170038121003081c10000d10711f0307200f858500351a48004265004002039102c0e0b81c0c050005240040f940b40c118040e00e000000e080d1a81d14158008080c1545030300310543c07460410040d031042032603e900465045121136120030782d010704010100394040710307599903a140c901000115017080d444029018000d01c141c000f056a040000288181d01960036289840d00c501222000c440740580e6001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 520195134 1250 520193884 520193893
    0x1b0a0f0b09030f0312041e0803040501050f010902040e010b0711060c010f1b1b0c231c1505090c1f03200a110304090e0a06060509011d1003080a020c0906060c 69
    0x1008584e07e21a00000301002101030101c0440e1034603400c4103684111000c2d030b0710f69180d03002e1000281408030f0302030040c90181d80440c20b081c10301e007911031030110611a140c0c80540208000061009108035240e0a08005100580e5204100b030558080c02c60000003007811450103031801c441048070130202e05010883d40c1e4540e4403d031380f0f17070f420303025120000c41c1511030101c2618045040380c070f80c01410b442612710402e5214450740e040c00f00015a02064030303171070028541004820010341300840751086a00e94610200301c650b21840c0f1540307881e04503c0c44590010208103003c1180751030a80190307408200d03039400d000b1104120340c1440400445909844031810030002400c1d414404c403480000e040001c070680e444c05603601c9004003034600800c0030101ca50402d0080d4001c00040e4403c1100900b03081d01d2400380f540c540780113203034060b40101070f60001c0e48096002440b0241c4000310100650390010485485140c00b0744002e644008003100c070760180406c440454082d20303201c0152644078500e00c1c02070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 520196384 1250 520195134 520195141
    0x61d090402010c1403041e23100219030507060f140712060510051207090501020c060901030905121306110606040209010c1205030a0c0e031b0a0f0b09030f0312 70
    0x440b441d110040f8240c0785903522003040c0c070701c90700c06000a200800c81e842e43d100340b649080250065010040e0310050304810354021072070100170038034848018040d08079500c008020b00c0d201c0580c1440d0980904940124001624008041d00107018190302e41c0145000c001603440711095400f1900c0403910341041d4494900003418261141200d0201c0b00c12408000c01c0e81a41d0f2404940c1d030f0f04648031110041034000c28a403140b21b01d00341c01d169001070b05280984e07210f0324010000c0c1d00d4030070404503640225000950f4020b2640240c0000c906a50f0000840343d80d00e404007a03410682d0840e44c8206401280b02a00140c80c502c114001e07145201c00f030000d03108a80390321007000025031194132040d050000c070040d0030004c607a4000c80d21072640c0c8951030715a40c030f15081161104072030301c6802c4003061000030101c101240c0c0300002c18044241c030190f682002c8080704000150300b44140e62000440300c2c06600f02140f44480386000c5c02d00010142d0485450b43d40040c0d0564136809281d03250b254408112000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 520197634 1250 520196384 520196387
    0x605070c0302130207140a02090603070e1611030a031a01030e060a2a02010921020d0c06020d021602090a051e0c1905090a150f030203090322061d09040201 68
    0xc840f21007401400502c0c2500c141d889100070911404500003680000e4215011360502c50036065108008801030001642041820a80c03000041c088003001c11101c080103800701e0055500a40c0c40d035000e02142e8540b401914014050321000191001061010800030415402405600180e20044000c0e1545648020908000740380c0070340d034000c3d0a81d107010a49001c1101090012801919900100710366060342003022141e05102080c154030b800050005044603400710303000407a2809403804031409030607414181c01070701418500014072403001520410900500502c070307000710301c05c1e40d099041d030344c4084600d41107600031203e165450607122075140c2d0031111500c14641c07002d41303c400d8131b041201000c40c02c421184070000100c08250001903000d482e00c0d0140c2c0240080c14100000030b0908004500104080c1e580c03450f007401e01da004804501907035014804d075a0094601d441000349407820407802c8072140414403900307010840398050104156810301c000c0001c4c4401901141d5140c550703030300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 520198884 1250 520197634 520197649
    0x909160510210b04050408120c0909010302060d0b120c090a050f040f06060b03040f061514040c021e0d0809120a1b0606091a010203070b0a0b030307050321010605070c0302 75
    0x204890035039916015a5003695a80c03042500031b034083d08169854a005840741d0500100141c00034280030b03406d00c00a1603d607504440241546e0781500c0d02c949500364510484054901d442c00315a208140e09183c0c0301c2100001211080c5500032641402c2907100d00350b1410803100300b59103103011f101c010400180429205000c0c001420f03c540c1001640b159100641e04080d0030681301150000390240c850010301940b8010401640760920030035600c90301d4031154141c40700080c407003140030310788404404400030300a02c0b6180d01c03003441c1d421111100c4809910b0681341d940000c92440032517440130101d2501c81001400400642c3c0d8052010303e0318040300c0742501e030176030110403260614401c1e28070040000d106001e080010040303044045045810944030010000c5100c401a0440d4424020f160100da03000f2a03091300030500c02000030b030407490303940403078254850114060442d11000482c03014041a100604c6038010002c403440503640d88480e000c0341c4611904a0207400d41b42c1c0c841051003d45040030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 520200134 1250 520198884 520198937
    0x20a060c020117090102090a050f0a05040f09021f170118020708041203090303030b06120a0f0b0607121803240f0c050702090a050103050307060209010e0909160510 72
    0x10154140d5000c00c08100f41080d045030084030603500410000e04a050180d10400039241c04c4400b07510f651060b50100c0c0020700c0a00c02c8030320490700c1c0d240b20000d58082d81c0c000310140d41c015210201c645031040312040c1002c1086d43d41c60000b18200c61031912110041803840c144d0fa00c200304600e4075644252107401940205105031069802080001a00d52000030003100c4a0b01c02d0b21038007401451402c010b003c41c3c240c030118030301810301041324502e8a00b84040c425401924030f60001940d41021260788000e000141e89107401990010f040c82c00c0c442d610015010320000340c0c0d514025102c103017100b040b00060134400100007280c0740d0400120f06400c4580e803803100e80d1a030800119490460700318029510019105400b05000050640960410420300ca07032104030001d00707002765403660392040d81c1e9206000b0060040b07940462403007002c2c0c2c82062100b40700d030801401c0d21000d042c11500283c545104404000740355991810000d42403c0c590002e40188030607488044408454221500c100440da2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 520201384 1250 520200134 520200137
    0x210c0303010308070c150804120203090607060e01240f1a0a030b010c120903060f0c02071203142a0a11150c060f0106080702010603050a020f06120708070e0a03020a060c0201 76
    0x40303000c00e91b05015212480d4580050b0355500081c145406c18005014000540d60119003007040380500b130340c03940d20444d0700d499405031000880720a010111401807180c0e11801a5040c03058260302c554221070072176082a070350742e059010b61396030317554075103550b51164919040d03502c0000f401605103030390080d444249004018104201c1c0d0420380d035034020502c0100a0320401054031640c0506c00c0c0b0185104071060b69042c901c00300500116000d004c1e41d5004c02e842242c110b0030703c8005000406200c0d0707041c100c2c50030305550007e0f11004402c070b0448480e241c0c1a4100600401c1480764001b005002804070030244c0c0180302151204846000c0c02210010116200c61800003082040c00180041105510415404903959441c3d410800000d01b9a2000b52240e011a810148203001103100812400b41c1168100d44d6500818a9080400e0107402a030b54900d00b0001c03080108861141c02c182c2451207003400b5510054a071681c1c03010007400407541d000280d004260b910082c00717100d004d40d00e070b0703401103005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 520202634 1250 520201384 520201403
    0x100b0f040209040e060405011509050405030403170f031018020a140901030b09160305070203030c030109021803030a020c03100603050c0d0611031f17030a03050402060f0705210c030301030807 84
    0x4180b401da2030051706580c101e840d41e40d02d100c083d03242210520701c5c0340030b0105050240001d040680700c01da601e0095000207064494407141c5240042d0086044592812402d04015140d02e841c0d01030004000035886403001000300c0490021078003240d4400c8035040041d507220015200c02c0e00c08400c5450f00815080c50626680d03452050465590101e1980300d0404510042c8140100020007000c2e1400a40200c0640d03005009010304d000e8030300700780d07410345024440050b250403c141107c0d000c5488001c00c00d416010014007681000e40c042101c4200081c10340486046012103104001210100d100142c00d54110000e29a01490007070300c42268540500300210b00d01540e940510420743c01941c1d4080100410125000804903441c4107000801c071606442c00c0d00c12aa1040035140d02c100310409003010340e2603000904541d10b600075180720703041c03018090f40c8400161400583d92840824a00100f0480100042c0d1074191441294034002c500c402650550b40703103540d05c6982c1d805c0300700201c80e04000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 520203884 1250 520202634 520202651
    0x2190c050301110306030d050304050d03050406111603080906010513020c2b030c031e0c022d16050604060c0f15020702040f090203060c0a050408010e010b03100b0f04020904 76
    0x40901850580600000f1404d0b5242404c0040528004208640300b090041c2070041101080c0c002c01c50030803124083c18003269a550b280391000040280d40c01d0790100040101d0003a4840030300c40e100c1c10460f0b1294031401c640e0b45482403641c4e9215800d1017115030003450500c1109408846401404814482c901128030030078141042d4082e01c0c032528240c10b0940d240c0900c8004540c2d05006106180e10281000c00084540c5004681140546021445500e403034085103a9524403c1100070000598090090f08030301e60108001c02040107201d803243c4910600c910103007100029000700c0100c40004180f9480e051030180241c07000d100030703d8140d0b00d8080c44000c1c480440c01302000940b80e54461070005994407014410841142c07030070340d4000c1201d4945801c60f00144c0300000e03166040030152000a0b1141c0a102040303c2d1841560000c01055091168070311803060150802560444114140c40000c11500e800100310b03440751408540c8000050030901490a140d80145011580548080303034204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 520205134 1250 520203884 520203889
    0x60703020c0c09010801020a09060309031b050c0411032a031609090f150603051005060c0c190e060625020d08120a1805060a0b0d0b010b0301050411030702190c05 71
    0x180242d10410742d1b65000200051f00940c0b040c5010040c007000c0c10100520305190b02c0007408548885c060b4148811040b400704144242040980740d47c1070001c0c01030002c407201001c0756600d5002514402e1800c0101e000740581c06c0007165001001080c540049421540da031033528030b100101c50014018012404000318a041c242d000d4100030001079100454034036452004404e01f0350003903100e4420903207000240841420440c0800d0201e8100b103031b0181c2c452141c41c4500b8200b10356031945c50f17031200302d2201150310901c24100c80320403945038007511601c0c2c3c4d40d02028407035984115455003040604082c007040c80240c071031442c50085400230b0310010f50441c0e591795452190b403010044c90030380c8a0000c10060089401c2c000c013103940c80b2a0740d92070162445980d46a43c0c5000182070300501c1034480310f45902c40e440301d8846100f000d4100c507690304c0950703480d1a0b20ba030960080c0105400b990606121409152065085a0203980242d004006100700c2c4900300c100b4000c4540d0417141c82101260005256 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 520206384 1250 520205134 520205149
    0x80705031b0a03171207110c0f13090f0c06030902060316020307060608011b020c010e091909201c2901090c170408040e09070b0711030f010905060703020c0c 69
    0x8206000c0d013544e9a08064250311159800400510410203411035511209401045100c0040c00544811481d400c0c000c0001e00c1c1c0c150b5a00034020010b184c166500140072503114a54521400761604d941202d0b00c0e00800c50580300c021600bc0c3d0017240800100e608132a10116000c5d21200368410740f804d000041d55841d0a48942c0d520101007030791280741c42c0c0d46c1c904c044111241c071714006000074a100c042250010b40b423981c00c1d00c00540725003086000141d8010b032800001100d205012404c010800e11803410207000f2004000d00380c2c02138156105c0c54081c2c1400368240d201030851883c4920104416aa014070703122980f5120b4400050305802c03494986020000140038000010b400b0541d20340b0200c0040c20400360b144010041088541448003040111084806407080640c03010710702d907501040c051400250750f00c1032184980005214080c030006030001031100780f04074107a51440410f002c5580c00c2e00d944500c060103940061000ca40c560740240c5c000e0081c1c10b071a005854040c4007660000c1c0a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 520207634 1250 520206384 520206413
    0x260304080a0e0d0309292113020307030f02011b0606080f03131214070602100b0904030e011116030506010302040c110309060904021918080705031b0a03 67
    0x8040c001c00c03507594140c2c000580c0411108241c8004079800800d85008020380018864568440302803807007241c0b004092007413051580c1c1d404110545c0e511b44201c00d80c1020421148168100e048003000c40c01140901507200c0c0c44a030020010404030742982c85480214400c084100d06100d58514140c080c5001c10410482d2180185c00010307200e0301e0545118140002903290075141e800410013500700101840010041d0741240000c000c0d40d088924009a58030044c43c0307103100700d110f0b84000065280d80041e51701410084154140042d100c000305001c1030020982e0001c020411482410701a548a441241c50b410034403c1190051712a80c034085040d5003040d042510160060001441581442c0c0500c1c91212401d282c1f03004200a000b2000f030306d80c09101a094411180014841d28543e03440e015900c59109482c00c41007e0f01c0e1801025204d0000e80441100f083d40c1200b0004d6010b10200d80300040b508090044c11949007a0f401d0800d410200c80e22441d4080c00100002c0301041d000c0c3c1c04880c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 520208884 1250 520207634 520207643
    0xa121404111f0206040b070e0603090309100e0102030d0f02040527100e040b0402030106090e0d02010c02190605090708010603081c0606051204031707020c09061c260304 74
    0x716034414000740104402400c01403000503501c9050181e040750700107101035105401c00900ca020b501c03080421a10021000105d41e41f0040100a10404a4002c001010112003c03605002060840b500c02c0d1412031030b01b8101800745e007041c88030108040c030320f401001e08560600700041c6040d07218000141a902c22911403440d040000b0f081004403806416075076002800720b200c0358503403841c1c15003041003c02c2c010401009010030402041c110345007508910080c0c8495101031004001c00c41c0c245940d1b40409500d00c1c010340c20090301503107071400425444283c246a914085104840d42c4640c0d000d45005032111607148604c00001500031000e1081358080d521503802c0d5070b900c586c02740c024800020b900810b52002850304908101040c0c00404403864110850017020156859003425a44801c03c0036105001c03c403010708108695a0100c1c82c400f4040c001c503103416140c0c482d0300a118000495501070090301350704a0310180802c0c1084445889049a0505418882a210f0440040c1d400a880484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 520210134 1250 520208884 520208903
    0x20a08010b091b25080706050f0a0507080c13090f060f090501050a0302011b12120e06090303070c1b1e05040b090a0203070c05030c060411150a121404 66
    0x14505100b40c40d4110301904003810200c0180744101c1c0d0325100d4505802c28144641e1410340e803100d0781605003c8180d0f040907100351030701e032503040c280701900c812140c500001c0f12a034001459020345205550203540e076035490300c10b6a44c4280003048603902000e5000603814034070a0001d00420540141c1c07014014101004c02c5562410202c20321111103900001070311400e01c4c00500564071401c24510459409107000141700000d800e48504451503030700050b040c0c0c0c9400364800803103500100c40300761018aa61040003207541e15910743e070b243e120640340004560070800100300043c2c030440046928500550002200304840740c84e2036014105030740200700b1000710421007241e05805900e0300e4003c0c0003c0c0c0c0c0500c68182c034100041e50707800c2d000701059601c3e580440802c03405485036140204256121045a0740c030880002040c0e85c600040b0341c2240c00c1030030900c1886488c1480840c1103280302d003500d680382c10004070600a40b01e0754080da130700c0b015043e5510159592450400d04550155014500e0031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 520211384 1250 520210134 520210151
    0x80624030f07080c150a02060f06060f120f0601020d17100b03070306140f09070c051002040308091e0d06020307051306030c020105090d12090c03050a0506091903050307081003020a0801 81
    0x4401c2c0b9071540145d401007424001104819000314145a201e28400f01500041d43d4403000a000da0050003540b40030380f0404200c030305940c00c0c407842d2140140e41d044101c58a81c0e0b906001241c1d03074900c03c1c0c1903900140c05415420664a00c0b07295694002c3d01c01c1c408008060703107550b50101650002ca810340002034072560104015103030f400c00c51103414020b440044012260304046644000302906007000c04c059094a001032090034004664803c0c155001075581d96940c0c2401c181903040b01c000c444c40792441909441440381c00309406800c040010340313030951440c96900c818000303400080001d4141311080208291401000c3c1640f0058440e40d2000965134140d503030000d00311600200203403401c1d4440e001c580b508642200c01c24100c1a41c202000c100c2c6401e40c6444c5100404a507c024141e105040355a8100310000c1069071146d02071100310f910310403d41e411002d0710a00b2034405808140c0800200e80c0c09441501c0080c2d01040a181c00d04000c4d50781d41c0461560113482d4030907512a5940c0b03015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 520212634 1250 520211384 520211389
    0x40b040c08010203010605040506160b01081f0501080d1103071a0106030c0e030705040c020a17190f0e040f0b032509020403080901050307020a0b10090501080624030f07080c 76
    0x90300103840c1c104000c505560400101070514400ca0044510400f000305403240c1c10944ca0a40501c4507030300c54a11038503540c1d038005144d9568144c85404602400d90700281403544180e11420341212080700042c160500000000c3c0c1e010000c2015544250100300304440110340d9000860007040382904a924041d0300d0420010101d81035859007070108130500c001c1c42540d6800041c114107446003101c0001d40704030030315000d034546031402d0b00040c40101c0a40c6031207035035002800981401e1220301801c0d0500307007a90604407a2400b101c0d0003a001b2508440080380c05040a90000c0807001184d83d0001c3c00c40e400000181ca00b850322011900c41c5c07050f10784504214250700583c0c00080005000c10341c09d160444c0e41c0d9000310b020307a0b0f1841d810000084002070303503203100f08030b1403a071603401c00310420150034040c00440b18001ca5000d0390301401e09160002410642c00183c0a00c60840300e0160300c040360b21568081018404c4499a81e40b6110b180d00900e607404090160f80024802c510040c580d0290440c103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 520213884 1250 520212634 520212653
    0x5040807020906030d08060105090a090f1b0f050307030513051c18060206010e1f0902070506071b060b030f0f070e1302061b10020a03050a0518031804090506040b04 72
    0xd14065002000031020046d003110200750004800d080194440c0d071400003007260301c5a01e9104400107420f1408402441023640c4c000c81d03040c10160070180d40103011b058140d03107940385d281006000520410009042ca48241e00003500101a0071140500c0140354544070300d403000e0700c070310f604140340d2043c10700c0001500301c0f00c4200c01c2420656032500003454044003a4031900d05100d00c0451031640c07000240c035004030b64500075044003802000c180850715280840300075004014112814403c50300482c20341400fa070000501041c44408a0b884510941e403010080e03c01c20b00300c0c6405109038028515290814011002c4403885c0b0402004410300d0440005002c0745e000d06461a07c450908114016031100800c61380740c0085001c0004a54811030641880e0405528020728094400b003100c02c03506606402080c0074034050b40302444181c8034042d00005d0b07403084640540c56944100080a200c90b20160900300700c401c000c1c000102034103180c1b690760404a04440c01c4819041c29010441007104806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 520215134 1250 520213884 520213891
    0x603150806060102030f0c071d0106090e060607021002100c110c100512180a0311162106020702280911032806030602090307061d22050408070209 64
    0x4005000300c0c01e1182c0081d440303105161a031030712507000141a4400020400044005000c030f91502c61421984030106080c401080c003c000006464500004085c808a4070160188000900ae42d284c01110b41c00c015155003114460800d5014000d1301c80309041080c440d50340c3c940b40c185c880e981c044c2403404500d8104001591802d1093340c8036a11080760070750140c20380c1c01100e82c00343c2e080d90036258040610300e1003d06092008552050f902d00313108040d03003c0000b99250ba1410204c0700500e07a1190020802101e5024042c0d0700384125089406a084001d2604110360080000601c0d000c1c0a0b00461032884012904403003841c104521b4060303070310201802000802c64100d08005080c40ea03690310040340b0019241c02030021401c0f000341c0c5101203a8050604040355054100851982ca141000194200300969407003405501340004185001e0028000c9160020786407a55082240042000c0340304000a038000c803800380407a0070111342c21842401d0046014580c0a0744801240c4100100000b004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 520216384 1250 520215134 520215149
    0x10201b0117040c090b0a08010c050703031d0c04020f0f0c0705190b030402101202120601030c050a0801031e05030f1c020f090d020627150c1005040606030204020301060315 75
    0x602080046202d000c00d000688a0304d43e004164100f007200001c1400d006a00000101e51a041011046641000c0104003d51181d00d0a00054045401107031540801182d03840c0e0340c2d000000050300c0f0789816802444110380704864075042c44600c40018101d90003030b030503070515a40900750130b2060b403078410100340081034442200c4095609111202c0b000d800044c000a00804406010340c54150060440d480d10f460144001c6450380306518400165407815119140442c1c5420384030501d40380b1a0b001c80c0d01890f03144e1154206079107180d13900e406000c8801c2c03c0000019884e8007402c00503c05000400300d0802807004180c603080950401540c0c01000003105130720500c1000724a1582107400183c4072a6101120303404e0305078040d40007089851060410600c8080c01c14803a45c244071440c0304445411003000d0b1188003100040340f0000020340f148029070049584142403a40c0104031a41005500c00c0c801d0b880441d207a03a480d804038080e078100b80c00c1000803d0329600340c0b46052102d01c940c0e40080500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 520217634 1250 520216384 520216427
    0xb27030c1c02030409180609030314090102041203111903180b1303030305060103240f2c1005090a020c16030b011406090907051e0910201b01 62
    0x3101c080d541303118034410080b40580310702001070318880c001c02c4224440d07080305040c004294a881c00034000e01500008203c5440d404010480c0341c04d051082e501640c03615508409000b01703548060b9000303503810812100520686982d250003140051240c000c95200313440d20800e040691483c01880511a0810421000103008038403402140394208030849405090025082d2903500c0100d001d0006031918001d0264100c0c0030509850301014030b501281d0803007015040390f031b13203a1628810030800b00e000e217600c118641080c11001c02c6805169604640d0809081c00920b942d00c011800c80c0004444426295501040c0d0416140c0144028010454102c00c4002d0450460b56050380c0c9150602403e11040c07066814101c0903125071080b81c00040009042c40d40e5498a803034014034550251006426066450542c4103852848101b0750701409801000062a00c0e1034510840d405c64104000c004046807211800380390702d005000154100d003c00031a403140e0b07600301c000540f01c043d4406007403400c81038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 520218884 1250 520217634 520217683
    0xe1905030f0a0e10020d030b0303090d0615120b01050405070c0c0b03090c04060b030103051e0319200c010801050105040e060f12060c04030309090209010c0b27030c 72
    0xc01141c1c00700c14000803103502c1d01d4003100c003102c40c464501691500081c8516071090301980004162216520540c0e052050b4001e40040c1500da00507120b0320f03030b00204036802000008103170b41c00240f400c50f07014a01c1000651349a90840d110b00c0b0020064610301442d03001403000d41064040e2583c0942c041c00c2000c00129150303104e1076240042d1161013501c5501001150b20480306205440b000d50008100b448825102d14840c20030794400c0c44129124800d01c00e400f101e099039003142e5589481c0c038202850a014180580c504181d902050700740411518201c451600b0341c660080201c00b800b40c000801050340c0c4d040003d41003c0b01a00190305011003400b080040381d0354201c038264401e5003504d80305804000da1010480364100710741c00702c103540640300400c2a8408500090800c5a0003030fa1101d8207140e41d45110340491040c00f542500040c1d1801000021510410b45035800c5409041c1c0410700b00720040c8459405141045417084070740000400b00000d84007042441300a03407030b5055202c01e0300c2c0e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 520220134 1250 520218884 520218893
    0x1030305070b0a151e0501181e09110c0d1437050a03050c1602101206090c080f060d1203112b060302100e061c0e19 51
    0x15078a4000c0080018000040750f10700540c100400180325403e15a44081e00c509400d0b02c00c9140300c014410009020b00300182662044100340c101607214a6212032450030400e02050004c0f40c1d4036000318442080c0304c0000c2d541c6e41840740192458a4007541c03a100c03102d124402e41084000400351040204060541028400c031501711208850300942e4105034048507641b40300d00b07980e24400580e0710034000045414071900000142040251030f6800c000c182c3d141000314685000b030141e840015500100c0160040c02d1460b07c01002d00ea042c01c00107641c00700c01030b5003000c0c0c4000c0d410082d40d181c3c82d28028241250442200c6400690f00190411a40b03054008500003003034641c1c0281480e000b601c000c0d10898000ea01c1500203140400c042599401c1c40010340300e03043c640300d41c0407070344491035002482d01d1142e900ca01c5065a1b8020525098900400c00403284c071aa0701e45100d42c00b2004000e803000c204554405a920b0850325070020455106003142c4500b003043c01e2803c0c5203020a0150b041d0f0005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 520221384 1250 520220134 520220137
    0x6040812130b0a200d020403051204030503041a0c070b04050f0f0913021302071b080a12050c190f1e0507051c060e0c03060a020903030405060703031803180b0301030305 74
    0x10b099000000f0350140c10619007002c6441150644c52100400035002410304510780080040d1b90180b800c50310280d5400c0c1b512401c42c4981e01c4007510581040c407051100f005402041034004c0e0240310b6081c140b211016040341020216400900b1001001604025a042c030124404000b0022541c59400e0350f10300740400d401000c003c10184c103c020041d003002c00c40d592815003203030500b0724420454854583d40f4061090144100102c0f0040584903400100168000703000380c4d00540c0141c42c0701c0d9030209060140d40c2034115a504144c680141c0344601c2a140407c4400140700340107004842070403400c2c1c10801a2a001000301030742030840f03030791520046540007800c101102c1003074480c080b1004005040240d181168640180100d00f0a011705421083c000b81a01c513840c41201910150740390441c140f022481081c0300290990010301c0100010702e00540500b18044c02030401041c1084010642c0100300e8002508602090300360b0b665075621903d40d5240000740c074413500c0c80380c0b4550440d00e014100703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 520222634 1250 520221384 520221391
    0x3a3213121106070908014d120403120b031c02100e030d110a02060c0703170a051504270503040905010e0414060403170a0e0105130605060a050d0f110306040812130b 72
    0x206051400c0c2001c240c044022481c0042c2c0301c10001500d03080d0704080d2239003000c03060320140c002a00c450113100c20341150340300b0740d00000700003001407108000041c0b16010803055200c2c08002d5000751b01501041c00c456010340051103004c10003855584001c12180800c485001c40f648040020500104110b15000999560025200302c81a61184603d1604030b51651101942d40c401422a60900940c80d43c85d4004601881131f08030488400290034003800101c4600304c81a0160418015001a0110403000d40c1e545890045003030740d140c0742d101c0c404181600e04c2a0300183c0e43c000603800f08424851082036a02402c03008802928650420b610010702d0000480c0c280034002410328040f45008141f9480301c02c2105008000b0b22480c548a142e030038900c844504250381482c20003000980a2404841c1c88085d11001040101c20321950349170051840e404020841c0c1d681802c61685ca02660b0030031556100700c0c4210341c1650383d02802d0310f40400d083d2000d0305458214040c15160f10001d030414800992 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 520223884 1250 520222634 520222721
    0x3030301061803120306080118020a060e031608160e0106050d0c05130e07030b04090b07082d06153a321312110607090801 54
    0x2a80482c011003076030802c1460740700034590b100200f603c904554054022104075500c0100070001c10340401e100422458800034000e51001b0004c4043c001c0c58000c1410615815016040340e1002485400324840c03502d0942203001268000100720701031000c610301c3c980140044040860705549017000c0a00b0a000d20702c90030f0241c0b03494083c0c403c2000c1c8204152021510f50035031000d48035684070701d2030320050003e40c0c5d0b0500190800031860501d0510703005504055902c000f4070041e07a030b2050000c4030952409015031024500014100280500041000e1082e00c800c1400d9211070500c00100016148030410720203001205114006030130721001c5800d00704410702c50b40d0340803c42050000050454040050040d01482d01c0c03410b0000c0302a8810b200e100c1803401c0f4225001c2c14080e40400ca0101c0221059842604c41e0b01141002402411001900d1606410200156180341c0055400c180d012035035800000c008080030414001e0034001c0300342c041046110141d5038100c0c90014045110305107003011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 520225134 1250 520223884 520223897
    0x50a060902010507060c031a04060302090a0908162009011d0c0c07080705040e01020403050d11030706050a090b06040b13021c0501031202070e060901090504020114130801060f050303030106 83
    0x8040d640920f080711080365108004204100000d0300141c014200d10f00d00d070b0590440c1e901404ca40c0e003800e10520090340d8006005020030f0340d5090b10b4074060b10515030b045540003c14818690034543c244403100c0018030078014502c250f0b070304802d1014500b000b07102e0755220302a5a0b00401c00301c00d02124030342004415644104a42e9514604c50b02203204403581d051052188400000b03000314007041c0b04058941c02c4506004034010030b480b15082c2e00031030201405540188100c504903034010740100c2240900300081d40d042200c00e8803104d080318000c55109031013a440b040d0803410403c1c0d40340e03020380c0300030b040750100498420f030404284240ea108551401c4241c0c00101104040d011a400005001004206104a686038505140c45050510010001d440340a4002c0b402070060b41d01540b10b40e10280070720b4a1a86840d01d80c002622000e4000e80c148004032805909808190005022201c0d203441201c03106031408816600f100c1d200d83c031100c0200003091050040e907601000b140c0c11a0f036145000e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 520226384 1250 520225134 520225151
    0xa06091b1205040b13050f1e0c03070602030a120b090c0a080618150a030b0103030e0a0b0306060d0911030a0c051e1c1a16030506010f020d050a140409020702040513050a06 75
    0x11442c200d610f114010140c4110300004a0602c12503028623080d10201c1d0aa40b1445020402d00d0358aa0a40c0500f0001d03800c00d10175011014412260b03a850b40303801c2080030401011030b4002c10142c076025035a00c0311001001994204072904880415007188058808824182030490f041c003552002405105100a403211514056502d40b400c20b406143c01222110302543d6900c0c000e040004c0500886002d08200c0304001f540f20340c2c0f0340903203104c5c034006440c4038a4000c140c0d01075002400e001008880c50590740c405141182c80070080c03840d0061103803660310211400d1000b0040c080d100c00007084030111070440c6440c11034484511509800301c10701c000390440ca40c00c1c5000500385101d40301040c2d580c20741904110301901c0b10740f1280801c103820b450030003842c0c5405004603440041642030302c001d40d10480e042054180301e00c0061001080d43d01d49094225000c64100070b26a0090b44003600c0765402148150940c5072034860190403075032074444950001500e5840741d864441c1c0510250200da80c41941 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 520227634 1250 520226384 520226393
    0xc03080424060e0103060c11060c030a0f0f0608010e07030c0e040611030411010906030c1e090b070503070501060806041e05030f1c0501060203160b0a06091b1205040b13 74
    0x7480c0c803140140d0420310410342c441c0c503400b04607030092000b034404038140300c85180281d005407201d41240c0040070103440241d45d00b01c070a0740c02ea40050b1002c170801d50744101c13148600b081481184d40040d000500400c0240c0b031701c0b503c40e00350f4143c0201e20072207800c000010400584a810000c0884106100a5400da6554101710b001000810040d1a6448001040004214410039500f0500030301341c81d40502ca41c0ca8210031000c540ca44a10b11010461030b07264440c0044503c0d46c40c0410a1040c07921305141619690480314a0300a260100c503a944049180c60170400b080c01000044c0c20708600170240382c41e0a803119443d5413218590782201e002122582c00520100744126039019184845442da29210b2400303040720500701c101c00b071403032a02c0c10b8000304200c0d101000300e0303140b10281580c004014905458054035402c0107800d100b20b40b9503403000011041d142c2c2c01260031610b0045203103e809495820003405403104080030307142c498588403c110019140c0c0051540106c0120009024003038603290 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 520228884 1250 520227634 520227683
    0x11210d08090c1909050f34050c010f060f09110325020a060207032a150b011e090e09061b160b0a050912090a060e03120a020c100c030804 60
    0x40302c4210304103000c101914021104d030b1070107404043c1e04940310036600c800014820340887c81c48071000b4586543c503160b4520030f44c080c019030700400c000018040700c00034000d01254030360b40c042c810380c1550260403c81003245203d41040803000696062862801988802d1410320300c2070fa102e00850b001303040165452003006035070744840e40550115950025418090022150b0384e030204852494060400c0c000b400104c03410741c0080d40554401901c40544115401406411800904201000044410b0340304a100413400f0762400e61110b03072102c0e041182100f9400e4008101800755846031040c44000e5002c814014007101c1000015512040c0300102d451480d208400081c03d822030001c14800000741c281d000c2030107140214101e81c01548003008070030260080b071442c2a48800d01d040c0c10040303e0300407110800610802825980300400c0e00380300c207005400214010700183d200c0541c01d0840c0c01c06c1038a80f20094030604058985103165500203008460082008014440c0c003003000b40000500071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 520230134 1250 520228884 520228889
    0x207051c032003030417070c0506090f03011d0c01020703050303010302091009050916081216030311070812010b030f04030f2001050603070519030f11210d08090c19 72
    0x5494003520085003148550742d401c20b4078151402209246d6507040381984104950f0960f81c04024842d130a45400d003003022030340020419030342040c1c6c40d02d1090b4040da002c0c411404040654412001c802c80d15440c00c515011b9070510260656026850500100c0c41c000141c0c0e044990403034040190360b559080c00100d420300c2e03030711200f07115040030180100090b0104030200c240f0000464a401c8680c1c034a0001c1ea910000c4075a0030200904100c1c49100b1100411201c3c40076000b418082a010000c0ea000102d0340d007d2402614450004208009510800c0b04a680100140c8884500710700340071111502484010b40001c0601c00b50707400c48040306000e042c041c0c1420341030082059401e100c0c004c0d0301c0d0181c80210f601d18030a00480c000400d80d464111071106110540000c4403d03840d0542e500c00340d025141502c02c0d2000c0003107020307466840e03554019002120500c00c81c070000030031100580510f0300c1401609441445110300411192071000641c00b00100c0044031702d0381c40d0171080346400090076590b4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 520231384 1250 520230134 520230167
    0x1030803070207420e1e06070b01031514161107082b0509120c0649090201050f0406110714030606011d030616030c0207051c03 56
    0x45030800c44c0c0c04c004154001c07018152200404660100304000d240c00000c0304150000c54482c0a07810101c0c20803109808140d182c141040613201a988000760180e003040904aaa000540c4014400c008142824000e00d06204c40d081c440400d00c0100360b0603051000704042c003050000c0750452803591080c080b1602224403502641c401c3d98803048859103841d149000070003602c0919804d901c2076501e14107418141e076240c2d5030385400d00172000200000740302c0550445601e0700c01c80c04044d031542e861034006c1980350841c409000c0004a80c560014600030642c0c03920718000002c0050000680349140f082c1540940c0080c00601030b03010b8801a60f0342d0240e0f03000200c07415008240071a00310741059248040d05110300171160040e80d01e208503807801c40c0d0300c0385603900358000310007203000e95000390000542c2d07844000f400d480d102241d8000c40d16003102159800c074030314031180103030908503014410815444014409480841d00784004200e0141501d0b8a60030240714010310b4101745841803505910b01300c1c42e03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 520232634 1250 520231384 520231409
    0x403051c150e15030c15031e070207240c021201110c011410060c060209040b030a150605061303120c050d080403120203041e1509051005010807060801030803070207 72
    0x711070000b80d951008980004048001c80303c11980c0d4500043c0d210240300005007540b00700c00082c42006283d0b003000d40680329070040e88030603004c01c1512503170340e80c8140d0050b03006012941ca002d114080d481c0300c2c00c4402c58011941058840101d034481e8184901c5501554400c81c0c0459203440c1500400c91603105402900c2e012400d94520b41c0e040d0081040e0359020000d45103562102c1441403103502142c42107d0224120210b1480021040e8000e842501c0c0d0050000900041c0040860700300010084221001c000d003034062440e00700f00c1c0c07007203038060541601c000741440d04080780c070524049103000281007000b18440e51503416100c1d4442c444400e50003400e0760794840d001c050141c1050303000e0304c080b8003007074180c90314450440f00b5200b03503485241c0200d014400b80d940150200d42c3c102c80d00070181d40099010208203c150454001e01500510500c01004071000b1441d0310421600c068100d0007280d00841020406d01c2c1d404080c40d410369400c480000d03960780701c2880580c580710305684121504e840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 520233884 1250 520232634 520232639
    0x708180c060406090e010506031315140406021207022e020d020f0403140a1a040c1502150c040311011805030d090305241f0f12021003050403051c15 65
    0x5026001130102d4400b16003601c0e159894070304003e280e00044603907103190304800c4820004145196200c514007450281d000402242004d0100e1a280e0111000e541084d0000703100010048190080c0d54404010b101810281c001000c3e0000c51b405108078000c0180d2444622902032400b0354102c80030080100001c40d520703d0200c2e0b4a05958000f40310030354450019900c884807580000ca00f490050b5484520031086655482c1c1c030f409800c3c00504151814085a50041078008003a000b04580d00e841e0340080110240802001c1d40207800200f49400001e010b100c02c000003040100042d139454400d00b0f1030441e078809440c0720364503844c0c03503400a50b142c0300e8401c82404040d0002ea5603010f89005d44255100e4690051030281032010000350b50050021042c00500680d0464a0040d1600351410700c000c1c0d516a55082c81511103043d80001e0b901c0c001d44618101149003078600101c5a80083c00e080c040c0d8a03054601030210b01a841a80f6420002d022000c0b075075005a90214000a45080b00d1429030354 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 520235134 1250 520233884 520233887
    0x60c110a090c180e0a0c2006090c12060408091c030c1515090b280510020609030f07030306080a05010902040e0102040e15061e090112050708180c060406 67
    0x803030b000848003107481c2100c00940ba99248110005481c2d4070381072400551030b980b504400030080710901408000d880c0c0c04010314070303803c2c0c410310040d8141500101139a003091182c0c14140a841d60801d40710b0304e44d201e00b02c0c00c2c40c000480c009078000e411840d001d86a030028400301d40c4494000c1003151004c000001e16a00f0107800c510170b20b0b401c0b800340c0c0c41807c0c4c3c2c9007d149404c0c1141c240c044040740a00c0b604c81d0030007158110750010328202501a2a02003c101d818061054445100c00d20107041e001c900014030540c10030f281489844401c600c0204014108100100d450344111101c0800c04003001074044103150003904144000c0c5803540841e040c0440390b050240c000c1c03c4040c02248100c2c14412194000c100c1402540c0944034003044244154480146400035400100111504408140700a1103440320210a040c00d4101d000c0c903507aa1050301c1c000040030050710440c0421900d150400b4060196402401d0503801607030923031201d140c3c901e00d0203004d2415040f060003642c0503a0000300440c07040e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 520236384 1250 520235134 520235141
    0x3030a120b0a050a090c20190302211e0a050714030906030906091204050f01032c0303010602060a05011a03090703080c03090a0b0301030515101805070e0a050a060c110a09 75
    0x18241e603520780300301c002e000d00140ea07c0310100550540a40c41080d03069a4601c0c40b50218883c1c1c0d10a004440000f1801041800e004400c00702e2550a610041100b1004403103607400541070000444446142207003000340079056005880028120400d29110310315402e03010000c60381c1c4144014029070301d83c5407500c127841d52480c0c00c5070004603500604031031751302d0300c40302d0801d81d401e40d600206110503803c1350070f004500a01901099100c4424203141952442021009482c207401d03a10018540d60340c1003100203460008080c0100d06031526020040205402c0184600142e1040e1000160f60b034039030701a036a00e003007500e410282c4210380003c3c4050b10348400000500490005640480c0525a44c01c01d00c1d250340800d2101030034a0700910a1100b00003164249980c1c00009034494035850783d01d82c481c0d0303e15a22901050a9110340d10005e2003d0306e904101e4001d094403040f40c0040c021410000403441d0b4140701d1144405000040c14520208120213003000c900c5e040203450a4401e40d607454844014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 520237634 1250 520236384 520236401
    0x8030c0a030e0c031c141204170c0d110a051c0e03010509030a1808070806070912120311040302090f0a0c08090601060c02010309051b0301060503030a120b0a050a09 72
    0x100c0d14000c0000042c1901283e00c96010f40020003800c6600901000034a898006410b50020891901c000030450b008000203171065841d08201c01e01c1d24031b000d1074004851031080088240c85001400320a5041d080004d510760214090300d0100740c51403c1c03000d60b07442c110702004020210b02800a80010820000340e120b841d01d0b0081c1e0700e1645008501043c182211402d60320015150000c0140295107405a030b111002d02050020114680e9a224401c50070012150051112900b100080c480c01d158810b16203405800c00100050342000c07169258603100e407461020ba800d164440c50304810a6190106032001507402a2904500d07140041a000620000b1a220b0380b2103403030503c5c84680907201e1451a846070b44040b000740780503424102c0c140c0d102e14400300105d041540380c0c1c00c1b140015a060042c40217140402240241030121102014251030880d00200e00075841400280c540680c4410303030b206807001c074010000c0c200040b50007049c8000c400d030300080e420140321040016500b82940c021940f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 520238884 1250 520237634 520237637
    0x3030213050409050a0605130b060d050c10020c0406050103180204051008010f05040210080402310f02090312190c0c080106151106010501080c1c1d0f07060c080d0908030c0a 76
    0x903500c500c03150903100e2304000080c00c131110b4500014111700300030040311034284c0074001702e0f1014440400050b481a0540f03403480b00581200700c840788103007000d0081c0006050242000d1010f05a4805a010b0b4001010406072082c0e448170301195100c6080718114014240607c001d103c641e40d003000000c040c00040d103080b802118074030010000345100e20140d5002d02c3c2c0c0104035034101260008000705c212002245c61504c0314800c08904100c04c003500c1500303604159210050784500c4050101828601d0038010001c00e420300b0840c440b9240c400940c2070810752541d0600c2a6803560034289681040f145404c081041e61a00301d02183c00c1e10f8031100c04a80304182e5a40c020005881c4202985620080c072449005c22882c40129109010139002360800105a01c20180c241c00801e17501c4c0103070741002c40f680c1000c44420b03408000000c400c3c446000d0b0b40340c51100a21032140390000c010140148440003504003000400e503444030324566000b110200360050942a120300300166045016070040303400a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 520240134 1250 520238884 520238891
    0xb0409060f090b180703080c0102091c02010f020127050a0f0609350304080c010c0906140c3007060204140904020112020a0309050a06020d0605010203031303030213050409050a06 78
    0xf00000e801c813800303580412458002e040058550360720f01000d90400441403800d55000c0c003142240e504c500701018010810f01d611402c007107029000240840d52129075070811641480042e042d000d0008101000d81101002d21100c0c6040701c3c14035600b4204003d60041c054001107080206100c00d035007003a048240a42c03c19030702150b8000e908414011800814800150313550b200c0400c00400034080e40e03210b0f001e030a0b0b132454800c101d10702600311400243c4010110f09020070078010710341d0018180d043c400c407140e0454a07202d0a00031950b51104e0b40c903e55000c100f07094201030603c9545080003100c0752219954507480782c2092414501a40007070040044803504000c0840c000d14041c0302280c000e0350107071141403908078035802407006036002076000170500d0713202c0c0801d00000307408104014400d4042c12005843c3d6015080364800ea690a0303200604551003401803100f424000c1207078809569042c100140c2d140480604040007910a501c03041d48145002c83c44028003001203a00d286c807620409041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 520241384 1250 520240134 520240141
    0x80a2d0e0312040e0628090203040311030c010504152d1b08150d0f0201081f03060f1803140705120d0e060714040e090703050609070311150304060b0409060f090b 71
    0xc140008141d400345c1b07441c610040c03080007088202d5000b590498060b141c03802d02240b40c02801495988031540813001070303550300200010301403018044c1844854010f01408059000203180c62242c101c001041c00c04c010001402d039101070194801202d0058180c00850740d9200440050700090044402c0c504801001c805020b20380707446004501044e9000400507082e1149070011036203020300601010604102c1c110022031070300c8205003c00114840d11020441114010001c41541d03510808084054840b0484500081c3c0001c608600e5a0903e010140c4440305030038094a081e08107401d8203c0d124000031070b5000810a50422501a034801048a40701d40f00c9080803100009070b020442e684020900c002d0221540882d03a00c0d03004000d00301140c14642e101d03211603040c100d003610001d03071070b42c4400f501700100640140034006002045414200c949243c814050390792100800040c040c640d00c60720440641d689900030340345260428001c11168040c130303e04d20014146210191a0010a100017 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 520242634 1250 520241384 520241419
    0xe01020c010e150a090c091a0405131505060d083115090803030a1e141021080919080102031e2e0b07080a2d0e0312040e06 54
    0x80c200250380c4800346c0e8400f103142042400080c000f600d030031038a20300a05180f40d80d9079600d0240c24040c040c8040c2c0c48400e09114a0032503ca20300300040c4029160030130041124558400200d0540c89400c000305c00d54555000c00c4a03a0a0780440ca8018032030380c0b849034150117015414058074255100d00000e000707058114042078400300c180e4451080b40d41d10030800030307007084103d41100e02a204035030108010150301950300c3c001c1c0c4000e0030031500c5000ca034100300185c0382500c0c9110401404808400c1c0c8903c0e88100050a034442d0844026000301000590320b0180d80320700c3d40d40b0b900c9642840e0900b5440d42ca4400c00d078044e5005490780d16000ca4032101001890f01c1c034400c1c1d00c0c00390005100002e07103078190740310b0004450303100d280b07681007580c20481c0058030410a0000b84080c9114006070b503a20345c0f5821011341b464200041c442c081070341510541d240f1104060b9017958152082c18074803580381641c0d000914102001102002407000842d001950a40c00110980983c030704960103c2c1a04a9016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 520243884 1250 520242634 520242641
    0x20a0e103305270111030f0705211806071a160e0f09070201020f1b070e010513050603210d0e0d140f160b0f0a0614040e01020c010e150a 60
    0x101d02d1603040010710190110f02c2c3c1810485103400d818140038091000201090b0b00f580c1003e401054034810000e003610400006100d040c1c4981e24104a024403c00c8488081d0450700404000110032507000d0041401c42c1c0d5041c0a491445074808600351003000322034844d030320340345054554441c140c4c4000e140d480360501821003500003000241030700d0740700301003002002150500035129000b1f5542c02c0060322016100c8100405e40c1c0d11420a041d245005070740c0c0303071518020043d0b108541038092800180490340c0e418041c02e021501126004c40c0c3d503251100081c0c10003801103141722642404840d03030170101c8020405820282c80310a0108130b0070405080c250b49a056501704080000d50f112004064409200043c010103e84030740160300741020603004c1c03110030403440400e840c42c103502c0f0100050203034a5109207a00c0f40b60340c001071064170314090300c489000310404030807441541c550344404500c2c8000d505440311000d000000340b0409280700b09840c1c80c2d04040300c071241007003560000504440c10501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 520245134 1250 520243884 520243897
    0x70c02131508011107020d0f05060f040b070e4b030f0a0803180111030106050d0c020a02130e0c062109030a1d180a0c0e030a020a0e103305 61
    0x43d205e190401c0b0303500700082c1140c0344004881602d0640071400100c4d4042120600c03850340258a00c020382068100005400c00c001c01003000c210314404800c0041d10b0300030303119410b5401030b0919803002c400f920911400302180d2120340b4044480c18000a507810701c04503100d030b00f50002d0b070585003001541460b03103458600308080603081d500200040386c0502c01051004101c10340c4c0c00c00001b00c8218039072020b00300d648207a01150000b800494041e103501214401c0400107007140c0004e20f0000400d90118000341c40600700403505a58800340884508414810844500c2000f0150b69a0b0307140160094004400c420920a002803914001100c40744000200c6010009544841c1610360b80705000b402e40c0c1ca0000d1180b03410900303201808400c00382d1036083d9401350b0150381000c10f5022041c20001c00ea404010311841c0b02e07601c0980054050380380c0c440740c502a00e050400c00c4034a50ba40c0c44803250000344642c00915802d40c94000b102e6007100443e0408292000003120303034038000c40750400302e526000b9074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 520246384 1250 520245134 520245161
    0x100801060b0a0e0a081212071110020a0513080d080c040308120604022101030b06010e06040b0f0f0705160e0c030a0506010e03010f140a0905060a05070c0213150801 72
    0x100001a1098042e03c900e00c200400186070000b807544031032002d4241012004408510f21000c56806e5910b2000540d203540002c003813034401c0a003041d88013100c0e50b8100e4040030b503100c194005070032114a07201e18111a05510151015505299038075802c6548403d0040c0300000910311101043c0242c0c1c0a000700c0b000c498001195504086442515a20900d006071080c0c1c0c0c451b900300300c00c07130441550300845040301000320400300d41c03036146007040c0c0614800180010304014501680f840139607a401c043d83c0030788103036820058071942c07101d10076100b0740f0514010019407200400e1840c20004002010301540b01c0210403558882d5513404403881c042000d907520005c00401380300244090b8803d5004651060051416103144041000400c0c00c443c1c020b24414610b40e2190326085110740010f100903044007003e00c1c10851160580c40c2c054132040040d003845451511303503010400140c800d00745002c1c06900200b0109008034554559402032002d604d801c50350014425000503030700c1c0180700e8604128083d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 520247634 1250 520246384 520246387
    0xd15230c09010c060b06070b04030507020f04051b09040605030a150c0504120303020c0c090a151a031b04030623060406060e101205040302030703080f100501080402061207030203100801060b 83
    0x584d600c0102900300c00300e100380c0000040c002c1c000800c155000302801a0300075182da0b640d5480c0e500500032002c40d0030401c43c1c00b450034001440034200c1c0f000c9507041c50006001d0490745482072600010b002c1c1003a907004540c103214844100092000300c81e0820010840c24104010b81c1d0303503c840c01e5526000307a10034002c0c45940e0f14410710110340690010100300c00c206040d1450385d0705903000140008001d607955010140c0c1c4428490000680810203005010300243c0b01211102c101d40810766031000030045062003003003810001104002409940c06180d00c91000e110740c0c400c8070784030705404c00e9401c01080d04460200124080c0d041510a078415156656505485d52214809204078104001c0b0b500c01000100904127000c2c1105114150007540f10380e01940da580e815040080403080e0103040140840f0302c45040c041122200420320084800a09042c0f1180c1e603103000064070b41c060000780703411240004082002096050b8001c62044e9040e0000004e51503d40150508135007180c050346a08400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 520248884 1250 520247634 520247657
    0x90d031a10120c0201230c220306110d1404051005070c06021303030e0a3503070f03260609060d020a030c03020a09020a020a020d15230c0901 62
    0x3040142000301c00350505010074201455010641120b800394050342c0141d5640c100110031101d404001486040c0614019490707003030451700c04442d0b210340c5c100c0850601000380442000040140080010f58020b08100240d090a080b0350725aa4000101715850302d02d0070a400c4504158800c4e294010350b000802024454051110f62004150281820701805030444100000451900050a140c1602e0003880c3c0401c1c1786190180a6856001c50203118080041d42400800b40c03a44000c01e1452280c24202607540005140d44034403010f003408075100c0c4c007000900d0000c0c04201e4411120301d034400c0c0e07210000d180e07281600c04c02c6582d02c2403881401c000c000011415a242c551100c43e000103006050003921940382d40002d54038040d80d48103c52400c001070040080d4a0526842801403180b440f066281c6688090000d486a0340c24000170320a5401483c01402d101110700c007100d80c0f03a54200100480f84c800e0130b0a0141503040b5a04040108030980011440b01c03c41c0c003614070908060711034100000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 520250134 1250 520248884 520248889
    0xc0b0f061c060207061404080f0706091703041103061014031005090d0206070e010e0913021003380111011e0c0e030105040206031b0d060806090d031a 66
    0x69000d4506503000d00c000d40030800204464603602007861040c00010783e00c40d6a4907114045e82d101414080c40d88002408010100d100c410803039100407445080c043d034554580c942903009200c0210060b000b2600d07d003200e500c0d07800755401136004a0181da038a01012082c2c03403c16a4400c0e04460141c1da240e1000d20400c03001c00b854400e41400c1d00c00a0036a00b4041c5040c101404840c3c08840d0034081c3d80c00700d02441051601406440d801221524000018034801000a40b03190814600399003c2c40c415400a5101034071101c00c0050103500030640c840c0c200344d4040040150100d81c90316120b0030845885a4400d000c4060880c5464038214601107810384024015130f01403481283c1d000680d502d9483e800c130004100d401c11008021520400103141c402036074001e11642c01101300354040c1e03150005000c09a034814080d241c0c06078980d00e03104202907200c050340001c5e0003041e00d0448080c0c1801030208003c200491001d2007a001c55007280c84100f88054120203662407000b402e03940c1c00074030b5a80580d90 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 520251384 1250 520250134 520250161
    0xc0904020711040e0303180303060916020309030a0309180605181f0801061403010e10021b0601030507031e0c09050402010504050d0f05060c04050a1701060b0d0e010c0c0b 75
    0x6000700c403401c0c00203003060b001c00c0c151000303080d01c103885400000c100000d07a84811100a9a455010003e500f545041e60108044c2040503100300c903000300c404407070071381940b0800449803205400303400d44086101318507020301a011280a04442c1d415040c00002d0204554802c1c2000c5030001400d8681000c01d0b111031481082d00900b0307500144d500503103014950b02c1601800402440c3c04000061701d2032820030058964028001c00070701c42c6c2d0400000d501030800c00a80f1410a01c0d00300001a615200345000d0042ca880c00d884046460055000000034807130b0108444045030b000340364140c801c1c0e40c0c03089500180360b04004010440081c8105c20b1080040071750080394000d10604000389010349070000902141c0c0d00b02c10880c0d105d030500d0420020048188080c035000300201c00c4041c2050306100c00145048514000d01c0603071040c254103034200c107100750041001001c2021103107654440c40200d000203412203030310030103640d070030500204d005501c40c03406800c100342c01500110242d294114480a403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 520252634 1250 520251384 520251397
    0x20a0804050d1e0506161e081008011401170706140d090b01150e0f011413030611070302070e100e1b03131e03050307050d060e0415050901050c090402 66
    0x5005001512076801c200e21203283e5540c5001c0c0d40145558900440005220380d807522074002040359038803040e03401c90f40d162011074540c83d0741e0a0501c1d1960b5580c0d4080341d00c2149a102100340e40c2844609000c405000d00118143c0d40034582480b03100401c4041d283e621111071003602c001658000140741c00d0501c400180043c0d00d4009004201d0300c400c3c1d03c1c1d4840c0a002a0001910038610305401e80440d600010284010701080d18080b0650b5000000078100d60340f1240c09181c10030707000510f2078400100300082c10156030300c250b040145110720307000e40d49290050b940c00c6015104403803001c02e03a10903501d6064818424201d01402860508804039011031015003848542ca41e640c140580c0c40001b00c0146224800c0010355840030a050700b401445024000101ca90482d4540703c0100131a03070040c110b0303500c003040303040070390780c0350006a00c0c4402482c5903030004d030708200c849003440f00300145181e659800d20742440c1c00b03101c9602c030796503014200d66040e5a101841c050400c0711401e1810580c000e041c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 520253884 1250 520252634 520252643
    0x80703031e02010b030a0c140d0c05010c0809040203010807050a09140112020402070507081015120204020a110601080c01030507020c090a1e060e0f0106110a030305280905060106020a0804050d 84
    0x940b00a01c2c00402e01c6d040d00c040f001c13100038004041c14000190098072042c950341c17080383c3c1d43c903140c1d00c5074841d41c80842c0310717003d5030b4100119800041d050120700c004075400c0c440302a00c115034070b40e500c050441e100d45043c01a640700b00b9034400005100354050113100e0343c800091003942e5059190034100c904042d0188000c0381c10039000d108400c0480e8060101c800203205107000b800454050039150003c580c0b00c2c0c2401c0707443c0801d0040a12071902e10801e10b0451544c16500103a440841c0d1700141c1e0015520b240c0c0c030074248114000401c0101010401580741c200070f803401d100d03c0e1203c9205030380740c0b05558541508418040001200f51a50b50445140c00c2c0d031021015102505122205040c2c5105030420488001100c2c01e00000c0c3e0220754000d40181082d15028100380e14122980d41c55850004024040644810100c1d440c04818030240240b50514801e0340100c1c8036100502024218484042c0e609000d1b100c00040c105001017242c60906501c400541e1516040c0801c00c460032151107400e68 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 520255134 1250 520253884 520253891
    0x507170a15200d0506040e070e0a18050d030606030b04052e15021b030309090403030209060d06030f020a060e060a03090501110423030102090109231005090901080703031e0201 77
    0x342844051008007044807494401203503510300202400b0a803a81034003047c805a020701010080c00f0900200ca075004071a01001041d05c144083c007425503891980710142203801030b00c90417900c00303425034040320494019031014045030355400204012298200c5011080001e000351400c05a003d22110300c00c0c903890b09000394101c0e034590010b095850b07010707503491000da0301042e05060407000003021015a184101d00070740c0350407541d078042200085c0280c40141890b8002c00c1e01d00c1c403603803081d040d0303803c0070103103a1b04200341966410044801010030200303074080d140300c85005c900c80f40300322a0a0300c42e01c0080d01c4070345040e0501708101c0043c4444402900c0030b5591301403c40e0030707000140c0100300500e00201f24521460044142c0035940c0b11400342144668070420503084941d801c1041c0c8400c03105580100004009010001c19405400b001d049a000c140c0b03403e507a0b0345071f81210160025802c1983c07001d26a13a01d03240241e94801e0503010240c0841c03480002d042c41000410303c01d1164910034070010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 520256384 1250 520255134 520255181
    0x2e0c0c0501121b1106091b060c070810050a140405121b060403020c010f05040f03140c042d05090a0b1017070311010c0201120e0304120507170a15 64
    0x160100d10a0684103c0003c0300e00b0943c5a0b03140c010001c10f504580b010000d02101c15401250403110603440711128001c4a0215080d000420180300c603200602c0000b0540d03611140c0341c0040070003048101c510003030051030082c55102e0300c442c030030b412441983d01c400148100c8074080f4a1302d030315400c01d10b001d0a14000e00094080004000d001c01130149101f5001400c4104204002400e4812400300361000c10005000402401044400c00d82c21240c0108210f41010241c021141c10306211421550300b190401c000b510800c5140c02080440d03444100d030b1031004180690250066800965400e030082d4040c4c0f9045000c1111004c0494100c00741c0c1201c2d2401d299545943c44206124443e265899080b500041060200310041e8492804003442d0415078803c0550010300500d13419a8140c41031039842d80a00342e04501041201c01600d00c0320180c2444882c4ad15200d070351a02c050041d840044c010703400c0756a0088001030048581a407280801c49a00e07901d00c9514010204808101100c08800e400b5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 520257634 1250 520256384 520256411
    0x909110c0a060b3d2007091d070302060c03071a0907050406030b160320040f05040603210504090c0503070e03030309070605030a06052e0c0c050112 65
    0x40d20300480c45101c021501003040703010000000c1400030254540c03000c410311130311100803105541c80401040b504811143c0d48403801210041d0110701d10300692140041222039800b0300242caa0201c4100003030502c0f6680304002e0054050740e0740021190700da403201070203000520300280588400007005003241c1c180b460070340380d8021345611014080e0005a01e00b040c000001e100307010319400380c001528244081031940d6280182c81d400101210401c0709107011019041d40300c0d411a50031003040c00a00c000c94428492540b0055000307105100030b250400380000b901c0c0c02c19014000031039030400381110407070184030003032203541404080c1e250130070400300310100349a4014490070210075500e07510705482c0d00d002c0a024040140440e0140d01c0f99106004020702e0150018a08083d00c8551424544907244e0150800141c1040c1d080180e00001b41d28150f01c4028040b003a81d00042c05100c20b00c400655003140940b0052610580508103d5046005201a50240100704152108000c0c00189400d00b69034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 520258884 1250 520257634 520257643
    0xa0815030a030807081303120e21040e16020705060d0615091e080303060d050114090a0b1513020307020c0d05010e0f01050c07030e010903050d09061209030909110c 72
    0x40403808103040005022550740c0c02245c0c10f500c110001c0e0180d64a0f5402d850103881c22030508050241c2549544da020700b900c0c0c0a00c40306840d40c3c41d112000c19100071003828084141c000340600019070840384002001c40e00c082601c001c2c1880e05401600450782001c0c1801015402044a060b202e62100d000203620030031050035003c2c401c210350380c0c9984c11382000b000480c8980d40503645801c034201d80000740007070300022049030303084842100d091030811034a00e4127a0141c00d001200d80e20071400d0008210300c070000800d01407811441450b01b46c0c0d40703650307060041001d03549010040350440350ba110300c1c03180040a40d00560300800349004070741c1031035615400606a402028412a0281d4403142c0851078102c00f00036401429541c1802880280340100c0342d03081c40c0c087c0840203010002c8101c0050040e900504240d0051504071065402280b4000c801800d09074280c810280001d51581c080c44030000e60348240640b00390326540b0030841900e0401c2c020003411003c0e0b0303403c690303010800c80f2048000c010030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 520260134 1250 520258884 520258903
    0x5040b011d2a1b06040c0b090102120c011e020901020706020d0806010315150e10050702060702130608151614030f09010f1e05010504090b0a020f0d180c05060a050a081503 75
    0x100400840c0307006e00d4858051105584108101002807081000c1c0da03801050100c000e110001c015912004021001c5025248c2e0429032a800305180741086031403c0150001c00b000c00b4280c00321849155100c5040342d5903100001c61a000440000114070a588603400c0346030300d154408030008100752501c6008850041100400000c01c00c00d45c020501030070040d1a40000d00191f0821130f08140654021501511a02400900c00c0c0d000207030310722460002c1c0c1d0101d406400070b0783c2201d0111005200d0040d1601c01591855107500c070041c52981c00d28403c4e8490095030640d400c4250a54036103007401d000040340030781a1a281e540725a4032884143c66441261400c800308503a420000c2e05100400040380c1068100a00443c1844603290100340300964980d041100618016a2060451420741071030040c150740e034825600b004242c0501d9448aa4040c164a000e151800c4046903590300f00a0644a40c0c0301d2500031503001c1c0722217085d05010321803041d03020140d070076545160303680c2c940028100070581 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 520261384 1250 520260134 520260187
    0x609020105070b07120609050601050a050c010e190b0c0405061206040615050703092907060b0a0e0405012a0c0314070302070e010b04060207030b061305040b011d2a 72
    0xb0440c202d17000607010300b400414204400b008182807440008002d48200002c1506200000030410b01d00c28095110289480114098421030380d0306012444182e15120030590b0306460480102d150001080c080781c04944000740307064940390445410b020a048000c201540c025900d0200103186107001c0100104020035035283c4d50785182d280b602404200d40b82d006a401480070141e84044440d02c2c8220ba00744c841c08904540c2c8484d200e1a010014080900074560403c2d00958001807418180312001c1c01944036000900843d07885400d403014440320a09070b9040300710204980c41c54103014014140c5a0f5000b4505980d80c21001421300940c0d5100341012070040c0d0150000700002480d18504030301500020b6081481c0525210009644102500003d00346401c2d0300c0100310941c2e6202c9106095031401e4a040c4003520305410020070030b407001d02c24509142c00501c014502c2d030184200c518820081d070402c07003014800d41201c401034070b4520705130494140000c1008548145981d0707030301c0c50900045c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 520262634 1250 520261384 520261397
    0x61506050901030c030e060705031b0a020a14030a1706010504080610090b10120b010507060e0a0606060527010c140f210a030504051002220812070609020105070b07 72
    0x389030004040321482070408007018030302590301403071140c01f1400030740055103841c3c907e80302d858a0340c803a13000f400c0d1500204005107000075190b00031038012401842050080621a8034100322a0015490b44284074104000032048c0c0d05420802c2d00360a07000f500014103140c03d034201a04c4a075441c2c5803c409503040840c01d8003409040000b10b0f014010040c04c55400e032100c2c03055100254014189002d4840745500003a01c56101000c940d02c208152800560013400c1030080721702e24140340d511002805002c2e0f415508104020a09500400444001900400c0c509109113020300d0711110081203e106c2a0410650010280204840b440141500c41f51b000c05400300540c1045114a400c040610621341d0740c01c804101400c498440c000e4941208807801d010610795140e00e0700c107040c648950342d407000c0c0920204486480081041c0310407028444113140f107200c0d94aa0502c25135030341441310170b4920741c80d00700a0000001e015400070580944103041c1b450401030355581c0e1583c6c4aa04a442e80001041c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 520263884 1250 520262634 520262647
    0x903090816140411070602030603010b0d06050702070f05030705060903012a111605040b1201021804150524040e0703020a0f08090715140415110309030703060906150605 74
    0x60081c2c400c1112008650130000c88130003220010b043c0c010440050038465011000400c2920213401170403035070741c004003241c20009071858804c4c014101030301e4a000500c585400403032190f042d503940c0e9060720340040041c07038011320305030030400315a0044801a40554a45585250b00300008031040451801010200641001c40100a100741c88131498410168031245c2e0301c0c414a407401c50000c0a8800c1900c0200300700b400c00300400c40005a0326210000c1750b2000840f210940089042035121007011903091220128a2a80d989031640a01070185c3c4000032401c40230b03d001c1009500d4001c0c0d510b920b4aa4100355584c0852241042c0c01c441d42c07008a500000c0c0040207a0740001c2102144446050007076140c00c00040107591000e840c0564460070b02c3c4450100e803101e019182d03100e03032044006c4005a490341c5600070440c582d00400c090002003000d6061520f200d00380031003030b24210032026000300079680c0303180c80b90720117400f0130541a5102c56450780e41240044504802c0e00140c8101c0d100c007a6201c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 520265134 1250 520263884 520263899
    0x80f0712080c090607080c1c02010510082b0909090317060607050d0509060919141e01050a030b12011a0a0609030b04020f030708070602060c0309030d0903090816 71
    0x60002c0142241050402c805a8103a07145070643c0d40c141c2d00007106540340c0249004261801c540c0302e0b10000181050407040c00b000e81c1c150401486003a000b1989403095640c0c961702640d503800b11640e6400800c146407203502c1600040c1c000086c0080d0f520b00452140e41e90240c0504490f000042600080c40907002440e00f00002400c25400410944281d80303001354070b0b11070030b4941481c1041039081103800a40c3c80e17800d98890b404d5038549140144460b5001e80041c03900c0214407410300c038070b2111031410340080400d8a816400840040e03850300d0401071110a030f200444140d4041c0c4c0885003819602c0459202c1d0361a001350b40d0100c40f0450000050768011100e80c06641d15a08800900c6118410b40a101c00780d8002c000208403540302c802c4001688440c800543ea008025264039013501c946038001885017070015048007121300795003c0d1565612140c407607801c203101c21581d0344040c0c1e008000e4810304802c250710000307943d0300034900f1258a9444804050500324117038107000751054211014801c14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 520266384 1250 520265134 520265147
    0xf06050c19030e04050a0b060408030405120d050d05040f0c06120506060405010c030819090b0f071b110409080c0a0302011d0601050918030d0c1704110d080f0712 71
    0x741c080700500a419012980d0040c20088002030081c0a40d482d40007192072440541c0003c0c64481000301100d8640343c03079010301562038100d44036a0384190f0540600e907036205404198150282c201d90789451800350048680000752001400848190030742c00901c201003040310140b800905407d0ba0307113100014214a0310410b5401c0038007880e1049104002c10085030ba0800381d01c81c11903600d810940c03019034440b5042c08004144545107000182440040010050b94481c214843c0c0390000c0c0000c0d02da12901d00403103801d680707070040c441031004030b007040800f050000f200d00c140b0301c50040000c52182c6c42c81d50b482d4000d80042400081d19486a0134200406030280a8070801c4207025000510412194000390385d01e10043c400c41d40603d00d2100420106458013440da02e4000103901180d40e2101140304032801402d4080d655070000e04151542c1307407200a0038265500407500320742e070711070450700c0d00081045030f613401c40d8212070f50b54042019610070359500c00500000c0e405146403104000c140302000e01340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 520267634 1250 520266384 520266403
    0x170721020f100f0f181d1b0403140a060e0d02070b070b06060903030c03070b010527011e0509011206050c030727083a020c190f06050c 59
    0x15075002d0396210031096000032004500010341c58840c410980904090350320009440c40038030750042c081350228800c064501d04101c07100f4000c040041c20b9442003c1c840401002d07252a03c9065005c0108202051080360b800514200800981e006180316544149c100d54017000a00707610b8001c7c56448001c56010310881000301401c1100d14a072008135a40c042c544507008208902c541001310300c0003160745040040e100300101050850b6030f80c0d40e4a08110060410901c94180300d0342c50700541c0680b00d0355030340101030b40407030701850444240d0a0200c8040440d0742c032480c039804603424560002d03881d075500c01075500070580c501c1804080240e50800d1000e03520002e048002c2c60a04005001c1c45660001450b41e03400303010017940303030301c8109811860500b80e41580404068480e829840000ca210740341c2c0480d01e010008440c40b00800b80703510a00c0740d88000f010314005030300030b5200b800c3d0600300b0585a20010700c034001e000d0106900c54109000d41400b5402c400000fa00c0819526a544820892040b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 520268884 1250 520267634 520267639
    0xe0607030e0a080304060c090b0307030b030d0302040b1608160606030209070305100e060604181b03060609030204020702041404050a11031b010f0311191701060504170721020f 77
    0x104982d80d92181034480c400604010f0006581d2901507141c5881445010058001082c010381d690505101c001c0107080c40a111034403034081c540d11036410500030b208072404c403808a10002d080000c0300034046c200c940c20f010190b40b900002c200405440d4205040c0850640c420000007031000c0c1540140981424010406802d1501c0d00040c4080550b099040e042251000308611051350340e4500450180d00a5500002403406503032803a401c02c031b0140c0c1248441846808400c011500d5010040f0b09070342e00d501c1000d0129920000a00c0503003059001402c42500207080400c0c070059001e4401030040c4212401d8542c1c0d000607600c00f00300980c07501c8000e01c1c10011001000854152401a049060b0880c80907062204520440d00514020342100c00e0441f800300ba400c1e02c4a064000c4000c00401424029000030003031540d449900c49500100e50507520745650b0182807e081850502d101c11820201c0a541d1040c100002200001c2c0003282454180300780d04002c10304a5841400146100c0000252 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 520270134 1250 520268884 520268893
    0x50a06030b060913060507080f310f080a030c110102030c04050d1109070504060f080c180d0605130b010510020a1203062c070503090703031404090e0607030e 69
    0x408229410a802d4004000701c4600209490321154040e40340c20b0103800404c10303403d0004200e80301c0e8100c012103200d1460400c00c00041c0c3d0715a2601c1d00303a02c2c08d402801c03607122181c800340e00484540d4000880b5540c07242c0780c44c4804c000da42c1c03961303981070300300842050000340c440d540d0590540d440074280d00d90448007002903085007000c000d039846074010750080700d0040c00d41c605260b0a00c80c410084003c50bd00c0030300000b5590a020400908991003400740f1804a101f15141e4542030784200d042520071021200da842c100003100c80c806079409151640640c3c003450041c1d02c0c1c070104280e4414207021b550f8001d14070b00342a01e03902c0c1500d50014160b124510a42181b03c070a01d00d650042040940c00e64400c2000c206030b01074440541c0200b8041d04024500303024070101169a814001c071708040355803541d09505a940d40e100e012102d5100840d82c016150b0020001040024000c1918115002a4034601400c00e6164030740d2030125010868840d819a10201c248004c841d01440307003880d0034401d02c0261 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 520271384 1250 520270134 520270139
    0x1060b180f04060914010e06010c03090509040f0507090b1005030105030604030804051606050c010e0a0309031202010f0c0509120c0f09180303090321190c0c050718050a06 75
    0x80310340d054000103005420000546a85585035480710f0b001e046590010003928a9008101000348001d00a40c18400290700c0481c05030b40c003035a100c2482030790550b1a103240034280824403d9010001e4000c5444070541480240056010321040e4040d16081d040040c00e50b541208203c0200180f00ca80c800348101000140807a85012034200d03845501130511114030389887c54072518190482d90b01b444890303010324020840d694840c0081000b5503d18009100400c03c49044a4541b401c09200174041500300d1820000035100c2e01e065510003410b07000003e01d00c1c40c59072062041d512003e40c13840000308005240059841c1c4410410a0220030400401c49034954401041c81044004141c9204440b590001404060107092070450b0401c0c1c18284e0307843e8100340e40d240d035580d0401c1500c081001e068502407504001c2c810090b03485401118a20f1200e054030708040300040002c2008041040408035000c0c0c041001084030500502e00710b213803c000300145026030030031500042c089201c400e045c441c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 520272634 1250 520271384 520271407
    0x160603050420030705030d032f0a0f090e070e030f010b060a031a0a032607020d060c020f16080f010b0d0201050a1704080405040c170a1121070201060b 66
    0x6001c2d200c039420b0a642003100d50200000e150460030b41c0410780c540f0640103680c080c0caa041e080711180d9034a00b048603131000074003603c680381e0031082c0400e20790228091104818451140c5d240d50a12046402c0501c031103a03ca40050160040403107050001c91078640700e0300b000e420f0800c016606503105074001c00500d1805c000168203441480541c104140d220000e81d811039190380100c00260724010500c00b1625901d14101d030401d44c0c03005202e05004c0c0c80d4541d41c2010401341c4201c4800541c000c04a102d41a05650342130000c0100c95112000c51140e0a180c0c2c00f04030040000400d80e031405815110b01c945458a05031518100e89000d1a01d0303410000030b410152100008131610356030908250740c980140700e2044400844500140c441024404140000d00c5045402003068640a603802e02281d50080000e54003000f820500600400740e5900140f03407c00305500142c00d85007555000c40c5000c4480f15004454007080303506c059006030500511004c66024801c16004200c4000c4142c2040054202c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 520273884 1250 520272634 520272653
    0xa090906470312030906070224070c11090a1a01030b0108041515030c0501090501090b09120c032401050904080708090102070f090f0f0b0f01050708070210021606030504 74
    0x10410400c5115065102442e40c0c1805035408040d40703503000d6501e81c41c00202095035288280c8074980940113520540148881700d050200001001e411201d16549030b07a203049072501c4025500340d440002c803540e400500c0e0f1b14550914007800c5a0000440c01a1118100c0744c040c07544030021b6410b041c5080e200c1401fa03608400c040340e00c90b402c082750710351280840300c00801804c1100700c08804d021035402d0120400c102450803806480d030a0b6525030006445400548884220780206240c451080c000000a0300c0d150052042d0780302c403d0103403000c3d14481000300303203000748c0d20880365200c0017040418240080f403400481c1c0100001c81e00e40342c003400e181c0c81d10b0f0640d1080c034030050005640020a1902640200b244800401c070b025103280c03001e0b81d22609100242800b50030f5410160034488802d0862101d030107800072204000300510100f038400f1f0015a00e580c0080341c1218001c1060180b0400b503030f01d01401e2504044550042c0c0000102c80005155444041e009141858602020301c004034403800c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 520275134 1250 520273884 520273991
    0x2031b2a09010b0408370b010806010807060c1e0501020f0d050604140601201006330e0d060f09050607050a0503060f131505030f15060f0a090906 64
    0xc201031030324908001c03a1414007640102c94109200490006c50400030700110542c102c8604a041da401640c80b244201c3c2c0386c64081c132408001811010303a88001c100e4181620f0350303a2250707800b40c12a140081e9181826600301a00e000b210070800f01d00540030f041540212684158211000c108004440085a4501d84094550780c100060550841540c1c0c40d03803059503501c00c2c808400c441d5000a604c1140010300b405024140800d404400000240950006030160700c850b00e2468000d140000300040311118424045d40794460075001e4030b480481e015110300d141d190301d00000030a40340a2030408514000d00640145c0811004111440545a02c5000d80c1e421450072140144a01c9a00340098000e045600300d150343c1c186030100001506500c00301000c110354054080d1607842a074107100a031100604000a0107104a138000501a860030001349208168000d0801e00041c0d2174000c244115803141d0401c0300c1072076445404030032000c40b00c0d074031070180000304990200007001ca4408410b0781840c803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 520276384 1250 520275134 520275163
    0x601200c1005161b080f0109061b0906030f18050714030a17090d06150f05030d09090b01020109140703032010050912070f0c1502031b2a09010b0408 65
    0x4c00100550054203071424003d003500302c22181b0151044c0d08640c001c0410001c1120b00030724090241e0420020318401c0342c800c220310340324103818070701e040800d8002d0616094000d14140d03450350700a034046070b06c264180b0a80e004800070300780d050801c4010850600954142031103076003c041d00e04000303803c0b201c08200f070b0003200c0c0c400c070740352128000400c00300c5814040060a090412042140c0304000154500882c0d80740600d030301c00e465440c42819110300341c8a00880000d5403250050050060341e070064581107106100014090400f929201880b21410361560195000000c0400c18154001c090140514280d05540a6a551280e2041da1503448840010107141c5420008001c11300903c50030711101c40b240d00c00d40c5c0c0c480d120715141000d906100001c4681c01060840401c2c00700d070301000c034243ea600e10380080d480e04400c5900d020340e01c0094820106648607910760103c44424000e00c040314200e9444074254150418020007014090503044160304002c2404100f001d0440000c02c0c0f80710001a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 520277634 1250 520276384 520276403
    0x60a1202040b060d0915050c0a0c11120d0f030b1827011409030f03040b190f06090f0c02060a0c0e09071e110a0201080601200c100516 59
    0x29101080240007007241181c0d10480c08103491450340b000350018403200d0b1140112000d8400c00c20030500c225142660044105542400031120107402801c40d01461030050106202643c4460005289009a0302100e441a000044010750582d001307204074a21483c81c0c1428091280c8210219000e800703d00e05496010784010081241c0b02900505103100d003e00302c103110452500c3d0601503019081134480c140d112650400000c8010101000380c48130340c0d104520340740c40c40d1516116900c13201c07009088051054a81014142d207030700e1a00c030b100030300d50f8444008240e49182200803011620f400000d0308081d81000312008005034003040065002030b82c14000030392098a0030048440303d0703e90813100d401024400500c070405800c200e002c00c00d11480c0640c005810400700c811240345046002c1c0d800c042c0e000140b07580066000e0721400c0d80c03204041c54155918401c861551070914078000c800b5000d504034203401315042c18066251141401c59040040c5041c44951841d5484540c902c1c014020404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 520278884 1250 520277634 520277669
    0x2072d03050304081905091c0209041115070b01030309121a1003020d0c15051602040b010e0315012c1801090b0405060709120b040204330f0e060a 64
    0x1c80d80580740300e410040b6614882a81740c55010744550702116403648100c411240c03e585944881c080a001c855028008554035100c3d45d90300c1d401c1c000f500c103100c1e0744890303040020a000c048510245c45d2890041c10b0101c0a54950f0602500c20289038112420003150f140082d4040381600084004072011011007034580c1d035600a00642c100404c3d08001e511202211009007400b0043c2211000c1d60184410b005041d190715006070792610490403010180c030300c01c840480151403d9405018a0304060601a0b44101c100c00080d00b01002c18941c0c8500000010040c005241c00ca55100c4903640081242a0006002d00c80b02100090007800ca50001c1074800c40008080401c1d04001401c40d07000035040060304241c98038549900c0f04884010008170180701c00140e841e400415688803c3c0c104511007001e845a0702840044c001c0480041400380001300c030700c10501144128902070160030300120719007038104081d2402201040d4040041a140103041c07001541d104009041220b42a180303c4401c0d45 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 520280134 1250 520278884 520278893
    0x160906021917070602031f030f080a0201020d02030115021c09030f21020303070e151c0608031603080a060608010b07030201060807060306080c030f1020070602072d03050304 76
    0x142e030b040d20303100d00031828000300080380e0040c1d4000c07180040ca00703607681940b41076901000100e100c05003c10030040304d40130101e00d03610300522241003a8400540340041c944c24007001c0e40d1082c5c0c002003000c408a140d42403115030500281141c038a4032030b2107450407640c400008000b40344a000240c41c41d900082100100004002c03108d407010a0f5620340b0104c91490f90010f9100e03001203804801092903107215032a070b0b180080712100d58401c00500b043c241650414141c00f51081d507910b11000b03070340c0c0300808514450104054405a81e000400da10310a61b10300d0014145140a018541060300b00b040c1840803541028820341519400f0198980314655410101e000d07041561052555000d0740f0710105445500d50854825203c0e018212a40b1070461424596181c04040c1e041c0c410380c202e145030b1216802581c01002c849491103e0728900112107581603001c0f94400b8004644250b070014a075010041c0e1088150000c03160702402001098849030300c03107a4110080c00040c10094004000340800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 520281384 1250 520280134 520280153
    0x9021e0102150403030c0807080103020d031d0a0324091502090102150f060108070f140d0b0604090b0901050a030c05060f07061a03100b0307090e07120b1609060219 72
    0x10302c602e62032200d80f0b003080d081c041e0040003000c10301030000c0c0e92440081e075483d0107201070074100e0b0f41c003511000340d40001d44c804944113814122131761245186d02c10582c1d016691180071101560244000500c0381d040400d41582034240401c6001101d81040c038480040344c4048440c02001080080140e6592500d0780100e0130b1070205880b910400755001d05002c00442c0306010b440c402c0c0c50a0300c5501040d11400c109940e800d0000070440002203040350f071036404c521180043c101184444202041e0800404009001608250044091581e0f40c0003810f4180c904080d0481c010002030700c41303602703040c00c42d00c807003112007868014030340541c0000850700842511003084411080c0c02120800800d44c405c0a2484048000304000384a40b203107030b6050f40d49100740c0c0b08017407041400800a0440c94030780a5120050030054403203407900e01522800040a04042c40503411603417044900b140d03185891090030302d1440480300d012080141011040c08000c2c2c000a296004946502d107900c6112100d07d000d1100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 520282634 1250 520281384 520281403
    0xc02030f070813090e07050d05190804080718061202010c030c150e030a020615180903191206060f0c020118051e0f030105090304171204031208070309021e0102 70
    0x266444501d0008204c0c0720780d03214044580815054900080d40c40041129044003440301070076603000b50700303180007661320b4500500d110303441000e403141040e60320290a030074401b50342e101151402821002c0e405000c494460800a8011003004181514030740e00000c0080819000c014240504d8101d41020b024041401c050300c0003400c0e105000340300050700e405450ba001151110054455070001c904901c1e00c681c80039039180000b901c08912040c0c480f911040e4008040c1c00c1d0200381c0070400c1001c8044c115011161018000e50f150b84da426015812800304071903041c1d221030104000f206040c140c00d5400381c9500805502460010791101070441d61100144496011640c08000840254011a20701e1000114814202c0b2017240150050b02891700b81c400c12038403158a6002007000b1300030f2000150700c0080001001d01240c076503032042e8800e2880c940c0b081d041600e80d0104587d107540210343c4002907640c0006149003c0c01003c005901043d540c2014000503482d85241543d010003e034401c1000030ba2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 520283884 1250 520282634 520282657
    0x50f1203270a08040510140a0c02040f051e07140417101401140306150d052e0e0c031b03120414040c02030c060c0717030a0e0c040c02030f0708 63
    0xda240307540742000103681305214990240c0f0004031119041030064031020030749070321801c01e2890000c4408049030069160b08080381d2041c0d561501d41c5e10302425101d07052103840900100d040400b4221501050039100420707140800420611814011440b201502d0403aa1040d0030351840724501c18085040c00203401c5001052454050342054069074003861604895841d0440700c4a185600d00745512020110b505081d40403090410885600342600e65060084c02602652898004c0010080e080d4001c1e011420307030340d50501c07044629140540f00700c0f408d07021224002d140007100100802e403a04410340c2001c050490411030002c0b207850a00000310300fa112101203039500c1e600c501420720100342c0b0700041ca02803480c108800308840d00010844502240510050506d50b4a0110101c00d50380010800c80d407107105903c40c00000000d00c0083d502542141c6008285038031803c1045160102d44141c0c0e0340315505000300608400c1d008405c5840180364a03144c0d035510343d000d05081c000351044120700030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 520285134 1250 520283884 520283893
    0x20709090c031a18072301050712080103030f0806032e020c010509010c0f0c0b0901090209040305030a0c093807230a0308060405130803090a050f120327 67
    0x22200480641c1a80309825113640c000a010000c191507603035607203a0146505140c450416200110742c4401032044080051405e03c1c9846441e5403100d006d0000e01e200b920200d500100140101900000502020741c00c40c54498002e24091000a503a0100c41c100300911071000c02901c20304143c034621040c0307811002c82080d0764a003c681e40941c002c10084500702c5082d441c10f000d40728030728810100b50301b0100596070398189012007074462022401010307003c03c203250760300e143d2503005031a14171480d40300b14002d48500342c8a19100e24018195031003000c1e0401003016030f4800340b0081003201500e003e1b0500e010501244034841c0078010b9049450784900714404140401c0ca81c0030001d000d401c60071090039600300c003904240f01b041641d90342c0000c1030740100807906400c0018920304184d803049034028080360800d84808e80036140d0440715032041e00d0290064100084203014040200103512010300e40c0c10003040b010001c03038207034112400f002e041002d0320f42c4000400d00484650b50502d1034514400d2040d078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 520286384 1250 520285134 520285163
    0x3041b060e01090b0a022a0904060605011e09120206090a0b0a020f060601080601030e01090b10051e100e030f03041214031c0509031308010501050906060a020709090c03 74
    0x68202080507030304500240c0755090119400c1100000c1c2d03400ea440c035800819075080c1091008100300c803258000d1540710600b1400901036510002018007c900910300004c0d11400c0c000010320405080c031103403e881034400391020080b64085504003c6a99064504a00c0c04283c8009503080c400e4000e21035001011540204840f83c002c0002c1ca0001125002c40b002009111716090b2200d6040740c0003408907403c000015400e501030382100300200b012000008030b05025507246000c0d0075041d0380784034440c160301a00f40100d0070454030070b00300c50500045103501d1405140001d0640c803080840c60b0200624401c400e20303541c908111141d15610440c0c166901d0359120000305c0c45e002e0100780700341d07480d801c0c00d100c4860803030021044070f020001c0e0600c074062030800401e0500c00380c40301030b084982d6807204201045117101da198101c80903002150021805524180400c100c902014100c1d0744903100c10041e4442d81c030f800050701d104480c040c0002059940b0701c2d0030550603c00c03203a4400303400d021084000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 520287634 1250 520286384 520286387
    0x5060f010e0d0b06010e0409060b01030b0a080c01081003140706090f050303071b030f080307080609130f0c0504060603091b05013507020c0102070b040f060e150f07062d0203041b06 79
    0x20340d22b2501c20b903410040d415030002001f0100380707030344101002504140344400301541302d800d80700e40c8a1440d44c0414505a542c3c2c0e01c011711b407034040615415540200c402070210b568014103000080c5a904031842c841824940000e85034400c1c800c0c01000081040c5101030036040100c10f08000b59003282c000c500b03003040d41c14804982c0e4801c444c504001442d08001a0310fa00e400b10074503000c0d1b402020043c8028041e640c4c3c41403110100c010a94162243c0c070303400036903a61035000c3c0d0809018160303004501c90708a440c181529040301041210030300b2042409101c140d80c00030001a0324215040151081c0380d51040e41400b20701e2800c0c00d0044262035200b004401500064250100074081c0c0c200d4803190782e01c03a00740000340260f0107100c4501c60700306000c01405128180c1c1e401c58a4000303201d0321300c000d100c1404034503650010700e802d0782c04880401c0c100e0030301c48544a451091040610310158481c0f126142c0d0001140010070000304a41c0800800c050210400ca07440c4615100c07003092004984a010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 520288884 1250 520287634 520287641
    0x8040f0203061006080609010608040f050a0605090717070602060403200123070804021320030a09051203100303030504030e12030c0d051206011b0602030a05060f010e0d0b06010e040906 81
    0x28407001c07404585c003043d641e0500c850b4a5040304d0056543d0203080d225035449403000c0800410a450b2486400658408075100c0d01c0750798041e000c10304c014012146003c2e20390181500780c00d6041d00c19007040d181001059004100d00d0f500a9051401d840100441522180354681c0d003a11841c0c0c540c641805d48140310345182004a805071249910202030b07440c0741c8100c508501c00c5130022340104194144001d020465003101c14081e5010600512800113016810300c581c008030344014035103480d100050f007841001d001d009000110000b00a185203080c03000320b4000745007840000d00700b664130070005003810702c01d0600da06000001800340107507070061080c89580c7d40107030291041d28054420f0210002e0f00910459404003088010800c0340e9623000700544003c5008116100406041810070000420a01c01184103403040c44001419051603001d102c0030084210707140b07043c80300d05070720901c076903070390468015015601081d180c04541e6403900403a542d24000d01103d400a0401c00e00360204a510782 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 520290134 1250 520288884 520288889
    0xa0605010e030c1503091f0504021c08030103080333010833120a0609060c09030b190e010c081f290f0a0215060910050108040f02030610 60
    0x9880d501d06282034820141c4540304400c07041c1c0d110810540c2c800070b01101c00c002d558094180000c3d03400d58011358101c0340c000a103112a100a0645d00c104010461924120034a0041d02c4240110030a401a940f900c600d48030600026003440302c044001200b00e15611045082c00b00c403228003120f214818540c1d4140740c0c6c000541e00c0c0c040b905241c0098124055481c00c0d030b505424005400700e90110705840403840d1100440307265005503030500c640929130801c100c80c030709040c400c2a0005400600e0306144c1c0842d08149180010050a9070003000450036100c0655000062106c4100c0400c8400c2011001890036642c003005a50810f004020101e4000040307a00c00c206210000148940d0244c0303c00c1c40c95503500501c154021110f41d80d90002440c03e03174410340e03001449140c0b46040d145103d94441500160010701c0140d015800d400d05200f03c0c00e810981003801aa1030b02200c0c00c0101a0010411a60040a040120081c0014140080062550540742c0c01505444040c24481172600b0601c2090 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 520291384 1250 520290134 520290137
    0x639030304061d0c0f1c0309090b0334030c0f0e16020316030207050a122306150109050603010906060206070c0b06010e01050702040f0b12010608061501050708030a060501 75
    0x20303881000c1d452000b4652221002504041c4c030343c4051500411203450300c0310700c5140d000b01d14600c8020380300303020704e5403101c019000740c0b904103011740790a0b00d09080d01c02e40e003c03540c084d030000d48200f040d8002001410402d070103090000b07056040b0a802000110806505c00b0b0700780041060005440c203c09280c1c9409c2c1e6a14010450407a6140015121101070740e0324440010b170700070015960307100302401101c1c4c841446071040e134001c20b40e14400036448800b2500300c04450b0b021041c9000400620b031003400390090110980c0c002d06002004015140c0c0d0004141028565011481c00c406030b10411500b0040c050040c0510307180d50715040250001c100500515000d40f0694000c199070a0040c2c00302140c06500801007482a6182ea004440c0c550300ba0100c01d040c07001c144071440050361079005807079200c0d40da842c00041844142c0204036440401582503034840c1d143c89024826002c020949617440105105404624001440101e4842c45940c0300609042004400d1061740d80d00c40c1c10100448409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 520292634 1250 520291384 520291391
    0x21c0b0a150305070e0408040f090f1415060c0102090405090c01031131090e060f10080a140307140115050604060e0103050a1b020c040f0506063903030406 68
    0x807500c0d03a100000c103000c06001507110f400d0401080010b241c1c0320707a2291141c0a142d05003503460400e811084180d800c44c2c1c0c0e01c0d64603021804030603082d0384101c0c0c080602e100800d1107682410300303102500c00d105603041402601d00044a83c8401004d4040791558500944208150b180880065031210610aa4603002904000b0013030100e65100040c2c0f50f001103007010255031505010003000b0b003944507240302191901e03540000600001140714201c4018142c03c068295486d1038400008001e41c01825581d905189140134814a0000070310b10b02c5480c1d10158044090b00b01490651850045080013000700d52007041c441c5010a040d040b440c450302c8a240144c0c0f00075101d00801a080c0a2400750200142d461040107280c4d45c821340085401c43d80400000a2030b4004010403d0017461a030244009030780240401a0107081038416401420309456080051341018400142c807403288000500c0583c00d1030300240780031125120444411100e403c2d560b40c80c001c83c0c00b04641c41e500200c8040d12003030f14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 520293884 1250 520292634 520292651
    0xd1107060e060d02070609080729070c080906091c0302060c070f061a042d020a0c26030403030905010b031c140c0304060206010f080d0f0c021c0b0a 65
    0x1125550781d00c0e0001010b031410880d2481c034000081d000000151540c64446012001040d0001c000b04001030090703005541302146c3e8404030050048214551810f01c6444041007440384d4010158150683c1c07100c800350740c0d0219000045c104d4001d11048a0744040c254218a00c0400702102e0105500d10079025175600da524496290807034064000080c09080e038072400040000d0455100405a2502554044010709804041411266001800781c0d50849960340304005c004224121407000f003a20905515082c0e03800c0008101d288c00703010040aa50358a040000c0d460303900d03104044942000e400054584c502070a009028091800e0161815441c0100c2821a41408125030ba0180f241020314560a60014003c03207070590b110036400b064490030300142103415414002813000340380300e50040c80654103204203c03c840c2c4250b80720900e04d5225018484240ea006280e03009518080d082402513100980049500e02d62004880540c1c0324080d07980b981000300419120f0b02030300014404124030003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 520295134 1250 520293884 520293887
    0x607062c060f0f0c030414100c090f050a1401050f0c01060302011202091005180901032010080a110418050106030513021e04200d1a01120b01020309030d110706 70
    0x1d0300c03840340998042c0300113a40005010000c54100703110303030030070240d43c07070110541800c0c10b01c42a8040740c7c4a450782c0003205403d80c001d0b1210040c049401c4109020382c98000040d9081c41c1c1c03485240c88a04113149407010f16801501582c2c1680e0410792802d54802e88042d00074001c0030310303000032400300700c00c2040303083c22596074400d440fa40f50003d01082901e240902c01500c6980090351100c07105540c3c1e0701e42c1940c41c0c0754100c2a03402584209204852441c1020280c2c0c0c0180f034905800e070180f400311034420074490344a5032951f001880040c0006114a1060034100503110301e030400001c0503a01c0c00a2010002c4030b50082d4100d5150303550402c4162540804070441052b200001f0b50700c545038200c5140e00203081c41100c0380100d401880010302441d210308191003030840150001d91000302082c5c001302c200b10750080c008054a12443d2030440c8150000280403049030344e040318002940e805242c407441c2d001300122201880300604958202030200802444070020b00307205120b6005541000906a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 520296384 1250 520295134 520295161
    0x22403090f1005060105390a14061e040507050916030c051305090a140103151a1503090f1006030c050405010e060105070c0e0420010807020c0607062c06 67
    0x1604144c2d82c40c1d1401001f0034603038840c00c1c0708084244080d0140f405010000040640d11401030700da180140a40031014145078000b840740c2c0c1c0200d24240c104030100649403140302604203500e14688044071180c0c4580c1051440c010340b0342c1005801c000ba40c0148400e070080300703e0074914040642d400f0b00194510000c02c44890240003164144845078007010f000313910304002c005038025100702000401c0c1d03045919600007042c00382c0c002c0d505402f1400008400e0007142c015403184101071a100c040124924011860030050005081c15242c1c0c00300104814001c00d001c0142c0b48a8068112102001c00c034031506c00508040c07008561460306450001454113050103498100d80360f802d910041613a803000103540d00c2e440070000702d0300400007410116a040d45101e4190055019419055003180541c0541100307210f034007100c80c1800500010803580590002e041c0b4029202034601d81d0321000d4a18144c80501b0000010607009040400c90386505078080d6002d048483c003020480d051a03c4014001c0c240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 520297634 1250 520296384 520296391
    0x70506061504090e0f010c0c0c0b0c03090409050102120106020c0a050108010806010902071a01030c0303080c16113114090307030e010923030c011b022403090f1005 72
    0x80302080c041082000f05642c408503641a521058550781d421401529084410100c480c0e80803400034a032442c1030201c038080c039001a294000c040c51030031007916182c075a640150040b0034403564a03031503207800300304d03007901591940700c2c940d20951380d41d5869410103901c50543c2d007000da01841180a0014203507101d0180181218095005400c0307503401c02d081140a03521952095915580610516131800d6444134468000d501401e00f8528031419494010800100506542c0280609101c5020100b050128443c2c0240e8098506070f0b0000e0301c00041480445290000010b501710914203002880360740f00d02c00116403064004200c0300030910340d1010001400d84140e0902d0b0703c10301104000a01444030139000070300504000c2d01403566001d40341d0950f442e910014080d00303421840e00c26141410002c42c0012182424030300301052200801d260702c1d00020a02070705c2207100307006d440440302203880800c2d070094100342d100c3c0d40c80c541010303a59502d4447c50341001c0d10b4071401040318404011881030030701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 520298884 1250 520297634 520297669
    0xa05040519020913030e030a0309050306011202030606190b070501020717031e0703060b0307051c060810050a0e010509030c06060a03320f0c0a1a07150b031207050606 73
    0x40513192000908241c030403100e0304505210401c03090310515030342005480d8510b44aa41d0364003019042c1014507081c000180c0c0a102c036035a403000418010703540402e5556100301c06480e0301c0b01c2010700c0741c10134070a11031507030020300514000075081c0c0500c20103400801c0494003039104120500ba03c504010780c40d01c022901c42403015001d006a840c2c48015111450300302c81c841c58003103019501c60040400580c010340d6100040340001444400541e510604400400385040080001030b180106850b280d00001d0341c10700340700f55942c0c0010305c02c1019a0044014007a098000c00c014509844100d6480c5d100380c1d614a45c600c01c000c0043ea01c0c1c644101c40c0d8094035400209070700e06940c1009401c0110345030042c4102200106083c805042c0410410541891580b01c010054402c42a007440302c03020340b9030400308042c0460800c0848581401d002c903021560b00040076420100701c0c440c4440100070320001c0355894054000e03a070010010580c054900a80070390305a0300c4540f075080030040303964100c10700d540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 520300134 1250 520298884 520298899
    0x5040b06070c03121416050f0a030e040b13020d0c110319210504030e100306050607020607080f1606060b0705060c0310031a10060f0219020114030a0504051902 70
    0x10744040142200d5118a00300301c0850505420780c1c41c4140c00100405112846c20180d980030302104102c03038203503400e019000e8005041580ca0081c00e009951030440c0c041c44e1900031030350264417810310404031654801e40171901c070807504020201610303402e6102400102106c602c00e014900100446e400c07030900b40804103845070720b11415908180c8000b9400750030500301050500744101c078042c180c46503100350b49131024a44220100501c0d00301e25821101014034000e418005501c46100b11140c10f81c0403118107840350382902e00150700f0700c14510001e4000202003484040e092071140500320311407050a00340000c41d1140c2c5420581d00640a0181c400ea1200f0b000c1860514030a0065800140c00000e448009490391584c1031500c4540290710388019080c400c218800c0010040500a052185804407284203501c80c000d64a00c00ba545100100c00280c0c8404116070041c04001000054510141c1d02c03403a09410020082401b2201a19a4081c4501951021704070420106d20f240c0d0061012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 520301384 1250 520300134 520300139
    0xf1501050109080c130e0102030a060e070504060c1b03080a0302030406060b0f0306040902030c060f0c070509061005031e04050c0102010e030a1d060909040f1b06170907091505040b06070c 82
    0x4249400c84084624410346d4032199203000c9202030004511a07000224085840b87c50b085030505120030003003161003001400e104c24002561320103000d070030380b5403c200c101d0900a0a00c02c141240f05155100802034100022000035450b050f4000d940324038015182000019995000d01c2c0c0944940783d900880c2e142d0410001d8643c0c681a0710466009001038102d6051485500200790a507100c0308003a00000b10103d140303c2448010002c10000d80025101140d8500f011004200181c55001c2e12600780074000c00018000c40e120100d00c0003182143c40c0005c0582024108680c6410800407902d00650a00300c0300c250801c00007044070010030b010b40d152000c05414544a60a0b600c103818404c0c2c0c8008100040ca82596441c0f0040d4015405a8140e14040c90a443c25864940740003125614890034000100515904849001c0110310102c12000843c0d4a46032541c4c105001d58203d1213880d858064030064080800c540a000e0b10f01c2502d040081801540402a139406400c100402c0700361000d006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 520302634 1250 520301384 520301389
    0x30c0b25030e0705030106091505040c090e070309020a0609050907170c09010e0901030813060201110d090218010b1801051312050a0609050610090504021011070302030f1501050109080c 81
    0x110709520b00b4a0039140d20035211000242900d03c1e0b90f0100c410203842d5200ca500c0001080801030040100310b030100215003001601a040214511031301d071180754800001410140030342c01c0398001ca60f0080404492540302e4101070150b65050060f180103114640001d00c009000301c0f0780d846174400c1812501200d035544142c010380750340030f81c01d100d04000e080d100d0505517032145840e6130f0280d84245120383d113540340054074900c0d2064590005046a0512414189005042040303400502c1000004901c4091500203c2c00c03035490a14014954040400001100181d42e80509000202844120829001c08004450324064072604000b1042034003020880c0c9040300f400340d4100c038452021341e0100d01440d12484100c5403010710554440c3c104508100c1d010101c0c4400002a0074884001c004600b07098002c5143c0d840018074241c140311141400ba40495010000b10006580c001c04407842d50410b03011700c076250303420b401041c0ca0350300507280045450341c01001710301c041e140603d000340000a411402c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 520303884 1250 520302634 520302641
    0x6110a0e06031b161202031e031302060c0c0112111603020120070b0f01030f0b0606091509040c08010e0a050a2a090902040b0406030e031303030c0b2503 67
    0x10310090343c882400780707900d0411a0018004056503003400c0c1402c10320504084200350506802041150010032268010261410015016490003200c4580b42d6540007801c1d00c4e0a401d10034040c3d40441c0c08201820001800110504001000c2e0303135131108185221989400d0b291700c0000a0410801070103120f8404500065412165000b40b00100d480c40040c14040b000081c2d1000112562800040c0e04040c00011100e040e048101e00042104541c596100e5400c5000700c08401007a039008440070600c0355840c041501c54100340140149108655801c480c55030354032802c140d030301940c00c1c02100303910385004192103812240e0642090016542e009802c03401030900920345e600681d40d4020b403c0b13130100c3c22000d02c0c00f0640403c011030308070100c03041d0240c8003100f1540101040d44c0100420f204410103d401e0b80d00300c0d4407904002ca01210881d0995042d401000c914075000000b09000006041c0d0084e045400304e40100042c0c41140c88140a0301c1595104001103295159101c4001040711702c80e03803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 520305134 1250 520303884 520303891
    0x306050f220b0a080303040606060503010b030402010c0302070e01090f050f0609040b2d090c0916120603300f0c0b090f0607030501090c0c020906060a14040b0706110a0e0603 76
    0x1400003824140d1100254800c0d140c1e4200383c40541c0007001f000204409441084040c0469003856401c56252256014082c400248020f041100d0042d00a00b018000c1050b030000e05041c0c000118a0760b100d9103050000c18003c010b141d9001e04003808104003542d043c0040b402180040d040d002540c0c0e45880701410800e010b4100c68072140e1182c0e404a20302481c0743d003d10540000b8400319841e007056101c082c80e1501e000c17511842855400140885070081c001c511840304214100380c1c078aa0700340445070780103140d02d43c006061800200c00440d006c0d00070210440c000102c0c0160600c0b100915036007255510454082c00020a1040a408020072040c107081f551004216003216038000680007803d0404106440030000310b40c0300c40041c0414800d600844500d4059490084002480c0b0740001e01a840060041c40c01058001a02b406461042202400e184d001c2c1d0b03180e6607550b60b0703030601c0304c1581d00c03040d01075401500d0a2000e010303200c491000c8481c150902e40e130b05084c404200e0200000f03544041c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 520306384 1250 520305134 520305199
    0x11b1a060a030804031a09060f0a20070804030c151b21030b01030501060f171506070803091b181f0609181401060c05010b040501080309010306050f 65
    0x140004001032203c001400654883e445145588106050301c264240004d444100540c12034410030140c400703c202c881e03501035401d104c04a407640300349101e48001c5c1982542d1001cac0c008001004420b00c58028018001c6a110b086902e08107695a11110220403412041800068200135055100c1d444020410001400750000d43d0b840006d01103282c460714603803008540440d03203030342103142150380500c9864010f00c12030030f118542103040c0100500a4040348500c80d0007854036000300341c0307010b0400350030740a0702c2015254a944043c0d605003060140c10403103442c00740e44200c400044410250903041c0700b40c42400b5000f806d500305014580e420b00007005000703444041ca1141c00485c0341c1115840c04004104a844843d0f170541410f070340c1400c100c040c0d908a0500e5013007a0241010903443c50010781141c40f5440c2c540615051072a125000d0844100095030060401002150138031003c4020035100e0b000740c80c1000f07110f50f42d01c01c0c8070342c0d051003818451340120814481300c20341d8494511001d02c3c0800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 520307634 1250 520306384 520306399
    0x801060c15090b090106050108150d1a01060c0b090712020904020d0813050a05030a03080708280c030b010201060f0909030e120a1b120f02130606030b011b1a06 70
    0x1e412541100d508441c01c0d0b03a41d8070f01d2818050309010038400c10000e1308081c0b03008000d502d85208161203800c460b859483c015002c0880700340902a2907001c022450600000861995039a00001011001030200c1590040b42c0440030400d018000141041181c41400722304240078000e40801044000040050340c002c410031106100168108000b80105016041e4a94480d41080180700740844203411a41c0079911001035500401e07080414958442120b04d42141e46981344011540e1020350b181050071280418180100800002d0704143c0c1c211702e03255400c100028030b4200481c2624000c1c13164213492820101c041c443c00c019500306901040c000d003085400b4000160105003001e00d08040400240c1241e60840200900c01c80d9004c1c042c0320200464040509000440c03810f860074542c01000d1012403141a800c42d22040d00300121200e800c941000099a01c1c3c2c40907000c1c01c0003d02050008000101c1a0480307051011100c0060350428015958244032985080c440d01015001c2d5910100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 520308884 1250 520307634 520307663
    0xc09090b0312210106020d09050a1802030606071505040611070c1707081009050606090103081219050a1b0c1e0503040b0309100501050612070807030e0d08010f0602030a0801060c 78
    0x20b0079403c20300801c1c89900400b461a08084020311409064101c80c1c810314009000b041240c074400701d42503c940e5901d400607030ba42c8030040091440c0c4a98507008040300c0c9414205145105141c0c0300f14400e60141c44280641c048244a0140c0380c4a402001440c1d40e1486d0018486000281c102582c100d564004442100361500f203124036040da90744104d451991190a55400c0041c01d000307003134100340d09440c46c0c803682d419607907104c84500540107042c2c0303548040c100042d10500800034141400c40024410462418103000120140265030f007115400300c4644203000980b07200d040b40003134164015a030764074801042c06c44041040410380050318030344001c0c0f10124032440b002c401903010b4203601000303200c0070940c440035400750348059104520410701488003500036203042070050b41c00740709403901c0c1501d81e840d0881900100305403411490a4031804501012064101c5c2523070341612401003807451019942c3d0001c0b82d80c4d2142c2c2064000051980c0010020320f40620b2150f0f103400d02c50076010103130302e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 520310134 1250 520308884 520308937
    0x203010b0613031e020102030d020d15080d2c1c050313080d03182402030109020a080a0612020909210d0c0806010819021308010c09090b0312 62
    0x4005000d0381d00301d102e205070104108940d0384288281d071006145840000040d94002075180d00580381114030302030700003030711074900740d010341c03000ea4504584111484002c2c0c0b030307025483d5a40d030907100d5240840e801002c0100b1030016010085081049030902038000800c1c0340c1442421006020089103d8410a4074440000c0c420f00103014940d8807803580f40035007480c000e070641c030340444c1606050615141030100b0109104011005480c1c03900311b6018506110741d84088502c118000d0001c03a0306510201c000308420405800910341000650780b460185e403510640c100444406101d15070701250030f02c68600060030000d03502580300c40228243c0d01480403040b00c4241c005811044401e21840c001002d0107001100e200e8036030b00c1c0825242c200c1c0390340342540001c0c1124401070031064490004c5400079a11017440d40445540903441d102050303460b5900c28120740640281e0030038401086403144085400c1d0000d20528020601c010001c014901e00c4142c502544c1d0b00504d0529003080c0b00107000e90b00c41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 520311384 1250 520310134 520310137
    0x30619180b0102060f241f0e0a0b0903060f150a170c04021309091707030905010f0807021b060d0603050105010311030d0815060903011a030d02010c020a06020901090f030c0302210d0c0203010b06 85
    0x109800d854204888c5a00c00030003400142640014a1140040c8101101c54500050341c80c5e0054048843d0300d003a4540500f80301641d07100701c070980d600030101c44000c9503180c0c02c003000d42c01c2d400b07040c4112203140502c80208400ea01074050a0b41190303001550420884a003074001300c40940c000c50210b401c03100c00c01100c0c41c079035008890540226500440400081d680176002020090700f515112016083c8024000d40f0795034041500304144480101d0040f050ba00d1a007250444a41c040041241c0e46e0303a460080d018280c241310a80703070364a01c0081d016450030b0220340c45040c0046641c4000441d1348054540c62040309001e5102e0300300c0404d000701040f6403005d20880d402200e1403000741c054803200500b01031500351400c403054216410b0017290066281c000410b114000c0d0300c018003580ba20300503801200c0303002d03455000003410111100004180304450051034203883c026039800883c5800120000c10803005001c61100b25403050100c2c41c01e040c441c54408402c0c0c2c1c0f0090021610005040000b07045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 520312634 1250 520311384 520311439
    0x607110d0501020705070518072003040e060316081f020f070b060f01050c07030f060f0212100803030408030103031b0204020c030a170c030619180b0102060f24 70
    0xb81c0d400110740050100801109008010884500712082e0b18106110701f803034000343c010340c02d10410301658031020f03052021501d034400d00c40e030890703480301c0c1c2d2120900c4000c4410750b800380c001e002d202c003222000d410344c5414034140e4040c00c00411013403e803103859902114000b405054019400e00c60607007800840c400400b0154011200c40e00d0a0800f102000022440c241c501c41c1801010040e1489580022a00d01c04494000b400e001c4001035905110010b85008030740505200c1c800100b035980b000700b130001a802644280c1d0005d0800c0c1e00d9044180c0d6074030003600d0240420340c081c80104006031050002c016030034100400c1034900900c03a8080307001d030303001048641ca1580001c18600c064541c407402c001c1065507030006500b2142801c0082c4821444088c040c076000d43c1d0203610481219568011150040200403604582460701c0000070f4001c14101074110f0060080d01d0201d03020621400400d03000d62000210b8003c80c8206881c80c088588290b20116002020500c800c00c0c0d10380e603891180d05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 520313884 1250 520312634 520312643
    0x2130306180b01170a0c09020c1605100e13060303020a1202030406051e19020330130f05150a0501140109061214011706010609080c0105090d0203061303030e01060b090607110d 77
    0x2c4820711840c4190a1118000740305800ae00469420081d079903030303140c0000f0001e01c1c9040508651050340702182e54811601300c0740003103604101c00001050b074002022181d460283c194100254074000b4102d803284594440c910005e07030b0903c52000204200c01001043c803845800c52407a203010380e40300540340314002ca1104007582000c6490a001800400034172240d140070789140f00100b407403001c060001d4501034914003000d0402e0303003040204080ea1043c50030441e085001c4a1416210359805150410704841800c00c0780c3c100000001d01041c14180b4105051050f180d42d80214100203007150b4812882100b0b401036902da0414140e169100b03030015019000142d0f84254403c1002c0080e0b1034998103a10060410820500401401801040e207000f003440c240703001c4c0d6598054030005201d500c070b510800703035060103070303400b4020000040c108548500c0c0c420b40b0144405103102e0105400c95400c0c1c0704110b800c0c0d0042106001074500040203003010b80c40303501450a20204000824020a0055400c0783c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 520315134 1250 520313884 520313887
    0x80405071512151818060f02040e0f01080111030603212104060e0c1c0203120c031206030d0c060f02120112030809060c1b1002130306180b01170a0c0902 67
    0x3028200300d880c4504041082c1060040b20070140308210510901c0c5c102500311070b942c0190750810b415907011140140020000b0740c02c50f0421800d00c40140b042031003900c03855880e101c1c2882817900b00000345ca20846008000e041d15030b45030650102031010482c2c005d904110100248658100184060390080150b5250301d402c038a03140c5425030440310001103000c0030354090481e5100740c0e40c804290aa03102c2c4400c0300300c0b4044240d840424030340b030182c8075454070008001c2008100c49000102a000c043e0f601e600480c030340d4642509060305c4013051203141d40001c52400d030480100c1c0b1160000d150500e2082c03001890012000703009812510281c01800090000301105000d05610140141c1c20419500c05071100e0304003e01ca070b0100384103032140c0511001e803c1d90400303a07844080c0480c400f183d56000d800e564420001c102060321030441d002c1111187e2800941c5403c03041c0d0300c803505802c075a12000c0380c001a42000e80d800603691160a1f01351191040c002c4075400200c440c00b064000b01301890016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 520316384 1250 520315134 520315139
    0x804050a0204060602150f090705060f0408070e190e0303010605070f0203070305060702070608070e010c02010c020a0b03060a0b0c0a02060702030a12081501030207022b0b13020405060108040507151215 88
    0x20103586c0740182001200044ca403060100071000400d9a00c21030307504680c07490b0f9400d40c1c10130030700c0c0600440c1d00411260003070510016104c0c5802c40d42c540726500c0b040ca090a04220700c0c2d0300b0800c0304c2d032503041c00c81c10381d0007440140044d5000700c005298a502a80300c2125410240c0c0c0080e1504416030402c40c0c00303070401414080c0d601e03010001403000c1c02c1c46007040511340c5055107000b0111094082054104981450280700b5a4012022240d0241e0080e114001d490b486002000c031070f0b40217580c2207000704005400011948140002e50b010491a9006003040302e0780c40c1c0801000390040801640d040c01401a98400540c003000104200e16a9855101441c030305004004110612403c403141414010402040103030341e0400910407001c1c26102c142c0944408048018045144682c02040700440c4030500014401c1d040c0c80b05901ca10854040c0403982c2e0715001101d000806403030040c11a4480c00090081d401c003e82104000300c520b1510300040c4c149503440307078251114088110541e80506005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 520317634 1250 520316384 520316413
    0xe030f1809010e07140c0d0e310b19030b0f0a0635030d1d011103010329240109230a0504020406080f070c0f030804050a0204060602 58
    0x425450800c940a0940b90303d071001c550202e000080a00c01041118041c801c08501202c05443c0c0c41041c000440d50080c4002c0f01c05429019692141842540d01e1500ca4080700c0300081d0a007500d08503003807113080314100031107030b50040c4c5043c6a400e6401400c0c0403040940307000d0310640764019070040144c8281c900f441c10002c400043d01601513080c1d2400c0500c04d10019074041d11310329026042101404410010200741803105880204081242c0000200104820110f03042101c0641407291180803864003504018201c400071003140c07c0c1186c0910040000c1400c00400580d00d0f84a10011100b901f0845001c00d034031031040f0303001e420050252030004544031910390840c070080c00070f0a00440403420900d100301c07c034a00300f0140c60f60340c44c41001c0e00301540b6202600750041c40058425501d40c2e480c0d50b406401e101e0100c0c0c001c1c1100f0300c2d000000e2501882034018030521a0080060601c41c64603460454a41000400039107041c441c0503007100060302c0b184070b803074000c16a660250050040c1d200c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 520318884 1250 520317634 520317667
    0xc070308060d0c0b031323060a0b0d031805061309140c09040207020d02130e100207030f050d0209130b0a140f0f010215010b09090a02071a0a0e030f 65
    0x740d0390003604500790002c00501c0f05010501520b680882585d201e0b900c2014070074400c03080b114003c10304006002c120038010710b40390340821641040001e940a60b510161400100e0b8404180369900c51304501d44800440e028400700409900c100e06001c10080c3c4a20206070f20b41d01003488040c010710304c1c8004002c0550700c0e101b0900d4465250007204c8082c1000030000d102c500075034010701d11455000508000b15502c4504642c08158064842c04940081c10b450320002c0c043e590003d42c0034041d10400c02943d4001d4401c44103e254140c40300141b02820640444180d0002d00200c02c455908002803242640c1c1e02d001c2c1c44042841120200328460910244449400598000902140d041c0601600f0307913150303031402c00d2498050340c03002410040500100d00c0c0c22943c50958450300c18110002c940c0813150702c010000c1800989030101e40d0789030601d1480132032007494070180103480d001034000d6947d40e4425400e41c1000343c2c0c02d004507215070518000d44c259405880d00401e03103000040da1354001c641604 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 520320134 1250 520318884 520318891
    0x606041d06040809030a0f0609050c100c060510080102070525050a150e06030c040524120a200702040c0e03100c0c14341e0e0c070308 59
    0x2903020344015000e2140d9a912000500020701051003c0703440d0b085078504001c019101c0e60001e4108440c4840e03410b00ca03008240904055810f402591750b1060300d0b080c81b01103443c6048495403003048820454541d64020700d8003034080c401581c0ca5a100080707841c001d0002e00002400340000c0c00f40f540e241d440041844483d103441d56428404c501003001140d60b802400c0003100c91002c0800943c65024804440e40076070211050303401341001c01400108601c40c8090015030f8006d480d2902000c06c86c0700c6050190080741c40d5400c419000b0840d04140c10716543c03030b140e0402505413000c280640700c00902034484a1002c1c2480e05800d01161500540ca000d004945510500342081001e100081001c2501c90300e06110006003d80c403010380404440c411a1501c0d0b5168100707a0030040e82040401a5441d0343c407c0c002e9840b606450450f4564040340014410b80700700041600403161490603040b908980400041c0e1103101c510b0301c2e000203009210b003c00d0341c861442c40c4402c86d030307d084a1402902004004c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 520321384 1250 520320134 520320161
    0xa0221070f05010f030e1006061d010201090f08160c170c090402030d0c0c0e01171b0102060a1e020f0c0f0109030e01050f160b010503011821050c0708060604 69
    0xd41d02081166040f02d075079140402c9501c1c02061085041e90000d2911103906100078090b4900f250004005911480c507100c52050715009400300c802c0e900c012803c5c0d40d641c203000340100c0081c016400020320642c1c02400e4035040c0c080d8090540b103254032138040100e1a684071680541c500f114040709a41d05110100f12000115105001e90034240c02182d80d40c01060f0340308050101800004041c05034110740003004110742c1c42480d00641c5c685002d44800b080d02d03000144070303200300244104041c5c600090109004010f80c01000507580740d81048018011441a5110315160329080312000e600ca80003c0c901100020740c41c81c1d86401001155181c07806010251035581d2603c40140006940030541281110007440c1c003d4440301c0f1403080420902c280d50706507240d2903440100508004074901c05604880d0102c008006400301d0804003020030060502c0140300d0075a091088201c070702e0400601c540d0302c0f120701e801030030034050341402841c110842d0000d20301c9500080c20405e10b45400e0041000d00d8140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 520322634 1250 520321384 520321409
    0x1f080711010615141b010b04060501020c2b1712070504061409040209130608011d06010e0a0e0601031406130809041a27061813050a022107 61
    0x3446512800c000d859900003042000109854013601409000c0d11141c02103c94440b42d43d4039100b80c680d0013040d003441528080c50078078500164540c004655040500400b81c03100c501c0440000b03804003508944000c1c2c00c0c4031920014000081400110740304080c44030240309a03540d1a0040c400103014400909800802104000030302507180d010300c40000340100841c1d2292503040400018001e0300441c1d10498100c2c1c6e0301000800c003100c450b004001114138842c0200300000c140700d1402403101c1c0f034a0a1402e03607844000100810045502c00300c3d486000c1000000f038203584240030508006023030788195407500d02d41c0b107011029202800115002801e4120304820b2400a0344c403001071303010703485986101e02d50311441203030802c0c0362071200391146000403c10040080040d110804150700b02e001e607490b0b1000303400040d501e81455030780c0c0740d609140e46003048444d80d101000d4090103c90b40c80300312201c0c00303120800c0b0010f03100c144050010021000a50350b40d0403444070100c5c60191141d02c1007200841 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 520323741 1107 520322634 520322639
    0xd0c1403190609020c030702011101090204020c0d121413020a03050f070f08070503070b03070507080a0e0f04050f0612030408161505090a0b091f0807110106 69
    0x10810400c0b507191100b08030300c104d0040d8150800305605c1000b9030005580240c072034401309000500007055803640341c5e0104060340c12400c186405075110107540d4900680040400b901d103441c05908021b07810306a2446582c0c440080e240060b0107844180301070a644488541602864100c811035a58180b00c0c603840d5030f101058400d00701101020100440ea4002c0401c000c0e0451303130014020002c081c2004019801a84060081d1043c03040c10000080050111805002021400c4d109c08600c082d0ba50b0a02c007810140b000028800c0d0324007420003403960203000c0740170b400c007606075940380c0c1030380b20030031814034500c203d40001e8101c0c4611000e4041201c44004180161442d40204e002072011710710342500c2c01d014005585502071708031601844204410006040e103807070001c003144007010b040600030840c00500f0f080f81000800c20070030003145a400c00b030301c3d17907204440b0f030000c011952 = true := by decide +kernel

theorem cover : BRFrame.Cov 520143884 520323741 := by
  have h0 := BRFrame.cov_init 520143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 520143884 ≤ n) (h2 : n < 520323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
