-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2943
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:51.332213+00:00
-- url     : https://prove2.me/submissions/43900252-19ca-43dc-a956-c3a4ceaee0c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 529136690 ≤ n < 529316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 529137940 1250 529136690 529136723
    0x110607020301060f06031b080408040302060307051c1d0106051305090a1202030421030c06020c19050c0901050a030f150b180711010e1e0f1605090609060d 68
    0x6000c240d2044102004c95100012005c5c0c01d0b130300020003260800c205410040403128100c2c0c41040444000b080050140304c00d001600785a006940d0001b02810180d1402e403032841207005414071801c040078000e4440d0010b10202030b40740807012640d10607800911032182080c001481142ca01440581c000b07580e0000140e09502c1000310300300d400c0d0090340100784946140f000035102e50140c0183c03410307901d900d124510341c8070740c0414012000d5050f5460800220321030350b4080203580071200c40d07003d41c4158040207510b418160050301c038a0b2310600003400c42d902a041400b1019505038021131081e80c6010b020000300310390f010f4951a255004401410b081064410b0800608001031102c0e00b14100801c0a401c0280d1580b0342d42c0a107081d5141c40349842000c86602d8281d0780b0034141c1103400d0300b0965203280130103804503512310b8a1404405548001e0b03064603050780352594407646941a080300e50030802407400d205203100d40285043d0741c550700518101021030032402c0080030003802c1c3d0404004451 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 529139190 1250 529137940 529137943
    0x5010908010b0d06110f040605042402060a090c1d150d2402070605090606040515060717040b0304120e011e08130816061401030f020907020109050106060f0f020a1106070203 76
    0x42c03000148001b295241c940b1b846000f415500203004114a040d14007804c802c0c1261500500c006480103940200308903a58860340d030014021640040351000001c40c1c0126042c0300902c10028a06400040e040591400865130f40c040c00161713825034069098142407074007060b5500540c0074075030320400d2190500006180781d04000c2c03040d00c10142c042c0d4a0442030001c611408a0b15a0090108a8003441592505502200131004039611207511680c1041454000380e0482003030480a8071034550b0a09150341d5500d455002e500c02c86003111210a01d41190586d140c0107607807607054044c00e28020f904400092460703101d4100c0030b2030700d0003130200200000d2103501e811040d03204101d60200030591500d1384003a100741c66801c40601110014182aa0700d400701c101c0b440720341d040b0781c0c010500c0d01010b051502400071154018004d082195220f41045010070400d0107140014001541c48907000800242c0c02070100c40810345140464021850440100f5401180501e49c100201ea007581d51f01910f10000b07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 529140440 1250 529139190 529139197
    0x70504270f0c030506011416060e010507090602060f070f11010b0a1e0501031509050c190f09050d030e150405031002070b060d0f060f18050705010908010b0d0611 71
    0x2400c0041c1001810300802006412400300710801d41c80620040d01ca641c010756011944036041c0250200034406500d010742480a40000f6038050500040d1005a400d06d85095a1044031000013040076000c003085029410040c0c41d501010401b54200d140c101340c10010700c05410355151004101e55480c0c0f0369200b076000c1d40180388032100103000c3d441c6103a440007a44a00c40e8241828010010048400205540203014140b9040303031240740039040c0f600b051a8100102005400015103003001c1c0b00050a060000c1d2a4400469407a15100b0301900c00f01c500508104160300014050210070400d0400683c00480c50000d00500f15403001103003904810407190f5008940c46258144683ca039803068038080c0e5030007015454050401c0601ba41d031264140300f12442c01c0c0701c0041c610394000f11180007003045035001c0301404185a2000c10000240c04e0380d000c0310100030605403019004000100300542e0403113545001044464000d0150b4603130080062441280d010f0702070300640d140e00001c5074400c0414103d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 529141690 1250 529140440 529140509
    0xc12070215030405010f0c020d0e120a0b0a0f0c031e0c1206030809120c06030c0d0902060406050315010305061e06070c0f090f09080a03020c0a150903090905070504 72
    0x41502da180600303046000e04144100c0c00850703443c24079440e030024800710300c04076201060385a003003442a0b084180a4044001d90102c0d80a004950340a00003c2e2a60800742c040d24400c6000303d0000091019941261030342e00f41d140a2614003200301100888210001076211303640040082c00c0010840144d40103505a40d1050b1024a09100407081080c1034001d0518084169441018030804d26441c2d0f6682003c000c01c9076209600340000f64181c1f444000408201b40500c0d400700d844640f50313021a08a8100703800c07000208502108000030001c9842c0e818030b109900b481c0601513400c00300041400200360707184039009c6100e6900c03950240c0d29103400310303105241c1c0b0050100b1000c0ea520036150741260301c1d0259078012030400f40703080298280307805082881a009004a80303402c0d1074100c250700a5100b521114202d026020100d00801c45602c0d4201121a1500021448104514004060301c042d03401c00d42105103400e05102c202d90f4001c00360b9083e288100a5074401e40e2490342440da001a03801c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 529142940 1250 529141690 529141729
    0x15020a14010f05090c1516061103010801290d0305070c0e01150206010e24040905070f091509050705040e04050a0201080f090a02150405060f070b06060c120702 70
    0x10848203601580142c40001d4840310812583d1034500810342c6a58220032085d0b806444503550046030344001008010301e800b5060b081c8040817042d0344610603500c80140703c500c0c454001c0010005a0003e0040c080c1c2d200c070064440e640985000d004589901180c1c0002e40903205040c2403904150042040700c0146421807481101c0d03076036032100d80320040c400b400341c94426900d409010301041e000250150603162041060303450341d503440d242d0000c1e6444110f10303006950500c0002031480d0f00e9134410090101d001c0c1002c0d008003420071000118603180e030350003801030524040000700c02c0345610f100d910640e80920701c00f00b002d032100e49003103c45000700d80180807400504000d210400400144603042a8802e07203840f00c50f40c0d10505510449402101c00c030f2440e0704519030010040c82d20920400c1914041004c150905496102050854101c11070000039034000103149000d00105000055001104441d01440c0401d00c0080a0321414a10180ba43e030200c0031494808656540c1440108102200c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 529144190 1250 529142940 529142963
    0x30f0f0e0a0807080d1701050f06041824140d0c08060a0b090a0c21021b07180203040c14030304120f02010905040501150c081b0709050c1315020a 64
    0x1007595442d902c01e80704e05074541c403031081200400d5000c0c51407081001030b914520052030303103048107202c1041e00c80070020741d03c951f0030040400d03108c1c490b4004200c418038921001a06541d03d1103c205004004000c00050b084194410003c0c1510b0300c585500001c81960720300398840c00c1d45850008452150017519480c042e1004100035000c083e4409000100e0484003144a622090326820031144444003400003e4403445100d0b844402d5800070341c0711031000303900040c60710f02d00702180841105500e8001520380c100d880100242a0381c111703a014841c041013011891424999503d07a8519124456a00303201000b100807200307582d081c000c0c2d40040c458a002110328540314500b08501411a84040b404252044c50215440c100351040c181a03071080300e6030284c0b20340300c2041075441003102e2070200e0700c00c0800c000501c160200341400f140c0c2105400000c281041c1419203217801e40d0001009008084030600c40d19a52103040c409850894910b0701310390850018042c0224107100315040003400384075025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 529145440 1250 529144190 529144199
    0x7060b0a0312020a050d050906070b180d1106100e1602120d02091f1209060b0301060e0714030c0307050c0316081e0702060f0901020f0f0304030b09010504030f0f0e0a 73
    0x8241c06003500c0c40380e17003543c0840201e0842034600c2d0003444d09142d0040700c24059400080c1a0719101c58000c0e0882c0641409880d030344180c03510f048441800d810006070341141a850b00344003041030641120200b891130040710b042c007600b02010800101814015201603040340002402400700180c002d0000c148550364440c100d4042002c2e40c00801114003920b00703c4120300514900e50224411411683c0e25080000348006082c00a080d82c010169261652910b80d01003541c0c0910810006218400c001d00092408080c0a4042c5003440807501c0c00e41c4003001002062203000c8201ea0f4002c01d54200562640708120506156000c0c00210300481e030741c89006041403069800150500fa42e0b40d80c004400e0716800903280ca0a406a0b20009400a5042c42100c4120b081c07903000e0b1450340010f104580d4032408a0118900c2c010140864102c160030013b014011b0142000c40c83c1d51064042c0020311150030f0564004000305992400e40080210808503000b0381e80c0308044003824038000030f00081c03240303459 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 529146690 1250 529145440 529145443
    0x21807020106051e01170c0906030901050901110301290c010e0f010f0e07210209040303090317040203060403120b0a0803040f050f0d0809150c030310061407060b0a031202 75
    0x55004580c40380402115016040f01560b1320428024810b9413010828840c544c0807810003000502541c01d080028080d54415440303c5c0701131842032005000110341418501001c0e4212103404079480001141000140100c0c050100070103509040000c00040c0919014000d140d140104240c0a0f400e5080607061075003803c0011358075241c541c403100208181c1455844c0407040b01c1e06045d00d8101600490410400c40980d003081400b1070280b0108038510910703a5001840142080390300b2008a990348c41420103044d40580c80803c1812010315140c10ba0501d500041c0e03580500400041c2000040e4aa859006886420004680c980900704007501c40d00d0395155900c03504280528080070894040c009801d20b0044114083c2003400b400c9808000307a80c0c0c07644003407907209040c000e41100c0200c82c140030711072030308c0300034200c204000000c1d50b140c2c2000701004440d4542580b21204112a800407000b14012047c125512540c0c0240005084081c0301e010800500d82540f000d44108545080800500c0c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 529147940 1250 529146690 529146701
    0xa0c020f1c0311161e05030706121121040309090c0e150412020d080c06040f110a0b0d180803250503040f0f0615090f0c080903160218070201 62
    0x1080d1504400904607103c59a03441c004894030301446081c80d902040f644080b0446030801340c0e10796086142179611400420f00d801d140e94020000905201c0078035003400031621401415000c0c120031949010061000d00d542910b485c0c0204909800010100d003c2500960070100104240182030001092581001d880940c0903507115000d031011220030044594040110703825105221a400000e014680070f02c0791a07941c01e20210346c00c00e81040024901a010440644142d119490400b259905458818401d403411034040f800340054040a215145a10040d01c05c0d0b80f01c01c0d4000034905981003c4050380416018010301100000418800c03418078103901d0010341450f440307041c102d941440c02e04036400d2108540140220346285003010000b6014281014224002c0c072001c82c80c0280503400c600c09140ca0392200b08003d0355115000c41c00d005070b00403048600e01604000b4054900f1b134500d030b40c0764491300865070700441c80c080c604421961071311080702000403418035000641c03411010107402082d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 529149190 1250 529147940 529147943
    0xc050d0e1e01050f01030803040203120d05060f0108090a03030b0f1e0406080d02031207200a03020601050307050f060a0302040b030a05071419031104051009090c080402060a0c020f1c 80
    0x8007415490070901c0341c14041c2c6401048203020840190b031860315281e030325030805030040360f040c007840007400e40b850780020240c10780070540301c40000c4e60306108040000d454801c00686041c40b00b050200005141302041d58120316806040104800d000d001c0040c440d0b940403101c5030b60001c02c2030314462015481202008122505441c100001600d80a030305944150403407042006030f1040004c07440c1103143d811001d030482a03500340098117503212078406d0b200041005003d00640c1c001e07150141859410090b290051500b900640301150a120205140c150345544aa0242600041002d0290b1196049800500c58541c2113074480c2070048440d400342c40142ca00e5800580454085070301c90100c1c10032902c40d0131000c50300807203110100f44254060f00d10300041c01c00b503030001d11000a090712100079102c0503828540d5049041c1e0306110780107080b40c4034540e0802c104140031080000603140c0c90100c030842219820880080f8409200044245400c1c1d042160011500c140d40d07000084035075150015135 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 529150440 1250 529149190 529149223
    0x160311090a15031103011506050306041b020a031407050a0f2d02010305060f0a060507050f06041707111905041a0901061b14060712021c0c050d0e 64
    0xa8030360995081c140e03102040d040c02d86041840c02040000c01c0f580e6104403680c00a800410001e40c0e021100010040c40e40c010004101e0003c100301c1da0b8942403081032a400040e070034042419540d204000d54403070340004002d06101034400500403c0f2520b0080c1c5d024268000d08882d07910600745040d4208042c190001c981aa03640b40c2c00c03122014941d010795000003c401840402e03441c450700110007a20f005010590449124580d900c16500c3d041030b401c0c00382030282c540903602c403c1c82c60304500e08000b4001c1c00c1429001003013032100140c205c02c1825084015840000e0300c500315820495607203084404a982d00000310302046805040d6a900303034084840499003084034051500340c0300210a010501280d00c840702200500c812406070200a803958a00c40c080c40341c643c204e42c0c1c2d032a044003402039402140c0e4080e00400c0140ba900000f801c180d41090740c010360801144c8e1480c3e030001c4011a5098130b1268554100111441c8524150b98441401d0f1000340401900c4d0050680c5510740c4c443d41c81c210 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 529151690 1250 529150440 529150459
    0x7020f0d02010c080f060d0606080322261203010f03030f08070903060e030d0e03070b0c0f0301150c1b06030f11041502030909010602010b011b051b0102160311 70
    0x14140184558580c0b420961201034465441e90001240075000400b01b59011407100e00f0000850050300c01d490140007090025035440b0780c0d0034010128210035070200c070982003040300d00348407544100d9038400241280801002c86081c06400c8142818002c1e01e0a40a40c030010000058039005042d2041c1101d001c2d81341e50b108065915002c03110760004850500100310110320800000d803042e40021180d079046030560f07003414040c07200e40f03054074442c0481040e180c1c008a9080140500c20310318a8020050710107403841d1900b00c030007105490005203d14001c0c01c0744640301c0559140100d0810b40f03001c5d801164241103080b40d94240d22002c0712401404000303850480c505c81ca1000d60701c5104c00d0034121680e00750034580f820310000d003402040c010400440c0000c0c0b0091082c2d46600070a80c0c040c1134550004100083d15100040100500c040900da40c2010a82c0c540d010441c04100d02203851051200207035000302550050749454405d0321102008040050300100f40300c00c140c1800c40b001402c4415000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 529152940 1250 529151690 529151713
    0x204120b0f01171e16030803100905010617040c0b0703170604020a0e060702040b0402030103210309030804120e091f12170336010b0a2904080607020f 66
    0x5050240201071040398020500b08000861141541e100268900111200148100505c50170184260300480340d01c1008000d000320001880c0f1544041c10000704200000c2d03140c90001800c00c1002c80c81f920b1894132120205083c021441114400340402210082d035407405882e004280750740f001d407a81201010782e03000c0b0381e69241034000c90b0f041c0b16055170791540701484803041100c6e50380001c0b02260b0055035200c013002280c5071400550300960088441a040307103500310303100c88150200c1e0100001c0600e0440c0f01c500085e0070068440c0c10a82004c500f070b078400301c209001e89800d6141840643d0103180070341008119000e40b40400e0b050701c20780620146c2039a6a80b2010104103160300000c0090090529031094194000051a0b2102c803c4024941f06522441c0c10180300d640b00b03414584660b01e5124441c10340c1c0c424000d40342000001d03680c424481d860207511000200200c4502d9034846030418540c0f1801c4156810303a070103412290203440503030a03c000065591241c4035000d50060242603990b45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 529154190 1250 529152940 529152959
    0x307110f0409080a0f0306090f0e0d02030915030c16080a02070807080604241401050f0906090402040e0a140a0b010e150411121e060301090c0306050a0204120b0f01 72
    0x40d9099000c1c1e43e060404080040c2601e5180c00c0c5807440040582c1c4a40003d942e492a001d51503000c3d54182d80020051502400e160405c0001d0f080f85d02035500811690016450702c19040207000071021955440c0e0b101ea07681d041c45803186009101032001203000850501c1400307001001803039020340844e85150350390005a40c42d95250b1260112641180d8002000305901200d4600000743c011030b0f02d0a401c200c198078404980800d6800003200924000500c042d082c4601c2c00c41003040c048992140340c0c0782540001b00088402080240540d444a030000401d41c0e0421540003010760024407184512044800039603152407050056800c0140da0000003802c00000d104180681c12504c140c0c007a508041d000e10000d025200e170110342c001001c0004204a010320740b071903801280345016210549002c078980250030480079017198841e0345440800f100080501c0791b007604503988090007003410350701c2d441014000c1c0075a5203c450803076011142e001c20820000501481150301c030440441698941d804003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 529155440 1250 529154190 529154201
    0xb0d021c0e0723060d060f03051624030b1309080316050703050a180b190e03160e0a0e010e154c06030606030b1207260307110f04 57
    0x4002560b022180070105013031020091281321441c0f903012564540c0c0d6200343d480c1e10300d2640259410b030031401354070703000c8000b511010300140ba03c0e84120b04003a07108030146c140e48030703e00c03105014156560320000d110b440d00901c104504c280488100110105030415801070741c000ca5403000780364496a40c081059010318147d0703180342d03019a01c50b801c1c80c0c46400c00b500c0442c0344103039002c00f1b9560100c00007144a00c460051004001280c22074984801c20640170304001070110303a0030711a40121720024044610700050354112000803803100f44c140c42e1a48030030020031040014a1aa500b40250a800581d00207805e07000441c000311111841d590f08251501a0000c800360302c4c0c080d00400200100b240712110044c80108a00754072402400418030100c40784000380e40c000000700752504d008100c041c1d01407040e00c0500b14140c400d0b10940d902c00c001c2c19281c0c2c02038040c0144804200c4946001032248075030ac09082c0c80c0c000e048954494040c1403580200480444c0c40384201e880e900110794608050098 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 529156690 1250 529155440 529155479
    0x1413050405010f05040b030d1719110c010b0f090c0d0e030408070e01120b040605060f030f0f2103070807020f03121015140d090f120201051f0b0d021c0e07 68
    0x5100c1e000312095480700741c0c1c5270040d2462926520081426540000d80d101d9480d00c502102d541c0c5940721503800d1b80500752401801014420200c0340d01000e803940b115506154000b408150480c0c0d90071907800d0307120080200e41b1825040e44004980410302d84000120796065840200c1076080584c0c1e15408454441c3d250b0000a140003000000310300020240e07000940c200c4001054010400c188401080c94480d501000c814981d200c03505440e2802401e01902078581d40c0c00c0c1e1840b05c103c40301c0d43ca1005034400a4180002c0019280015160500c2400050340c0302d460141501d0740e420603101c245c3c1007140142d690140714031110800184503842c015000031855499102c840201900d0340074141150005150700210540383e10f4050b002400d801c03a90213640c4d00c190704041100403042002421a1002000111038100d190420654480203945000890310f0841089680d83c01c01c002035000f901890300480d034200c1d241c203820b0242c4045604022401401c007400c80382c07401d80d9102c0340c40d44103c0c010304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 529157940 1250 529156690 529156697
    0x303031d070902160b090a03110a110f01110604030503070f0912061a120105041703091c0201020f04060e1203040609090b0303070507080f0d09061413050405010f05040b030d 76
    0x4104524280d00031300700d020300d505904030070100e480d1030341603408000300c0385e0095039042031186604058000944c0940312490f00f000781034007601595003c0740c8101080900344a200304c00601d0a450784521560b001300368500061b113189050614018006802c2030310013402058840d0300c46a2254070907808030040320b00c2110b4098140303409407244c0c001844001a00301143c403200108518a4590805042d001c2250000006003881d0606000c1501e86031810b010319880001c0003405080c000c0000d083e14070003500103132a1a040c00904c800d900a110382d01c14940d181c01e002ca000107000e80c00c0501c0b50b031450030944040742d1248107580001d890b48502e002c0c040110390040c00502c1041015480a003001d0400b47c100c07880c10800b516800e1070480664880c80d0264011600d442c03c9000c00d00802c8003501d40741c1000c2c8032a41c100790021700b400307011915200180780d01168003201003030804004001031101500410880d6100c50b2120402400303400303058015802e2034000401410005000d50308140a03030b9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 529159190 1250 529157940 529157953
    0x30201270b151005210402030c060f0909070903030e04091707081b06010f0f03200303070605010803130602060f160909110702040b0607050a0326100303031d 69
    0x20394200c07038108041c0040caa2801c8034000c500c21034907980300418110079503454141c1c5a20b15205691018052180c0d25012418814103202c0183c07800030b0302c10300303119044580c42d440ba0180800966039015512030103500900c110107020032107810194440540780070340d59482600946000303000030b4400b00d07580200f80b101c03102c0140d140800e015002d400a1846004c019103043c030907002e400074030402a8480040c5400c10801002405220394400008040314030b116800d0500c0d580b0344140c00341440d0710801e14548045005070807642e01f4021121003990001e020020340d40c407181c909580340c100d6040c80100c3c019007000446d0041c00028468441c01c0030740300c0260326039518503d40c42d9803801c2601110a00c040c803000415003600c1da000f807120341c00c10140e081e134807006ea81c0100720564006c03800c054000c82040140300b001c6100030458800080d0981000c0308244180c289125600070000715800303190460f003040c0300d10320301c0707940146084074020303070b010700c14440d407a40342614040b0345401c2118030350b2101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 529160440 1250 529159190 529159193
    0x50105040f18022803230d1b020a0b0c25080a12020a2a0501090e180f010c080405010c080105060d0c02070b040321020303070914031e0a03020127 64
    0x64250700b0f120591041d8034551018801507101c091200382e0800c079140303101c260746c55655041c3c0312200ba0350030f44200020003110b00c22890281116a2032003502d5080141116008250344617040302d400100707001c00c2c40c140d40d181c02039002a11100d0700c0c1e00d070080120050aa0701c440c100c203030302e17400b00395440403001c0c2000d0b40f030641e03590a81c2080c2c14428000c4d40500303a13242012441000f0782d440740442c0c1520030410101c06a44c02d04c0441e2458001e6414000d40c24810702a0541c030042007039000301186810070a241081140d0f44c0342104007000d203006036003030020720b512540d07000703085a018600c50f02c0280100415541706542c1500c007401629049081030244207031200781d54014001240150065540658881500503200d074044c0d0026240506c04890aa02c030b18184048030191400c03a00c09103045040440005251210a07c2031101c4860740180c0d228259800380003c0320000c0d031180f40041000210040e81d0f80741c041c2c9403001d5016500e03120003006140ca5519191648102d450b1b40d4500e00e4469 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 529161690 1250 529160440 529160449
    0x1302210c09090414060403020d0e0103110d0b04060503030309010b040b040905031903020409060e07020607140409020f2106031c020c1c0f06050121170a21050105040f1802 75
    0x60058030008a40c400c40018813200b88a80c0e40a01d0183c1c1c05855031a52201c4041c0142070782e14100d41c101840d1140c072860501e0440241c5180c0d2082c04c0e0081022068800010060401078121660600002041c02000300d815801000914025901070007903a002204000c00c072040320300081d10503001040142400c41000e04401c802404c642801410991a030311820121100c40d080f20305605401c41c02d00c0403160301002403691083e17051807d031591500c1810303840ca943c0201e2041e050415004510021601d24460546034400e4040350295003a40641600076156481940d20500034061507910444224484007081c1901e81181c00802003400c403002442892a030110554141c005000b00680004822054040106006240105032541041e40445070b10700c101e0468006160503090403c0007c01e010107103500310000440c42a140c0500304401d5900c617401400d0b08480d2801c412a480c2c010400743d1255040e1401541c04201c001100c80710081101c19500c2c04580240e501c40045005107003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 529162940 1250 529161690 529161709
    0x703050d180b0705011a030a0f0b10080f070311011125091b02060610170406141e010b0412060e0c04140901150608011a07021302210c09 60
    0x206120301c4416603a8400b01c0c1d900301e800c686011601ca944034540c1503d06002c80f148400641c8003100944140a05030382c800c109500c206800525188a00d00003031000e5000c410303188020f04424098401a02c9103840c180e0b03c451540c0000c0720184403080c0140f03640d5116818034040c0d0080c8100034100401d081000c1012038120101c80024682507050215606038240201c03061a410034a4401240c00f01d000041d00300380004121038082c0d034100304103440c010343c0090b00c1c40042460004808860f243c60a1250242c03000084111640c04e0280a0002c60780c02449812080301c1e103010300c40710341c2e41c0b00c0d01c8000107440b4034420a81074416000e0514042011640030751041d01d0158111501d007202e440100741650000c0794454004030034402040201902070141d040c0e903944200300d00394030608100c40640103036010f0040e901700042002d640000c098400e011110b071690003c12110406c0841405000a50f12440d41108911080407001c4c04440308150700c07071b00070490108468140841641808407170318 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 529164190 1250 529162940 529162967
    0x70e070801060318061e0f020c030405090402030a06060f060809120a05090a05090112051b060a05030901182003010506011d040603080301030602090a1a0d0e10060f05040606020703050d 81
    0x5640100f070800013542c0d0721860803005d050807180c00341700c0c000351b500e00201c03200103c00482e6a401000600b5502d40003104071026100b0444029005403164000719241090f01300703004100030320700704022503520320441202040b10042d40e2801c4041d95022059074407210100c40b5405050f60a100d0301281a00550140810b070b60080c00b011400c640c0c0383c00103036814400381c1c800c0c003c4102800004c800e105003030240308100390030096502c45081112012a0051040d05151020040d0200128005060a4100e2400301408100303102c0e00c54100e0405050050224060f11516031001444203074605060064038452203050710740b8501c402034108100c603e06000f90320746a0203aa074071408070003c1c1007800514040d6000301070042e01c03440f10340144403e07600039401c0b9800ca145204c1c0d101401c07503051000c031051403d21000101d02c124942d0261860140106807842d0401e080200100e100030b031500754007040b100210341c10301c0000d580f246e0591301c55096000250450b08160f014000e4280205019150346 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 529165440 1250 529164190 529164221
    0x2090604140a0b01121503060b12010c051201060e030604060c0201021c0605040b0303160f06020d0c121104031a07090b0a0504080705060c0a0213020f0406080603070e0708010603 78
    0x2141c00410142090704102c070342656481d50341031619807079684821045820040d00200b00144800c5140080c80e40e6a9488010b040700c0e15202d020081e1740761a8468240414020000c1c003000c1c20102000c1e10940000310081d6403840088000a0300c103203d015040c10340480600502240e8469071100c2028000c4d07d0054425503408007d200400140c05043e403064441e8084001040f5007024104030540c1d28010219109030300038070103450040c0e00c0742c16000509030300085015440145181c610b000c1e025422010315950f161044905c00c0c5604000040e114650120040207130030300304040410307180a40e00000e4122607002c0312081d5807078184003c654104d9184c0c00c19034400c564170343c12241d81358800810030b400a08003040801c00361100300640c102070034088540e03508048448004503a180c1c078000e03001e40b140c00308040303050481d06030b50f044a083c5a01c000d015941d59840300000b40a866055928131b00034803886400148188052003098000d44c1c1543d22203000341d2074000d0440140010301001c40d2017 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 529166690 1250 529165440 529165451
    0xf02030c12073f0516050d1e0203190e03090d060e0f0f0c03010c0f03020a09090e070311030102030c070201110c04140a0c09140d0602041a03011a040509010302090604 73
    0x5445403880c540511151281a00080c03010200740d8483c140d032103444458201c0d003080d0901001c84403514224007601c030185001603c4030081ca14842c0074052004010070361407407520070f221801300280c00440c0700b0705090320060100103c0410880480704d100418441e40d810a000b90810b61420040c04803160307000706d10214020200400320f6040840e07040d050035555010303d096600c8000305001d40041181c045008202d031140c96040540b03019400e04000f400c03d9800128041c1184c003549541e0003403e0b40d10410061425420322290b078680c0b0364001656000701558030400149014000c8a110b8030b48103040c1802c0401d81d60054698100c0b002c0060a54010196880c0d01c0b526540702d042c40303503000130f075421800341050f8420340c040f10340049103401000041c0900b4018411400c01500c20300c001652603500860203030802030000d0003103400c42d544405a503d68001900328100155043c2d5072881d00d011000400500201d406d40b2440c4200c0f50455250401040946403045e6a198030035800390000c00c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 529167940 1250 529166690 529166717
    0x9051e15012106080a02090a0b060d0903020f01110d0e0601031e0c0e090105420307090207060c30051801020d0501030c080f0705060a0513080606040f02030c1207 71
    0x9441c290740103611207900a0300400291f00c0c0000380780b0741121840004120500c80103001c511244103400742c1d10303041501e032500001010b208102114500c9a150020070200c852014650306070f070b00224000c5000350802080703080f045000310f2928100d9034032001296800d102c41c2c0a08440768078409041d0754070441350000140441c0d0500c1001d00c1010400300000311484e02c1041c4000d840800c1c9000c4510384101c81c4003080ea061003140403c83c90541e01da85541070f40b59840080d1402c50107400c03800e00d09001007584400c0042c030742c02071440c000c42030b00e607010241c0c87c00c01ca03010394041650b090b00200880581c00e5614108a03404103420480c809202c2c40c0e9552025041400d9911681c041c0799031655840c010003c1c060040c0e0003001801c10f0030702500555220682c01d60303450005001d035500c0b0b004009840c0030030501070002c54110061041213444034690310300501c0c4e21444111121800b450030215500710b040031600c2103a11540082d1441810001ca01021442c2c1d00c500a2801040c07110320402c610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 529169190 1250 529167940 529168007
    0xc0c060e1203180118020607260703050318060405150604151206110309070303200d090f1a160c050a09020405030114150d030909020409051e1501 64
    0x52059402120b4400040f0301c100d007a50842c1d20410007a5100346228400400503620f41041745c1c0c034160890707100550040b005c111503002c540c00c070802407200c00c0c00003416020103400602441c800c2c2c9811000e203540400c4104c019464842c1143c004060380c20448000390f008040c00d007129003005002c2c000141c2400e0500444108624035041107040c40143d03c512020030107036008158030031b80301214036401c609118100c1595604203000040c103000020600005503101091405507004030740c0211101c14441e0b40e006090190140191103000050513004203a41905d84d1003071020b810f0340103501c0e04d000d001480016103c045a2411141c0c013103900c20014a1307681d40d011000191070003040c016507a5240004060840781500c1d00440301513091410008041450010700b8074400c410f44a00410a03003510f422505809a500003111182c0701003004111580b0700ea002c14801c041d00c640b200925200e40c04068100c1c0390846807803090101d04000780c00c180d407040524004003480c038003050b411600f0040451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 529170440 1250 529169190 529169197
    0x60c1204060c29011203030b0918120a09030b070e0d0b090d030e0c10110312100501020f06063a0606050603010e160e1c020a090c0c060e12 61
    0x500005200b61464020b0000c0400e582591030020500c0e941c1e900140b40c03c24806107014030031902400d02202c2c440003814001e40251011480041c04c1c03542c14506480d24a907580282d049641c1144291350310040100c0211080350785034955500c50311030a40c510b554140aa44000342101d0800650300903800030b80e100c004001012503c80c040f041064900032600f54586200e60409c0020541041d00031704c65042e010030940b610b52000d441400300c0c2084003000740c41c450030400d0f03440542d110004155140c4040c0140c100d02414406401c440030ba036648004980e100400409080da0303030000808a0007074608190219080190728034034010404c80e000d0f280d02000c0000648000c1031141c6108034003001454410079000c1c7c81c0c1150540d04550400e000d940c06100010040c020480342e42e06000082406240b80001c202002060600c00e2080912402014580f84004034040c003401e120102d50b0000da405651810810b503540c48441d130321262191400b078002307420906258000c5da51028888082c58004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 529171690 1250 529170440 529170449
    0x360e04030215090705010c02040c050f04030807171c0504140109050c040e01181e0b011212110d0c1b080319050415031d06091524060c1204 61
    0x25003204444030700c2100d020305005001c41c03c10381007000309000c240c0c2c1051480d0300240d010380f0000b680703490402c4103a07003a202d03482514080c4440070500000b0004418000d0012500c0348042c06404030700b4500c0c07400b1501071101100d0003800302c0612080c40b110240d00481e0b00034020b0841e00d043c292914030706401c617089100290740d01d82000082c0d1419040c14062074103024101c800801c10031403002c00807403e00c61403500040c51900b20117400442030301c50322514118150030201c0201c295940341546144422607803801c46143324180c64456000e8080c501040c07c1e800f201000c0c29040c410b4a81c221980e0943c840f088548082d0890a0b15002c0d10180000001d00410340007140e445c16030034582402c94108003018010404108810b00c082d00301e40c480c103c00c500c518203001c20032903020044d0b4440107580c501514014814034040051b42080001c070500c8045900907004d5564440c8400c4003080e102c0e42500411490400400720701c2030801500a0011030008026a05202c800c01c00c80d42049c1e002d03030300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 529172940 1250 529171690 529171693
    0x204020d060e0609100b0a030f1b022b2a23030712051803010c03390507081201031104060b0c070501030209010c0203010203040f0c06360e040302 64
    0x90082c8240d2400098001c0310840744c02c1c605241402e00700c61503144034028032900b85804510303036081d940039410081c42e03540b841c9010311204c515074800c01130b81c940071300350074006108141226031002142c28448580c00d01c0e180c0c00c1c1c40c0311500003800703032114080c071740e10602c25142c40c0e08088011940d468103c0340d9244201c400f00c4004003500004444032100d519001310940080004100095049030042c3c1c80c0c1c00c003410007546821260701180c500304006c00301c0340e425500b416801e0382840e0307040d400203220524004055821403502640300d9040c583c0445034056810307100c94080002c0d4010806000c07820311130000985031043c0b9541191a0074000c0c3d0084400140c0c41e0f11840745407900d80207a5014011840c0f030340d41171000032141560340342043d102c6d060502d580090700300142d901c100d0f182244e550700500259642c4c20b1510380719120314a841c8040e2403001d40b10304040344083c89014000340c02400c10f4100c05d035401c01d030003010501c000c0301000c90242d0b00b1a0703000000d1006503000f04903c103900a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 529174190 1250 529172940 529172951
    0x309060e030322050f1504030221061e10030b01090b061303050304090c0e09040b0a0e070b0d1b0c060203060409020907110c040b010906030908040e09031905090916020a0204020d 78
    0x4203002c5e624900500407441014400c400c03110349030007602924103e980407922885480042d08802e600400c422400b80114055101007264407500401e180d8241ca10810710100706980e841081b41d031100361400000d08441e4020010410058190454034078800001e212901d003019201c508000164a42d008550503000410301304404600f902c41c0d0f85203409241010041c590240000600503d00140014182ca41810208801d801c00380d01000860048008a17404140c40f00501c003c690003035a0001c40c09420204400362806603c0c01c04a06c0000301c1d207942c1c8a0307000c182d41e441c0294000400098009a8841200c0050b139200194140618416207c07103580e007905901d0319044c1010101d00d0760089081941c1d005050341c0c40090702003242d8551800041314541403400d020701e0300c11b82e400303900c04044010600c6076404000c002462404284445000c0c6027034030003025151340c0a01c1c4038869012440c000083c144040102e2403041e1100e4500c191403014400358002030898002644d01c9581c00da451 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 529175440 1250 529174190 529174199
    0xa0c031106090609041a040509071a0c0c090403050c01090803041a040206030a0e010b0d03081009060b0d0c11010c11010b0a0b0702120a1502030f130309060e030322 72
    0x3810510300e0206640351494405998041a0709104a40885001d50765076180f5614405204c1007541c2c003102c0c02002484141004441155540702c6409850a2002e02050030000c2d420b11004541c86422910041c25078985c00b6800c1014040c002032054040c04010805509211420311808010724070076205281c80707040074140703400c800d00365823498080310000d2414003000d40d4440c01503075401883c103480442d503640100501c502500c1881181c1380c000803016000c00405401000032449071182e035804840e042e40d0341c405242590b03424440d01210010801407944a0011b54004e03041b4528036061034400c0b070303200030340490850748060f0480c2c1c0065641c10304107507102028029080341d107000b242c3c140c00c07482c00c020030102d26200c0c048000748192400c0020300d583c0c13441445070f81c0c41c040e01b2a0b1043d0700340b000300701d00718042d600c00c07541c1882c000c5d45c244c0054401e11984240071002901940c6190007036042c001d05565600c0c00d4a081030b8544010701c000b80c000d00800b480700e1101d07107034035a0807030085251 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 529176690 1250 529175440 529175453
    0x609030f0e060c1209010c1505040b0c0313022e0807021b0112091a131b0305030307030e0106050604080c03010b0301020418090305120a0c020705191403030c0a0c03 72
    0x4008500c0c4220350820501030310910004220b0704e40088400c9180d07854001400607582c1c2150004018070141124081400d0110341d9408144103501407600c00c8004d5607080e0403c0401c2c40101ca44070562842d502081d00581014090303004002c0032400b8aa200140c1c41c035003400840c01882c80c20000441000070804465414400c1e980401c40002900e00c215201c0000601181c00011045020554a030590f20520040c10700b41c031004d0761b00b61002e5400b804d000640b03007a47e01d0030072816181940b0410028840806910180b03040b01e810070044d600310348a01c0e00880291220510300c3e4815929860081500c0d61500d00900007040b500008142c0203815000341400c1d03a0203000780c0e40c440d1344188002c0081003090a1901c240c004049000507840c44e01307107400e54880c040c1500b85031501039030360100603542c0070951140b000766500b07408841401d90781d94100301d130140c195281d010714250414810805400700f0032255900b1400101079a0910340e2085020b803801030104002d80d2000007183c1c0c1002070004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 529177940 1250 529176690 529176707
    0x14090703170f03130203330618010806010e010503120403110a08011805120c030405221508160b0f0a14030c1306030203090312060d14010209040c0c1e0507030609030f 73
    0x289804030305c0c250103100300c207c01004019200c65640030720300d001414981e50350402d58120841380000c01090350b1180041661268240616650205c201d0004116071600040b00051440401002446c190440e5103100360890000c1165400c0303910070001043c40c410a000d1001982194039901ca0711902030300b0054030b03002c112108018203080812400e0001c48000c4115000d440c410360702c0640d036180704103441d103251418081759080b0a140071000b6252212240d44103044030121011a00c0e44503520010403a104800e105525001000f0448204171034001406040d001d0303454182484142000320000c88107a000712002c000901000540d6203030f8142910382c4070701420040c41c0c00c500350300c0c100700d519035130b0701c910010180700c00d600d02d0014681c1e0703480245240c901d0350701484401c8240a03240c421070107504101445445907061104c40860244114101d81029800444c0050022165404504d03281c991032420384050003205000720100d41e86000380035800340710707640b5143c0018005400400200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 529179190 1250 529177940 529177963
    0x1415090406091a09241509071101060f0311010f092306030a020901081e0c1b0d02011406030a080d02070606030f1103011107030c0b150a0f080114090703170f03130203 73
    0xc403038818880050211b0780004028032080d6603400c226100c2c401c0a80d1800c40c15920101700f50300700b00000c610785042d00c2618040741d11544500c609441500300550381611032403076000014079441700400c2201c0080a0f805110955000d080300c074040480c020802a90040f620800b0b0107400081d130010b5075a00240c0d103a40100c0d6012032125442072100b810f40d00401c09802c0b0004a140030401c2c0300d41c00d08014104c0403c60f07044003120b482001b0040040e0203070810b004031022006101001076564207003c03a5106405921003146480e000000300b800c802900116401c0d14815030b82e600100014070145440d10b64140507014900340306024030f00b01420f451022950407028001401a0380000c0d8028109151142e40080040450b5450f00c4078010b480900c00c104a9100342d40200014503900f080680e403041c1c501d600020700406404da00341c40d10020f4203661801c401ea100380c40800c00700d1001d0907060614030f1409825440d080c1c2030071001d5019002502c0f0242c80d404408031800c21450200705408016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 529180440 1250 529179190 529179253
    0x11010c082209060e1905010308031f0e13030210020a020c0103200403080d06080d05030403110a02130c020f030c030405100e150c0c04090804140a090608011415090406091a09 76
    0x2981589e0324a5050300021704088038860080d00000d2041440c07024000c09060101024806490034102d00c1280c0b07200c2007030580242c01503000c1c5440c1c1d2800ca00894030502125001402e80700343c400c00440c02010000344006094451389005912164100000c1c00114000e0300e41c80d840d004245408401c50b0340d280d200384075951107080360240442d080300503264041c0c1c0505007081007640414507541803103219507009502c14031079100c900c3c0048072644403c004a038140e08848c0341011419000e90fa82c85004806000f91380107000c100000d16054044400c0554586401c00306654948041080304480c002c52928080303002c50401210b1408120380d118518007104c0c18803091006441e0181d280c030490040c40303002540b4a01212003a203940c1d040000414028204202655441c3c070050300070883c60001c2c44202c003c0b40d01113100b50810704100354220b98020019445901ca03655601c0c0240541070044540c0340c0340700c9503a80403212882070709110b4140080035100d42d50391540201c41c40c016481c6d038003480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 529181690 1250 529180440 529180451
    0x510080d05130905130f080307020705031b19090f02071505070e06133f0510050712021c0f0e19050a1e11010c082209060e19 55
    0x580741ea156200003119100b5400207007036103400018901404180c1009080003c8601251b002c12280754011441003078a50700307a900640e180e804040c0c0760861204035a1500ba0210b00403030b01854907003407481c05075406954041c501c0f580e500302c0d0000e648d4046000c04006501050740030500500e8058910140d451040400840c50211005003624100b5596207000d050007141d0340c8008170058401101500000c4011003025144020000c182020080041b00148006501c005c201400c08140d050f800e9000001d0200070400c200c1c00c000406009110a0401000d4585211502e41c60f01c001e040c460041c10741d4603102c04121141c0d00583c3c01d03041c03d81ea83da515103049400340108c0818840c045020b0b40d540e058005c00c0d5801e00503c0e1020b84440500640540c004d07428205081000680c811445501c01d1003162824000540f08170003800d0024008101c10401100d482c4070f503001441c1c19500001101d00c807640c940b100e8101321109074200c001e44192000610203a02d60155035100060f041d14002e01c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 529182940 1250 529181690 529181707
    0x21c0512091302090102190512042907080304060e0c0604090507020d1e0509030c09090303150d030801032303270a0506090915040213030213061410050403060510080d05 74
    0x41c0c410040c1140c142c208022907009080240511881d2080504a110652183d4468140745580106041d84241c4501d0b010be0329018504583e050329071a80d0030040050456840e511600d0280203440e4050115000f08007040300641d45c0c03100600041c1041001c00140c500e8090401fa20781007020542000b481204400d41c02d515941c103810301c4206034185443c6403141052008289400f41d6131a080ba804041141040122032001014510030f002c600400100c0486010070f1181c101000d40d0060300203140c41c2c0052000c150700d000001d418a9101551039030446403000c0c03242c21500454120248078280307030654035888840c890f454002a10440710f0100c160700c3c1c000010140d125500301180103031a000001084009040e2001440140240c4255520781c50503095a2a10300c65010880c814202d031001c0020204540c40781c1c40540381d044800010349142c200410010030042c1d00017008101c000c00012001400c60300070f640c060201c4260359240316042c1030a55081035040c1c4801e0042040500c074600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 529184190 1250 529182940 529182943
    0x90703050919150614011209020105190c05060405030318070803030f1914060103240302060c0309060409050717072102040806090a0605060a030f021c0512091302090102 74
    0x40c518100d444078803401e405515280c03c1c01ea41d07180c00d0750951450940c00254110f40c0340c0c0042d0040000741d81d400b14109204184c24201d4400317083c040e0010301e0a0126591104602c0c84080c5450003900340002c134680199509454100b048500b110a41c0000c41880151005001801c1501d1940c2c030140c5001c40c10500c1c0303140d8a0000420369103a019001c000b04080e1741d101d0301c031031207181001441441054a00030380e150791000d007a1049400640382014660202e29030148502081d600310101e5281d0a2544d020008141c00000203444540000c100c000750a55802c00204020210440080354a02c0c3c0058003800440c21000c032100c07000e003a034041103202940105100d155030a55801134101c3c3d981000c11034000c2c011070300328030303803622500d81400031110300092a40b82d4580f05480900ca95078030001444102881440020600750f11001000c00619161340415600c604154000e0021f50154039001d1a1400405801854002c0080d0b04070a0381422100742006c600122000d40c60700700c205d00000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 529185440 1250 529184190 529184203
    0x40803030c090d0f03080106020d0e0607030c0204060918020a06030207020d170f0705011406190504091505240901030f030c0f150e1605100c1106070308060907030509 73
    0x50145a00010b0102c603182c0c0c031020042d18407604811104140015882c014000460a014950240c4a400c41406090b84100d0b1400803204024100600304242c598054642d0345c680c0c0c108a034010388650000c94902018828011100880e06481a240e2134500512002c100b13280c100008141c010450b59001d40c03102140c07201090390002c0c0510481a0b49600308140340603121550002c014002102010f008054011041d174130141d500060030358950000f003040c4071000d0a80301806000300c0e6400c004c039242c50360222100314041e0a000d1040c10191200d042212000c4407c403d5a2001c01824445404013042031454a18281c0c1c8021165040d9112210b440080d601c004041102450300c0c80200110103098046041d48003100f0440d0040504440380a8003414070008058401c0304542d010a03465030b4040011100040c1c0800da00040b21881200d1a0b41c0d50310042d901030141002402054031034000800440c1e0090340d0300369250626104000d414500507140e00d04150a1100740011010b01103480d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 529186690 1250 529185440 529185451
    0xd11030103080f0703030605060d1425110304030c08060106140f040512030d06032102030414091f090506011d0906062113052509020a090b13080f0304080303 69
    0x1d54413401d031442c1c22006032200350040c1d40c0214004c107000003188080d410040502c1c45442ca000001d0f9200300032880c111100002d24600c0b08803503034840014900511200400c01c1c2000e05880c9032a450340c5800182114540c41000319602550040000c654840301074001d800440040381d241803c403581c0410309000710300446d48203c24400c03d400307040401300121103442c0c0703145405000040c1d8a0400c48250350021030301ca07080311a200799030307500d9074800b01c121741c01c1e18200c40c00c04034004911414829025801012683c0d80c2c1c0505204c808012840b2054400408101e0004134062406100042581d10082c2168a41c0c402c00408007005580d5517915076400082030b642c8a40315210f1340482000303050780614040c0110303400020301c9100380c501415270340c12071301a104441c92042580521840d80c2c890341140054041c1d444814811050650024010014203150149102e40c503103041c4500c0398441c0b00a0312104144400410801e14140401c281d1045810065030501d0720745070106480c1d00c802040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 529187940 1250 529186690 529186717
    0x1080307030534050d0f05030112080715021801050708030604050a15080a0b070512070806150c010218031642080907030c0608040507150201020d1103010308 69
    0xd031a083c0c0f010303440100750b452040903010340c80c00c260b940414224441d03c0505035036070f015a0040e1303495103000781ca20a240d005a0f0f5101881c5a280c84e160b12080c0b049210115010f03c0304110341c0000c01ea032840803030710488607224016270b9000c4e1004038440305261542d030941405414022580802d2628064980c00b0320f0642d00850303256140b4207402c0051582c11004042c5400004c2e0100744c002c0c0000d0351a11070b51161182074080d455290007901c0c0303401800d0484180005020019040310b114030381564005002900c2508800c06603c010382031f0303400c034040c0030f00d01d03a40c0441c22900551949038130400d581170960103801043c0659154030010030550140b12110a00d40d105140070350a4440f0101103074400c200d0158040d080c151013500d450b13281060103000180c9000125104c0c0340301103046c0040b2540003001e102e8040c07130301a0940d940700008000756528042c401e40020246c0c243c0300a00720806031030b0700040e503802d00740050008a9000d60868401c9603000d200510000f8480c0080f1402c0c80300240c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 529189190 1250 529187940 529187947
    0x706031b050a030e070f080703030207050d0b18030705070311010206060103050f071d0406090504021207080a170d090507050a17060a111e041503020c0d0f0c02180709060206010803070305 82
    0x1610b19181440e4041b0148094400d00042e403050b0210f03040c81501d210fa4242c070358807940d5000304610440600342c0a85042d60140104030b9100920310b5503110b003462407040d131781480c4040d180c40b400c021031540203559038641c4140c00801580d050051135480300313090808204a04280d10340c03618000006042900340314160340c0104444082009010303102a00600c1032009070f48413084034002c0c2106807407c07409848142d10102c1c00507004241c0d9000d13030724036900034040d101c416118407801610002151307003400002c0000c070f5283c2401e40140119680030340001e000c004c3c50300052004103000c43c0c0c85103000c0c00c0c1e13450000400f00008202c0075007141940c4000b180e0075038200030301c81d07941c4625840d04000d201d03071121950000c1c079014003904c100c500d885074001505d081d900048d001e92003403c404220581092100d510498010662401c558586280c50f82c0c00711815808540703070100c44d0241d1700a900340c0000b000403c0e43c2c4561100041d01d201d10141116526104036640c1d2401100c10080a02a020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 529190440 1250 529189190 529189211
    0x9090618030c0b091509030408060106090308070b0712020307030b03060702160b031f12060f140414010f1805010b0109030c0b0715020f22180e0109050a050706031b050a03 75
    0x1c0201c000d6090510505c0303160b07403c090b00c05950fa5401440744039142e0190710000243e1600441c0d11a0031290010b03000c03803901e40c1a541700729014100406003020300c42c403e80300d407032080c3c0390b44003175071164245840c0003811842400c20907150a2008100c0b00441d40401d40c86d01c19405d04190b00000c030380f1845075580d20f90303e51029000d400c9040341a1030b00b14908034000001e840b104100d058000c1c5000c2c150401c130402c0548414800d66402d0603e411043d664100802d0001e44051040b001440e2900000250800d4105000e800c0c3e40340086401d15200b05141a88107014080c419256050002d00f01081101d203181d86200007540d042c821900800c1d80800d118090120f86550440d0104071100210754560b502c015000c03140d0084c00034941d0010810300104c00ba01003648404084e1145085111900d8524501100140604410300c2c249075481e51140d500241040141c4108140315001421400741409801411105c100c0030302407d451456054241c2503030410708031b90841501d46404907940b0f100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 529191690 1250 529190440 529190443
    0x61406120d1d041407090b030103080301120501060806090a0c09020306030604080304060f2d1413060f0c0903020909031c05070c1a010f170c0409031809090618030c0b09 74
    0x151459a000350800c1d40201c18900c41d00ba07005c1c410044c0d85c03282920240c5501e1184041d0200f400b0060001d6020001840040b4685005441c441c0c426000894266101c40000f8140101901d110001c0d5000d15180d904210f00c41c607624000c0c0000440071425441c03d80d0009544080140c4050642c0c0343c00808a03040c00f6280c0c1010400d101050000d014180e00003241400c21108e01003004042c3d10300e611081c48158660007030902c52200240440701c2d5440d00d08504845400c032a00403240d043d0f8944d24000c0088050041003038111007500c5032102286540144017854100404015080c0c004006c000848446016600c40c1405d8503840014269102942502c3c3c180796000003074074103030760303140800818642e56402c981610107234490340d00d480d56200e85480034030a018018000b1134000d11a000300d9810141d1262188502910b0050b0804c40c1e1501e06400e0001c072500099030702d60702c0701101c1c2d0500c8100c1c0074201c03000030785000c0300e1120078068400030300b000d0190304010b04c080402001300301031060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 529192940 1250 529191690 529191737
    0x20318041d0f031e0a0c1b1805061c0b040b040f0506090c01031d191a090d0815241917130305040605030c16061406120d 53
    0x407400c484400d104445150394903082500d11060598a04c1e08840c68070308910162101c074403e644418400302d28643d0b580955880ca41d12154910b0015440010780100c0b41d41002c10a0320705101c0002c503801c081c0d0a000c600c44401010440034040341021500244a400300c0c181d201d034000110b11999207a5180c00424034032640005091743c401c80003489010200400c0d00040240300b6201045080741d01140e24016010070100c2803181d4010b000c120125450b43d100c0516200c0c444c0c0100b54103800e00c025081010745003514989055408400d01242c41500b0a40c07080d04407903486081d1405240032000907003201f410541c0010280c0306000c0d030346203000403002a14141c2036003190b443d40680245800401070908400e5400c4100001d0004c40c4404c0e10b0842d180d6502c50300b50340d038a0320f41402c024094a2980c000390201444005c100441044200320310050700400f0700c501d0300491101000b5104c0000c800019110303600c01c0300c0301500110311010004e1441c4d00e0a003641040418011058900c1c408440c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 529194190 1250 529192940 529192991
    0x180605040f020d0f1a012f0a031101110d1a03011107050601240c1109010e04030f0201050702100c0201060e0f06030d0305160c05102a02031804 63
    0x2810070469810780d030718035005066402840107040140802200c81c0c03d0903500b0000d00811480d00c00110401d44d54803404002c0d1614000b03800c0310410041c01e5144081804003100421035035048000c5c01b80030190301c408000c2065003110001d2040c005035240395a514403400c000c412640da510008829500c0201547c0b010401d03008000700710700f5400c0f011026281c0c3c02000121120b00440c00007281c04e446101040308900710b0300c841c14920062820b429980a18001820365120481e41019a09aa5401c0309140070704881b15183c0424286450054489403a1410b060256410001001b1f0310540c00a0000a40030000601041040e10b40d03005a00410302c50300043d04881f01d1404020f5000d01100352140941025070403a00c000c0e030007060880072070300300741d444401706e8203200050000d0500c01c023010400d441c0074409549550702107440c1e080885402960102c08c1d0310b41d601602d045003401507490300e02c00c200c0d0b0000c3e61030542d032408500302c051505040700748941d0340c070403620101c0c0020b03100c030301c2c1c000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 529195440 1250 529194190 529194199
    0x702100c110603041b0605181807080c04030f050c0405090c030c091f08030a08090a0305030a2d050711030702090117210d0c1b020f19031a060118180605 67
    0x280c941e500181f150b80314240c05c0044909807403190756603080402607d2114a40c4103048042074482403405c40d455a00900000341c103247c18407012020030f2448001c040304070720820040044924610030b0000391200280119080d811a804204043d100440c04000001046a4118042d03540c050180440c0c0751108200035640200d1002003000c4000000a1030130000d1a01c0700c4660385e032031401144c0d480000b9000100043c80500c04590400302c039421803c3d00550000603541c45c0344201c2494404a0304440d041078031141c843d0180110a41c00980500f07400300f500c00907500d094116008946080f034184228030f0914412901c0c8504220103100601405480c1030b0f90510301c84a038180d00d503030354110003503c8003400d1900100010301400b59150b000010012507620420f940140c00f04040e1050103840550040808010017040402403591000a540f00c0c8009100017520140c41449043c0b005100034140300c401540342c0801c031980c820b07040c12668000301041d480c4054040d80c00250a4039404590407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 529196690 1250 529195440 529195493
    0x6060c0109030e120706140f07020607030e0f03210705161211060a0914010c060f060314013809010f06020c010e060901050f1303080702100c11060304 66
    0x20583e111a00662208040b528018411050070707030241c42d80450300c01c50307000c1003c1403a21303c1910380c00c9003c0c050307040b03043c2492402c119a80e004200103a011000031800604910024a5a072500c03203124050340b80b064006012407000e48110700c1d880b22000b01f1031024140086070ba4070401ca010841a007403603000c09a000c00003552070a00c2c986621261001700c1e611481d00c0e01c5207946040800c00d60344500069600c410a841c5402c3c2c440c20b03e090300103555810000810130346404640c413405804001c82514000089491840c00c1008101103104242c031260390508070415500c040705c01441e0122101300f01514401040a00d80c00e4900008a00441d0014034200c00040c044134660340c82c00460309503809031071410180748011a040910920130720f61001007844807201552043d03000e80b10504503174800c0340c944041c0303a800c0c01405c102584211000300e00003c2900c110300703000705880e00c17070346803400c0c44035081000b5901c0a103040a44445203005500210009050280c5084c01010035000032115070302c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 529197940 1250 529196690 529196693
    0xe0f0406050301020d3213031e020d0e010c081206030a0b1510020c031c0e0409260415142709090a050304050405070c1b0f09020702010e040506060c0109 67
    0x1a105078140190040310ba03012800440022041c0b01401401c0c928188106d5681c02d00d6400011505603c2501040007400101c1c0e0104000302070b20248a056800030010080e20b0b0130010196071800d6249030400a601596500140d5a2001c0d554888a009152810369071082d010070300d004899031010308403031b40b0441808526941c504140382d07240c00950704e501d40c0c0c142006091780d07500c03403400145826601a01a001d148107034424610580249031800c450198441800101501d0324410152543c3d2038a51860203012048005c0d0f501441c10f0701c02003414146480c54401c201031100201c3c00511219a01401c0006800d00403607861200d50940e0100105148480b510491802070f4400e000b01c0401001c2030904200085140a2540c03010095140c9814002070001510010700341c9010701469040b184005a50100702c1e6103108a404070f4255280d15011080007405072950210440620411181e00540d81c0915900a4400e06541c0030130542c803441c0226129109007502c161743c65103040070480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 529199190 1250 529197940 529197967
    0x20f070809190f08061b07030809011107080d05010608040f06090618050c0405010e2710050702060a06050a031a040f02040510180213151218021f0e0f040605030102 72
    0x20700340d13460b02c2c0071101242e584081040003410754100c1503070001800c1c03002c2c10000c2e108030b80142d8840d40082c00460868500f0110340300640041c0011180760102040002a441c0b1ba48500346c01045c0030b00d44010a03040c0b940ba2007506000e05c1d140a09081d448100e82400d00240c0d0300700d04050801c4402100140e03966041050710781c0410890b491096062400010350707121900c403018020500340e001c2e00401100c450214031041442072982200d401140700c80248900c4510559104031031640184c166403a00180030340403101c65401c0584030301083c50003480410600000c528105c40e01512810640c0c941d41805040c2c4c15800c0c0c1c000754444c3c02d10041000050100501504882d101c0700103c281002d030505207004e038041c2c041c4189010f240d07017000308005141900c0c00411000301c0d003814980c0c44c1025101009aa881c544000200c00c10707030075001c0450a0020700f2819030600305607004441e8455000090034084c05035146071040240081d06401035503240e002c48000c0000500856031400a801c001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 529200440 1250 529199190 529199219
    0x309060d0f0b09100b0c0106050d0803060109150c030f0c1205040f09050f06010f050d090606060e0301021206041109122b05070303110405091302090a020f07080919 72
    0x7410a142000c0810b0650304040c95040e0040161601c40c0c014a800c01a0300c2c4002e4100a04d5050950b40f503d03c0000c09440340700003031003d18020481141c6e20714100002400d03107000395120900e081401c80642c0d0b1403e5004903a060202d40c5072a04904031860707403c045810741601c10020b01140f05500f5000354060700840184104e07002510712954040d40ca041da802141d40c00c95039140c14400220000340290f03c1880d00f2101c000e068189141040c135481c01d49802c0b00d011043c21070301181d844505012258201e548150315000850080d440d08000100c290341616020b07210740d00550702c2c0c101e001140c0000c181070303c0210310007810b9206240d401d1074400c0d603212f66541c01c04038546020103401c1d10380240400d48080020036a1901031502842d1f41d03044000301b102d626504100c0005000c0030402d641d40c0099a4000c8074004c1480039040f105004205c1d401c40058504c2c0840c0d48100f100c00d024004007829036400c0b81c1c0041802d40c8510140c0e010510030381103820950013008483d400420300a162a0300d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 529201690 1250 529200440 529200461
    0x1b3e061806060102210903011e05040c05040209031902150c160f030209070e0103020f0a1d01020f07030f02030703120203040609090b01120b0f0916031b0507080c0309060d 75
    0x31240c06840b50401aa11a000780041032003083c40e864903801c4800344400242444e0030081c00006000d401d4940c04c80510203052641200b80d500c0c3c1003480248900703540c1c11805010100c0741145132008030f40000303960754445ca00300030744c00c0000032610b020755a07203d95006241c0c042c001c04d03694468400076956115500110648482d111700340e40411030f040301204601c142c0394043d01800d6280c07607102d002ea03800380d40080000c7c1019003c102d201c1440f2118409001c0941140e2146030007583c110900481600c0d41d0640030b41158080c01140410740380000f100000c90340c000100c0302080720381e800407a05018158202802002080c0c0d442412558000002e10454103903585000340c4503100d020f60015250910101ca00080e00070b00b074102d50001c0c95204850790440284064412182000070440029007243c900184140c0f03000340b142c80320740502030520540036001b082c03451141da50b4405172160082550282c440b21002c9042107614404008035115418000c0170360342c80364628003c2e80082d1050340721 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 529202940 1250 529201690 529201693
    0x605150405090a0c3b072601050f0f063c0306060a051306030519140121050106030506041502090d02060f070807061b3e0618 55
    0x7000c20401083c03007446154860b40b0410a00d10f0603484034025a2104c0c2403001c0c1d075020041140c955021078502500f05101c2400a1100e80740407000500b84690031000040e64001c0710b00100100e40203c3c851605444080f512008110020408109401c0351b4107061900107400085d0b18035a1410300b01104040c0101d504103100c0d200c83c0c910007035400c0c41c050039142e44c2c5c05414004541d0500d00b100107400300440d203150490a00c9550a003079060f55200c1c1d801800400d03035074014072410318080d201e51003000c202050144103444102103c501e080b0303414840c0b065914544030310880c050b04c03524080b80300ca94101e0002c2c0000c0e40c0785d041c066142c10041d00d0846e010b4211000600300b0341101c1c0240d404d0003400418110011066809204591b40003210140c0168000c1000310005074111000c1d004240c01024002480208a00c40e1030514800304400c4c014409298811100c5107240c2d080c0d070144610000e40c40ca01640c0011600c80981c51a0000e081d20740554810012150101c07203200466102c1d800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 529204190 1250 529202940 529202951
    0xf0918050411030a080307031e090b0919020d060504020a0b0f040501180320010519020c040b04020f0a0c0807080a0f02060f010602070302120309091003060c141b0a06051504 76
    0xf0107a4a000c4c5290040c03942c8820310024a6680c000c0e84131a000c003001801004140072002a01c404503202c03d102181c0d603080110038014107c204100c0d03585402123440428201c80690303000200040c5030150f004000c140c0314400a41152165150200204179000352161600d154400504907904640140d900069001800d602481d60045100c400c6030b8001646041c9840343e8460b01c020100340045442c1840340030028400130f500c5028401d0781003a1141c1c02f8004056281e401c000c10398000101540c0b1450050000c42074203c03812040b1502914981051221450b107031800f0710681c0640c03800540403203c00b15243c0b5480d90003000c1025066020760903611995240100e140c078602003801190010b0388000411300040c101100c1d4441c2d02d0030048100d0342001b03800b10001e10b140d42e08407400d02c18410380580820411882c0c0c02200d02c00a00c50070012b500505881d0034400f40c4c000c20101e00665803011180e051000ca0034000e0311030140c2c00007800d00075131814200c00512010040b451501803440c02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 529205440 1250 529204190 529204223
    0x13020a0c05150c09060c010e0f0a0201170903090105070312060e010905060901030302060c07050c03070f15030c020c1329030d020a02090a050717070c030801050603160f09180504 78
    0x804100f882195a11240d0b410901d05400780000e82e008498030262540d80c400900031150420410b550601c45004020b0100b030340d181c0300051400320410780171545c07414100288048400c1c0801942d0000301c0c04e203003954484280e0b0404540c40780724000304070341240c5003110104004200352401410b0b02c00442c01400140c031118280883e4030710910000c1c006812140200c0e54a07a900c9005003074250090040351520304503d00041c3c20301007180e000c222044040300040029000300340c12054455000e04041014420030000a52a03e0992a03403d200766402009140302c0d02c5130b036000701c6480010810003c1d14440160360050030b65a460f040780d20a10074440c04c0f107051f51000a81701410741d03003d0500002600c0351044072014260190011087c41242a0000048942040312078030070802640c540789182e4803810301a010f044181c20140c0561010010407450b10340851503002c03280803074503200000f52040c93b412504107100742c0001d0745188446100b8008582d160700114040e03806048114410b8892 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 529206690 1250 529205440 529205473
    0x30203090f061206150417010c0f0207080604020f0109230307090905210702060a2d0e01080c04050d050106050310050609310605041a07050708030613020a0c05 70
    0x45141400800001c440051030509207403258000d40d195405d00e0b541083d4840094070110a1a0001c07500c0c0c0da996114210112980050300101010032400940101c80c20703c01402e450700d10041000e40100d10707105400d610340e40301e482d0700401031892000b005003e18030605a24492144d800c450b510903c00e0980109105089204008a40780c0c004003d000b03520145080300c801949500c0310f1041c0a10a11038800580c4400c0010030140040c0c0c1d460b405c00341c10301d078036054440f820320b00b1030101c00200c1810090300503000034862081e84400d0800503410740d2141040100352189401003900101040d82c981d040050541182c0c083d500100c0c16222519021700300d21007200c1c4111241d503889060100070410320550345200c0e480d5520340500b50104900c1710040b0308040ba044c0c03402100c2e40743e0340c2d80401052113000228082504000032540d40c8500b051980100136014000020701422000004240260b4030840c0d15040c124003100299142d02400304081c0074400d0750755050b2604d00a031801055450f15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 529207940 1250 529206690 529206697
    0x1f020406051204050106030507080a20130905012703080903031005060f090a060e2e110a0c08030c0601090203130f020301091b1401080f13050712030203090f06 70
    0x1400c0c0d850600b402c0d082400340340001d01c0030303005907100c2d580c400e03000c0301084052142801810410b00240310a004d00e00d8042c41003074010102202480c0510f010300801d5a03800455000140e0b4800c0114001c0e20b2030030b00c02d0040c98015108c124044103040000031203e0700c0da02c0c120f0700f10700036250101984d8800107290703140d01c012501485001e20b010801d0080e494100094291250f0f845000c908014280000c1040f0f034403103422000100f08640c882500910340309659601d980210704005251180e102031564040380000340c22070034803081e81e0622200103400c02407500982d80042d40c061505039102051500d03a400708c030b0700c00d0303250081c10004648404030780210381c000e18607940c800288030001e4485200098154000700e9065490303800c0e01000c1070240d40f030604001c1502103621400740c68078000c8280300000500d054144140c903070800041d040c1c011086a48860b8810f500101590140b51040c1001d407150414600c034200303003810005055000014055030a000e4524088010b08541088064003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 529209190 1250 529207940 529207949
    0x7110d180b13080f1b030c030601091109030304170c03070e0406020a030204080610090b10122d0e070b07150e010e100b040b1f08070e060c1f0204 64
    0x61030520030040516000020311100744801c0228407800d03110f490090806403401c22a08160f03000c0c20844001e81418100c41d240401c1c00c0700200700e081e00010102c0c1c0c44000510407008000d0380c1d03000642c8424401c8045400c5c0d041c0c0101901e40c1e4a84443c121000503d18026564045c4a81000d1003154140000c40da800d80c1c90040c0640415a0343c1d981d55806940705842c10703000c1540034803000503900400c00285004a0118001405140c01d1110b000c00302c0d1401401284660410301240d05910b4100d1303100c0c82d40860003580454241310000300e0910591101c543d4144c18100070342c440d20074403141e500400c0318405a50544003004d64030702c41c100d400d0003070503400303041142c0105022491080d140d00598244440310004a06031440d14403560030141803501c8012610f480360042c0b40b991a040c8148000180c00b00c400c603010008410b0540c02d0a07955a17a26014050310001146440703002d0010500320340b01c020821950345080c1c0950725150a08052441d0140e450054805c240540c14000c0c2c0c3c040c0d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 529210440 1250 529209190 529209227
    0x603060b0a082116210513120c030f030c050105010801020406050a08060424140a0b0702010f03020f03100326030a1503020405040c05010f09060e060a031407110d 71
    0xa900b210300b030b10f0404541c40100c1550100900718190303410503400d03621280102c0b442d1030040002040030b81354006a0f04d094042100c00c0110f24100044140002c068030804000c01c1d44040852401c119a0740060700040d0003103111103048010142d20402c10560284103900034482a41d803040510b09070b01950007501f0204c0c80030f0208002c010f2080300030f590f01110003800410151641d40c060505010404d0301d6501041031014203024100c2a03c00b0607400c2e040a5410403602458400b25840e83d000f0085d0090400c49107400540190f4800e4040d00c40030484002c0655680c04c1000894a01d11124030040707030610380724020b40030880341c0d10244103509200c01a034a461070b6104102e441c010305101852021110080002002607159403045c0380c481c1744950303805034806040c80c001600c1505c00445400412110440c1488269072000440c0c1002c0815186180c440c902c11100380d01400c94403c0f032289010f840d004010f5410b80c0b1844c080804160101076a10b111300c280c6040344d0310440e00c1940ca050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 529211690 1250 529210440 529210453
    0x6050a0609080607141c0c02150f01030807080418060e07030207020d0b130f060207060b03030309031804110d0f060512070e07022a010206060406031101081b04090603060b0a08 77
    0x14500900d05d05018200c0001070030310345607078800e0743c4540309001000c1c0d00311182e0740d90043d80081c0c0c041085c0030f00c140c182101da90032845c2011000180d40414080108044000710f1001d0070804c035103042e5005444115684000c03a0074546a100050460741b003140a1510800c0106001c507010784202d03200711f0b0700901000502c0155803950031040d0001381100ca4882442038210020800c950000300003240b01c2c060140e92034a15042c00000d4a001514a0348a50420410311042c00070020469900c01c9a0510b1394a070148000300060060190141060061700c001540c84015210765000d224920403c460802c402c42d08c0e0410f01030f07004403102c03241d1040c2d802148203000c1c0c0b03d1007880740b84c0c0c405010f1044a8005d0704210380c0303007090303118445a607007490700e003041d01e60303072580c042c0b0240d5400801602c0400c4458a07540b2100c908a046800d00c40c144030700311b0301181c0d1144e403041858000c0782200d410240d48030380d00c200200040030207100a8038050300e040300c2c141c110f00e802000303e411602c000c03000f82034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 529212940 1250 529211690 529211701
    0x11401120b032a0a0b030a0b121f06050a06080a06090509070e150604120302060a05070f0c0309091a09010b090603011820120901090b01120507090f06050a06090806 72
    0x5000f40c984843c1c841c803590040d4194100ea44903a0090080c10380c8080d9a501d03800d0220106090707500c4450301c2d610501c12000c4551240e1030000c1c1020303440015251280410309020010780040045810103508102000c0780030480a030000002030055080100c20031002e0394070030416046070403d9440e2881d5801402040188200703004100d501302c5910600301403034a04020003e031032540203034014415243c00050700c805041d01480f0242d4041d040e10000d20162500d0b250041400c2e0701a4005020300c42c03035504c90ba050603c100920303c041c280080c070800610800340e11000c484503488800c2840307440700c4d030b002103040d560610503142e03002005080f803806c44e4201101ca0400c2d0040b140c7c002c1e42599180241d07134a881041ea0940c045400401c0c0c0d195940140c803040c084100720060100f0680c0c0e060441400000e00c2d1402554115800708030303d41d00015461074460306292070f50740031840740307420301050309840707040c5a01100032101c048072081600b55031450252245c509510074179110390014400510f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 529214190 1250 529212940 529212973
    0x61d1509060d0204090c030b1203160818090901050a150f0303030b1c0f2904030318080315010e030708030307030203040c0504020307030b090c07020d06180b011401120b03 75
    0x5005145000d030400c2c2c0c03901030070406c41d04251041000a0345a11001c3c010b824082c2c4807082000180015601d0504142c07904000d500d10100300802d1400d0008411917a480c40d10444203400070020b00030803182c10140c2c61a4041e00098a50f138408c186082030040d00090300840341400c43d04c0030750ba4013408030f1440d1810780081c8021380707000f60050026100410606003041c6982e070018891032071004050b40c03d090040b4500c00e0003800c001c603c01c0100400c4009554001203550003585440c0100e5002031003c0781c003900d01c0304100d004080042c00b02c180841e0000c00300903050000000c1c1c1e103140d0301c002c000040681d06c2d00b1510819080307400410206002c1842500150343c400c1c0924042c17a070643d9540003280403a4070031240000000c0e540d1114030010720b440041760360414600340c4401e0034030342640c00049030f401d500c0600502480d41c620040020240310040340e04144c0e0400c4846055680d03078a40f410100400c6000180001c002440001c48803041b480b0b2416900c9010b401030406c03908a00b40c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 529215440 1250 529214190 529214197
    0xb060103230709170102041809020d06110417010204030b06060f040909050c0d03020c0a0503010b010207180b10170703021306080723090f031b09040f0606061d150906 73
    0x7408000181d0b03004500119040101180c1c08001c138001603550b45400c0b041000400300c9510080107606000d003400243c2da903030f495041c03c0707900182c0c00100c54810004030340003441507900008003181102415501908107501820850740030303103030104065031440104000c0e0320030f100555030200c1042c807091002c0c9a665100f011520720503c1100c0d102d00308107001481030455107508800503030107542c44046074248201841e004141c298000c0c4100414440041d40b200c88034060900f07032401b2410001202c47c001c1e000811900c078090030760240d40499100051014a601c2d4060014840400208101c50f01c079100f142c14504064120744180b6082240446110a024000f80100302e55503009954000f20340300050100704803004d02503070311004801032102200004007600d100ba08a0345c10000040c0500c690070428400464100075240c0e9036207010a0304081060010f006640342c5207021500316008600303451613a0000d00b44030031f030480c501d04011803600564070007010000c052261180c43e04004015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 529216690 1250 529215440 529215451
    0x40e060a050901030f030c081b1603030504230d03020303100b040f03020411122a12011a070501050f07120207020d030e0f041b0f050f03071407021c0b06010323 70
    0x251050341c030703156000503402489000d1703400c80b1102711a000b840d0041003200c140650500020851910b5a24003a00c28016445004d4144401c55007074070501c041d003214107406001c01000d01240318040c1c00c00039070300e030011201e140f4001071407507004c107134400c0030400d0724201ca0343c481501c299076041d6130900c030240003598000040c0400600c000361035140d031510b00c2403140b5181c161341d0410b00c412500e0710084c0752021542803401642001416005560810f0312410342e84010708001004201715000b0949101d105000740440d442d00307090040a91068450324090000ca5076850b60034000421280128450b8510095010401610b054002070040c001c8081d4444000c2c491282441c0c44804102942d900002d00900c1d050f0551408400e1a0040100e15251a803481e0281c144514500d00ca000781c0b0001d46180184000350385500702e1200750b0400c45101540c00b403c0c103102c1d4604180413030a41c200d0703200b080341e410359080005155035102c2d00c9200c068581c0c080e0b01880440c46500880840c2038054030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 529217940 1250 529216690 529216697
    0x1503020d0b040504050f060a0b1e01050c0f030d1506020309010e0a08010f020d0f141807260106150e01030e01020c0601170607090608010e2505040e060a050901030f03 73
    0x18070300441c0e0344034458140b0480c016009081c0c40d0305c842e2035884c103103080100000e000602c0d010240c03805440d020325a034840e20346034110b40a003003402001070380c123805200030001c014441d81c070300e0b0b0821080200c09030810800c80b9030140030902c101041d00201f01854003480c801030340309000704403141d03109400411060501425408070603031070392405403d540b007040d1a1030391181c00041e20803a030a201d01ca4603c1005142e8000c03c20b400c0c21103001c1d03448034005440c0782e140c00d184141c041882e036824481d14008090288030000b04c1a200c29840014018080b1094815417134090001407004407450401d610f54015500c1c0d608101c181c2d030041d00201442c45908120359424007000120070307010031801d03020700041c7c40351360342d81d060042060b03140c04001812032040013191002008103640004c0c3e000e0544100003c182c0407940d40b46180620003211490317501c3c9540d840c00c855480031350084020816111100030301895a5201e50612105003042d20505403c082ca03c001000420950b00a0f047c810303100e0326 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 529219190 1250 529217940 529217951
    0x71809060602030403171207200a1a18120a03020f03101a09090403080a09020307060e0111120d11040b0a08011d04110906030708100615091503020d 65
    0x9a26404032a21500044050f901c002410f005202c0c01214114516500ca03044514022500030600440a000b9021106000c802a50b650b104060240415100e142e820704071002900607041a0021140004042680b08a010046100d03075001450400c041d0700380c04001c0c8610421011207000380d40c040303410340b81050380c01d020034070950701288021070299000c45916042c07182400a81781d080e241c80640b04e820382c20104a071f0032540c4c0343e03083c8460b84a6054200030f200c40d41c0b00100303880a003143c800001d501d8041c0c0100811070726044001c08001e00400c2e83d40210a0080031100f560320542c282811606141c1888004401000c9401025550240801e1541041d5442c3c21410150304240c0503c40440e10160050085030841d006081022a81c0c2018441038240341e107560343c010751201c0685001f43c03005000103515031000c00c4544c004008100456038103801458811000b02403501440082411102d00184110b03c10f1060109603282d010b40240e81c06070b5540250001d611140071008ca031038680 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 529220440 1250 529219190 529219199
    0x10312020f0718050105061c0b04020d021b011b020a0f02010c050303010803030618070507170903030c01020d060609061704050c0406140f090c1e040b030c0a0915080718 74
    0x901002c8010030711000b03c80000609601d0800039100140c00441c050142403000c100000303c4021500b60004513100000380001d15600410b0280c45a2010080c0c101e00010705da1400a0102403101810100e6000804c915002c1d000701000000e04c0c8060000141e0140c3e29000129a0040c1c0764160248141041d40903001d0700c0da11142150800d921100040c0c10220403c1445c0c105170142e41519405d02d5002c440514005c0005030443c0140d003030160640508007884105004010b045800801000701165103880442d11214040d41c081c0301e84150341810800d0002c0c403580a5000030701526032a841c0d0071503a15220354a004404402007083d5568440d2010500c4107403524482d010240001c1403404900c40100418020a240300803980380c01103440ca0304108090b0b000e9001cbd600300c0c0a5040d9400049081204e0302c0300a1300564000d0b03019a41e00100b817165030307030121000705240c5217a51a20f41e03946550b841c048854141240707c00022803800800988450b210b1205200105024a20104074507140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 529221690 1250 529220440 529220443
    0x1c050a0b18070f020d08241309061a0904030503130f0c05011814190305191e0206030c0d180311010b0301060f090e0a170a170609010312020f 62
    0x3148071035465180000c0c2480040b40d40b06030894880b150500041916020b000002080400000c000c0020010070046814110814202c0c9850103c001001c174485405d0907224000101300409040302c405240c81500311343e121031440b6040000d1170080c4458034558462b24143d07a01d41c0000c2003001c0001110984100041e030051b500301c013840c0103090b450206400d10300098401c00b01a460314000c11859881003007500c07083e805d20351a00b08207a49540b10156a0b1152903030705002904010458050000c6060441c2580c568040c4111b014003101e02e15002c840340110411907400c90080c0d00000200001948201e030b010040150f140e12103000109014010401c142180a48000300c0c0028090400221040f10900400815090480c003c20a81c0d240001c0040c42003400d100d41100c040c0c8460694150040900c154a80c40e9004001b04006103241190310240e54840c24113100803619503500400060040f010042c40707004050f004000720390a540342c1016400c01031884030118441c100d2070134901c180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 529222940 1250 529221690 529221709
    0xc0108040201230304030806030c09180102120c0a020d051c09080d05090109031206080a0213020906040f030302070e0c180402090d05012c0307080306030309101d061c050a0b 76
    0x3c09882481d201d04107031800503c1070a010709034503ca0b80c801008039841c3d030785051000e50082c2c0a030000c49510540701d0495800390207911456400742c031a0340104510119490001c00450145600b80c454240b400301040c0d90303e010700120071008540c10002c0c1d1000c9485070340083c100c0741c01240003070b0410709004003030425914115841d60099468580c044209a00195280005452940144541d83c20144916a200400d0340007a00c43c0f4008042e507c00c00714560b04440481c100505560381e101d80317030031a40d80c2d03103101488200c0062050b101b00140000380305205600032842c04501e9840d22424a2450310010800344803035500a07400c20080c15036a8404601a2200307100310300220b0000112035100312441000b01984400c80c1015002d1408120080202c50f00340d540248201d4481d181c2c0b00119156000f00c1208035000240c0400c2040c220b90407100218080c190503404641a089110034810a400380c11000c1c2e40160001c04015a00c1c1c402e07410a65001000c000001000e00c0504000350642d82c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 529224190 1250 529222940 529222997
    0x203040f03080609060d02040b06041a04081506010c12030e161a04081903020106080a030503091c050f070609061a0102070b07030504052b030e030d110c0108040201 72
    0x1111490345100300750304162550342c4404115402d138814a403250104520f4091484024850385c0d840401801c50741e981420b40d00981904568281050f0382c551401546074000e0040011500c602012041940c0450002c0d0b44140c0381a5030f0018810b1302a5a14540718084010b2102450385525225070503040800005040c04200b0f00950340c0340345010148000400c2d840c4004011180410051020040004440300b401c0842c81c0c0080008000c0d007800c90041402d5003298102d802030b01001000c1c10350000146005541002c10707a450b10a524040d1802403c1186d802c00104005000041c6151102c401500c4894024200800d48800983d1000120342407a403900707000656807860024107507410060310028001c0003161503e80b400d5620003500d2800b440c8112427060040801110410211612000d05240b00750047c941c8000e140c980035040403110f5034050300900c0b4156000f410184035050041e6581d404c50060040280c10344011110104020801d0b818801e0075003160034036030f40d10820b50350400d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 529225440 1250 529224190 529224203
    0x60109060c02060c0105280b0d0f0c1a0304110f0a0e0a151806050607030816030605100201050108011821050412030e1833100c021924030f020304 64
    0x1007080340313000c17a00c00748a147d078201103150500c0b6140030340f03c074005040c07c03a42120305550000080d10780390000084075000200b04003100c5503d11030a8007000069402039110740c10007a9400c402e6000e211490040c145107517484800d9001c1002400e601600c0340750003031030303001d0b001c104504c0f00c1c40c404025420950142020401c1000b400408401c02d00c1b641000c3d020841d0074502d00480b5441c010003002002c0c2c0440c11031190248100f030f80d02d000368071500041c03030054020950780c080440040d000300002d100307255070703542409500005020364007044000d040d80074541481740c800d0842c61240d800c1c46400300700309002d8100702c0881c18000399500c240f6941d03c25551550007040840910080104d480040700310402e1010510602c0361403d2080e00803054039400704010326412a80e0400108002c9007000d4000d00d000122509030359000103100d20160095034841401c0c2d07142d0030b0080188102e849405860207601001540100038200381030f1640d1424540441d20740720f04200ca40482c0d00940f03040300e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 529226690 1250 529225440 529225471
    0x1050d05091c050316170a0e01140f1005040b0607080d0603170c1204030c030f020d080f131202300d030605040c0f020316020604120c080f06060109060c02060c0105 72
    0x1c0f01d200d18549005080c00e490658481c0805042c52071b40304c0c0000e840780178640c4d1a0720041940d60400d5105d0f6900d601441245207541c14040b00c503500c1c0803001e480c0b1440d41c0c880304501213101c2c00e080c06010351400c03000c2e020134508a007540351000b568001441d0300f102c01742ca682d40000400e40c800f05c944202424800e50b0b0740c2e41c42c002000c0516180001c0041c006e01c000a100800200d010340d48440100c03a040031807080074000510019406911085c001011101c1c0454400400743c035460140050700040003c4081c1d0307540b43c90780c0e0503160340e00c41d4009503c100488082c1031a65048c40a050100400d40858280c903613030844594204454030704442c1c0000e586040411107841d0500549001014a090210090783c84100c025180c1c400c44806400c0d081c1202e00081c215180c520880b070091185050441d0050340500d40f4400010061141c2c400f24815064400304105021440c43c0c00ba04050310b0303180b003e514143c0e064a041d91004c2d42a0303031008050108041c0b02000b07014951050000042c0c03081c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 529227940 1250 529226690 529226701
    0xb0309030a1d030604150e010905070f05040b0a05060906120a021905030f01060503070c060e01061d01080a020904140307120f050a120b040b031209010909050601050d05091c0503 78
    0x110240e50078882c0760024010b01e211151400302d0300da500690400310799540d14003c1480c050141c40083e640c0106586015241401d001e40400e48809a410340100c40070059940c42c2000182e030000c1c5e031040c0d0300c03407003601c070821007450684028440740401611090400760851140c1e18840350854030001d2450300008c058500c001c00740c8001d251684607040c01c50440c1020103450048410501031001031120000110b111140100032082019611031414403100109102050281099220345516250000384400f8604000d40c00241070b100384000404001c40c145d000c0214000000d80f0542e40b40d0048194140c03001418001070088501441980210013078882e80240700d402c00180200130840144000e5024680c0203141c8601d41c3d040c0180820311003030007030006006040c01c900f682e81c54072840c494220140103034005021241400d80b81d82450325980c1d5244411b460f0101e031441e00084042214038035002c2c055002640000c026012507810801c1c80b0902081c0c000d00c12408070108401004100c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 529229190 1250 529227940 529227947
    0x81605010f0504030c060b01030615170603060c0d1a04060305010c0206160c17280206061c0b130503041710021216120f0b0f01030c020606010309020a0b0309030a 71
    0x5545000007000c1015141c01e4500800c8544c43e500c3c001c2401e5207400c0d203a00300c5d80c420340140c4058440100f5407030312406450700107040184820550141c411415001072410f140c08210140f00711040f000841c500011000c40900078030540c0b059440c2c418501e070a041e0305032101c0c45100051486000005122a00d94030060320304030b001812191401c0d180700a18144c642c0c4030750500c04141e84102e0b03142610441784246401400764101d03504002d6464000d51244502c01030181c61703200980c2d0295903182d2600424011144000900081c2903860610035000040301c1211a0703606c021172182c4250080c02c190354641c00c41e40076600011007560f4044101c103c40c50144818202405220000c51901e04a0600e200d006840201050088004402210744144c0150180b50189030380c8081042449402d88510b402066550f103247c0c000c865051840345c59500a108454034035034150000c084507541c0b200110301070a0b14041c102d80161100b00001149070071240694099001007019545400038150000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 529230440 1250 529229190 529229201
    0x4030201120525020a120f08071e0807020102070c1e0b070c050609190f0608070201020a02060604050603010207050f030a180b040e0a091b080d090620010908160501 72
    0x201d20892400d0240712059494007240805030140408520300310211500aa0400c0400c5101400d00c400120300d05441c281d00580040c1002c1c45901c5048440c0c541403402c60b4810400c6484079044844d038205070344d007680660304150303014881d0f200141c544003030703075544880307156880e80005d624200d090020051070385926110006842000002420401d60341c844600c1c0c00b04511649000310030024080e00541c4403040e10b1400c21981911624034140d907000071000d408058411038000500c4000070424031761041c002c8030000301d4280c0c0188425194801088002d2801800c450713810765007000b078000094001d00842c80650500700241da2920007000010700349002c000c41c40e0100b510814010f22110741124180c40960309400d020780c540782c0c0d4401d100802010300c113030302a00e601c25407020703a5115045999038006031400c0d0030a03100c11403200d610558a208103070250f200814001e0050b01550f6038510101c1408110001c000b14042d1700700d403500001d6610170310341180f104241c1d080040a00c0401d0044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 529231690 1250 529230440 529230467
    0x3181505190c020c1c0c0b0c12070f11011b030315080109030f0e0609090903180901150c08070b2e0605431b05030a0f06020408030d0204030201 63
    0x1840301e0b1548080094a5030100e1034a58810384095074250710480710303c801c0510b9164092103e0b41642d8807003130b20131256001044400300602c2000c41e07102020411038141d513602d59119404c0c0b910110169654103091401101803410000282c0f04c0514100d2414445c0e0b82d60b40c02501d0004869a440c0e4140607049025080f00e202e0303a050403d550002a0b00c41041c2a240b0b10a01e040008650342100180d5588940e001c80ba511154a00510a095602000030020322a089030092401d02844081c402030311030034130a840011007280407181c04213000781a8000c0551141089525004841e5079141a410064604110440c1c56a01000217501103d40519440502d8881c9a07500b610b00716004003544902030504166144509618180e0716491075101010f807054407026100c01040310214401ca07443c4101601c0c1c1100c403c00702d040390615a50340c034084d2380015010b4149918240c03168012001020000c980140d0b0070400090401400d2000c2c0000f12070001e4050380d100d1940c000142100c03c203446 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 529232940 1250 529231690 529231741
    0x3090a2909070608040b0c070c0e011805251103070b0103052e020a12091518021c031106070f120c121116111c0f020103181505 56
    0x103007840101d803c084e41c00c2e44254000da007860340307503541407800f0414040c52500401e40d040c80b60010941c2c000c030400c143e05854801800c1c51481c2c4d400b0301d1840c280c840940748031060b500b02c200c2c2142810790f030b00c1500c1c8088205080510200c0030040790300389540c0c000d00702903c0c24175180e030050040280910118011403040e0400b00b55108a582291460701c0d00030b08a170341d4140d80080c110041d5805142c00040030402501d04201556150506c4624540b403000500400c0740f03800844c00c00c400190f15140c1000f074000d0140d444480c12641d46811903284004168280540d410402c0c82034103041292030b209819a80c1c0f5120070420820300074015405030455010310a051240e03d040311540b001110408510120022801900c40c2190200070711071340da0b580401034900080402403004845500440036410f545105001c1d000b0313080504036050000004003442010760000c0050b61080c0c00075245440030004851080c0d44a50b28003080f09280b985d4076540e20386a01c100105100150100c2c2500c0c0040b40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 529234190 1250 529232940 529232953
    0x8220902090f011103030112021c0c050f01030e0c04050c19020a0308060f0321040b040906031707051f1b0305041b060507260a020a05010501061d040203090a2909 71
    0x3601c151722400140521075802c031550703030381d54255036030581412007540c56842600d65041050900c800411a5402190300031200c1441e050183c0d4420b1150410340310000d00500b110f04d090200b040301070100904107614844040c44014035144080341c4525034100e40340c00401082043c1e2401600c003900007000c0742d01c80d1103d1088aa055100401c42ca810000030180341840039030700c0e282c1440180566081075068020103d004200707001650300c43d1007030340d0184468110740300100ca404c10a038812400c00400e00e412071001d09001075541c2c1c165400400b4000c90125007120344096054054880106000000e0b442d84288014000004070300b028609480d01d8407140c407400c1c00b602038094440c810004000c05039281641c8600000004480c45c1c0c09038684070aa81c550325850001d56404d0310680985e0a54a40400080c10900034510500400034040203248808500404c2100030342001303000c44502e0040000c0c19002501615035625961200c00308101c000d040c0c1101c864a042c00280541008e60214 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 529235440 1250 529234190 529234217
    0xa0c0e0c03040f1505091b0409030212071106181c030509100318050c0109080606010905060705011e0203101205060a090c0e0a05072a08220902090f01 66
    0x650850350b02a802c000b14442099042ca410400041092141d403003c614000500150000210310b200080c068256440c1019001804010448003072590080169100705803035a043c81300a4080c01c071f07090055230341840c410b03031010214145502c04071f0347e1400c00740c050215000b0703464410b10040403040c491004815802c955680507225220b1040c0782ca116507641c15906039210311075082004603819002c4611038081c001d02c0c000703540d04601040580402c03010030700402d92a50000709640b0801059695183d03031032038901802031990114500350fa195480d03507441440031070001c24036181d0342c03c2c0f803c00503500d1600007684490410240c00041003000d4070045000400c1c2c0010311986c001280c2d40000a075a4810310307045c4070241310340e4042c84400d0021010041e80c2c0800ba8840c511a07100c40d00c0d0843d40301c0c000d01d605503c004203488100d110421144001001c948030002400c1c1d071001d000655003180040d044c0d140c00c10203080e8032594040b500010744104904050150060003042802c4c02035051551 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 529236690 1250 529235440 529235461
    0x60903030507082d060a090617061f03030c031707020a1e0305040512012003060a060305060d0303090809030f01021b0304050a0e0601030b0618030f0c060f0309010f0c020a0c0e 77
    0xb203144c00c5001d4401101240944d6940035200b0010140d402e000c0000c181d4458400714421030805000209005e00710010780081c20001d03181c0042d00101440313404150a60b603042e200c41e140d4010a604100468401c1d6016103440c0400f240070f0b4169170010281400c0a280842c21a1254100d490807141240302c0c00c0002500901542d0558404480c1510030001c2281d00c54018a071820307200643c3d14100c59500140c000420086001e9102544e214a140340c45000507820350f0403c2e00c169030040880903480c2d022911a9129000f060310680c505450032200301d000a203090255254240c3e540d500003402d042d000504450342210ac01d0482c05142002d01e0078000a030082d07541c0c40f40d2131741d80c901500000e04a030712030f42c0084109400140784540710b009420b580f910208810500c14003900c1450021803401c840003801c019183c4000b00100e180080d0000c2503d1650400b0b0034464507036480d481e40ca5a40f0f0b40c20b001d410010442c03907004212030001800c1510200d8615400010040ac146003880107051a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 529237940 1250 529236690 529236751
    0x519170301060e0a0f0b1c1103041203050604050c030112031709030d0e0d020c120a0807140c04061a0d060b0c03070309060e0d111908030a020f0c0303030f07050706090303050708 78
    0x188003030340d40103c85a03986980500401c2800601d042000020042040a150a103403461b4bc0c943c1c1c1e00b00829078400b0244411110b05481c2d56200c01424801041f500034122401103c2902c00e11301400c0d000c050400300304442c8415a0595000e4001081c000f81d5088544190130808a0714401020345140050b80a5224100c8280c540e01610441d00700703200090b81080b1910b00c40364400d091a5560b001802c224520a9031401d8180981c001c10703000c400545894007404041e1041200b12004c81c45c20034554100d950b001c1030b0140d1495448410000c1d204010340080c000000e691001785a075500180360040c24050715030081e00601c60410074412280d181c010410030040d60100880c1164540007000412000340a000754040c404030050110f00c2c44000300142c10145003a401302c07100e0107484410300da119180003020ba41c06520600c00242c81300b189900e203e800000c02c0c01c00c01e140c005107440d03d400395010440150042034a950610009591005209911401406035046041c0350650040c0e140803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 529239190 1250 529237940 529237957
    0x16150503040f080c010606030e060403080a1e09061a01020d230f27040b060306061b030a05090f0a060f030b03071e0f120519170301060e0a0f0b 63
    0x120120004040080c202421220150482603154881e02c0c410700342e03406842c0314003c1d100000d017000312079084840c00003912030107981d00d91101c0c60030303645000328407004060808424441404003150740107800b034140700d140740450250402103000c4079100002521400d448001707a04640c0840030302d916043e0f00c640c0f4201241c04e40d10740506180d02450601c1c18034000c100c00c140350705000103041100f52462265070340200c80328401341c0529a080404010880e0f08141c481d80c1c21a9081000644610f0031030000d02b18900308038800e2824400748800e46166812035135640c0f021902c0028032040b14500b02c450f001c16000c04540749031800b410301030000c00c2c050310101424141916017000d404255000d001002c007a250080558011104031441900701000c01c1c1f142a90201c10350303402050703012203a8035201c5041d800070020a04140f00c0c1d01240c00440e840c0350251402d05c00d450701202990601c00065000380350300e5503005011811034041140c12203240c0e221501d46542000b0800004100006403045003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 529240440 1250 529239190 529239197
    0x60418200414010509100f0810080d030209042c0705031c030b010c0b090106090e060c070b04060618090209060d021f020709060e0f1e0103060518010516021615 70
    0xb00da100580740790190006440c0d0104004030304410140d070014030800310110903951a54940c40700810840f40300618001e24690f5008180707141420303030080d0000c190700705014000241014202152103801004a0070103050b503160b015071618001c104007e0100a88002c5000d44595046540c0e40e1007a041d21528641c18541c0b18030410460760300900e200701740f13584c01c404c8030a00c91801c007010038020701d2207015424005141203105224000005500c601c42d0700076007015840c0c80465240c1140000008004840b129201c0d035003c101a070508041c070750040c0d04681c01244503905072040100301d1100038490340c040d814005080001d6601c035040700b801005009000d0707125140d514803ca04152040c2c210104203424020000b070f080382000d000da8030a500051181d00035880c0c0b501c00d11004d200003100700b00d401181c1c2c0010700109007035038080c94003c0c02c4200c4d4012311110302c2d2a4242543c2e030440d002100104044442e80c2c1441c0c0501640a10003a8401c05c640307110b042c1809110560b43c80740e90001003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 529241690 1250 529240440 529240469
    0xa1112120609091009060219020c0306070503092e0b0103051b0a030f18030207050105070b010e180f0f0d03021e0d090c09060501120204031509060b0604182004 70
    0xb0720780f052100030003010502038144070760b010728100354020750f00c41002410014039140c25100e14078804102c5c1000140014090213554681b4030f02204c40d82c00191030b0b42e54a00a200000981e0310003091581b0010205a6003003040001c6000c0704811504028441070525017030500f0032042008403041e046085011803945500d4418200c07003100109250302507035031554030303208003040418814807003132a91502c80e608032500242c556004403150300071010002c02000c40180103001ca060494412036002d1001014540300a5041d075019240c503006071000e40841e00548680d011007041442861242607807414254a4200781c800c0082c0c100308420000220410042a200500d01564112182c055008080d01c114140c540da000d07030042101d0320923107020480d2400e01c0d180c140340d54000d540480c1d800000083e40f811a41407045c000e06142c038411275285030f40380a0b0032002ea44580142000c0d046202c420100b00c1c4102051104444000d21007001004020480c124291442c0e001c83d800d0300d6440c0301c1c0300c08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 529242940 1250 529241690 529241701
    0x8070f03020c0d0503010e06030106210609081c060608090709090f02120f0d0f0509010315090204080c040e0f0a02190e01141c12140d020a1112120609 66
    0x2c1c007496268041078060648140509948600a54103a8500001c090340d03039101c0340c04241c00c841c014804c0350184d03030095100d80000a01180c6110030750303020301c001240002c0c5990754400950310030901041c0b1205141c0510054240314030580c00603101038200314a43c0d0070710900442c3d4510040c82519000b0751215085010020203480c2001d41650240181d07002c0140218043d864406104107446540314840c44440313401c2c4a5188001c6042103034503410720740903903d4011805040c0e04000b140003461101000285036141c0c1c4014001031030700c50b000c1c0100e003c920342000180c501002c1d60310341c0303130b400b04001010101000c604101015412505100d84450406e0400040010390340411025003002000140704620314031400d100d50411200403190404a0fa543c8440c1c01c0d036900c019144030034204a1304046401203649020051a0350074440c103240c0844601d405903481560302c5400102c1052546200c4a01023064112101e6402c02481c2020103017180d60300c03181c100800242c0f1a4004101290 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 529244190 1250 529242940 529242947
    0x50c182401090909081e0703140a0504030f0218070509180405030a08060a0305070f060e060c101107231c0e0103020d110703080402011209020f04020d0204171c0f08070f 74
    0x281e0305070b0246ca2081001c3d01c01e002002640d0840c5c101038003c078104007408074082e11044212104000240c5480b81032a045454168141da20080200c0c1c1003101e5a4030b0310211505d0803022441500c050b500c55564800d1881407000020411500c15081d10700e0308140000958040700b0703100708508a10305140143c1d0740381c2c009841248541d00103002800b41d03020105103800840100b0042e50221703101c1d1200a52204140401c502c904210203030184c0029109802c044003e410040342c0d010034440d5142030480b643c54203204001800b0f079102c0045134500210035610340c00e110300030400001c1d00f00010a40000c030009010540a456624105540000c0b2810407170320b180c0c45111100c072003010540d101c40e183e02d409052100f058a00b03138049181c6585001c958522406000400342d809002c03000e800300c5210600001e5044a6070403040c480e000c0c031000c109203424810725040c1c107459a008100c006207650890a01340c1d20320500c4810810040c02e0701181d80e4114900942240c12868035002d0710503180402c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 529245440 1250 529244190 529244197
    0x4020d0b040305030411010509030a0f0201030b28060f08130201021005010605030901061401020a2d081804060f0501052d040927030c050c18240109090908 68
    0x300305800c400240014150b02602a611030762017000c43d0360f4218032180040d03507180203100d469903241d4440c45500f0009011041840030031481130501288048849000603405c0e445418811420541a00d141001c0c20038669250020243d60504804482a2000c010007032000181390902181c071281c449411a40300300024240961689000c1084d035860300c2c4010142e60003655000120340c00c09801042c03103032145205800740b010580013456003521596031005981502c41d0001040c0d410383c2141c440510150304421102407080301460b80c0c0303200304000c8460f1980c2d0085840d0046141540c148140c0d80c00110070001e0780d1090030542d440304100b82c149455202c060041c02d07140c210f110100440141040050300c1034900707485050024120450480460b00141c500c0300c1d1246110721504804030380100040c624490245059894400050780800e0351482e00b81c2d420b18105403860104150394448100011500120113039140340c56410b000020b105036400c2c000d0303c02181d528641002080305a0b000c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 529246690 1250 529245440 529245443
    0x120504020f06280e010e0a0e0a0e010b100819050408033403200f040b0304020613120614040f201207151707031806020304060e0c030703030206040b04020d 68
    0x385500000f080000c000b1510120700b00e020500405500e40d503498009207540c10703a4041030241c3c2c40313aa80c20760b418014201d5031442d074969540c0d60b11401c41c01c1d00c8041d014003118006860700122410411108010103145c000100f00c540d240c0b006100000d18443d04680d000300c2c1c051182c511047c42c052190b030000310060000044a01c104010550564264001e410304200c206140f122107205010a848180b09210710301e451168200400e0000300514806103400500150030141800e41070075a240d0710f0003045d00164501d988140c0d15000308041809100c868010000c009070742800c041d03507403400d15034242e180200f901544601d40180a61107000c00c15082c2402000344852800340107100da10382c561130040b03107500320140a0199280d8040c1c040065050080c40150389541c2e02c0440403030051519040000708016880c0b0900045011400038501950040c800000c0c0e8525a8a08600d480d000c500201d000790400c2c3d01c00c1000c02c0e000b04540d5446500a12003840e141da0f548000303230074005c03070260 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 529247940 1250 529246690 529246747
    0x10e060915190b070b10060309020307030f1a0a02032202010806090711100506030d0201021e0705010603061b0e0102010605010215090109082a01110433050a120504020f06 75
    0xd02d13905101c90140c40798003560000709110981500d80c40110291044042c010350194003a00007000020061100455658000c00900031446850010001e0440b01aa00c81c03660325004030a004020115820f0380741c3c0c1e10f030881e402c1500380700e07183c0c00608600802003117140310b00710010015007003a000d8032002120251400545185442c1402c40c030004010503603c05000c0d00c079078007070301d00d40074014400c940d11240c10b40d240748009400250141050740c01030b14220384554952200100090050203650481e60980300b002c0d4126910401c02045900c10f80c140034110380c10254100040c0c1d1300480c4003090500d61716481175560703440c0d0403040d0251810b03041c02040103000241e84011002d1200581010030207000c07401c0303503106000301d1507404d0b60604094201290000c2100b007000340c44500300294000018030281c61600141030700249908141c0800001084000a00a42d01503200122001041ca409001c2040742856004911311402c44103c041c001c2c01c000401e42e0711003008005030902001502d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 529249190 1250 529247940 529247947
    0x903080c030703021b240f070c030b2a0906070c0924060822050715090803160611040806010f0302120a120f0e1206010e060915190b 58
    0x32495640d92002806600500900e0031841460070000740580381e4000c02040e0b55846003d0a620120010344507000311b00889007040000e007001a1000036003905800b0b0b0320b0300003019145007085403080500a1074500400b03001c0c80000c00c4564000001c02005c13924a401a8681e124500415800e2052140140c2003029440340090290304d0b13500904c213044414401ea1542e00008407034891800303610300075040810240000204000c402c44000c4401e0500300d8042400e90f0700603150b01e8140301c642d03040384034117105000104011702e402032020001894007400652a1441e402c22039118850011380007443e840e164000c0030700d0340594005031005080c1d6002921042c1d42e584100701000426448205e002d111900701013200c0c200041003810b00c00390003458200295440344000c030b0708108802000001c0c081d5200410b40c103a120182078289559a241c0140600d504028003032940c8040205260301c64040703a010844406009128410304107011b40305640148461404001a02400e42003d80c100c0c4012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 529250440 1250 529249190 529249207
    0x8100f0902090a0510170c04120501140603030a0206011419080709110711040e010e070e0402031c051b10050c0d0509190f020a0317030103110a060f0f090308 69
    0x41c0d0040402d01800c65009100369584c100303104d400701c1e0030450071010403044603504071058500b0783d0725940980c008641e05d18240d181e14050400c13036010142a1801ea640b114141c1090409000d21904030780f044008500705000844000d645080502a6900005a00e41d501d02c1e00e0704c4503900100281038820803042c406446201150b43c0303a107580729801c0170604240002c541c5400000860380c0c80323034100610303d8140075010284030240c90b6200443d02159652890000e10420602030000039011410040080342481c1c0100b500e44061510700c000c10b0001c020708640c1c80350f04882102c1c2130800741442d031150381c0100d250040c1490401e0080b602400c3c207150400c11304242d04002056003803c1c00360300304581c1d200c41c04070903518001c0c1240c810000000c90f00768808243c05071101200d030340c4020820203d03a512541c480c103407804603180401c0720b60804001442084400e0380c011031081c0087d519003042c5c510301100108903100038160002030003844007400500910415000c0083c50300000196614001d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 529251690 1250 529250440 529250459
    0xd091a071e1406100b0f070c08070b070b2401110c1008190b010203090d151805060702010b030a020d0f050f031c0204050a0306020a05120103050105060f09100608100f 73
    0x842c00918018010b81c00051103080452820b40182c032040c4600740d0901c241d01c806801690b20446069a481800300400180ca2001f000250054154a403406031580b68525081c195144064240303000c10060040840c45110140110000c00300c00346403050844800407040703820820b0000072180c010b01c0b42c69190384595003000416010307200d00402160f01307008144444c0304680194050354010380042000903150f1a1504104028500a481c8026114869403411040b5031440803503401031450000030a00b400414010241d1010b014002801405021000a510b8025a4400a11400c400c900c90000d2186032042070b070340d140e403010403242508800361080d6502e420078407140c004a94209250005000c050095408850002d00351170380c0721b81075a80300700294100182040400c9010300826600c500d910b4461402503001d80700015107820128248050740e04a030398103a004904c1c55040c4281d60004084100c100d4103286068400e03601e81c896040107600b5254008507000d9494800400c00076074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 529252940 1250 529251690 529251713
    0x602070302010e100e0f04150e2e1e0302031f0b010309020102060c030705120a020c100203010b090f0a1211030606030606010816050d0207030f020d091a071e 69
    0xd0700e4288406511038200308103803911144c00e1002034a01d000b50542400c0103010070050160040005c2140b8544c3c84103041c0c250f020760f200f89203503840b2400303000151095000c41086440e009080c041c4881c100220301007210349034400c10340403040c0c10b000c10b01d82000544070900910790080a43c0c1409000031052580d424100206200461812038401c0d41740d03001c1e109591109606801070242171383c407904001450f400050494040c4407040000b04c04400030b43e40d0840c441d124030f010050300c8120100c0e6003450080c1c0c0e252150f1035607204200601000f210360041d110101c100300c940030350000851020800c01c000c10380c40402c4400b01075117010100511080d1080e0040004d904840c450740e02d00040554404054403400d0104039040046200c038001d8032070342140700c515401c06d542307005082c0a080b0126400f28205400082812010040250703042c081c00b0803008451510841032070801c44480f040c034a00301c240f4a508072000070300d08200401846c810090081451021003031042e54285034142c4031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 529254190 1250 529252940 529252943
    0x130c0b0705010507080c0a0c08030a06030c0e091204050d12020705090711120a0e010c050a080403031d090c0a030903030f060f08100e070905130609061a0609030a1b030c06020703 78
    0x1030464000400145914050303407510002130f5500c48e0032010300e0704c07220140c0d0700142800c1040c80c1c540d40040b01040884c0300034401085c1c402724090b035501e0003124403424945582281a0803c1c02000300300400c1d682c030b100e81c010441c0c104a00c0203080300344100c1a0b10746415980290f8000c17100364204615142c01c45151030300d416242341601d0b100c052400700d0347c500d440340f01501d04c0450030726281c0c070241d54401e4252270540d0303200b4030494a102c205038407800d8103034115500c100c000660810310450380b416001c0e11076402580584501e4801d0401d1101c180460040000c4030040541d2842d5040500d8030035000901010040e103020804d01d6119065084440c0c0c1e280110700700c501c03900108245040c1c0600c14408c1c112264000780c00381c6401d100400000d040050100b2030030003002c44044e404140c061148182c002d01c150310004080100c40e15a982150300468154882c000c184840605524049503401c9101c0e031041c540001c1d0f075116044840d0300e1001d5000a0200001030b00d000c40c000e500000c41d070042d203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 529255440 1250 529254190 529254197
    0x6031e0c041d06061e0a14040506030705210f070f031a060c2e05060907080610050705030d150f08030304060e070308070b060312090d020906030c040213050a150503130c0b0705010507 80
    0x82045041d47c0740c1c40d02c100d2043d203812440810000d034080348500054029204000355010303440720001810b03d503e000a03900315100b002e003d0240305600d0b400a9040382c21007854101030203d01044c104801095040c0440d1a0091400146100711503d0600001c15200f14420b0103910103a120407015004901d4802c103030b030006141c0400304500f45482c680043c800c0c1d0b626a2a240a070b9911414085c400c26142c070120103008050207450b00142040c0040c149000e128030740005e00049101a014200b25140d0004100307000d0b00c0301c103001002c8003000b1260b000e60480004900301807a02c01a070303e841c00651000c1c04041c1c0100341ca00030007421802c0c05004840460440b95440c10a0031003080c1d504c035400115910204440e04c81e801030070070690250b4000d000405481030b40c0ca4840c08a000d907482003000c0402d4002182c0b081c0042c0c5411800c60000d485444101c40f808880410054401c0c403000c0c0030034480c61680d10034942040700790380518001d450384130001926080c851804038080c2400792000c0c0c010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 529256690 1250 529255440 529255457
    0x20c1306081f02070b0106050d0b0111030703030510080708030403030905150702191806032a120f08130503100b0f130b06031e0c041d06061e0a 63
    0x8945028650965460801a0000010300002650b140c00341c2c5020382010380c1c0074044500401c10468105000f0850703911016954283c030310700801203c22602c10a418080f0781c52101e01000070010560b1612641820001f84580b070300c0c0c00c420200700e15540001203c0c03062800100e070809001c000780c4202c900c41e844400780b980d2200708010442c2e0b0010340441011b10207020480c050f240c0340d02d501b00c40c40b20360840d008425444241a2107805030301603100004980b127100070410800d03003010141c1d41c40e48842038032504500c2e50058107400e03121481042c6a0440c40504041442080405901500da01842059903920806928603000c02c01c2d00c5094032a01856a10b140e61800724010b005164100505984500c92840100000e40840aa1941d07095a1b60500d4055686442d001076000c3d0030b104004070751203030750342c41e80c200341e21070003441078201a6003030208200310024242806241040840c070300e140e5a8a44020807503501440c40b1600718544919203000c1e8034a6440010003d02010380e44c1c0152 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 529257940 1250 529256690 529256719
    0x60602010e07142d10020106140303160b040213020304030305070906050702030d030c021011092803020f1305040c0f05150d0b03030c0706050307031415090411030d020c 74
    0x8400f03c00c140d28903004880c2c2d08006100489208402545811601d04130303c000b40c08034049002d28000c80c50520240c0e5461105004100300070101c850074803011002980b070710401a01c06011540000e0000702220031003000314045603030b8501b81c1052614200001c5440b85401d0600a019010a03510782005c91382180c070202d4000d2240701282c0401d13030041e00420107801e00c800110000c10f004940401180520300c180d20202c1881d01840c0c10100c2000700c0141ca4842c3c000400400e514050601c0404100780c40c1c400d1203107803035840e840085a40480340100c0d04441c04021810f488002490400703824940002c10080120300140f0400352031100d441c080120751207805204a402004051410300d000a2203840c00039150364110740c004140140035a800c044005500519144094100c400410404020041c15036814456100c0c000480400c081d0705003007001d0100300322010901854051a042d070001020b114542280201001300601141c0c2804038000b40292900c03001140c040c803e10612030103a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 529259190 1250 529257940 529257959
    0x921080706140610050313061e0f06090207120c0305070c080610050f011722050607110c0d08090a1701020d0e0109030e1003090b0f04021816110a0204060602010e07 72
    0xc1803604d151102c915541f2100e00749890368030b1145007218080d4603200045407282c10045070290452214402103038007407110054000740e44040c1c0080c0e492910500c03400c00031407050b40201240080701d003480c203100c01030340c10100c4551065000262030301e61180e100082e0203900040741403240702084c11202015450f0001c101c030492030143d6140c0003e1700c015011118014104426070484021710506865600394160b0b801084030070402594240c001c94200043c1c00e0700a541c8417a080800b50191501080200004101e8201146c1c06025640e02160b21030054a4403554100a0301039000511010903950100c103020b0360124041e424018101281d50084030b105004581a650741a03c80e0406260468184010b0785240100c240416803110080804286900c01d0b1074028915101707500c005161a00500101403010b4140315650b402d040300700f00c0707803203240d0700070a03901c03003083c6080b411018042c0256803501444a0010750f11a10740580005c016405502080d8100c0c081816500305503503841100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 529260440 1250 529259190 529259209
    0x30711030f16090b0a08060403030b09150d0303020d0209130b0406051203040504020a140c010501030c0608040b0c03090102071b0e0c070c0905130b330109210807061406 74
    0x2103201c00300c007800070f100124058200401861015100100e00c541c1c03640154034001c010345013500820f65408401040b0700385510100d911a2a00007809094824203011503c1850410000360405034003040c1500c406c55150102c07800c0000040ca012040501940b00d84020260101011322462409000107031074180803241d0341980c0200c0024505140c0703040103000180d0b02840034581080040914090303407803c50400b400110005000025180d030452130042d1400e003694222106218032401040000b4004541e020350040d885140740d91251100e0103011b02900410800404511845810b800541c041c403101c00d0072a1280145a2841d403100c0755402c010388200f8030041e01e41c1d40c105000340203950300ba0700550380000120301c4420f9010402d0f11000c0d041803081d5403404410160000b958200c0a441c0b200080f81c89010f04140641d0a42c5400a0101026841490348040f24034107901096903011a4114016401404c003e648074240c2c98040010150b07100c02d00d081c5407121000c2207131400d24101e00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 529261690 1250 529260440 529260463
    0x60c2d120603020a05270c0a0336050f0706120c030b0303040303031e020f03060414010501020a020f0411032502071805090a051c1b03080c070c08030711030f 69
    0x8890541e030030001030004141d00b130781c61b1030301c152183d80c06662000d04035103283d032150304003401a07a1503c0c1c076007000409031051511942c064848640f00800e804075040260b410180300810a81c009604d540f809600b40070090660904d50f01500d0000070b00300780c1020181c9400da0b411481041004002441503040710300301801240c141c1d1083c8000c2c00020b0090380a441044001c50304900c0349210301003140140ea002615114250401106120540c00e041c000d80fa24040145042e40441d810301c00001d542d0f00c00b66601074841d102400e062801e54441d9400800741d50340e40102c00d9034030715044404280c050240c004180c18440e6054010f0038091001c10003900b40c1345403800c01000106110000009000098070003200c1d4050046448006a42084220f41503ca02c00d8914444900c42c0740140030b401030134030700d078001d40b80854134800007a510000d445d501c0755290801b152141ca407030401d038402682c542c0000449100018804051150420f041c2c150380c1d60480c11202c1130000b01e07140301c2c0c69101d483e22 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 529262940 1250 529261690 529261699
    0x181509100608030f25060603060903030c0c211106010f080d03050c030c1b071401030608060405060417070606121202030c1f1e0204140105070807060c2d12060302 71
    0x80c00c21700c2c201c10000312113401d0205000429410305803606822030380705030b0080b07608070303a80c1d2100004c154060081042c8022903003080b00300c183d12030301c60465104811649a810010450201105500910140d05039030721aa0840e4455030f1078662840d00000d950040640900c1041160784005110f401010b1048001448030350a50300c4e651403ca9654001c002161101c40da504468800120104803110051454071290b907103100c1d0200000d030407510284c0011010703412000c2000702040c000102c0c2c5c2d410a40c408603008001c0068044c0543c3c5004441c0010034450a0000c0005c5503080c0c80105045036014030580c003019a40b1003016696880b4400303e801807500030b03c06e803034036034907401a0407011203404060100e040840014810840398003200c6003050954042401d1051800c50310000061020030300340a0f2070600561214441401072920040215817940d64cc010220b205d00600d291040402121000801c2540d40741221803c4a01840c00002c00150250a087d50b0a00407501201d4006e403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 529264190 1250 529262940 529262947
    0x703050403030c020f1f0f030e0a20090a0c171512030f0c030304060c03060305100506130c02060403020d0e210708030406110705100503181509100608030f 68
    0xb6000d540442420405a901070b044100684940d140c002c0c541c8402c00e19030402c1a84524403100103048000d400d4002010507140822440949400080c12032002d5040b0b02231107041c64a0207a8110700c41d10520200f0341000407070060001c4110f10350807501c01c0b00000c0d02c94424a0140d030b0088000014100c5041810048034418031702c075400c00380502c03200c8404d4402034a00d40306001c1c21240351640700312922510b0390f00001c100410300c1010310414030015024641030007000e2954913016038441c4140885044941d4030b5002c07440c0759403800350705002c40307415540c140461020404007079107a4104071011f030058028902a85102403158400d626030090007081c0f88030088803030000c100c0402002c129811760f40320306600030400202c1000508000c003095914003d200c1210390f409409c0520303039070005000d4500d50020120050b0040103076a030106600049151103540350034254075000b403c00009208440b02414040c2c410070100e4104200baa0030b030010300105a03034024056132485001c5000c02465000d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 529265440 1250 529264190 529264193
    0x9090703050403030e0d0f17100e070903020409060204030b15030303190e15010f090c02060a020703180306050612030910081b0a180b16080c10022d0703050403 70
    0x81d40070907080303030081c03500298405420103a0340c42c0200c466800c5000c501107c2c1c10f5094280d04c500030307026810401e4426000c50030040c1c900414880d140c080c1418200ba00f00000718018810b80e14030000b10b400130814003400b201c904005000398000e00007034800c1c4d0140000030740f03030341034001c1400e20450700600214919a10390340940031108408640116581d283c805100b0544010070002e28802551a804817841d45000310a03410840141d110303486160425040c15481034000c500150f201d05100005665100c0925080360440c1c059010410700000600010003840302a60001e07208820a603220700701804410b1200b50351340642c124059000100f95402e209851060304090780004031210150a07004000f034040e40b40d50010301201000420010b40646d4103c80b0f0b051040041205c80681440c000442c140121546070404000d00068000a0551600340701049024890301c0c2012045454000340150244100724083c00510b0902003000f080a40410010072204419415154945060b185 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 529266690 1250 529265440 529265447
    0xa05010309030e1009030506042306160507030306090519060f0302030c1504030f0807020a0611030306010809281202032b02160609021008010f0303030f06050301020c030307020c06090907 82
    0x904c45080410a64080020010780200595800fa0b881402014001c050406402c2c03900290355103114040d174050002d0080540070300240140c2000c2e5890101d680e003820781015805000c0945c0142d03500c0d40307004208405810b0307031202411106c8440c201400f5441d13503680082180900c502029516030860000083e4500d070008100a825070807001d100d06040c1e07240c03602c02c0505a20042501e002c400000c94004610b13142030a00058010341c00d01d0b80381401c0034200240e81e07004c02041d190501403802c0c00f0510741d0204000e000e6620a00c5080614103282840041a9131420144100ca00c01420000000f001c1d00200c2a03800421081049480c4e0540102c5030f844098204200892644d41c00c21407914442611190722200034010b10021500040910500004150101d401e0081255110041c00070144040d80701e41203a4151078045a0842c080d5541c90040c8043da1007664590300c00250302c01c0c42c2d040800510300c0344066400b40e440b82e80504c1d0502501340708508005500040c90b00c00520075502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 529267940 1250 529266690 529266709
    0x9011e05010807023c060a050108030a0801050103020304030909060b070524130807060f1406030d0e01032d09050706020c06070303111204051f1e11120a0203060a05010309030e 77
    0x80790358030b03035007601d902010f20310441007170070130603031140c101400300302d800d810a0261038010841e880040d0b1911425180042141c14103005140c1056000408103003454450300801000e4842e0b07200402c0a1a590f2000c1001c41d400004102c132140564600c1c141481020984000b104440f4034079101156254a00707600d0724002e003401124404000d11000c03011901c54404c00d5040351a00c0c100290020351648031802c4444000c0013144640d010070a1b00080d60f41c00050f59020740400e003004141c1d1100240c00c000c69081c1d00201e0b072403040300d110022607404104d8008546071750060041e5920103840b1340703040761510042c600194222804004035000244290301098203e0719151540703040001e100408002440251400c2c0c80319409600c2e00c417500e21159500e50040b10071140300b0401d01e10103484140c1090256400f92900c1c50783c030f88800f601c00038810100c4a0314500100001d00341c1c0361400301440250400c0e1400d03405180800c0b004a00780d4024802c68210b07079003640700c04118807031800400c00301a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 529269190 1250 529267940 529267993
    0x3100b070c0306020c070906051c1704030b0405060412020a110d1103030a09060e010e0d120e03060a06060306061b0b0c0f0a090911070c09020c0c09011e0501080702 72
    0x3610071000400700382248040c042d152052400341c0380451400b03036403c05035881600918813070030075240c44011201d421040c401d41550b200011450b00b481500c03821030700340200e9002606401818040000b000740c04a4954495845440c48150380b141610040780e40d00240d1500504c9516000c0c0003480c070340fa068182c410003034801c0c3e01900d206a4180c02007815a00f10110490101d180d0042c01c1c085650040c802817030401c002c3ca408510100282d001074100c800f0110701a01d040b0006151001c00745c49050780849009000d000ca90079402c0040c0003400900e5540320b0032000910704403004c22001d11910300d5810115082140c2c0c0c1c1c00003840c0c0c0311001c25a5028040da900c9250402c441289481b0036800340c6550b1400340c8a04240074500b0341c1303131402d4883d03401c030315202d00c641044410001040031008100381c132810400141c840c0c5523204c100e03152602d4003900d598440d040340000170b4590021400c0103140705603e6450510141d44e0001925410001c0d9191005070704240307480203010001121101c18071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 529270440 1250 529269190 529269203
    0xf0f0b0a1b020418061a030d050d0f090803090d0206040b04080c0c0306010803251a0a0f0524040905100c0909020a02031b0a030c02010305070e04050126010203100b07 73
    0x70807030703030014080710311100d44c046007040e24240c903105011161161900c20900f0001d0703800c03504125400a80c0701c0c03010032412401e2042c0421a0030b0080310030390000e214070030080c004011116140c24000b403507070400c4074852010310480d094101c50038070110b81c0e54081c075030222000710503841c2c540d00d140e81030f0081035451f00580305901d005201c90b035040207030a00a100d248081c640d40e1080e089410205002e40c91007280c42c40d05510307903a000920400e500700c0c503050300c60502d4205840e644001009480d0800352594010705040c240880b601d00040905503001c2d050036a000840c01034811320080d59030b00304001c2c2c55078000401c400307000212030300b188001494a1800301100c41d10b41d44141c0c12138000640550041c1d10106041601225807515800b0a01030345d001002c0011050741c00074003410a0b880003d0401d602d0340b02050006010b04502e106098000b441400690703100d80d0070001c680035a59044130804000900d000c00c0540602c00c0702d01851003c903d1002440c10803040c543c1c9a40005400ca510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 529271690 1250 529270440 529270487
    0x2030414070902090f0a030c050103020703050c0d021f290a1d0907050a08120f07050a030c0b220b2508010e07050a0206061207120c0f0f0b0a 62
    0x40400d0246001400110b0801600e481e1540180300c07912142d40a882e008408258003400486c00c60b502c50422110246030140c0e4078074052408071018000c54501c4e0345a0322803090140350440e0003203044068507165141c02c03007441401071104016685001c5401c241c0d007d005026138400824425150300103200a0880001c41da40c980411007c00c1c8500d07000c030303840098141441511001402403800820084810380161400c184d15030391500e4080c1e40c01c111038040065009000c0140c6015203104941200540b82d00150368280a0700115070808116085c41030301c1d00007120410040c0d544a4801c0d038010081c1260310103541c40380021480581304940c10400d10250000345550b05620041e600d41c0c07643c0c0c6031480d5241c0f0b06200f0bc50a4050003440070701c101800312a00c2d4070780c0051050b500c0501280c00303000c8170001952550030030440d40c004002c103100585ca55070500190f9202c0c00120303039400a040c6c0c6103690b25130310b00180ca441d03800717102d0594800300f0610018500c128070003640021340007403900c030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 529272940 1250 529271690 529271723
    0x2107020306071d01030908131e0b0306130b2403091501080c04050c09041503060b030307120818030c0c030c0a0608160e030304090b0f100827060c090a0807120204020304 74
    0x143c1c103e294000027100d0700100c110b80386520f1080540b0002c4c03040d10300c0c50f42142000c00003e001c610510080c2d0800c15030300c1c2c869003920703030b83d10260584d078094125452030542c082c00c1c014075090780200c0e4810300e1441400d29103849500000c40f00b074101d4440c0c0010341406a01d03c010007002d03200103070411007255000c0c05494507903510780c07241c90300a90303a0303008074142d0f1880c610f0a18145da000d102250310a0304240508404901e00711005038800030185490603595941c408280c0000301c00018154092202040b0300130bc0b13680010300e0240c800d00480488107121041c10800900c02603501941c40080c820030041142096501c0d08070701041c40506040c0290b0314414046440c54000e07034001e504139500e901c0511142d090517210032800c4101594211840e2803140c1014000040c040c000b001040a00c81c0103107610707080007034181030302800300c000d440310350610010040743c9420002000748251140040050150000252481200d40d03001c00342d03203402c4c142d40801c0001d400c020402c0e640ca140500d002d54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 529274190 1250 529272940 529272967
    0x30a030c0306090f091a0c0403080c010e0d05040914010f090c020f010905070509070c051b190305160e090c04050a0608010504030306030c052e022107020306071d01030908 75
    0x5130600c4880d1070005007014a4107100d507000c1410103003d61210005824030174064070540465044d250020460395803011094551401080c910b55042c0ca81e00a1525950303405030301400030b20841d0340b007079010f000320700044041c1e00f0000000c1c462002c3c00d54900204100380401a00f01180c840e2140c01030740c481c0d1505101c5e260039a54029021140c0f5049004140690319000c1003954018040349002085020303203648056980b0540081405845000c1a4504095030382090024201c1c0300e03001b42c8803103182c0d01e2030070301e54410001e098642003c008d92004150746100070b218501c2480c40c4d06c01814186203100c2840020032019105000203525508045400e641c2402214003e0380719a40008407580307107042c2082c079240b02d0740001d4488c4901a04805546c00010620803860180c1541c0d806a118500c000347c2c646081461100d40304840030108c00404103180f4068100c4038000c0c0c0a0b54603075a155042242c05440b2401c07407007160303804000c200a155100741c2c01902c01900ca45811490a80d54055030b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 529275440 1250 529274190 529274201
    0xb040c0311160201111c03050705090d0b0a110f09031203070f0809030d060312020c0316180905070308030a050906010608160903170912060402030d140702040c0c03030b0d05030a030c030609 83
    0x105070305201c0003400300c6c1c1c903541407003015030041c101e20305141841d803044005100040500d002a203049005030108990032420b900050303240080000555503010080c40244107504401d034200e02c280a95144111000b00e500220b0307225000f9581c40741c90310700c110501920045800741c04100c1d180320520008414810742d101d4100594022002e2102c144d003030f41d130001d143c180c079148203a01a4224030090758480001d00e40390300a50f02c0d424100f0301c2c19144040c1410081075604809402845040400014456100000c6002c0c07803107031a041c0003e0b0b58116446980c3c81e002e1144200194000c070010320b0f500130506c240c0d0501c848924240b641d8a0381ca0b118850303403e0f81d022044e644000300040402c00c600d000300c92624160801006400c15182c20b0700007940b1501d180c2900d8043c1700e5004804007a85005c4030440700c62a90050082200040601c4014060030b21080100e001c00c2c03038054004c80d640f904a5101070728642c850000c40ca4004040c1045000d0851055090b0170706494506c0841d4190b018040e0707 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 529276690 1250 529275440 529275463
    0x8010509040c12200a1a0c0f010906140f1605070807060f150504090803280213050a09051312030603020405090c0a150503150a0b0d0b040c031116020111 67
    0x30000c0c4e49041c605040b01c0c1d490a02c020a2140b1402d01d010000340304000c0728540b200050741e101c1d41c0c0b9954154402401c102c140082200c00b9440e21800c04200000d03035004800d66028400728036560b41c0c4920b00c16280800949005204010043d110f5903101d100701700030103415100d40011428201c040e40c851f0152551840d19860180d1507070a60a1410080c00700c5600401044809110400300d0b92500d0b00e9510002d4034160050035102c841401c080702100185c50031101d1613404564810381c40c002d00c8950300090003064400c20900c8000a100301070790056600401c0502c01b0282c4441c7c4564a2441c0c038140b440040b010b040e20303404000056507407442424420b07140440038006400f58903040007040000d5410a0030000800000d0311845540b22050b00d40c8000c607d00208000d0211000040d21030500c0e5001085c03040c0d0002d141030103080d0355001b01c4170203038007a03074207018155000e107040e0b0a8410340c0b600032205c40010b2019030030b41214840c10707199560040c181038202c1070300003985a00b400030b0540d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 529277940 1250 529276690 529276703
    0x3070809041103091e0316022103040f180b010203091315091a060a08010b1318150f08030702010c02040b030f030a090e010f031203061e140301020a08010509040c12 72
    0x4442c004409240b848003c00617584000c0d61420260544c3c00305841400320f4042c3c00b943c245c0c0200440b4020f070700ca904000c1c0b098030003141e880359038903808890784924038040c400c03810604040b20711015034a03012702d01c04990140c001d18140040c900c02d025444641c045092481174072419800c0802e43c107040b49002400b02510301044240740d05642c140000c2d08114514001c1404001892030103500c011020306540310300c4116036032681c51001e40940806250445410b100d640e440702e020900c405d5008200c00d03040e018822074003d560341c190048450461203400b0b038680080200f84010761064400403111171004000003003021403140030a16002201c04581460303800010074400c02074204101400402030603001540c50360400850400c00b04c5540b00081c40540141c0c3d682ca481c60181c0c210740042c01d205030100c0d46000d4019071455a8008500c00c2d09906e00c48030098040f5420706001303d414580035619034044030b9281005014544500400030380c0d050040c07040c040b03031411a1300101c2034110300414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 529279190 1250 529277940 529277953
    0x3030f11041401020c0d0b0402010804051c0c0203060718060e01051201090504170403021809010209031204090e12071209030614040b01081b1e0a090222080307080904110309 76
    0x42c00a86003044c1d102c080d9114000e5000000001510000e0303440c1e0040e820710701582c4035203d0303250452600b801822540c511006018510003810741c000300359441c5a000300d040307c0c040d0b100c0700400c0d5204680702c144244540c90410301880440e0040010307908140040c07414902d04058004089480b0380700f0b8116031125030710754040c4820701c207088481070000c0c080f203010356203054659800644600c10718104510302100f0b100010b0204c42d829030545800240103410358031084420141003615030320900845029a140104481d8040e60015002d21108040c000c81c034685030148e02d03048003500700701c03242d0780070007091b0280440001e595009844031a060640f03800b00f28101898400c01c1100140c10280da20383c0001d502035002e411540341040356400984100c0061044e6164040c036030b0f60f0301c039032164022107a0000044e50800641c002c0c2070008101c0611500d4410901000c015080248101500d80c4d10a0162101044a001c01040c1d8201d0040000522a45014044103d40c00031204503a0f51382010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 529280440 1250 529279190 529279229
    0x509070602030a02280f0b06031e061302120709020403060c0e030c150d0e1005010609030302031c02040e0a0c0206062409120105090a0314040e0403030f1104 69
    0x200422000362855001540c28190307002c400035507401c0250303a40d4101c010340103d280102181c51450001040c1c100d58640075105443c00c194485060036100d15020340700d0441410300d40020225000d0a03035070800042c29a684a0409502c84174005a030141e03448103810315803a42c0c01e00c040050b0801041311420160705c1d1461820200b003100c046007524010b000ca110a1a1900e980118180307240803801c840e4201009000c904d251a0390081d502801d01c030924010581454030340000d00300340654004242440a40e80f80d4200310b130090910310004003d40d00500c00d442c88800d0511202d02c54840813040141844d503240200f259446050302d02e408281e90b00d045440803540d060000304d80c458010f55016817011031a00c050700c06041f039035155880054010419140c15035030b2000c100500b000703043c000e0186080802641d40c82c0d44940100b200401e100e0080c100d20080018107030307000c607003058443d10344d1740e43d903520140c014110f1085509a0325503181030f05c20620101e4400741c4003515010502e05800d4850 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 529281690 1250 529280440 529280443
    0xd2c0316062601030305040b0319150e060a050306190e060f071d030601051002120708040e0f060607080d090c0e09010c2a0201200d0f0302090f0906220509 68
    0x814501019101002d001031020903000801c80d011224400d0403a0354940d144c9014000c480c603100240d1803900c1c1000c040d18410301091020030195403c0d600e2003a00c940b5a0b00801103014400c0c4510383e015007021000801c0700c107040c032004c0301101003041c0129032010030404050421000701c0d440500301901d1400d00c42000c1e4441002d443e00541140300141d006000d00000790380360340502ca114031481c03490424980092080c0329292520100f05030707194940040c0d14221074190001d01856907210b100400055996440030a00303401081c01400c0140303000841d49903911a68000c400d1032a0042e00c5501c09000101960316032001040b130b25020741c5040c241321103198207642584a00e401004401d0a992021441281c8aa210042d000c240c5003080c40d02440103035442d030041d103141640383c40261300f4010000c40200341103225811640d10b1111260803068140d00324061a84040c4c0c000313081d4004061035041004900382c00c10b10050500842d854035096011f41034102c4031107811390b40d4850090144c1401c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 529282940 1250 529281690 529281737
    0x60e06010302031e09011112011409040b041709030303072f03220e070215070c1a0c160305070c050d12180f060806030d2c031606 57
    0x109280951460500e03180d4405201c845180b81480c1c0313a001408221584004d510400351140c003215000c0d00c640b240740f0f00c000c2d000424801e500f9000d03400255103001d446d00162030741c400c90340300004228a84964030b80d502c00c59403145802c40e0314402046024444d6404201039071140c002551081c070b031100c415460088600c1d0f0081c02803a0030441d0241100711a40100540d0885003000c0091801441160425811148130794450541052000103000880350302007054020840201082c1c9a00d2701c070044102c07001d00d41c007403010340013030b503103a1600000c00110110a500030340411882400c091002e64604400105220206d001c200000f0f000c0c02040280ba407140000c0c40300f00c03000d03000c1015548030a03103c0d918040b888402c011a0004a14092001031110700140a200e040d81000303588402c1c0141c994038060b14154400d12a51613034200341c07407107101e44100000c3c102e0480c80c42d6806281c0340d0314404038021000c07607050041540c00703041c402c0800110030003003ca82c2d8032020044801c2402206e40c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 529284190 1250 529282940 529282951
    0x30e030723040b041509060e071215150903020901080304080307030c030324060e040c120b06071403030f0702010504201c030f1404120602030c0f03070201060e 70
    0xc0119804218150080914000d0203080801c000111a0300e640041c0043c40c0e58075003070381d10038901211a242d84501c0b01440082c0c401840c010001e82d611003136862000340044070410001080c006903c40000015001003c10308820b03000b07198031a49030300b11402d50303038800c1c600c100002d02e0b0ba1500f041586400304619006000440107545054103205049482c0d01c1403160150174030200031109800c00d4440d0380010850b5007a044034500040c3d822942c2c6105142c07a10400d00010102c6086528501d094465006000d805403100e1447c00410b00309200a4403401c0c14132a40082c1c1071020f04085903040c49400f100c0003003000516a1780c50601401596914090540000c580c903090402000030002d02440b80c084403500c14860400180d980020301201848040351b02120540407a1000c00d9004186a10201c1454a4081040c0d01132181c2044c240114802c01c40d01030003000480d4003051083e402590424032182c0700d81e01e003070503481c2203c181364010b030341c2e48006039500d01d020404182d2462001d40c020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 529285440 1250 529284190 529284193
    0x2010e071a0a0302030c0d05071e0f080f09070504020c01060602060c04060546020f0c06040b030c090d1103010506040605031c03021c05090f01050c0f09030709060b0304030e03 77
    0x50481c80031039981c90203148070b00c400b070550010110b81c404514000b074412940301c00c201480945050000108001029a080d80c0c401c0c0d0808101e400342e5010b1081d01c0062740d016a9041a50340da10b0783d4030541101d0243c481c0d034190190600119a41d1140c1c0001c0084d040702c40004035080b450300500074a411070040402c40c12460901c400d10017954000110350096042c1e40c0090348104c2c0c052144a407944403a4981620221101e407a0560020300084000d0181c05d40e400745d0300c07282d4503040c9103903d420071982010f070300c03450400051001045690140da000403a50011908207040500803400f104641c020a071050640340c94059043c2c5424050182c3c0303c5000d8400b4400d9516100120343e94480786008081c008400703801c2102c400e4480d5040d108404c440342c10240d80e107140050120020b100a9540000038042e00c108000c5c00320050094074001c119030400c2614150724003c1b04c001503080000255030500909900260028050003140040c00a21031040e0752410700d4070b40901224a00171059001e07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 529286690 1250 529285440 529285469
    0x10110f150108060c312601020405150304050a02091015030c0e04090614010b07020108090313061404050303030c03090d0c020f130f050a140c0301030c061209060c02010e07 75
    0x3001c140c000355040e003600031000c5c03480f810400d81c40c0c8043d01c2c0c00380c000301203d45400f90b0004003c03000002c505403001e40164500c2c4d501c0e225080003420307840740d405115041007510740406803090100300110f40c02409141520902080d65000a090180c1500c9040d1110482c01e401e00048446446070140c48481b4203041060054540001c0d040410903041c45e0702ca01d5680c80d441d018403801d504101044180000c030f1169030360711401503506503002518103170300151101e8000340483d40e0000898401044844840c0e103103500d4080201d032480c82810280051361802d000000780c645040020714050000e1042640d281d01c0c007464018034120050401c00100803004a0500c00741c1c032142a045140c4409130703a08038403100249030707010241282e46040c1030500c1c5044100300540005500500303092803c5a0880416103130035400c0d503183d010a010180000f982c03407400300079240c01040c045102e4119010041656455500c8403c100e074074841c1c510026175156070888841d01000c0c8181005480805072100c003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 529287940 1250 529286690 529286701
    0x70303080f09011a060d1d0d090e01030c0302090601090306020310230919020c0703050a060c0915120b041a0907020a030e04020d0b060a031401090501080a0210110f15010806 76
    0x3c210000344400c4c0c0c040e100005412031419045d4028001c103031010660780c055440e210340090b544202c0e0050400000b03000010100f505000c140e1010304880e00172111002e254116004c000c204840034001606102c403000e00007000400038006540320b001880303515908140b8005005105060205a40c1660341c8000c0c818102c035620140d00d56081022107a0007040315030b0070201c850091003039a0281c40d01d845100800801c0000c006840084a4460386090100003a46442078680d80c1c1640a04c103070f8106082580c038003075807054040300c0020f0006480403c10341a4040071404071840500301f10404a500c00800c202820820402034010030b1510080c024403099840050082c510000320070b129030740014041001000c5608078940038a0018403080e80c4800e00341d00034000701918008800c12010410000640035001c0c483d09040b100d4202c0a480c402c0c240b0703420403401400c040340c08010b029040307026040040c0c0401401e6044082c0c00d0040146906003004400030b100164419100f562082c400c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 529289190 1250 529287940 529287971
    0x150301061e0912060f180302030d09030c0b0c070302010b0303090a0909020a0f0e01080f030a140306010306090213031a040c0312022107060b0405010f0b0c01020c070303080f0901 78
    0x5818000307a11a000c080880340011210301d105644040c001c45840160311052194592000d0040301c100707542040844e40c0d462821005a411140107800f681041c4a040c8402d00c01e82c0041200d640700340350000b031210143d41e030581c0c003e0059032589450381740800c5400c00c15409214a68114808034000c60401c90080c000504841c45400b4482040f61100001070444d116580d201001e401581021001261614803a0403106824130407114148106c00803540d0004011003213030602000c0340d503414110500004c1c00e1541d944007074445410075545203400200b40600707101400103155240300e001d4169196090507410400e8202c03400b10150601d04c14840020340790045e22080f20790080c00c440c00c030580c845041e030605540101060700b601261801c51480c070711100041c18900d2048504000e4105c44109100c2202c10074052000e5844072400c09100c0901d10001808006da0307160000351401144468160800103554000c5020824803020300a00c10b8180c0d440030b6004000f40020080b0300c4180e80d016 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 529290440 1250 529289190 529289207
    0xc050c090c0d09060605121c080408030403081f08100f02030c16020d0506131e0302070e2212030b060f07080315031906110a0c11010314070e15030106 66
    0x1200380c0f0b90b0740719440d040214a810010003030000414a10202c0004a002c40c1c540d05040c0074200c04880384108100700e140117180750f80c0200e800460304c500359a80d954094510784405056100004401401b50240e8200150180060440302010740055001c0d850900107841c004007060003003a00500c03c001005070104c040c0c1d1460400745910110f0030003d40049080c00c051010088e1250051008102c2142c1e2130140600070745120303c0414242d1f014038030040034000c0400e500140140c0294904010b46603d4420094002c62706150254090b90301520107140205912022522500040114107643d9014400e801000c0800e88a2519100b486c0b8030701e20042c0304051303000300061800300c081191002c920030f0060010b0380280454103000c01e20241c036204259035004c03c4441500f031441c00141c044011050381c18041280d100e580030000a5540c18803941c003a001c0302030400d40e807603030040c04c00c03a029000ca6000c0c070314984a07a49048006d00600c070140c0304620200f080c8000410040100981c0408036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 529291690 1250 529290440 529290457
    0x303131a1816031a07090f1508151f1b0b090106050301180b150a03030e130c09060503040512030c130b03040807020915130b0405011e0303050703020f0d0c050c090c 72
    0x3605600e60b14182d040d02c41000a8101c0d107c9455968804192000300503000449580a516070010315501c91201a000340141e5103480d41200340288410205203d80c0070355020306646003000300c0b02c52040030304400c207114064801e4484030103950030301c0b42e122000c0c81820080c00382038000780610109140351003503072560032200400d4101d42e200043c2c90058582014551050028010440f840d5a03080081c81e0040304280c2510500d4901140c00100d9002e108088812405444014680c4d00e4090107403020b4100030b20a5495010341040c642e5101d0440c80118032611021101980307a001c0400c1c09440b00300b86400c0007807424010010301c00801d0072074003510030380c1e0340c111503041850340ca04024200d4a8510041240c200d00701b041501040091a001000916810756041040340c1e23076101c10310070610100e10311a10700c2041c4c1009101081c03040c0000c01d130580c00303401180c0c0c4900c50030701c4c0103140189140c2c0e000e0004118040d02010040144140ca081c010100c405130544c0c108110720365050300c1403814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 529292940 1250 529291690 529291733
    0x51503060415021e07020f040902090a020c1f050f070305010f0b16050a120e090c0d020c03070b0c0306010801080d0210020901090812030402090f090303131a181603 72
    0x40031080004203404480240d0071600d04141a801c2814100d0b1107900400c5d0704030705c101110b4030031401e01e0900b4031421034010740081108184c1e45501d03004000941c09450f4101c1d0900a82115181d110f00c4060f4480d040442c00303400141520345034802048440700500100c1c20182800c00400a484030986c40600b51858030401e02d0351500381c408062842403c0d10350003407050240030404014031038180241009448952102e1000120080030001030349002c88150903130380800d012680061402d9405850000041d48c1100e10f40340c1c035510f5581c0400000c4609496071040007003009050f50340042464014920701c0020200c100c000c400107501ea040b10050840c1455011a0300c0c07403240e10a041d040000c15031b0f20b0035154003050f0381001049540c02154140d00845a203000700315454882c0ea07180c0c0c480c1d00c40301c2c043c50450311a01107120b40d80c08001001c1d01c03020000c43d9035820421280d101d4a004035010b24440100d500018421400d004185900040d041d200c10000c10100e02c000381610b0044800340e2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 529294190 1250 529292940 529292963
    0xf0a060c0e040509010c090906082107081303110a0503340603060302040c0f0507080c01090804090c080108060c0403060e030d18050c0f010509131118040515030604 72
    0xd0841c0c1d11228008000d0348141003c00703001e004a819070041c2c0d44464035603104031005446450030700c2a940035100d52104d039802003520054621780c0e40092070400c0e03004203000d45048442e86480320700da0801c9030040001d4004c01820800c000d042d00c7d00c00d996410950301d4a40103843e100020303498202c2d408484c3c882d140d43c0100c1c030314101641030869240d00505c40c01c0324200368540c03900400900f050301089004500d0301078981d52203030040b86185201143e0344e940301d1400000741c0e1002c1d165000a00310540c5d80d901c40032400002514200030f403010b05000d420004828400f1078004040c9501039020101ca41c0000050200075403c140c100c1e02900e80140020844101a10800b031461040703580440409191018032042000f4002d41508814024800c40d001c0c4c400c01d40c2004641c11007019001d01150f01013102c032003a810302c5550940982d40040000030701c0402d02c00c050a6662195140701814500702701065420301c6d00d80724243d041041031040d00061900b40300403071303502c403000390000d007040c856003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 529295440 1250 529294190 529294211
    0x50304030c02040c21112d032806210f020306342a0b0103030320030402030c0d1e0305040306110702030a03050a050f03011e06020f0a06 60
    0x45151103180c560251003000b4181d1044d000424424505801c8202118000d440e5100c814150040000d004190188079191244000705021b42890403114900146041c1503990a00e01000000e944110340f0620446c41000c2e15000c0d099009409031034801045d0700e408001d01540c001002e2151800c00c05400b0b80036040350b40e060410200080b418029414450300003001155600c1500e00c44a021040d118000607404640010000c104494038a100050314a04410240020044803448507240300180741581c202c4c0da1681641e00c0003d0300103a01003a215100c07070b0b005e8400e0840b2032000801c500d0800741181001e60000c2e44864000c1c0710ba81c840c10030000c0880520801c00b14030745202c2c001041c8141106601c1c900a80290032a1105454091070540c4604601304440120346c032180c2d004019000710b40070b680d41581c02e40c20500345041000300c2405944884103c240086020b08441c031000d000c400c5060502c128064601e0f001081150403030404c440380ca0034000748900c034903680701c000440c1c901e100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 529296690 1250 529295440 529295447
    0x2d0907030b0303040305010e060c0c0a0221100e07080a0f1704050d0f05010f0603260418020d0b040b0109230411120106140d02030c04030609080c061e0705030403 71
    0x5501c48507810302000500104000055005040c20507007081560503503959802d18052a0041e5032a4003541e40040e0004c000624000d062580104041c085422010b02020070359850528a055800059503940b40d102040b1101008400d009112502c001c00f003801d515070f10821b40300d070b034498000c004043c500b607083c11040d05407054502500001d4001c1c001d04c101828a0341414505c480140c1d844d518058510281510314010303182130301d400546c1c4a4041e2481040220300c29151606040044070620021904095484814100103481c103030150f160142074042d9411140c881340000c3c8104e20300013100590b40d1300f1454010482d8006980d90301f01421406910a104e0010441c480e4070910346008444081d1021016200110580130500c1c540da0329000281d8080c01000e5074a00a03d0090201c14a44041a0000c690040441d19032904190f40d90f0354445c01c0c0c5511210480342201c0c0403d4144289900700f0010350310001510518000c40000d604442c1e403e0340141c03002040210000021702418003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 529297940 1250 529296690 529296701
    0x60c0c030a0e0315090303040605090c15390105090c01020a021912030c051b0f0f01110a140d0906090605160f0b0a0f050609060103050403090f0608062d090703 70
    0x251310041458500c0c00060841d103d03402128110390b0a480e010114840720000a40707006844800f801100b1101001280b40d040364010718248119516100c924200c42c00f441c0036013003041055683e41c0e038580e003111200ca9007983d800400e507101541c0011415445070b0303800540c10b001c0940540384a80e616440300729040003051640c100810380030b21076104070101644081002c000c140900c0c00e03a001c400d480582c048200f045a983c0551041800305c00400d50702d4400030100c5440301c1410403030256090005030ba1b05024848400390303240f0b142000c0703807240d40006203c5450840c0c201e14041d45c40c60b0502c0c0d0041c24400340c6008200402401050152241c80f001c812640c01c1c940102c40c201000f06103140c20010340700c084800741c0d042410100c0004044070b003809014014a8000c00071940e40c2d640400442c000d0100170403d6041100c01280016102440004070001e0401c80e0380d205118500314050001c43d80729003c0044098881c264058214051266410181d9004544000c10703a115044110702400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 529299190 1250 529297940 529297963
    0x513050609030f070608180d0806040203060a0315270c0905040809130c180e0609070c1a04030f0c020d170417060405101b03020a1205010e0603060c0c030a0e03 70
    0x202e040b41c041740303d41d0058001d40c0b060074003040070740c0d440080f111541d442ea00c88001d002d000c188944040350322440e00350090341d484070300903104145d01c558030740b00c0300c1a1032031840e800318050b0b0b514481d0042043e88041c40300c640b40c03110300c07490700ca51585079a4504039400610402d924250784e08045400c116548046500e04503005000d9242c00400d0b0500c48000c2c0344a0308040046500350140d1020100f000d0300e040704913a0030800c1046103950b49824000080303001000e20081101e031200d4980010501180d0224403070200250082c07030701d03092070054112207071004034070306010b0015110801a659540c1c07610419030b00a420702c1d9001c0103569044014000c54115586074003810071180100c0100203101489030b40200c1c219641e8070090040d14044900d40078100c3c406103455a00c00c4080c80c00b0741c0050054024600d40f40c072480d441204004100c500a8009405440c14a810320003e450104000f0f5003003800c06401078500031800441950b00d10032002004103200724481070385101e643c1407000d4000349 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 529300440 1250 529299190 529299193
    0xb0d0b09160303081f050109060e0a26010b0319030c061104151403070e0105032a09010f03052401111006051207080c04020306040b040c020309100513050609030f 71
    0x76480e0303d400b525081c01200c0020f550490186200384107020240381c0380c12a04180c45050106003001411600749141040703080d00012102c0d170008840c10f202c101c6018440410960f2007010014400050942d02c1d42412a4802d92100c034090f1480d00402428045c880c3e414104a03c0d400201e10b8a8800f0b0302030350300c06030015040400c0c0001d00c081c14621034402c00e20b00303030307a4180704060300f018062107400306075014000607442c2840c0c1c1101e5401703500116000740e511201800e0850364802000f214a403c6000030010500119002e0641d5030400c1d1403c02760030f410300702441503250215902d00111841550104442024820b10314181d00950f2030a0b1042d0044050310700411031904900081c0c4114441e590181c402210585514000412040191540d150280a45511240800019401c007801d4103030310540e00d50040d0710507500d521034030540490359000b45403140c080c4010498451041d900c10414000708000c07001d000200035020400741c0314216601c603203c4030a0302c00b1a16040d001c24a18516 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 529301690 1250 529300440 529300483
    0x6041212090f0b0a0e07030b0604090311070f0f0510080a0f061a031f0f0e06120109050705030c0103090b010306050703090807030c050d0f05162a090e010b0d0b09 71
    0x3400110f110306440b801c88100c4c180080c0030440010355403003985201c0541103940f4800071402c1c0345032542102d101d66000385403480039003600c09044e40c00c2002030b9000602c0f40030900d40412406810449050081ca0100c034036200381074081002403d040001000050043d6030f44880003c03250540c5d2010f80a030298102410b015a0320500c01c0321140d00075115000d002420310341984c3e40f11000c03c519801c1d1007401232180105132800d031048000e07120103000c01c1d40c86880c603058200102c0c000d208070307250207000d040140410340c500014141092480c2e600d480c1090b0501c8002d40128a000c1c42c064112684080700040c40e980d549001c4008000b207410081c000b120000e60f82041c103070700015400303030207004405544000ba01002d06036603545000221202007502800721110102c000400414082d01620941412940070b600d1000b222a148152410310300101c8000e201c802d0f401d03c11005c2d4826010000c010400900f0300003880e281c8034500080c554640880000c2200034244002c5481c60190464142c0d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 529302940 1250 529301690 529301693
    0x3150310021b0601080c010c143406110307020108040c12141b0d0f021203130f080f030906070317010b07021305150f04090b0a0b1206041212090f 64
    0xb1241a1542c11020703110b004004a042d04000c51603844034603058440d0303600303104150741d2140005180c403954040e0f8082e020104141c0c0764910584032449010418080000c22004215290400150818401c02502c054003120f01000041110501602400d0294183e582c81ca4141b44010480d00b01018151041029504000c20856101c01e090412000d0300c034a1812010040362041c121800160310041d568244004640090140e800c0f207130029014500700d840024240707103503900c96030141d500c546141c1001c101c1404800282c001410001d00035110404044403601c0e41c0380961000640f04000000791002014001e4000f41c14682030001c5074070340e81d03035201351458044e00110403d81c0200070a440c0200380c609640f00e1725225001d08150791705149200020f000802a0085280390442d503100020000715412444162164068140104d081e045603018801444940382d0300051a910410505c000a000c1506400d400d80c010300c0c141000d4440103400c0c2024001c0888041d060001c1c005100c2d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 529304190 1250 529302940 529302967
    0x4080a0c030b150105090d06020c060c0d0c0c050a0b060109090c03020706050c030906070f030e010f0522080d09020a0320190b030103290c030603060a0c02030315031002 74
    0x302142e00076030448515584005903200d820007450350440c00668100103400c1146031608542070340d54010b0a005082a0031030341031a10b007401c2540c8680d001d001c086800c42150300540100e40c101c45441c80c09141540f501d03540c490b0380d089a940c0c01444054247c0c0050102d91044802e80010500c540b000e01400c100d524016000b0341c0f01031000d8611500b0000010101c0070301c00d007120301417610310008201640c3c40c1d0360304882c00c41140302e61604064444103020303141c41e024021b45a0b81862840e000880b4100107002a111509a00c004071800c00c59202d91400714540c80280d0700c20010449011901c840382d0700c005200b500c000c0d000141500701003a2940c9000c1110350a0081e07407030042c0d03a6411020700c84016829420183e202302013240204000500000b080c4030490750b800d1010074042c0b24042c41e002c2149030902011650007070b20640110800c50603140070818907030842d20000c410840c07601c0740340c03000307459100007003c480c241d2844124010f55174504001401042403075201c11504d8000c1c444806 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 529305440 1250 529304190 529304213
    0x60f18040f05010b06180409060609060e060a210303151208030609011403030a030908040305070608090c060909010e191d010e0102162d080714060f0703020c0304080a 73
    0x142d41e90342c81e004403e030050074410122a0040c03a800c105809442041c0c04000281c526407030102c1d45280c6425000820640c1d0f1702408024050315180c040c8036182210900c26442465070052360601040200000c502c40f040307000081081d09464041012000011183c4c120760180c3c0c00a8004850700440c0002d01001a01460241074111140304030f41e42e98a040440401741e4869030f40d41070704108440070200307005e640039807846c41c80396400a080a5481d21000d0400041d40c4c0004041904402040420241408548203000c0219101410210420b0103e0b1b0521014000e9607110128000400c000c03641c5055080814180010140030f45c26440744a0070288403407601f5512503608088400d40c8100d818000d44a80132020039158120b0b20050700c0d61114407164200c00040040b90016490000c0341c9807550084041c055070500d581c1d080146020380c0c000c014059208102d4018105000d0000804040305822140b00e240161f02c2d1200100414111700ca1540015510310464600000300408040320 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 529306690 1250 529305440 529305443
    0x50c040512031e040e1b0a1d0a090e06010b041a030702012901111f0c0c0f08091c030f180504140a0c0906020304051c061805010f060e060f18040f 64
    0x240700c4261034000790280142817004d1020f80d20041441f65441c083d2154040d06c01803511100c80708281c403007910108000c1c20300741d0028400d29817100a5900d6298003041410f0040650a11a41c6814504400c02c00c0400366280d0031607000d0b030700001203110f1600c01d40090800c4224006491010032203000340101c1060826616804034600b1184804a41c1e004a005100802c640f00b10150f840407008907240200045c02e0310000b4006500100400b04094000301400c15215800c10b0f65500142001c2001088010704020300b907060081c03a0b800040e510401c86005102c0606001c0d000c0016681c14a01d41c8a2541045401c07901c0c185207015104440041c050040401c0c010070489000d03c12012207007119540918400342c2d108000800c5a030400c0e40c02c13412500d199040a54a44010395500030a071034180030300d400c1428440c0340050a100d000c1c40380b031107550a1034900b000413900e8880d42c0c01660100412003072080034801c6a80d22540c03a261070341404e0419682d40d0070742b146000d242801610500210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 529307940 1250 529306690 529306709
    0x1e1c0201020f030906030f0717010303120612020f0409020f03120403020f040603050d0e041409060703110a0e0d020d1416080a03050403060f0605060a0201140604050c040512031e04 79
    0x50082c0380001c02200d1403000054001c81c91640c503081e12010b00880608030104010100728440041c00b0020b8105000e944213640d40b1010f420309803040000e445050b00300300c489003a10710440c00140da409094400d44c003800da4001c100d01006000003034400070781e181116018050003405043c4030092800520580e8800c44400b0030201030f8a0500c0102c8141740030080217948140b444440c1c59010705e0051990040040c00031403030030b040349529804074609445102541d448001840015505400303100c40e0b0040d401d410b141894440c1200401d8030781c2c1a0040b03401214a58440c03011340d00d42000c03102080d030b007044401b1954180942895518410440e03070701c6c04e400c1200e5000c10141c0020079422209601980c5990078141140c4541c00244880c0c0701410020f65180750000f002c0d2a088089c0060000c40e400002c1c1062074405081c084001c02448a40314a2a000401c0203000a4000b907405441c810303501f005404488804a41c510300c2180705280451448004250b50010b481d07000b84240c1700d031140b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 529309190 1250 529307940 529307953
    0x12060f05011d041509060501081c020c21010912170105031507020c0409150c02031606020a0210020412140d0f080928060501080601080c1e1c020102 65
    0x104102180d400703000d080c0c42e80b0810306129512442e032003100c60300036009000142c255a152200790f01110442075044a015803900010822500c003400400303020140782c065809039402000b80207445061a0340410703c68511304588440410005a002c440341c02c5403030003002046554181152058100900ca4002032014030302c00811001ca6180325049950180c020f03d01d000100c0110744040301c0081c01c0c803003148950f440c040d04c03a64441c0101e03190b19024a0480341c00054801d0010b054900c10032580046d90b00400c00c6010f841c00d052410b40b540c41d0464030058907038010b803008030308040507900c9107201c02d400850041940500e21998071070851040c80c10803007807010101c1c025140c2640103c1e41c00031813203c1240c00c1c41d0314014810b02d588448050191000d8224a92124a50220703109010f51300019620383c001c1048400d10a49002d440c1e0b94004122940c034182d0b425a940c1360001d07a16000304010040d490150400103000384004400400060807a0601004030f490901e07694810b0f801440303481c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 529310440 1250 529309190 529309211
    0x5030316020312040816021c021e010215040203030f03090102031f03110f04020f040b030405070909051c0e09070e10030b06160203070b0c0f070609050117070e04061206 74
    0x41240c0f00c00b050b5419040c5150b641da1076500b11508403041c0b0126003103203114003038011b07079031406100100f2340020100004000640184111a03503906099018207450a0900c40c10360780019030001c103502090701500c0c0c0c40d99a440032a046005a02c440481000003005010000c0c0f019000b45124401c4c0b040c51181c4003143c859505d041100354400501044e01c1c1c003003c81840e0902c16862403c007032000d0b00140c038101c065041c50b1410350256102c0e04541e40044140710801109204a170028102d046084c48807002603141c407500c5981064050140041100c2604030860089025800601d0b000f802081c41c1e107006d280140c00540e190b020b03984074030045100381846c11f001c0d10808880450242035181410b800580642c03c0c24050003060f6410311609500203600601c4400510b40102079401500080c0003070021545845080d030002c00c1407201e90b81040c015039a10180c00071800d40703c1e1b201000552209034003910a42182403c9c00d41090508274081380a82050540c50481c604c078000802100090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 529311690 1250 529310440 529310443
    0x21b0d11060c030a110d081501080a0917070b060301020903070e090a020a0e092a190305030a0c0c0602011b1d0a0f0f050a03021809100207110f300c0d0503031602 71
    0x111000460038580c48c4903204654441d0b1072040d84148001400112103115498201070155148505007000800054103401c00095201540c2c000800b90002c0d07060182d0400042e403500481e0180021140c0e401c000110160410130007401c480c3e0300604140d58650300c5103124031041008680a245503c00d5801e040140c01c0c02c5070080002001c90700108994910410030440b81140c004210202c407160715074044085442070004095401ca15143c0340181d00722441e103101e554901c0e40c081415a454410503000c80150140c2c600012401c500d091008002429111030b601d42c485e945240e00581400d0022898100c4400d040c800c1d141d044001d6040b00d40e40c4d8042200200381030100940000180390341c160150386180e2843c4d04400404191380c0030200c11402e000c1246c01c03140c0f054800c10500c460f001580c1c2400204400005810754440340b0301c400040103001d00001c1d1009080160b150480d0049000b01c0a00200c10901303002030568030000141d05045540c0d800589500009000c00240d51041600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 529312940 1250 529311690 529311707
    0x20112050403030f1d15090709020c03131d01090923010506030c1e060706021e0a08012114101104091b02070b0901051c0507021b0d11060c030a110d 65
    0x907090001c020031801b1000590943d0310240c6440c9607446400f001240d4007079030340054400070050b00700850322410074283d04004071000b40d0120b008212115510501e080000320f616055801c0d0102c045174900081c90b1104403400b1060701c0c0840100d1040e00724001c51019005140101d00817030440d0150050a0104040c0c00c04104103c01c0d42000003190301c1c482d09212000e440240d025080040c10301103420b10ba0344031400e20890550b40303060005602d01c0d1854008500e5809426a8039030040482c5002d4003007030801e1000100500400c00030030b10102204001c1002c08460008a4014450000c1101401d9400e40107405407541042c10100c640a4441032803501d140c940d23030103500410b401841d180c510b1249500205050f41089802c12030740c0420816620041140c111841c8002000e140841d0000d0800c0c2040c015040e0009120808411560716035442e00f03c4190400f11a608405011700041c400d4810411004014080401e0203d00301da0800780b001b690380d40b100d0560b591021410001c649085 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 529314190 1250 529312940 529312991
    0x5103912050105010c0b0a150602150a061a13030203010c2604032a020a03030906030b030a081b030d0608070e010608040519031b2a05060a0309020112050403030f 71
    0x90b5400c0307410011407060100e141e00541003500008e240c807003007801d012488016400040c050390041290740d04054240580540c81424141c08102d514140400b0268204020646003401200030440c4500e050f102103a0100560303009000f0442c05e2a0000041e18108103444d511418201600c00009a0b9908c1c00040d40f1517980350795805118038205554812000030500e4040d1503005503845a00142c813084c25541c050360282e2600c1d00601d150070001004d46400d0b1745d0503400f07504000d10312030002d001001503c29110b418100d4a03441c15074061480d2a41c098000c0010341e49041c2600001c0c04080406c880059811030312a00c0e83c181e8a5a03000d64111a062740c005105501207102c0b4011a864110440340c018821b00e003189440d120051000107091028034207031a4800d40c140c43c84240315599200e025440098032175403080a10342400600103000c0d44108105058903880400c045a10515503640303000340d2441d040000381081e040050003820080e8541024500d0090361079400c2a40038200ca0710324 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 529315440 1250 529314190 529314197
    0x5010c0c06110717010207020907031407030509030909100303020c01051204080315060a020705030f0c0117070c0c090506100e0d031d0a060c05070e01030510391205010501 75
    0x92070114101c8180540d80c031071071158001c034040810040e06030540b04c10004050f00025072182c5440c0104541c0c240c001e0550014545041e000c000540f00380a6250341c00201801e00184e03541c1c4d2640c0850940c41786062035540304c04010100701c0740480f4405810203480c00399086861900180d40195040d1160a03202800207110720005070000388960300540d8131a003490410305078401034402141d81d5410180720440075800c05e5106111a00b030412a0803180e400480c0148800051000042c014911002036403180c52104400030361503500903d07030b00000c1c5903c160b11403002c1e91784842d054020b01d0305548031407050103d414000f1071944103c0462801d6400200101524481071b5011340d50042c0d69050b110701c1003042440211507070b561014140044c1566107403540c011104c5e1401a09248060304040e1141060b14014008201c00080c0030005032598040020343c4140e10b100300400308070f0120a0a80540c2c444041d24980e040c2c0c1441610f0300d503254440d141c00c41c2d001d9034140c00740c840c01d001e0b05000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 529316546 1106 529315440 529315463
    0x1090807240c0c020906030114010b03150906130506130e0109140f060615190504060f03090b15040b06040905061003020421050f0f01051005010c 64
    0x10290300c80c008212845104002511125000d43c01a004105407000100300e91001d43c03020341341000b132070800d00d11580c0d01ea04000c40c950048805100c01025901000f00798100400704030b00810008004011030900d10a400c4010903000382601e5001c2030041200a00d11020f124078150440c0c284004540c034007140c10480c80d15180407000400540c4001024540c079507012070202e412002c11200240c21489a04044205000d48288494142241d1400b810f54075086802401203a04548800c0300b1460304410503011640706e0b04000d0500d0744560300003500c880e4203043d035018054004100041c84491040414500d40042c1c210200081d91a01400007a240210181000d4141480c096240a05205a450310460030111076403043c0072281c41802000010701c001401d00002c02e0854041d42100050907000e0481610322840d200807806012907503500c19141ca200c0f25420103420040d = true := by decide +kernel

theorem cover : BRFrame.Cov 529136690 529316546 := by
  have h0 := BRFrame.cov_init 529136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 529136690 ≤ n) (h2 : n < 529316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
