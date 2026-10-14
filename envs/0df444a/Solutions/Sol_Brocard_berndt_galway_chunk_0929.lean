-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0929
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:01:51.826338+00:00
-- url     : https://prove2.me/submissions/075c462c-75fc-4d0c-8ec4-389f28c5b24e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 166906474 ≤ n < 167086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 166907724 1250 166906474 166906489
    0x4060b460e07031404050a1a190509010e0f150f01060c0605130203030f07020906041505010f03090c09091a0c0a0c1103060702010606090f030b0a0903030e01240e0105 73
    0x901440c0c030074404001a0620312075000b2842c4180c441441e8000c030308240c80c0403070740d43c2c04d4030708211840b60340013050703c0030080ba06541b5480340e41d134040b400341a140c24a288030001c1c07002034003241207952202d81300324660101b000b11b164181c3c070002c010807007010403802d00907a3725000f800001e83d0002500040000b15480b00748104001e800c0100080ca07070b1911024100002d1078590000c2d00b42c080850340300546c1d0641c60103818610700070349009240f60b4403002040b04807025400d480e15407843c810001e00040d4801d00840701d018a00e4100000d1695003900d030000341e44d00c26413100d8a0141c444e0245406c00c5040c1d40c1c0d04554040c000e01324429814214607030820707405059040400c0202c1005800240860840607142810015064460300e040c25074009028015900814002ca0a071704000101e06502c8449081140c5c0c10207811030176501c5101c000d0000c0c01c8008400d40c1013503102d103103503015a2001e22030042404411250b51254400c1d0101c3e05000c800a503222082d0111b030640104825101c03070303c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 166908974 1250 166907724 166907729
    0x15010803071e050a0804061101053c011212020f07031101090b03040605070e030d05030a1d06150906060705120f071202031e040b0a0804060b46 63
    0x14038010700b92111060b01011004840c0060301ea4810666800309108080c0300420039950145d66811000011040711820780700191000c00e20b080e02c0180143c0b500782d1025030150154051259000d40c2d00c00400150711540c402c1e0070a440c05009800c0040800c045000c0c29102c190860014200c48001001855144c410703a10003d402c48030540c03900b40413a8032400a804c05014030100c0311b91a07003401d06140f0014002103400802044083c1c800003030750300d80001c8011207603850380e035010701e1981d85180150192606089030444035026034591011403d0602001e0f100c1c0d0040e001111030700e61484108040004042c0009018020400001001c00c00c003150031141d2038542c1c41d41c96950f1044240c10292882400006000d1f00807644031031804a501000070038100394040c0c286c689400d0f405528a58030320562142100d4500104541804c003801908241e911901404001411448079030109141240c00948411182d403034514031030f40007e0407400b01041520110326105035004a00b4028030031052030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 166910224 1250 166908974 166908983
    0x5040908180f120106050901050a080a110406030f052d070303050f12010303090f0f0609060c020102071e0302190807030803150d0b040201031b0813020402040306090308091501080307 80
    0x254501806499481200c10700582c081c0400ca000c3d031104003000c1c0202036502440d40700f400f40400000303407413130200e4050094401c1200588111184c036940c01030030810880c069030700580ca500000021404002c1a4580305000710040c04240002524550500062040c040c004401e25241b4503285540081d40d88281e03075150500c503990300007100f240b08440c096400b600c3c0310403004000200406612403420ba003120412031403028101d4885046d100d0124141c00787d80005003884d40100122071042403070801075801801591440ca44480d504040c0c60142c1c50150190741d200300c1c0400441c10400c1c01c00d8104442004170071841401c08400c01d4480c409480b019003844d01c02310101d24103041c2c400440a001000a000d1305224070549010481400211401c2c0d02003841d000c1c40e018514001d01094060981c0ca9540c0140c40d0758108088982d42c4041005980080c1e0900000c40012094451444568043e4407103404901d01200950315001d090310b80c0d454015442001080b14010002c10759240d107510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 166911474 1250 166910224 166910257
    0xe0d0f0c03140313020a090c02030304061113080309010905060f04060f1101020a02101407081609030b0910060b040e06010e0f04050a050a0b12060f04080f07030e030705040908 77
    0xe800d0803a0144018070900840c5500081488405980b0310300d4501e1191003910780200741541e4500d80c0044039160032465000d60004c10020f00007901d0b6520108848145424076820050407400c00402c045940c1c200c500c40b54400508501d456812111600050000f1070310035292900058400200740158400c80087c00602d107010760241d070041401064410b5810700031901c0f200b10362402540d40130490688131006140c070b5407041c0d524144010441c460942502c50001c1d6450f1903800c0003100c404020400c0030002080f0010001030ba081c1601400345001c0402084080c04090801e02181c0c0c0b81d501c400c4201204200800c0b100200899182e4082401d0038a4100c0340203181c04617020080065000341e003e4a071004001d9006020360059000705c1144108005100e041001d210740d0140303c2240d0750040d4064800510002c203805a0302e580640324401d12424442c4030040c0d020315800003001100411620001c04903503003005c100c00401460125001e1042c0f880301d4403118201d201c2e035008001080b0340d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 166912724 1250 166911474 166911497
    0x2040903030f0c0305090f0c01140a020a0f1208180604030e120d02060f06090405070b0d060509010602060f010b0f071e06050709150201060b0403020f01020a02150c0c0d24060806010308030a0e0d0f 86
    0xb070dc100b4440d240c21082481080a20b890040c06090001440d0000f040c2d0882c049411603112010800c2c2c46240f000040c021511983c07006c0d02c801c000941d5565204802007a50300c80404c06010301000e0f454260001d08013030a11000080b1108030007080c05004507a92000c1101040002840400721244400d403d56034800d05000403024060640105030000031080000410680c00140c1034480d001502003810b03d0707600d072000560548903101c03421002e02400c0c002d200101e9926224a1420704100859130050020b1f070303a603c810b5400448414000c115417040410461010054144820000c0d2008002e014103103c1c0ca4602030080d400040d010340c520180f8003245900070003c3c803104540003001044030400b00201092254080000e503441402180400c1015080051903101400e80c020184000f04852005150310303055072600e607a02c2d0a0f1258000541404207201103400b82d4007442550b41d8904c0d01310126420782e5030900c01000c45510018440000782e40c041c2002c0410070709460b20003102075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 166913974 1250 166912724 166912727
    0x90e0f0f1603030815030a0c06110106050312130e040515091615031416030f0e07060305040c091b0f2102031009060f08010b090f010302040903030f0c0305090f0c01140a 74
    0x5c030f0169410b0300b41c41015840424014400c00000031984195a11044216120203c5003682c85a204d6281c15074015000701c03a4421000300a0001005c0340c407004007525940d0000c0444004003a9019075031900035a0080c1c00120740380340450341c0000260010b0802502da03040c0e0078191071462091101501d0340c0403c80a41d40d03c2034106a03080c0d500e440003c042400d00030007101594070403c822034003192a121008107400814011806170b07480c010007030300c1e683d0b15001d4294090000100110b035140709680000c0b074850902e03c05c142503500b04100c0145002e1100d1030161440d29003007030010502801e80134614602c100d140a42c101000024005278407a10340840c0c2c0c0c450019981c2001076124105000414190b0900c1c0501d01100d20890007841040030b00340902200b0b074030580b80d401d80d09a2070f20060016082076000380180364400d00d40011561100b2084c0404c5581c0d001e004d80000303880d1014000c08000402c0f45002e110784043c00f8050308080d000010705045078600b100511039030082000c0e40d040e0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 166915224 1250 166913974 166914001
    0xf20091509250908160b030609070e030f1506040e060a0c050405030706230f0307030207030203090a0b030402030c01030606021504380c03130206070507090e0f0f16030308 75
    0x1c001c00d00c00c1c00b003112440d0750290070204580140314940c445c2112003411280d030801940b0442e03080d500001e15580f01d40c824002900c0d80184110700380800e10800e001142c400300244e06800315042c0240400505803c001c0c41c2c5c603180540564401c0d1304081e20000c1c1494007040352504500d699200184803650120300340c0d05402240c0c40164503010b101000150350340c01011241210003800c41d80c90450207030a0a145e0203001e0481002000c04040c00042c425038020713030082145c07078080c1c0103e0303003486500c40001d488119680c000e081d10410220a0000f1414108043c04106100f42810301c4500c0c14503000035074072203100f240c0b850700418481c08070301800110700b60300340040300d9a50b4844030130408101c04a465800c018802003822900000214203044030800e990041d050021030710f44130256602001229040110141c6490040c0580014521355901c0744807551000c03203019021652030018480d0402d83c1c11000c0c21140e4222a035800300a0008204a9050303a50608045145da210344010388003d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 166916474 1250 166915224 166915261
    0x70c0e150303030702010603170a0e0d15060f090f0507050904020f0c12031f030309030609082205040f110d1107150504020f0d020a06030e0102070f20091509 69
    0x5404000309004c4c00316410340081042c1c03406070410100c162900071032503d1922a004400e00014480d45441083c0e02e0118040d00c01c081c051910110304d0442c01e10300300d0481d519540440218441d80364108280ca0b120b0269044007446e000e0200903e261820f009000c82c45100403a511803540082c0310001c55000005031070410400900701c9044006052014985034029a90482e0f200d00d881109038001c80e07001e05003020b03261716945996640b8136564130000901201c4808440c1c0b8101030080c0a9280e0300c08070395981c45600b0b088184c03000c0c2c0c078000901003260451015001c1203402c00805e450012109401c403070f0210010900003d00f080f45080c901c46600070035000502c41c000e032400041138551190000340c0501d000301c40501e240c9041804101a0f1140c1510081d08030904550800c8418001e42c0708200003c01400007500e0200c280e501c508040c0b26010f006c80300b13000000320400d030000114109410415060719415180d0800a07080e242c50440760700c0540c422444a400070305075103400b1803c8104c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 166917724 1250 166916474 166916479
    0xe0409030807030b03070e0f010e0903040b070f032c040e03131206060506070311010b0103020406120c021603050708060c070c0b09060f0706020306040c0503070e1212030c0406090b070c0e15 83
    0x1f1070904141c18080c45500384507000d2000d13409030110380c0c2c0f103901008a4088608860405140150940d1080d02c0700c03006050540511180031400201c0410103058622084100d40001141011120402c4111120580c0c4100a9802030180c8040c0c0000303c0a003005031500c0c40400d4402e00701d0b501d050805040b00b034020580104020412104060300000141c0700c0041c000020321010348048011000c078025440707414005240000c0c480d500207002d80c81a0b141c00c1d61441a904070b454080400ea4258285a2085841c0d500851040005041c203005403034102801c4200c0300e14104203a15800c0b2060034078003980204d44000038000b002ca41d070784001c0300d03403907410220002e8448800b401c2c8000250012941c03107005509140c3c151b500248100120fa1040310f6035101c0180c038603042c40c10b215224006000750b00c040e101340c070500042178008802852145a042e201c8950b9141000c2000340032215941c80810200010f2020f07a00041804d04c031003058601d00f400c401000d5852403803000120205030181e54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 166918974 1250 166917724 166917749
    0x903110303130b070c0b0310030602210711011401140618130207060b01020a0308160909050c07031e021e0307060e0705100e030a0605060111011802010e0409030807030b0307 76
    0x20205030f00000742c00424003868410010f943d0b640c640310310600c41141c1c021909491000103100156280c0d02408801000e802007503070940326446401020385060300c64001084000c50700d402107a070240205540301100b00d00503007040d45001a014813510701c1c00003892240c48085219043d8111840c2030300700c003110050070b903508089001a850002d500c1444291480fa0800c41e084496500005070000f1180d4182d4071030300d0559808210911700482c1200c0c40f0b08010038200d000855101e5400b5490240611b1210383c2d55504481c54054190084080540c941d032400280c48003250f50045100070980c0401e144000c0c2c45604051034038210700c5085c000904503032414400c01c054201c00035941d41510300c1540c004103041000c6005640c2e000c5210310341541030b0b000d256003400044d04c030f4025903084941810300342800701c4146145400d60300b030711002c40100c240c10138141c1e06540c2d002c1d51100c0907040071b0354108600005600c0c002c08a4000074201d60030f140c0ca51800f003c0d06e40b4200902d00060000420f080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 166920224 1250 166918974 166918979
    0x13090507052218020901081603060b06070506010f05090906011409070306080f010c02070501180b0708090d08030406050f130b100f0602010209030c01090609090b0a030803130201020f0d090311030313 87
    0x3c08035900004042e030041c80c40100109821400080318000080007019001c4071a25550701d006c0904290718002c0c2d004507003403021100151040044501030560b10038011252030814043c0084140001c00d040c03e140d101e035004100f401e45580702e074002000180c600e1002e95850100540c05861154004a181e200d501083d003c4a101940500d1414030290f0a981143e655600115007460041d104c201128040901c108450b0a45030001c2484510070031a086c00c0811810000b00f410389000710030b850088000040008011183c840c8a6114008810500d0303207040000c807003a120600c211000b051000b0440120344020443d214038002000c009440030f5003181c403080000d010350005c01405009104020b0b180100350300801a803070603a525941d8010f412841c0c980218064201c3c1305500e03810100390080480440c9003440103510440d4402c51403110781010748002450000390b424400c41903046048a00e42441e403103008502107a0300042c4a00701d05d00304800003411480707041030040701c03182c00d240300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 166921474 1250 166920224 166920251
    0xb0405010b0a290c010b061c05010e010f030204090501060801020f040302010206090c03060f0a060302210610260c1809070603090b0703050705090a0e06130905070522 73
    0x10810070801511021510b5550f80211040070001580c44808800c003485071030384040400016021020201e03001003410410070000c10115417103684a08580c44400c0310316542c5030200c0c010503004241d96549403406615092a003540d826480c00020301c83c075240c55a603001c1c02800d40025002d0306810008564680c1c2550004035164050b110880c058002c210000710301d150049540031140360060081c10722540c0e881d5903800e101c1001041020180c0e5200c40100158aa034441741128001c0e80340d6009982141c03114541c60000011b10005200d0035800d002d11904100c12030180358040b241c0c104d1104443d202895901f080c8aa4488540000c0150300d0504040205441540603421300c0e01a580ca007a111003040702a1a1a10720142400034041c0110700f965110754000380d0311003001d24043e8181000e020010b014900303244e001e11301e682c001d41c0a00c00240341c40c0d141c0409048001c0c500700711046440c1d494036101c0d00584207151007441c01c441480d0710544078440e21004801428020000760707c0c181003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 166922724 1250 166921474 166921481
    0xe0c0a02030a0f0c05060718060804050309010302030717010807030606091803030b04020d1505010f0203030903040e04030c080a020c091006092904060807030b01030504050618030d0e03071a040f0f050a0b040501 92
    0x4042540900400d0001409d601445003c0d0049030000007842c9070100510054000c2e5002818207002c100e44c0c2400c9101107502e5008050203050368602501c106d501c0d500f00007056400700c1d003001028a1404444003e00d04d08012029220b90b418100800e1100340200000c00070700071001c48128150070201c01c69041403a10190f001525400d80781c0d19a030443d403502c1240d4902040340da40c00d1590081100380a11444103800340e520511a15080700b44050343c0d9600b046039001074482d000540c2c030210306031500345002e841d15544803103913003045c0d03440e00d140800081282456108038148a003151005410b8103a540c42920205031001c44c420340e0303403580c4100041c140003080701c0d04400030745440440a081e61190044030f002d2a0083c00801c05901c400d4181d5082d41001e52070348450b44000c222069003a1024020b106e40003600001440e00ca03400340c01e0084101c1c00e10a000d0700c001c0035200402001034000c9041841c040e8100208200454903403a10900d0103041602c0542154120380811040060540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 166923974 1250 166922724 166922747
    0x60e01021308100207080d0b0f040e0105100b091302030c09040e0a03180e06010e030a151a090c1204051504060903030b090106021b0409020d03090e0c0a02030a0f0c050607 75
    0xd0072210f0019407035070340b0002c038069498020034880081029858168098100c040c60100081407041d05500560001d070882c0d010104200c0265114010017481e124000540340007044400e50092421181c80b000418a42100780c01000c01ca078040702080003e0403400a0b0790a1640c0a40104504140c413040d140da40c0351103d00880004103158a5802c4103c22a8114801c440c0c080020400d2929a10300540e1000000a8115054407440d8194000f06201a110610900b1075180009075140c28400154080c1140300c5514020144001403120100001c000c984980c8072241e040e00c41502c075464000d0900c840d2904034803641c4482c0007400240f01056220080c0a0b110340c908010003481c41041c000f9014003407180b4405604001c910380707128034101c42d4141150300c00500020700301c0e4480d4006002c2031032120007030b80081d8041070140401002410f107140c001a5003020641451300203440203580b4480c1102e16810030503091225002240a030103100b250075801000e4030613524022000400111009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 166925224 1250 166923974 166923989
    0xe0306070503092a04090510051009180506013318090c0f1202040504050a021207050408071e0902181509032121040302060f06060a0804060e010213 65
    0x210401344403804600c0501450030300300c3d101c0300514003480040100130629008191410b0203141e2468200c0c000034400e942c45108200408041c19080202402c1262032a240f07203071003c0d051102400c0813078800113413141100c2d042c00f006101c00c12000414945003500e01c03103025025843c190400403013a002030780016009144001c0c0c01c0656038945480c02a1403644080401094200a0211b0b045c0d102d520b6241c207805a01c040503141c10b0755031011a089030411075104020f158086001c121b8040d00c040b850350006000c0c42c2c41e50400b400c0104080d16060b40340704480360041d200800038452070380061030708001c000c1c00104640f1001422001520710785440b014600c1500449191402440f0301c0c030070ba9100c1c80d405002070204880b0034400d01c0108180c2c1039142080b000134007032a0700c074540e50680f181c0317000001e0926016508191802a00d0908050109015010b191042207159169081680e0003917241c3d1802001e59102c1e828400c0042c020b0701007240140d40001010249105c05819840844852 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 166926474 1250 166925224 166925233
    0x41d010603150e0a0c0203040f03060204080c01141603030b0d2a0803090108090c030105070f080f04031d04060e090a2003030f0d06050303041202030f0105250e030607050309 76
    0x300e24102c481022580125245980454003040070303c48143e002401000702801120310b81501c6240311001506030354400c417003d0b500050180b106c000f0a00c9004e02201081c02e008810400441c1d104038130b400703041001800301c05841505420705109810013460044080c0c00101412281d0a140207403030002c2d00521080105000035025034a202c005407811130702d0010182d4142000b00004484805019010481034414664080c0e6180d0b801c0c880c0a01a00d03040c0c45405040801300805049440b00a06020707580d088482044003290b082580100340c0ca2404d500c4046002003400024020401c90b0048000141c0d00300403c03404510020324400400e0003044000820319406004283c00c10080b5071898160f0420f114004040b0102006044005a04d04010031540d81b90004a4615006580604c084039180059002541410300048210b4135555000b40428a020528944001e202c4130b00d00034404e4076078080004143c032480d03041ea4082d030014203845141c148440000d040703400603185412180207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 166927724 1250 166926474 166926491
    0xb06120a0b01111009030513060e030d0c120c03050d090804060e0d020d0f140f010906060503030a2003090303040b03040605090a03021908091914030705090c07020303041d010603 78
    0x1945003a42071158400c02008502ca080f01140060500e205c03086003405070070f00c00c84003803440380d01248020b0500d0b6507603040f01040030000c142c80d00441c407000e0801d010b42400b4500100d10f0b0050080c2c04d800309070400915560300342c5030440341c81c0304105040410910b094820030410005600800c2210710541c2c802e20f000420104001c409400b00780b0003035100340118a140001208598003103400e5000d80342081c12007880315100d5003840c003035840b44441a55a10104400c0000c90321427800034113000c2d0015824000598030151600301d43c01d10841503400c001e0040c2410800400440f16244809030079241c90b20750714141240b041e0010b89003269210b05000008034041e90024203000c8081c1c0580c000c0c03128484100c188048480d0a801c01d603003400302002408880d4132081e035039003444d03404901c50b0315120303180030100400e1046021540d4403230741083d182008070f07598209980c0d8102d4040304490365207550700c0c80064518492a0710032004542c02c00c484110101c0901881c0c0e040720b046480034480c018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 166928974 1250 166927724 166927727
    0xe0708010c090b090d0f2001080c0c0d0e060c030409020d05130203030415021005090303040501110405010e041104090903051b0c090f04020118092307090b0c010b06120a0b01 76
    0x800340c043d20000900c00e1110b06400c0c40c1c54000b608805010b0441c582004140303444013040311034020300005409109080160041d64420f243d030381e200d07a62446603030810041c0401c054031115083d404004100c0c0c800c00e040540d5484504403001c01203800200c96465680300350b140b02a411100c400e84c111031400e03000800d0f46411400c04401d865006010303602e4181801501450301000861407000c605c00c50940300c405e010705104150107005513000650b241d1400707140070350a4030401c05000401c0340b0709100c204020b90700900030b10b1464034205c6011420004201070301082e4007465015890150074911900c044c1a00003000b01603c4201500503180f40038440901641e58100501c4980c1001594001507500080452910342261052605c0090780d629074a4608074118260003512070709945603004d8040000a1280511100001c4118405d516000f00f018144d82047d101e1115a4040004d0404c0a140c0a6000e00107031200200001d45030141c1c1744070000c0e5003004a80d1840b02c685061400441503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 166930224 1250 166928974 166928987
    0x1e0c041803051c0b0d08090f01022e0f181e0506060904020f0907020303091603080910090f0b0a090608131e05010504060207020405010501050406140306010c05010e0708010c 76
    0x1160151aa00d107400b4400c01545400d400b503115540c03c00c1d0351940749030300c159598146000c0b5940079800440d151034400c4101f1115000180d000c80c103540c000c1002403009081c500550590049042000c400030030a02c02c003002405030000100550f528041d6404644100e0340c0030740c480b541c020400700589545102c411035258034810b4020300f9a40c803500015400f842c101c060140e00070301c081e0882511140c1840030580244c029182400960000700c2081501501001041182c651a001802c4031900d540c507002c03400c3c440c0d0003440d0b004008148084400c64050000040204080180c1c1c1d821540d55005030705c415040b56001c03400256075200002010351081c210140079651302200100c00510750360f101d01c112f9000d00415007000e50440320a0300821000c4c807401d48541e00446016a565101c1c0c4100300c100c40c0142c0002e4103011041c0010b10401c0d51100c1c09100303a600d00981e007940c940b00c0030010303030b54a030406c07100400c2c56080081c0f5001800010412808440d80000284030004032440246da50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 166931474 1250 166930224 166930271
    0x9042901061d04060512210a082410171005031c230301090b10020a150b09090a030e0402040b07031809022206020d0e040903021e0c04 59
    0x6410030010107644500c2c1c01007001a001d00900c00582c1030b41c0c42020607a55203101d125103145410100100a1104c10580854a20045020240c0c5444982d48010304001c20142444650400704083c0c141c16040c42c038110404804018101c10004544503402000c5507503249802030307030009a90204040011080707651003035400003801b42082181c46444140300401c1c820b00e0360300b0090032009507403100203044c8122054441c180381c00b960740e605140304a010f032148501407e001d03081003a0300451265021401c482149c0c5e01013099540800040d0310600500070030503409a00650980a02034900c2000480c918054407a0300c0c1d40101c0f1403102c0c00c000490055200b02514083e04100890010303214156403014400d841c00c0c0512080c9d1139440307400803030308000c44020401c01c450080d92589120003030303100c1c001c00030707440288641c1300d41d024020100880704001500640c5c0f52460902098028092107207980c01115590611010642c201c43c1d0321001812401c3c011071900844070851401c13030340100d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 166932724 1250 166931474 166931477
    0xd0b030309090c130b031311030c1c14120a12060602030f070302010f0609020a110a08040504021803010e072c010608060d050312010e010617060114090904290106 71
    0xb59950b54819080c103074003994441e410468254000315910400802450099000e14500b62941e082d40c900781200a440c1418039100c0e601a10b00b110380c540d100d4080f0b9603585a43c80100c28150b890340313800c1f580503031400c070a00887d02484840c0e2000105c4000900328040c236581c1c0e1152090461082d000460b440e5005107030043c0c101300681031051044800400c40e0510034800020f07111284191001200c8258101520068000401240c0305070310071090a83d04507043d002d040b94012641c2d23070311518031880c0309080c010754010408910720a01e00c02140c00340315010f0020300103e980c03550126203030415401652030014055641448400148403804000701c407401d908040d5908050301911039401c0105000e51108280b40403000065007480039150084442e280101e81d54100000c490700340c4c4050704040200094076010400408001c054260002420b0802d520404203141c000c4007a4810b4003c159000392010050008001800d140c4142c151101000c41844c00114004d000070ba0b5001e00c84d400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 166933974 1250 166932724 166932739
    0xa0b04091e150501050a0507050615010f020d08040f171b010501060c241107060207050d1b1b27110705030403060507051207080a06060203090a1211060403080d0b030309 74
    0x40f0079401200245511211070030000d007000503695440d0b242c442c2c11904070340d810859022241391541c00184141402003140054248000c80190080c030b108070007400508040034102e8480c041c041e00002400300503c034240e100340c0d40d03060940030f410403c0180c0541600c943c0303003400019000b0301c035000030842541d0204020001086e1b580e501c000d5010b00c80b02c1d0075041a40c4102c0703010341030019401440c410b0700c1004090707120a102e00340385042c005114803403c00e100343c0011010074030000440914170b281c0e00a10f001400035000b0255100b0f0b1001c0c0c3c10140382051411403c0c0303e00e03800101c0003600030741e2445060012005a041841d2a40502d01e07008105c1d038800d01051000a0032900714503400442c0d03181c0b1a0038940c54024100b44290151403500104018005101d46a125030069402422860000714981780790780022540070050340c400c0f031200c9035803840d06408005443c1681c00d42c00ca001000f8607100c40d1282803d07c034031f92001c50001502d5190140c00c0b48903013408001e49003a54001030290 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 166935224 1250 166933974 166933979
    0xa03090f05100e030708060429010f1211031605040b0d0206040302210303070f0318050304091a0406090c080f0f040b0712090308010609050603010b0f090a0b04091e15 73
    0x1510180e600d0850661304d4054450017241a0008014103803146004071040d807066880c040108520903900500c09030b8102c40c9030010b010148090f0601030486422680088840c902c5050011061083d449015410b001d85003a100c03014050054040903128100d0b0301b04014803401c000c100e02801c0da610001d40003d0144010270262401c86402c5801c3c0440188400c80c0943c418007a80c111f510407142c9102286000c02141d034680da05202d00c11004802c0070b0f400d0745004e0309880d86540c9004c0d51140702101c1d0307168040150100341c2c401404115410150084c4150764551600b003001d4904e02e01c9140000309000f00041c0c0014000007614060083d070100d011050b1583d881d006814500104030700280721079250070110140c12445210b40c00e40c002e9403950000e5040940040030702c0e117282c0c0064451041400144081c51034081110980007281d108a6074070134050001c44c089104035030182441a6020400084040450304520540e01030b03104030555070005110b007581241c847c2e00315095901a010301c103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 166936474 1250 166935224 166935227
    0xe0604030509030f0304060302030a050a1404020f0103060b0313210e011b140a0201030e0307050c091f08100c03090305090d03050c0d03090506070302070218060d0b090a03090f0510 79
    0x14008500081d0a81d40b000c1c1c00892800d1556000c2d82c811f40000b40d001080080603c2248038140e08940c40200500c09114039501c40c80340743e8000342002c0d225010b00b4901002e00e82c002c1e1700c580c0c01091404c0da501e891f8501b1800c076240041580f001554040e0007409802d009604200a1030301001040d142c041e8071021000c011102c070b11400241c0041d0130340c4a1103d01c042062040c4c0c6489240a98005100789000c1d031000400360f501180e0b820038a80c0c01401a000000e03400314611100000a8442a049507a421504101b0342c000701c010304c4803030f548480d01148244004c5a4805091300384d950a01070044d1039223046044408021006e800030300140502a854a092984045018041c0c6021402c00e0f00c140304840c1880f8555264501003940ca00b0701c00c04020061103050f0b03003c000c4d41000c6041c00400d40110b642c03130070f2340c1c1842451150740c0c1000950780d9466541350070349141c10103400e072030a241c902001560b41e03102e180140d0104050300000144407109001c00020341c1c001500310101807501100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 166937724 1250 166936474 166936477
    0xa020309010204050418030314150411040302090403020703050f0c090c0c1c0306060e04060f032a0609140409080f0f090d0305120c0304030c0b070e03010c0e0102010f0e06040305 78
    0x32405a6540070000002c042d0744501443c04040440401921651030a281c05000c41714903494200400b5036007010010403003001707a4001140e160907038010894520035100c00c1520305c42c44d00021350055002c0e090006156000907580d00350380c8580c0842c6c0040e50030900c0e086d40c0361100d1020640c0f20b41210006a0060446805440261821070032200180b405000d140340c1d9888550300680060380d42c040c00c000155100100500c00d400aa41c104003413030900c003400240e0354550101a22002d074140000c0041032410a000c00f0340e11988000440050700c03007000a1824038a4800e1010b00000b07110200144e2030603200e13211100d42e1102d050380c80d0500358020009542c02215040c0500d141c14451385010f80c40e1406026004c1c0d100e99261640c4081c0b6189000410a01030202e4024030317414010480001d410a060044041d04140b80c1e005a6803441c000725002c00213101c00c2505542402d294105590704041300d6091103809800a02c4041c4624455504444a00b0b60584056006401080c0032170700410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 166938974 1250 166937724 166937731
    0x50d0c03021e0d0306091808030403090b0d02070c090b091506071b0602060106230708040b0d09060b010315150203040b0a09031a0610080a150e06040b0405010e0a0203 73
    0x50350b4010300e64503000d42d184045114159125003007408070340302640d407501c14000134104142017048011151001e0300c0070705400c40001410320070004040380506004112020042c00111000c907603480c1c00c09071f884040e40108504444801c451400030903050110300030741000c02c00180015a482c0d171078189929410818074030454002408020800100d50268040301103002513440c0c0f001c08070b1900400902c0d02c03005034403141c200500b2290040050f12179070745609181d0b607014100390311002c483c200310590344030780da008205607800050861081c004680021443c2c0e03020f0141009500403030001901a140302940443d42076410720003d00145c10025116500520036204a90030961608005101076110198010201d510f0036010401c00041a44508001110404403845410b050380800c01c070381c070414103060610040e0300001d120030503103620118244510341002d200c42a07640700e51104004050355501e02803810450808980d06042c02014100c660514108032613503200740c4480000c0d000074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 166940224 1250 166938974 166938977
    0x804150605030a0c08060c0c0303070e040b12010c09061b06020d0e250812040b030a200d05010801050408091e0d0803270c04090501020d020d0207050d020a050d0c03 72
    0x340d80104050b102000000382079032041011049003801e11228078035200d00201041c0d0910001c00081460039804402d4176041013040c100140c0354101c1000140c082d04883d11441c1d004800003208010221b41504015501006a00c6180d00c00d6141c580032210302066402d451100d038000b0002e04000703082c0d68010442c807410701200046111407184400d06200300000082060102a01280c11034210600324000404c1b02400401002c008544103074468000d5210311500e1003008070004441c51025040000342a040b009007041d044000c002000d4250400e0786a8840146018000703d11078030140700307007801180c1060419007040c035400100035041800011090444250b00341d4a6216120b00c003101c2000c40c400d10307105440340b0b0803420360701c0c0031144400e000120224000eaa4041b94001003410b0b41d51620989011645400a043c540d02a100e02941030900360b10000e440d1049004560280070158441d07810b03070742030200c803c0c022070344c503403900a02a0068004117680b4003810701070700130110303024440d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 166941474 1250 166940224 166940231
    0x1a1312050a03140405010204061d010906110a0203010e06090d0507110415090c080402010e030d081504020f041502120a0e220c0c1401060b0409020a090503060106090509100501080415 80
    0x20008200d250320f2040c0c2c1c0c1207602ea0b4002c50300740304054100d0040c0400c0100341246a031070660400c002801e0742d50728420304090020101110851940071302510801c0c680140085c001204680b0b40107543c1d90003118281c1003400784010700c4078030b584194100e4103000c0e04801c0d800c1d6400c2c034650402004020480b501000086049130019107105240941604030312076440303480940c038003400050081140c10480078072a03007010032100c0c0f245e90441e8809400c0800b42c409500c1100103240440c0c02841900d00c040151100494000b4000d010244200910300040c0d084d5103080c0d48081c1c580c00b00e4024410b0480200d8444401024581007803050001c0302c03010407070040309424207841002c04607104100450005409409183c003800704c4680c03104101550711000308410f515044040f007440c0a10700038129100d03000210209607900c078140c1007001d048020b040e12980e5030f407910080d141e100584100d5000b0108900060030701ca40c0052403c08560041c1c442149a54580e130b01c1c80080406070020007451540d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 166942724 1250 166941474 166941491
    0x61a01142b0207030206010e19050a02090402160c0608090d0804081201090209190f060509040617100c020d09260303131709012f03071a1312050a03 65
    0x120744264122030501400060780d58529003070080c10703c58160800c1445644042c148030340015032843c054507280451600040540358046900040d1040d0b018961703115002250764189070021803207400b40148594000c07016155030301e40c1610140400c6a559104e43c1107401030b44d0f0f07a01c0c0629400c1d9070143c440d010991401c440c80348080b100d418207811651645030b010038111400e040c8249511512142c8100700c190a503d02103586035001c181e800b0300d601b04100843c05110a0b01c658000748080d11455021030f01120203501d4180d41ca02c801d03041d0000040c00d04c1d01c901c3c902800070070708901e07004041d40c51000c0b50b401c080e042600425951400714071011101540e101c40e1406101560041086c03100340500c030b80c464207001110003503000050f80014000c00103080141e07005100d100a45003904000d1201d000c2648400400060342d503040300716404005410010031071100d6444011034107080d01540f00d0707180c2d201c1507103144020b10401030507403240d00b40d0410242d024001504410500d031802284404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 166943974 1250 166942724 166942777
    0x7150801330305240604091a0409080306030618120304031205010603051602032508040e0901150e06030d050d02040803070c030c0b030f040204050402060d090c03061a0114 75
    0x412640607540041d6440b414030603c0c1407420980a402e0025a2014290070700384400900c2c10b20584c401c1000303440c0c5d1741c0c417041c4002c0410755400d1210440103104210703102d840d0402981c264022943c0340d00c20300401c0700103641c016101c2c4407000d20301c1d82d6030010411001841b0441c070403540301910903024408001c2c0c0c1c0500c0b190340c9001d00c038041d00c0c00356404551420600a1034000c20582100a410b5401c14451401001c070030314484c01643c0c10101c00c4d4001500381d4144030045110f80d03004800344142c12001c101d6069030541000a5a0b86041413002440c3d40e104500c1d40d501c00142c2d025036264020a00150707202c0d22035400382010240d8400010302d080d65482c1071501e103500c03060041b00e0b0541480010010b00452040c141c00410144032441e02d140703400100041d40000040000f44100c2e66040803c06544541c2c0c00d8507a140c1c03060104214212846c10b02c600030300071a100403141c0c5810444c0c3d140104044005030409060183c441244142c0a0041030383d964000742c1560341c444480248904d5142c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 166945224 1250 166943974 166944059
    0x307031103070e010810030332040806150d03081b040504090b010f06090e0c25060b030f01110a030b0d08030412030e030703050a0e04060b030109020a0207150801 71
    0x5040c82d45840c11250f10800016207806001003a1a64a1070413290800100c0c2d04841407880501e01302520b0501113a20000c00429281c0611480e40200e1000c18049550b5900040c81c50280c03207030a0300c0900d03945420003080180c03003c40000070006110940400d81800d08510010030041405802034109074685001c1401c540201c170098495079120001004501170100d4074001030185460b244440303070700348090032011401c090201c85d50740b003000030140e0b114081c0c840e0004003102c00e00c00d48850320804d4109000601402000c40d80300340203051000c421903405100c0c1e806400a4141d0701802e00109540c00e41c01040d990761043d8014001e961850001000140214400c0d842603130407403540ca43c0300000400300d400c00c11350000681d00404c58400880d8008003540c85842c4e451400d02001d50180700032501410540c0e0082298160200c001308201c00d50303802510411740550f00722065582d580d13031070b4051801da117070b00800070a04000050110040e0a902d0310003140941544440c454600e11462404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 166946474 1250 166945224 166945231
    0x1003050403111f05090114070c03020102040f0905011e080c010c0212060c0c100501180f1503031d06031b09030307080706091e170313020d0f120513030204020307031103 74
    0x121030f00407103002d202100c42c4100d80e08641c120008000c0c00c85c561803001c50201e0003030940414065064500c00801d8403d40454004c0c1c401580c85aa045035503035100d802405083c01000e81030603c0030740082c0f030415143c403410212000500100070030300c0e0000c015140000010002e0ba04081d070100900d00c3c840d010822030713024068403680c40c1d80e1528a1800c2c1420943c00c0c0741e0090041d03040600401900030003803224941a503440b107002424a501c040c0030001044d812000d6001c0c450080d000205140c0c1100c001e65009681da452000002150001c004c101c0c40110740034101100b00c0d2040740c819007002c80152148a4014080700d03d00b08194075040055041038070b080303c60300c2d121f40c510020400c00054201c5010120011030807200d90950300c0e400c0e0502c88100501000310b000c0001002d00030340020303c0e14181e0b009041c5001c5900310b030807c01140018800195081c443c0c18220300d41c210300c103e04071283c22014408481c5582d09560801000c1d6101400320003c1545039522510b51600001c002c42c013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 166947724 1250 166946474 166946503
    0x5060a03090f08220b0f0d140f0406051605030a02070c05130e0d030204080607080405011b02010e0f030703020304090504060902040203090102091503060109060c0c0305070f09050a0605100305040311 87
    0x22030303641200c20f04140f841c4400c4d080c07402150440d010480d0440ca0000e80f0410b602220903d511f46081d00511300042103030101801640180360140034004950480071401140100002d01403592058078044c84001e008882000180013000014815100c983c060500541706258000c096035031400019000a82a0260000b040d5615564000740004000224040031141004d500b401d2400750074a03100c17400100400f091100000009080000030350144028490000e9004580018210024000e0a84420380c075418407440a41341c000b04c030000103071034215625500641c541801c1500f105c0141c00c000d4800c0342c602c2d03251a850300050b991030002d14800c83d070a5000585902240d01002500300d0b221404141d4254104144452030340c2c4072407400c00ba00c841d820aa501080d492911121001e83c42d44050304901880002050740c01c00f084005048070100c060500c000e40700d1085101c2150000d1103200d42c0700b000201030311601d90082c1c011070b074494000d0805190078610b0b1300c045400e100700120410f2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 166948974 1250 166947724 166947727
    0x50319020118031d150f090405060a03050c10120f091505010303080a0b060c0a0f0203060108060c031605091302090315040c0303030207170a0e011b0c05060a03090f08 73
    0x106810390900c039900074880004118046003000b40c4000d4194880d07204601d06002001a820b03095880300350100308020f4020040071354400048001a2030fa0b0801400c4034030032802c0001041e83c900e00f07841074030f00303594100000d0078400e405d06081082108000724141c00b4042030303d601ca56008070318030410240e1070400c0008107a80700ea92401c00c10800329000802c1e140341c43d00c401800404d0340400c1c05e580c07003200d544002418180c0c00c030015a081c0940c0000d083c440c86480340ea4402c0055401010038014400d0b400c0b01c2c0d07581d8139414116144c1000300c1c1c030309851000610014070701c00340700e6101c10306145003800c0162038100300101051414811a044402e03060b000255450103060410100441c2d0b48603804044041c10690344071780380301d4140c0c40050100f503001701d407281c01e12000030601d4003042031201c01c01d035079561034041c0548152000c180203404906034109103030307410400132003c030341c070355840314140040509050400c202500940700b0001010303a181c0034000051040a1108000750151b40d445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 166950224 1250 166948974 166949017
    0x1003020a02150c1b15040206090315010f0302040e0604050a03030f090803090706020d020a05150603070509040605010906050105071121070b0c0c0402040f03030503040201030b0d030806090a0c020a08030406090503 93
    0x3445041a240f000041680c481780f02481d405226207440c54100364104c507003039540e4002d01c00091030810304059072543e02d003071b01d000010300d481200c1440c42102c1c400c1c0d17414800c805640071000d403250f1041b6000343c115000100300707138002032090b4000c00308019604c600007508081c645504180e41c008848540c881d40c8861000d00c103c81d010403200881542510003005045002c0c0c0e580e40d140d0484030b408400740c4e41600045101aa000c1c41041c000d481c01811707840071071401d802d109001c0e20080c840c24118070b04d84040480e140d4443c2d8121500103401042c4000c2d08240b003001d101c2a900d05148020344091042702c840b481200c24012100105080340c1000c0d112104084500d04080160004610462040000b005080c0341c04181a04403a058200329880c0e40e203500050780074110a0440369801002200e0300c008040d00b10010310302580c41564544150307903c41c40041c1c100e49802003000090307809030304c25600040e46040190b078094030425000c80c40e034106aa82c3c528640250045055544070b405a4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 166951474 1250 166950224 166950247
    0xc0a0605010b071b06050a0302130e072a08040b16020301020d02041d01030b0126030a0522050f120118050a2603160e090c03150f1003020a02150c 64
    0x3001e41380c515041c50240c00038640703c0701400740e02c1407884000600d500410512100000055070400401c15506e42ca041c41c90b01007070091400340d1420203800800800c05840311510501c00c20200400d5010700795a282c541040501c1c0415004044425443c4420980460050f00e0a00103000c00760403a0002503161802d01d0611500e181c4003c52301841d071500c0500400c00700b81d000300c0050441d4034028203070a0041c0f0181d0024512a580100000c01c0c1c48001041c00000c1d51090040886400e0851203140410700c003990403502203050303c5001d074080e05444400c5100d141442c0f041c2101c0010500010f030f03c1c000300600c402c50529013001691641c000c8807580062103164905005030340849070a200c5000180100444d136408007801707580c501078101d07401c204a01c0c011280145209801004034042e89040c0d5120321855204903107601451011300341d0305249040202400030800701c0282144200790164000710000d400c00303c1000118460103c140c1c80381d450b00c0380e0301d034041c510107046241d6407221583e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 166952724 1250 166951474 166951493
    0x80f190e030706030902030c062215110115141c0606060306050910090b181602010605060703140304061d010605010215070804030804241b020c03030406050c0a0605010b07 75
    0x403e00500d0308082d8110016500030800d10924201202e40035203841d0311004075a40e01003404d1b070010701c4007408000030441c00780103030703c404415089540f0100000203001c07200e400d840c111007100c4000039039540e0038845850396000c0d50165540140c1007000c0f01d402c050140c030340a0280740707068581e255956414860039138103015203005002c094a0394401414083d200c0e111015035441110200d941d9841909180c1d5101c3c2640ba03141d881140d103000c494145400d10302c0341000310901c400e02540c0b07010300024103030a00000f92410603070944c0700c0315074116001e6941c00160f80003c10894405648042d945c6000c13040e80100040044000000540c441c2803400182c135045541d0444003001c280d850801c0615640500c68640c0154186800b42c41c0c1d841c4c5103400c0c2c0c0c000c3d4404140300280e488034441060011416846003804d422031243c5101c00020040003a80c85032500301105406070410402480902d001c0c800502d4000000381c04c541c82d400490f2140c1c011201c0a801ca10025440000c070036060000c80300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 166953974 1250 166952724 166952729
    0x2703010f1b020c01051e091e01030b09070c0803060409061e050705070f02060901020a05071707090203270f10060303180e15030f0a030c0210030c020a080f190e0307 72
    0x42415580300d0001805c0e078068035154819001161303000f0f026140744002507072201031001d448140c540b01e0000c1c0c1580018a4a001580064640108407581e4640403640707a0207448141c1f10b10440c5602d0361600c5440d50710041030036400584500100c40010114450740c1030300391440840100f0201500343d96030903500003030855410444280316800c02308075a0407008041c01c1c1e0448807903a943d0300d0140140d0614800101c003230424019a0000200c2c40d0a007050036200d82031007410b4070340098840460804070b001c01d03102c0080b101c43c014600d410310340b44070710444180840b4004407541050030341c209034a0200307000d4540305400e846190810416800c4103090b03401c0c0c09500341e00f000040c1040301240e4040710046c01030178241840b6601d0151501c090003484505141c080c10b5985440c818140135141000000040313001d011208a007217442132003031040c1d00ca6001c02c1e40c00307000d0000d0591201c0c51245c0280c05102c200d0402004401110220741c0c1c0c00180300c44c0c1c6919520692214001014240101755 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 166955224 1250 166953974 166953977
    0x213051801060f093b0103140f011e0c050c0d0e10110c10030612060516050301080d0c231e0705010e1201060308040305030c19082703010f1b 62
    0x102d000b8055a02c1002c254012217054012080c04010074800429403c003c0881070f00e413007441d00001205200c440d03905114003402c040700b01c03034058200d0700305ca0b07080b120402690071010340c0b00d483c0450491003030340121000f10300b9880c200e420841d6a41a880c1460409807090002c0350040101c0b68160800e088a1030a9400a0904005181918481a40755851403072214400c07103549003a4500180203500c000d024000340362103090000064a030020081401b640c03030050320b10414130410750081c0b103003048905072801c400c0980040d015100040da00380201d80022036107040b4800c150780286074050081c4aaa0400000401c46803d0324041d012410103c801000c4143d0490300c4140101e90300403502e08005041a1910760500c44c4c0782901a004280b580c1005001e110009030000034001c00001401c0c02d40e041c1000d407955502c030f8007007880031240c0440c0002d107120b00600034030352150001e114038011901c4540000d1000c405810010b4216460010080355050744c0307203010f07411009080d02801d8800360031b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 166956474 1250 166955224 166955237
    0xb03031308011d0a120504080a060504020307050f0a0303050c03091c0b181f0605060c0a0c0b09010f08150415080f12031b09150702040b040515040213051801060f 71
    0x925070f268440a640f68042c01c140d26004e55130344510f110b2412180200707800016281303250264540306003e4001610705038441d11800380042440d151210075030041d01c8000300880c2c11603285039426a03040d001102c0c00e4207103009c10301001d400f40d00c40d21074880502c007a206440c00d8445561600035499500900296030386500d9214003030b000a00041e44014200d4406000c001c0c800c00c1d40b00c548060b18290300080d41011000c01c4d40346401c6000100341150b0b510079150365200d1911009404200d02455001c4c50010300e00d80388041005014405443e0410340c000000514802c6602c0440d05482e400c400200c0c064000c4441041480c00038401c02200c02104005803001214402d540c44143c0009040703040d910304003080340d007400c1d180c100031198081d1001c3c040340818101c080840b420798100342d500340d0040342132801e485a80e2503c0d01c2640c1c8120040d01c0500201c00403502804000d42000c03114004440700d002000c034095507007000ba4903000d0307118083e218080d0305110b401010000c4010307076034050104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 166957724 1250 166956474 166956521
    0x3140d020105040c1a0d020406021606020a1e060f0920030304050906010f1101110415052706070c230d0507050907090b0d140106090e06040506040b0303130801 70
    0x2404c8141c0000c1310100610740304115000f607180143c9104540c603e8903624400600051842d40104442c0c1d81040080405003800e6520081030341c490b80c140e00c00030804603500d403003c0009c001441c0100321f02c9010707000004841001d002039030125000d00f01c2c00d866040e40d10003003c9541a420450f540103030030940185040600c2c103800705245000c080d10392418050280100a40349104003041d130312481e4540000e001e410030701d030b030008081d83c41b0713010b41d6a40c070f280d00032841c0700d09004e0000c96420403241c032102144000400c2c420107000c1140109a41c5c007620070040100410112082403025117041c28026080b1401201100c551140744200d55001d820b02214103404180c01103280b000300d81054907000181d980c0c64008403041c1c0071540082c2c0700d00c040032034801040049580000c40408060580c03d41f08d9885010035104e20180d4803c94810313844c18030019113036003440d03008507401020141c004590607000400080c21504180189000420404130411510400b4010402c00c158840c0342540312a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 166958974 1250 166957724 166957733
    0x6020a02010b040c1403180f06280203010305030d20070303050612070f09020c010204091410081b01140d0c1d010c0b06100c15150801020a0207170a06020403140d02010504 75
    0x1c020403c7c81a42007040d050009039200b444080c82001b18001500c003646420455120310000c0702d010918188440e202a0045261b603100302c1f17050741c0d0440015414000910070030070241240b4150307808507868011800c5d0b009410000a010075512a4a000c52549410024001540c940c055404007a82c41410100f110010341060881516809240075a42c4d04221108a001e48141ea001806440c50012940c08007824107840c640100800d0340c000080d260f4551320382e50343c4c4d65800c054150100c800c00f010032141d03010b0300560000780040442d507418951020369880c1112103555481020807655920645002c4043c17201c00c14962003403c041541f041291601424688018492030051071000300031541140581009034180d980204a81d201009620500e0050919000c4000c10788100d1070b80800c40c1d00c01130080e24030300840703503009105079460414500e00e0440050014842030048100b18008682c2900051005d0350096200d9062840080d91240c41c100351a44400c0840e490304d0300384400203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 166960224 1250 166958974 166958977
    0x10e010f18170f0c0703080703111612030c080a08070f02010213060302030910050117070f05030d14040807080a1e0b0103060203090f03030f04020f03030a0c150906020a02010b040c14 80
    0x1000c0b0500e000d9190340e4120003890362441940c1e1846401d109000c000810801a14000e14041d403080d945c60351420f460070b80c1d085d036500302a00c2c0000b440c003280c1d009001c0308030558406035106001e4a0304100d00c4840e900c90700900d0b4460f9070189c0c001000401040720035600a6015401e400b51071000710300c0c00301a00d0705288618498003a42041680002c046484902c08202001500d00354180c10801075a407036010006150a02461540390b01070800c1c00503108107203c26690449401074040c1c0784501c116103040302c21000010800c800900f0901001c200b008c0100054000340224100904030795000e410320b54540c0c8951070075100030084020802001900041c84181125408400983c0740c3d2140c160041c20403000b0480400248004410455185040541c80380101e0080d501104483c041c4014143c480c401e02c0348ca28049014115260700003852081c1d442c5004850182c005a480380d40c0d5a44000d80e8050924100141c1d1121000c1000380740c944200305102e020780c200603110020199008005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 166961474 1250 166960224 166960253
    0x106020312270102030f060a0f0e04060b01030912020601180e10110d020f04031b0303050711040603020d0803180606030703140c062b0504020105071b08010e010f18 72
    0x440d00c1004014030324141c07016038882c030744a40038020b42d180e00d0043c001445894040b00c1c010701caa59020b000090a541d10900030050b80d00080440359590740302e44595028201550940703040668030843c440c00300c2c0c80e0b2540c011039000564040c01c21540342030000c4c081c10300c070444904940c516000c08a000c40310001110211075081001c040352601003a00948140e02072500308034580703400000e12501c8008074000420540c0c0c840c0d401c140000c400c1c240001020041404000c0c040703001000f9605c04070341031242280b9002001003003c600607840c1c1e40132441e01c1100c0441120065404000e0100407200044a030b40103442c1d400040c000c46c54180f0020355180c4040c4000381810460350000351b2404000c3c480726030600d6000c1c00e11a0748090181d50013042c101e00d0f5100710918900720803000300000f030340d006440c0520f4050f5125070401c08103449151070320394665001c0d00700c03943d1000c0014000e5000c0c050322064840c0c0400000705001c240700000f0681c0e4002c03086086180b813040c80701001038140e146c007200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 166962724 1250 166961474 166961491
    0x30706080f07022107031103040b16050c0a0603090201020606040c02062a0a020c090109021e09060c0d03270c090b0607140c040b0103021305010e0d0605010806010e0106020312 77
    0x20701d07803100c001c1a0305005058400d2a00348200f240000086a101e0004010301c92080e61100700140d44001c415440307010724000c102884004202003051103110500844032540590700381c0b40800700c041c000030304c0c9400551060700865202c4100100307540c1c0500a0540c000c2d41a9400d1007964603d540c000e480300b03001008210114211131a0548d0110310300d10184074503103500b401c42d940301104c0c80007a40d1500e42c00302d03051040e00e00b5400071900200074000d42d25072100045031907d9440c0d1182c000c0c0416044601496041403043c04400c4c4001070405c0700250026181c0c800080c01c056040b45c00d403e0401051290141c5000450721034000303500d1030300c030700c01303c80d44200c1c0010154070484c0042c199210f80880540071001c000308594040d070707010410001d1404100ea08000d40744103500154180d00901c46501215960500108010750103400602c040c410010600c0c10245140e40d102400c4500030f070006500395101c10018004451030466031800b40405000941c00c002801d090f807000c9000c018003105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 166963974 1250 166962724 166962751
    0x108040b0705042612120604020a030b030a0c050306060105040521010b031c0806040b1c06060b0409090c1a040611150406020c010c090f030f023c03070608 68
    0x1d0754184140281c0340a0007907100303a07050061900703d100e00002d01000041d21640034008034128100300e4101207845000c402c40a480c1c540e034a8004001c025000101858103040d01c42c0c2c0308000c00d54007070000704800e51089071040001410076040c1460682d0041c5650306003c0f0402c0f0501065075038500f05091040760b00300d64141403200c0e1180c1405010410043d94251050107605540c03158038100c0709421540310795800d0815940d450812003a0703580c0c40f0809411918640c4c1c813000d42900501d003040d920740582d50209403e42d85030020b01b01b9900c244c0c080b0440d99a20b546072001c0110f904505030003082c501c401201c1c03000e60700a9004951042c0e1080c00e092205074040002c8220040c00045210405c604241d900e900e40b9041038006540a00c03001c0701c0951904019060541c0603c00740b5050b1202e0403041424503045039030740d030000000e082003130303038080140304181710003604200b10348511003012080c0501d082d0400c00c580d46025002c60304284282c018800501c01300d60707c1205168080010070044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 166965224 1250 166963974 166963981
    0x4060503030409021602030105070f030c1403010b03040303141501030609020f2a031804180b0c0c01060801021801080a0b030d050306120a1b05040501150509120d020105180c0108040b 80
    0x1d04c0b0000c45c003c00070740650a050402070715580090040f1100041500e090002a401d1002114bd099590894039a08242440140a176a0702107005d1980a44030f400d00141c442e1800c0c020007000300701107500e003c0c800711860340c100003560f140c0280001070000844c29404d150118030307600b0590245e8000e49605013901800c40d42d03003900f5020716421242d40642520ba41d0000050341801d1000701e042d11a000314241203003544650065070f00c040440350400103100c4075442e414500c010503803081070b01c48129900c0d0000841c2c840002e01c0148108615003a035a0a1800c01c1c1c80094004d400007000c01a2052410122420584012510300300d8100d17a032034411350340e69031040044c01c20f40162090b0b5182d840f81e18402410018031214685a12120a048040859861003004242c030b00034042c0301603840d550b203000b4280310b0052018000000004090308606600511540e151219604a075001030b9103480920030031a00041402c10409080d001400400c5982800a8800c29019000404142040000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 166966474 1250 166965224 166965247
    0xf06010e13080f03100e010e1b0a0216081c080106020703030e061c06051f200703021914010507020609010e01030f090507081e1905030d02040e150406050303040902 72
    0x1c5445408400f0324107600ca080c1002041c544401034004d65040d10701d0f0700c0c0045071b030228082d400d0b885a000c4041c05800140001d02100ca560000d0101c00150b10610720015000004440740e03001920355440240301040d02d072440b2421207800e10080c41d040c080d0781c100500000385e004c0384004c140e07905414012000240316010560034402c20000328030401402c5c62180107440e003604502c04480c2d040b156004620b403480150304005c10b50860243c08034210740e0903140c0410a190302803015121700015140700e00e507240c010824106d04011021410124002d092080f01c6000134018a040700a04e401c500f051142d034003190240c03094411003410302801c2c07080001540e119800c0160343d00c102c83c6007030040240b640340c810380d51261406102c400d0f0181c092a984503240040c0035501c11080d0740b00800b49041d07070450f01d5460081c15001070701c16020030860103c501400380010302c010034071281111002c0c50085904d10000c1c03a0100e00c140b0541c14401c042045540c0003054a0984100c40d90040c2e45503515800e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 166967724 1250 166966474 166966477
    0x402031e0309040f0c0306060207050109270c02030a1b0206030a1e0c0306081005100b03090102070209150f01022e0f05040f0213061508090f0703080405030f06010e1308 74
    0x2c007181d1207401c2007000003810324680c00c000744005094805114145d2203c406070785801840c016036001402d07103041044002e0682400c0c090b4980c460380051017031016420040107880c19400000302517440001c41d40baa06600c0440080103400700101c02400b074549500140040c40301800c1200c0e001c0d1103000301e0f5042c3d1001c2070f0030f21052103208030400450724030240c060003a051078450307400c103401841d40030304807007480f806943d1107210b204c07907400e00b1039040102c04d51054101420f45042c82d0350910160300183c480710042409500c0e0300111440e003a43c00810441c407242005c410074115046071010400d160300c2040c80c0c110700880040d183c0340c08110340c2c0d902c0300240340c1c80c59004081c030306200500c003d008204600011060007541d0559103405254200f409403601c0d4030507172a00f804203c04a030800c6103c2c03905c0a0300916150305a030001044080c41d13918103900c54000762103441d0005000c20240c50200400c814600c1c00301c003e030070750f50b14041c81041583c0000b052003122400b400d81410800c8400790 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 166968974 1250 166967724 166967737
    0x8060f0f0a27050f060108061506040b04030b0405031605060f070507020a050111150414010605120307120e030f250602060105061b03040e0103021c08090409061805150106080402031e03 81
    0x41185c04030b40e0b40354040b45d85c9000503540303009203c2220640b12203d0404504840035210b42c2c03900a450503207550380b500f0460030010b10944041c0801e210702c2d0710010104c000c00d001c2501460007070009080c1004000c801c2c5001070007040510900300200401a140d00e11701c401218000d0030a5409102034005507800c109400d072a1040070750100c4100410094803500c2e088618203810002c20103a900c1d0018000d0b9540c00f03030100011940148680000a0716074104018071400901d081e110030260000468946074100800c170229802c546002c0c43c04100c141d06004280c10f030395500c03402c7c1e079141c444007a441d03005c103005031030080100064031045030f0000740607025a07c20940807240d48594a200e51042003c00b800128801c1790640041c00701c550340c1c0c1c0c25214185401c90807040c03034409500100401032012001c1110f04076100d07103505041c2030500768076003003007401000175009031042c800840000010580048003440860030900c80035803400940441c42d220585940d00309440344295043c554050304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 166970224 1250 166968974 166969003
    0x5070201110a030e0c030303010e2a0412060b0f0f0112021306080708060102010903080601080603100c030c080603070b030705070c030609030e1e060904021308060f0f0a2705 76
    0x1a40a21071036250b80130101d407030180301c283e07010704220104254492000b80300d1602c000f00c01d0804914084a24249001300c10010b002c031010720721045600c025a84c02aa2040403091030144012091000385c2c09600e05c03500c03085540c0b82d865420480000c0c42c03403114200050411900182016420340c140d41104d02031801a03800c046659074480005000746c00c21540b041c005210035011078560750050041040b410782c1516501555136403074004444d0308100900d00c59041c0b003000e4030054a03010920503d940010155000b0641065100004d4850308016100302d010784d0200004002001111003a40d400445501d0015603440c42c60410304800c43c4260005042c0c00e151140c050304040d007003543d0802c2e112094500311420303044515207031000d4024092254101908104140349850942d0041035061084403180c45860b8030f0b8403000349048021517141c00c0220307495050110400c480d00d407003036101c003402c181030003a4803580e00c0d105000964864480750904040d00c2c0481000702c01c0c41102c2c4490f240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 166971474 1250 166970224 166970227
    0x6010e15030d120f0207022806080f070f0c021302300a11040e1005040b040509060106081306020f0a030e160e180609010c090602010902060313260c1006180507020111 73
    0x41004423401580d088004c040344c414100c4000501c540158145446040344101d80243c80d55030345015140340c0c001c00d68080801481d444c226005030784001050300041d01c2a0401070321040340a20803060030b0844100fa00c11828110401c524408044a500e588520034110100780e040c40500c0036031203030289070001d442c0c6040a60400c400400d42e42201012074800302c90030300064007a90706010440b2025564070a40d904488011322801e8054401250480340b03907658440c000c03a50f80c0f201c0d0100c0e00083c4000703803815000942032030040d40c140254489580701c031010300702c65626002d4120310313640390348100c000c03030001e28000440601c146004c102c22a0034000c00e0382e04e0703841d00010701c0d8020200c4002030004120040000326595205100f8114800d03405000c0d589184c40c4c00c0c900d0040c0c4071400d501141c528501c1c021041080540f101958503841140040f00d80700c0700c0c0c101e50030342014414002c0c40340e031614060b0108035003820078107801041c407014007002034103458091003240035150f81d5050200c143ca0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 166972724 1250 166971474 166971499
    0xd090f18060b040306050601181202010f022406090f09070e06010e1e0910060c0f02040e0a0807050607020102030f0a09060609060f031a01050f0909010e06010e15030d120f020702 78
    0x991b400c043e1040009903a0040101144450100358008034018242243c002d00100030055010709940c10a14440c0c0c01181d020b122900f00c0c20541100741c40440d1180c031500b00902120f03040001c0d0450f04040149003100c0c0a203080e11549035502010320451840107001c5002c100c280c0d0158003802c500b10805800c201032202c195102c0d0800b40006160076014030242c50004410034220388120b8161103e655650800c0802900c40c811401610749050341d00a680e40514068004108500080c0620902640d6165005402d08904210006082c9010759004000300003050076050800f0358012001040026800e510f810280c005111a4001a4405191685c00b04580321660591000c40b4417501000101000e10035072100314070310030b00c80d117a000743ca1600000b40300d01d0200a865803081400c0c00005202040c5180039184c0384083e806101e001c40c3c4882440500c104948005440d23404c00c2d0010400498140401410360140072018103140d9524442c040e5501417a80441c0d15441d00203088809040c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 166973974 1250 166972724 166972733
    0x1101060306060e0601030b1003020d0b040501030c0509090f150703090c0e100515030408031801062312060f10120503041d010e0604050415020711030d090f18060b0403 73
    0x1280d80240541404100f000644542c424001d00d01483c0002d015204110b10f9207005801070741200070809102605c030b02c2e15030b25a448034420a40214042e92126165514220910420160141186266401618104000c2d00c000201c50040120812010a281d03072000e5046008211144c0c0080070510380440c0002e540808101c454024000003080c6246aa030f00c80402803140020351a80480040600003d00801c1c0300c1009954001c040c501c01d010399941b5000c10b107084072680c0d00440c422040b5051140300112805200c1410603200fa00c90451200c010000941d40303100003008d80c1030401c21900010094940c0b040c0d52401000c0020314094002d00321b03c5e021784c4079002030052a1400d240c100d00c1c0701001100b20380041c12a02c0c1c85d000c46406803a00003d00c405404000c00a4803288040042a8014410352005000203801510a0301c3c1007600358080500b4500700c9000c40040040c3d0010601400b554028640111040403403500c10140d01c076601c6101501e000d038403404603040701140020521 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 166975224 1250 166973974 166973981
    0x6040b0402010f0302040e1503070b0f04060e0909030712050904060803040312030b060703030f021608120603060915060d0210021e2409070f090b04140403050a0f1101060306 76
    0x298400d03283d0702c40c001e050300f208900301c2c0600d124a0200d00309a00114100d0003240c10905020349019050b601c41e552502c070150300e19400000002000d6070f000504010040d80014032000b14041258580224200840102c1d583c0c00f800e04040c11f815068000c032007185000301d049a12608002d4814401c0c0360352450116280d030024841510303d25005618001098441d00c506252860010040742c1080d6003920114001c00c202185502205e5082100452461103038603006c944c103104a4240381c0c3d0310300300c00d60b00c0c00306100506841e002c2d0b800102445400c00011542c51130032441c40b400900c081d0740d6440014407624070305074083e400050080e40b2022055010407101d02c2d01043c03460460b003940000c030401c0da07103012103075401001400e0309003e024042d942e40901500081e40314100e41d451fa4803140544100f13025035200000d01582e800e0780864a00303050140703912401a5641b442403a1030f068070040c2c0380e0320440c42010704201854907014403045c000c54140015400340002003040c04e171a0b16020008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 166976474 1250 166975224 166975231
    0xb04050a0905010e011803050a091805040212070303020601050121020a170717040227161107030c03020f130f090c05060c070e062704120903080a0f05070506040b 71
    0xa501301040304004140501a01c2c0100f00d80c8200781030202c40584048400c0e070804601c980402172441c4c0f00040d205030f01d010201c0c40f030700e10305000212414507104010200c1c0c100b4800101d9504245c60401c04203802284071070442e04282011001018011043c1e4003010700907210f16000c5101162a61507035900c03000740159107100718904641d03038030346100a6902018000d00001c6001c80040064018106080200c1d9558251040001c20a50510b01500e07500c2e42202c01406030b07251429008405644050010280300a20b4007901d500c606640354022003130a1404080c4c012081d0300c2c0c0520654841600701007001d54034100c20415403418681c0d0101170000440141e030845907810001c0b800307280020032114038400410007400940e00c0c11700d03500b00e0001c1c010001948200320022429000850202d002503000000d240444c0f03c1c9402d103098541c5806c091010320800c81c002e1401d2000590341c3e002c4035201c040501304044080d203150b5040b9142c0c404d2102c000c24070b005440c184420880c540700780a02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 166977724 1250 166976474 166976483
    0x90d06050406141506090a0801050f070906050405060d0c11060709051516120e0d060f0f06030c060e04150e061305070c1707060608030a0f02030a140d0b04050a09 71
    0x11000f001100910940410b45020b070000e04110140c800c14a020300081003500000b51002c0b0b4003654840d03807503003116001ca03a14844440e8078400c00c40d80c15441600e1202400f15070138600d061504000125290713010b6440c440c0d11460769800c2100e4218000c0b030041d1442005081150501c0c508210b000741030741614840c0600600140c0988107220320300da03040e120010360200303581501c5040c41e242e04940349080007008090200503c4416810707110003c5406940b8010359020400100a0050f817003100e0103001e8918010f464040180b0015030701040000071503410f460464020107007040003a00900781245a00c82c4000241d9002450320a1301034403d214802c11110350391480031001040050700c40484118001038260b4032044002450610031032880c803038130071200d41821041d644542c222051a00060100d510214181e03004c3c40c0e00c40c498604ca10341610241d402c2c00c81c0400040c224240000c0841303200100410428a84607803070303224000c1890000c00038030140c200030500720b00410b5444410f86 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 166978974 1250 166977724 166977731
    0x3030e040902100c0f062c07060f08090312130b09010902090112140d03020301171507080903090409120207050a1a0306031504231c030b06090d06050406 67
    0x65900d42403180e5541e541d0090703e0310301468a00700085480d001c10a50454100c03500c00c0310396001c14281d104541d900c0d8400c006180740359030402d4844400ca80c3c41c02000038142d0040c5000d0000d0b41c2e1018400c14000c1d081d0804451548960419600790701610a80c0300300601380c40d04000703d241c11a0107620a40780560552186600c5807021582a10001309010790044070180c01001000302c20445212342c64069104504131003401704c0709505107215444183c0019030080010b10903421800c046200c000d100364003d107401407107141e80702840e0b00000c1c01c0c0401d12001d00006548800180225246074200400c1045400d0142c6805079041621900e0400141300d0107402080c1e0341001e950f0b800913102c0c101000305100c004000c405200c1e500081500340c26000c1c0c20600c14824144604090280d07100b01400c0c024031840d0309582503040c0c4507151483d559071001c10300b6042e4890000c00040004170a05d4081012043c4a0200c0c182e4864802400c1d0465180e018042c00c2c40144d41c06075028911485003803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 166980224 1250 166978974 166978997
    0x3030706090b01050438040f0906050a06061b060b0a030f05070807060201090c09020304020415030507080d051206010c050c0d0503031f0e2a12150102030a0c08070c030503130303 78
    0x148420028100044100184881c51b4039070003281c030f07003440d000c404010008101085031142c210180c0c1c508900841e0000c2e1510203012010320305018100240034185400c4d0034003c0080f204228030380500201908495a8011003995174492040c1d0b40082c5401c84a0340300f40f984145020b80e9143e005101c0c003411409074070400b0a0f4240306009000c1503d4001000050490404c04680c000b580b002e00201d92050781d0740e07210307d50120003110a200640c090801341954524009400d400c1c0a005410081040400c100340c201c03000c800d1a0310307a04420700b8a0400300c81d1610b842c0144c900802142c0080c0c3c4030529079014020080000700841c400c020508503002146d465620703085002c1c2d228020f40e01d203143e40d800019401050515900b400c50b40c43d422202c842c0403840c2c1c0700e4a80f64000119003a80c4a9030104000869200000c0181c02d03800c00e20066207030680c114402031540c1d1160b0030041c00071100091001c148410000d143e0060364015007900c4d6264413691603903402c01c045100860101d00310f105030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 166981474 1250 166980224 166980251
    0x913020f0d05090f15181e011103060d0602030901090516030c0b09180a02040b040303050a0305062d030102130806010806100f210c0303030b0a09051003030e03030706090b010504 78
    0x4013102c82c0b00041c020109013500003900030100318004d100c0791428102c040c108658020412034a003400140c160b8080003403003803a5080b0300303440c04812003000ca60410000d010f8a034032034080685807150050360050702c0392159a1082d014003245640030700980703e0341c0e01c403891004281190408a0b44954000e40e5804c1c2e94041e103650341d02134660b8079644452125800d0210b6550050b9007580710480f00401440c00b500d490004407075402070323002a03001a402040707500c0415018859150092800c540c820b02e981380f2040c4407220740d021031030328182d817171201010368070241c0b800d40591304101c54100701e003240283c07900c8102d95220002d04c24040c0074418140422101920175400300b00b500e070320462802a15040070507540b1412503408612801c0403203107000c0b10119401110040155210342d60104a1034400c3e41001030783d140580006c00f100d8a0001403000c9840800451003c60f541428040020031000c00024114002c01c0405401607061440b407200b00449402103606035a4200c5007045440b20300d991 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 166982724 1250 166981474 166981483
    0x5010b1308060603030f070f08120411121c1202030f0601030b0108040b060d0314070507090e01060b250b01060201020d110a1706040e0d2111040603020913020f0d0509 73
    0x80642c0c0542040006c034184016040c014080c1c90700441a11a004000340d40c1c0f898a82d1000e0300030403035009000284410498800c0c80558070003021110300d885a0440984030b82c03160950b0300f0743d0394060311915508072031600421100f81d004010b02c104544030b183c000380d426840b5400312102c0d400a07191484811096005032202c601440c1c1207640b40e5299a0740304140582e81c221071000364140300307034a120b0b1004081124010f00c0503d110f02c0203041e0003854164014192031130032907048542d0341040024446c1c0c12504040d61013010b1030400c0958000b44010301149552030241019000c1070300d01002050513601500104201000c0325000c0019008007140c02c1041d00501c1040000600b0209001c3ea00300d144100b65031301f01c6401000091000149034003140351150b030468900119403114941d4410445000c44020703070400c00070090008121104001202c3c2c03041d4054181072541c08a480c0415485000e910844001c904a0465a591101d00500100d4110312030084040d41000005000c0c0e01c00801e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 166983974 1250 166982724 166982731
    0x70212061306020f091c060c08070507030503060a0504020415021b0618131d0705032806020c010c09030b1605030c0d020d1a011101020301060801031e0605010b130806 73
    0x103016020081c4030368032100030b50700003811410921001d0000001c02e82d941110351840d000b1540b038040d0049600e01d080c1003511103880c0d00c00103020009040000150f0454121041035030305140c100c0d626900c1e03200269100f04160440ea03000352002c100840d100d04160a011070b059080d03002c8440302038a03a040d020002c80c0b1041440d42003103051014021102480c080000300f000010030440c88040e4010240080391000b854482c0c04c00c04102c0100381050b001d10120b03010341070980150080502168507000c4444592480050440c1c40034150703402c0c0035459068981d0340c1160340081c40824240d0384000c01d81c03205800140c0e524075044012a000441061982800c058141c490754219a05c0d20800e80140c2c00c580c0c60035521036000c116480c8170b088280724101d0405650181710b01202100000148074105864126020340c2c4100010b000d0355411040c528116a803101003411010b58a201c0040e1441412070300504040c1444c0004c6046005080504401d080c0e14090b2000070b03544441c0e01c0c0d82d070501034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 166985224 1250 166983974 166983991
    0x203041403040b0a0305040f0609060b04060b0309150601050c0f0601140117040206031b1306031506020c130219030507030b03030405150c0307020307060e01090e0103020f010f0207180207021206 85
    0x100008100e045c06900503960090140030f00100c2454103488100949130032801c200c1d01103658102040c1700c0d14043c800d00c00079004101d030710790461521010700747d961040030b424400c01d5108140060340682c450710840f05d4400b17070344041e01d0841c95000b10745a60f441c0c1c20b01845042c00c52503103a0030800d5100700040408134141c00944002600e542d020b104590740045d00300902d10303041e1504506404030003c02000407003400d51203540402c1c40c0c82c1c0014119504036550b00d400e2880c09001700074480e4000fa90707a00c5a0000c540410b500b41c42d000c0703002c00902c207107045908002862104409001c1d05070b407242c0c0c0b00e0f40c510f0300c0a0203101e09c0b41081680728842c80c003c99501525403854116800c3c1840b025200d0303120060300300c0c2d20b0a40396800007445d0071520741c00040002c1030303210740c0c1c0429640514041d0080c200500308040950540e0b000641d0307502c100c040507040140842d002e19040d231080200500030710900340d002245400e8901e450000c1e5104040503409011100d880c0600307090000348072403003503284 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 166986474 1250 166985224 166985227
    0x10906080405151f12020f090405030d020a03180b091509031606060306090506180304060f11072c150f060708191d03060403020d0f0c050f010203041403040b 69
    0x104988044445005440000c0404501003a10608007130050250050446004640c0000180b44101701a0784990401e140c021081c24081c400016400001d13602d08404900d409070f210340c0752000072401003284644021082000d03034828814004c285541c0c500544524003601d6100880c400c00002e45241514030b88004d034010002507107010080c00d00008132520806001c01c100e5620303210a8207440022006603002e030084020720000076000c13544907030301d9410280034600f0700340703070080145c1810ba80355100b4060002c4d51450030048002445164003030300520180d1002d20324030380070164108444000c070b125000280070204d100065840c1464a15803001454400030146820502c082a0040e100c21600e0f0441070181605000701c42c0480302416080b43c0d40c0060150001c4000360340c221611581034001d821580c248404031f50b000c18104000201410544d5103c00350700000c071031039050058041e2050194040700768140c1c1040d0000c40c02035000700400c041714500d0121140d1030344603030b21403182c10810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 166987724 1250 166986474 166986493
    0xa1401120c0902040801050f010f0e0f0c07020d080a02010c02030405091518330102070e0c07051209100f020a0201300b0901061701050607060b0d0c05010906080405 72
    0x890060450303526100d25008039500b60340310504816138109821982d81c0340d441350104103844d15003007070795030060000c81d0b1182889840d181c61807030350703c402414802d8076400c01c40000340d030341301d00e00d00f02d03a40c4c40c2e03002e05000940009801c0c0540306410014990005508040581b203c0602c00415103054420003408414652600480c404a86440341a02038019500f104070b8139500ca1068007640c403e2401c03080c620700f240c58880b502068400c040d10158418180440c98150b9079a00045090503540300700304408280c0ca032080c1c281400d004807400103090b80301710242c0782d40707041d60032001c0c041c41102560420342141c01c0c02c0064944250750100d201c01644020f03141c0c4007542c070401840c0c6081d0503507107442c1829807a00700c2d2070602d0700245c4a02411252510f0001c0c03501d0905070012401403000d86440e1000006218082c545890184070711442100041114014405c05030702140c00840c0040c141580041c20f032030041300110382489030502003000f05100040c114000c1010038455035108018040204c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 166988974 1250 166987724 166987739
    0x60b040b090112020301110307020c030606060705030d0b012001060f0510080a0b19030b04120305060604061d04020403030c0507050f220e070603091e020f100c020402180102060a1401 80
    0x41e40843c143d0b070642d210000a20004082001140a0703003096010785203500c010401d03d807418a0181905000703640400001c2c02144000c81a0350365418000008142411300d2801200c0f00c5e039980c41c0328940c0303018500c41d034075540805601010460b80d008181032040d5584c1c50411a01c030f50b003070030280c0c041000000064214413982e8004628400000c04421050701000d10510a004007504216180b80d880f00a020510404c0b140c84905104146414441440c0c450042035650003980b0a0400340710700c0320381c014403860646166585c4050701401c11521aa07072828018044c41e02d480040d10b20303015400c4045424100078203c0b209054026200210742001c1020708042b1042d041407040c00903944850702d9040940c24401c05008280a650115200f9503038108181220035604410641c000303031400640040e200c10b1480c0742c0408007100c3e03a820031a031401040e14600340c0c41c10002d501c107100281140c0d018842c1c00b400c3c0d546103401e0303088882d1039845a640720219451015044000320030034004001e043c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 166990224 1250 166988974 166988999
    0x304050a12030503070c031803110118031211070801051315020708070b0c070c140102010e070509010506030403110a0507090e210a030204030213020405010f1b06181e060b040b0901 79
    0x3442131410b00e10b40c0d83c407100d419510306110b800450700010030490203180bd41e03006180f422070310f10b01c0c4200300c0401d10b9030f41c81c10b0768944000196014000c4220301c10120b600d09102c5074008011010007030249180c00d2503180510700c01c102d0110380d40390009821030b150350050300c01ea81e072140d8400d441c145026180e45a0442030603005010703010036a810041400020f8207100d040c0010b01180007c82c042414050000e400e46003d50701d200007035480024108100c0d40c1d12440c542c1103078420b55000d0358a0300d65040880310749012800c2105241304c0c04140b4400c01c600000c413181240c0710301204100c1c01010181c1c0b00d8880d2a4855001810501c42240a100200001c003c103c040c1c400d0030014071b015940e0f400305140c0e48c108400402c410350b001c2010069543c000d42d160b2045039481c40e04e1205100402a08048085001800360007940e45091307000e50b803030003c010540c4058000e101101a240c01c0300c91295000d44c0c00341c04807882c41c14a41c000c56241440d004500319807070000e0110b0010b1b070902407107031240f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 166991474 1250 166990224 166990247
    0x6020708210702031c080a140a0507020a050d09030c0f06020309190801090c0e0c030115030504050109020a08031b0309010504050112060b040e0f1b0409050601020f010204080304050a1203050307 85
    0x41c1e94104500360050758108480c0d0a4040f0402d400c032504500440060b0250b00c0042600c1906410000c2c80d0100d60000840541c0c00041940c0c005466128524101d103440140c0c3e100610503ca02c0c40401c60681e04042d01703e0440340700b070019101590b141d12041c0c25585280c030680004d6071082c03200c43e9603440c0150600c04100450f500341005a41e07140010b50a40351600070640d1141400d0b44103100f80c403202301c00340d50f002d5103c541c03052440d490840061150080707091440704140da00d1010900f0001c0a40003810b00d03c1e0001d1030400d0060b141c100180d201e0380103001004000d0004404009007400c00f00030388554440c144c5a003801d2500d8007005445100f42030814018903952414003143d41e81180e0042c1c005060f46000420703842c90181503407008050040c11201c5140c45880050101c0d244510498055915295000c5001e0b1140340040c0e1802070b504041c1c2d8440d500105e40810300340400009001210b10031199007580c650b4a1201050341c00c1403440140000740204005212540156142c803034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 166992724 1250 166991474 166991533
    0xe06390c0f0313060e0301050402030d1103121611010605150a0203040e0c0a090b0306130b01021903030b150316051308070311040c0e030a110609040501120c06020708 73
    0x8041200030a541198018080c980c01090001018413a03107510009400203014160020029410581c002030b584072100c540300400c1001c3e88000440d82c000030b001303490741c0c8180f2422006803800c00300c2c902000313800310616202c002403810005600b2400305000707060842d40050154000008150009980b0713a000b680a2415407000304030003d4491151a012441b0b82d010041c1e40d81c0340c4601c010000d10442159124015a18081c000d100560765580b052a45141d428440042c1c4142c281d4010307420700802400015011642601c500c050503090b8109078006070b0120b640c00d44d1420308018100d41404103541c24154511603c10524030307a40114014000013544441000b545a96414501d15129050300f085402d01d21042501d889418140140b00c01d24035a8104205412100d0010070390303c03501c041001d8442c408032207104110380c480000b12002510040e0040c03040f0740c1c4490303200c052580e1502c01221a802400e4000459510204000e010f44603984054900300940a459014180c0d16004070003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 166993974 1250 166992724 166992733
    0x90a0605031209040606090605090f01030e010c08160525030e06030109090512071110030f09082a070e34140901020d050d020d0e06390c 60
    0x61155002c10001030400349031021a030340c070515403060105840320355000006001242e00c0c14071103682c0240c00e80d0003121068880900c104400d0004802034004e101c04017043d035203040c1140e03100580c41900c651059902c2289a64010100d0f17108031580d00c20001070303982d441410114800d50000c0c0c071458107000c50207890a00d20021222000503625070080c1d11507111180e1700c030005810803905110b03030070b05010317036070280f5050104684a460014030140c0c00c040c80307401c4040e4008140c40c000c0d0301c011000d64840b074040007416518517229a540d8000080548916419604a41940300300003182900154010183c40014074110001812000161450880d18041080030308030b90404103880c8119803103051000a103040c50700c00500b80c008241c08459900b5001c11400545907000110230101c0300b00c80c0703400d40e500c45035010084000d01070800c100794401e0802407890340301d000000d10240596000b030801da5030904c60002c440c81039110038940c03550341d00b074806000d0500c0712200b0240c80c07124958001c0d80d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 166995224 1250 166993974 166993979
    0x901180b0a1211030f070206010e0115030f0e0106080106050915010e12010b030a060203060f09010303090611031b070303021207020f01050f09040524010207030b0610170406320402090a06 82
    0x380c008031748014840421104100940c0d50400900b801800d5425100504e0f5040c44007030220070105407024000d06458126681e181c4070150301401440d510300000b08409034440762094041c02c140d11641d0300c940707402400b140c0724010640203641001016100c000305141850107201000140c0303020400b10b03541e22402d2001c01d4a050102c1e001c0f0600c41c076801a41e91a0003800c020640c40c83d0b00415000718049001840000d401012507401e66589080c0701c3c1e40703002c403026402d1451140010743c980104400300a103000030f000040c0042920b1003038090310810740f081c500c810b54501800134081d6215020030780403400340d40514003c000889116641e0ba203448405004541076a0003034588076540302d580e00002007110091b4000c2030194a091028101540c6103444415250381c010704014403c400b04104000d00c58000c2d08921039980e0030800d40e61031850a810507400030036900900f8524240c40d03200f1814078500c10041c421a0a4941100280a40b00da070240040f0400050580072082d9460101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 166996474 1250 166995224 166995251
    0x15060f0f0102033c0a02060403110c030f010e07080303090316020609090f0604050a0e07030210200c0102070603020a050304030c1b090603021c020901120606090f020901180b0a12 78
    0x84205900480c40264403980c6082404903003408458130110000080c88520700b02c541c04200650459010324100c0000040c54001604000012100e03ea05200d000140c044059040d000004c1d42d010041c191035584d0342d1200426203c0c40104c034000003641041000c05100b180602034069054005030109040c01c1d00a40420621101500c02040164103502046007503e86802034641c0640811800d000380c1c203124034200d40e104443d02000348241e96100400704100d106002120401c411000020004103c40744455110b252110203580180501d40000c04d0f22070107402100c00c0e00a86030740f62441c543c0c0d0345c1c0301140c2070f8411a004a51b0700d500012022403000c9218101005000c41c1c9500180180c03940c410003640359030460714910340c42e00300d56006016030340300700c002811100c07091030152600d480c0389030020050015800041d441c80c0b030105074595180d001d6004d0106244281c84500c068030b8082552514441541310794804400b0410044181d1442a8410088031565010200308180305124 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 166997724 1250 166996474 166996507
    0x70b070207090204061116050f0f0607061104090b0a1802030702011d01020d24060c11100f0f09180f0e060103081c0c09050909030904090809010215060f0f010203 71
    0xd000150841c1060840e0700c811f110800340200414800608185804003007190525106c1d0354a00c03880350070b81d005900781c40e6001103a440603400041005401140081516a40c0160241c80c05117403800071074404900300814400155061801071040da000c46014100c042d40c0020548001c5540b500788558808080c402c489070b001c4015000580c0710000d90100008881303605080c81c07106281c0d2901102503449411640e801d803451032805103140780a5003018035070349041074061034128068003040c20045034040c1011040c0200f030f56a440c01268020300440380240d41d07001c1c0d600b000200080f04044504194032600304d140800101203118a50b1039191030600300d00760300a03180c403d0005081d06081c2080c5d6039080c01c1d402d43c41c008000c1031989075002003108844d405014003403c2c0700000b00c0c006075000c0060302c5403050010030511a40d0081d14240d4866005405614054483e02080714580010700503030500c690405801d00020000e03100400481c11445440c1074190b0000f0042045882601d48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 166998974 1250 166997724 166997729
    0x50a050601180c020105010506040e0903130b030403080112030f030e0c060304080a08010518060d080c1c08130519020d0c0803030103030f080717060609040207030c060507030b06070b070207090204 86
    0x2c1c502d446100d10034070040d06076506916144216454040180000e07a075080a40e01507070041c40c842141541c504007134510390322600324104440101c003c400103410742071400452044d0300c41c2d07545080903680d500c1c0000c100500c07200c0c0140482c121310745130f1400c00d120341d008084021f503020072242c1010403440460301d036600030b40302650300c040d00240c4070b80c103035800100441c010181a0360090a40d509005a07801d039120140c2028883c00c04c90240d8414400420191007205860200707503002030b0703d60140480604103041c0ca02e4081179003a40000d594051224000101e1a041005000d0f0f03130b0a50380004044020349101242d10052280f44c820100d031030310b00110045c0c0405401165654150f06000e0121940084400100500101040070481d0301581031f1001d100b44100251054641000051031030141841c4290858404204d041c0ad040e1b2141e0514503050140e0f008010340c1c0c6075500d00b1000d594030a81e2640d0404000c00101d80090600107107694460007500c141c030740c003a4442a07038a00741d0340a42e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 167000224 1250 166998974 166998989
    0x251509080405190302040e070b0a050a02010f06180b010302090618040e0d020d02071509120f05010203151207031109070302070c060c02090f0709060509010c0213060314010207110409050a050601 85
    0x3c80051085052074410400c00c0c000c4079008011076441c20324040d100b8440c04000c00d04011380030036060030080c001d4200c84031681818205011180d02d0f0b41c03180e41030308030014000301c0440c1003d12903407480d4002d00c02c6804022014064904c1d14900c4c47d1030344624443d40b01a9900995200e414a203180f40a0107202500509a8050311500d540620b00074a400080c0e00315950803210802408071041e00300c07034080c040781c0c0d80101c0c1d22803020250500908010350402c016042d54000401c1111120412450200355002116210300d10010108810755402240c0001040c40444940c119014070709201d040358025103038600981b401c0c9640d41d07441428034042d4403605c00300e0741d480d04a00441c0b40084200f60320000800f00009945080000101482801c0c4501410700c080003801034800d91080c0844d401c2d480d0080c4c1201c4000205a102c00c00504441c403090f25034103c0d0a498030304425041c002c40d18119002520b441c0f07080200010000180600c1c501201e00344103142010700013400a20410340248001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 167001474 1250 167000224 167000269
    0xd050a090309140d1106130603020301050118120f15020c010204051c0c0303050904230912030f15040f0c110d02190f170f251509080405 60
    0x910300075007501c2c15030b00034001e15003466110341940d840f4203042c403135010340081d8032141303585160010035042d124044c0c44600001240c0d102180c2140c040e0021412070740c0a907100a0307868003207901d450303203820350b409008281c481c1c60036075601090006030840301d500d01404010b506005403456420490740550703060000c0b40d4021604001c10f1405030580e0036003080301c6005107a45801170741e540707000f030815000c02001d01c10007003070140c0c03580c03100e070300807207483e003032042d05644104101c1990766080f08215031004443c0f00c2d001c5842c2407010000306407405a541da5462606507110680010740101e07081121580040e503a100480c11518540070343c091503c03143e00c0d00c40c0d0803100c0801d418140184e901084046d54042801400380008803040f0128660700503084042404003071402c0c20ba40180c1081d0000130980100700c05008441d080000c05515180d03204050301e96645140c1c0b04031a80b8103003805864031003912580806017110f6003201310400d04c100441483c0603140d20010740290b0000072410b115192 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 167002724 1250 167001474 167001491
    0x4030501050114010302030c030604051f14030f0102190c0201020c091e101203050c0a02042309070e0105010c030e061b150103050d1d10030f0506090106051602060d050a 74
    0x840e03000c8401d03c0000e280a500d103180103002c1001c0e522010f040c040c056603403400081c4005604082c041100f001d855298462199584080300101030980c0070130f8800e029030084500441414401c951000c2e111544c443d0030314407101c0058030180c04800c401c5c1c0c10742c010f2a00b0a959541c41411052240c03280400c3e0720101d503081c03980442d459900600c000100040c856007480050124900c5040c155807622b00180c1d218601d43c01681009001c0100940190800d281070081418106444402441103440a40195103440c0b0b02959416548140c02c8400120380042c45079511549202035603500038201542900380e10400705065030700611403d20120841d5440550402051100000169510301038a103654119121071303480e1418400d1300414856001c201e080142c10306040034220000041c05407849400c40e01000d0b0181c03502880a40416140200240b81c07850a4124103060b260a56116400d094002580c403451000c1c41109036400752090228500030749050040510840300410042070038107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 167003974 1250 167002724 167002739
    0x304112e0807030f090302060c0d060302090c0c0f0106030f0b07110f01050a0f020903030d1503051207120f090512030c0604060207020a082107060605042a050c1b0105090303040305010501 82
    0x1a140d0344ca580400342884500030110746d00041c1b00e074008180d44285940c4480c0d15464400505d603aa08c000d4203c0d00140822840480010180c00c3d1072410805564600780c81e03540345400c0326100d00000b800e024038080710501040000d0f410326801b56845c203000385008020003c0c0c51400101c0841c04c140c681d10b9004100360740000f402000e5000c01000b10540c2482d07101000203841b4020721840360f1030140d4038420030300e52200c60000600159000003c8c3e40b00440c80d10040191070748a80d40a40d00d030341c201501010b1940c402c01000e40c003411280c1e01c004030b090a140411074006051241490b85100074480210340c03100500c4102c2c0541e129920040c0e40b200503106102010a2039032001c0c4880e00b00212161a0501003900448010404a0400c0e621200d9140c0f002c000c10481e089590060319100e42140c01e1481c1180490800710a855564161068844226124800c12079420016001000005242584240d00c20314180d0141441030070005204042499504a980280d40e03030303915000100000c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 167005224 1250 167003974 167003981
    0x50a150c020705090406140907030308060d0f02040b0301021908010302100e0d080d0204030602040e0912030601020c120f03070309060f020105060a0308070c0f1d0c0304112e080703 79
    0x1059a09092104001240000e03403922101d120b0385000d2500700c000503003048a5035010308407003080110340c000c0074140f074003006544151038001140030a400750301265207458071007034007841ca070b51014041d9802020341d4244030141008080454156400f40320380a0036000c00416020310841a235034121080d89940100aa92440050a1814030649241c09913050316040c207000105030f00071071030507510301ca1b294503031000744541e5001405032032001c100800c8a41c07840c14540e0103801c00391b00302c410840d50703c078486010348002d542c828096884044000000d0038401901c3e50440080c0003a11038040003420618110f500c0341a0890000300c11010910116070405440f040c1c0b02034610080099160260120b00001c046020113401d004000c03a5007010003202d00e1001d0301401079110520460380d623a0780401ea1040000000e44603210b480e01c0003070640855401643e10494001d031030a040c1e80e000f00e040c40800b42110071310780340c10104803400e00c84503400810314000081c921b039603d00c090300d07040500804a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 167006474 1250 167005224 167005253
    0xc140c03060c03010806180f0d200c090a0f0b04050703020306092d0405010b0d03020c030f031c02092e0305060303120109020d0e120301091119030504031209050a 71
    0x2c0320400c2c001400501c038001501c41e0f00c100200354800c03003041c01e0101d080ca00f10802c8140e01035446038203007240440750b005141e540d08000401c02c2c0c90004200348200f40e1142070f50140c1e03035000420400040e0303c2c4040303a005060f100030440000500c14400c1030105041d40d808031600c4010a80010500440342810310f5500c2c0d1225142244512100070001d034464401d4910300401102e0f5015400b19060180a500c50084050010060070180728240781c00b079119252150400d12078002c80b00c1c802401c5a001c801c4034203041221007600007219030f030302d4031400a4004c80781050300f1a1250104140e80f010700c122282c101040300c29904c81440c142c101c003c0940780c0c001d00d00c500130f400234040782210040340c41295055826035600541c640320304500780c40c01403252420608181c81544010394154a0400095058031049a0244001591902c13580c03403d200301c1e12000180110442c0c2401024480e502450b046482850112010f1030790121680560f680018142c1d0540c2141d01c20204118540181041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 167007724 1250 167006474 167006491
    0x1512020a0b0f04050409020a081c020708160909060b0d032706120e01180602040f080105010308040605181f02010f18140c1f080a0b0d03050a0c140c0306 67
    0x3030079850501010b0640540c1c45801d0141d501e80384000215598041070801400b80c04040700c80008540c084c3c001c1055048a004026004595007c98899000701e25800060030014000500da441d01308000024404117100750707556a5034103008451a5180c00300e1001941c000d64034180d0803c01c00d03581101c8400000306007884140110310802c0542d8102060080c581c900800000d8102c4000c103506000d888a030b110100308900c14402e02d0100402e542c0580140c60310f4000c181191500c9400280c200c980030b0001801c528411f00081020b18401c0000380a035000b0307185038481500c0c0e034a01080e145070178102e0300400b10b0342042c940300c04194244210791541003850007d002c1d11511200da080d5004030048041c110f4130340e1403246e03495000c04004040088401904094800c008102211406031103031002c840012007680c0880d102c00d900340201c045041009000340b901a800743d40665035540700c1300300f40c3c3c20b2010400e1890040781001a004948100c69000703402d501205400300360900f0f80c020304049 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 167008974 1250 167007724 167007727
    0x30406180315020919060f11010b01090b03150607031e020106050a0b0a090b030403260601050316020f010908040513020c0a02041e020c070e0a0905060601080601031512020a0b 77
    0x1080e40c04224021403841d00b4401a80d85030800301081c145990121030b140b0080d09000001b400303550040c81c1a5072076510341c0d204030082441d007000d58281d5241e021400d00054004c03400340310002400340116040555000040310035030f10080419500e4005000582c00300b16416411121000c8000c6100e0314240107200800c0b4007070502c070000300b410203540141c661184001c07600b4105140503001e0360015104805e40b650716850503181c001c0800034560400000c444182c88111901c50400d210640580030507110b0034115914001040401c919411800d421031040030540c01e2018428824040741c1c80c0211091503580b4202400e000391100c02211040711203204021140390040c1c0407816101c0c999040714042622002402682c201e0f2402c2c5000030351080c40040c414000c1d41c0f00140000031607411a0f40f0800c16a01c0030800021548003c1001d04186c004400003030180d0700c980100e950121050500240b2580d103030507050f2008031076030131041c1640000c20300782c4203500c0c010f0301d0300c0c00038103000513103d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 167010224 1250 167008974 167008979
    0x112b03060914160507021c05120a050708090103230121020d060c020705090a06030b0f0606070204050402030f01060605030907140112050c09060d0c110c0a061803080c03040618 77
    0x100b2242c014500d024440c444092407640c24452821200040d030000c0200c440e01900c1207032504121000d50040701d41c0d05c03400445013400200e06040d07804164143c0c88160400c251900c030b4110315031140d9422410143e48660040e2540c100144603c0300004529952505605000c9078042020200200b5400e0b00c00d00c0c0303032041c01039641075074a1250550041c1d02003803491140c042a0314041302074001c540c1c424200390400200d1760b029803114003101d02454503840c1b0fa850f00350a0010152081d0b0358190019000c000c000d006d41401d8220366041480a82141d451442d801c01031800c50300036070807031000504d0010500914a80400201c401b0704640003010f0002040c1e007001030103001022111086807500ca01c0043c204800740000e5903400070000c1c0c4255954525022105e00400a000012000c41c40a0034440711b00c4c400000c0c041c40c0c410380602000c82031400c0000a41d1541540f016201201818103c0400040e0419016041c000c020f00300454449091240140400b101c4441242c1c0c20070300ea5004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 167011474 1250 167010224 167010251
    0xb060102060a0b03330103030f0e0409021819020c07171507080c04050a0303090306050f0c03070309050a1506031e03020d0507050c0a0b03100b0304050a03112b030609 73
    0x108105021141005c030808280d450f9146800d84400070440c91101c0c81c50001061681082c0140110300465507071124880240382000300302e40700c0c11800780d000001d100706491314106140c410b54009110103055440301d910307035500c0d40503640300f44103061041e04084820070a505e5450b16014103108040302622218046001b80761500c6c070020825000c00441c074012030502e000f0041250003820001e800c40000c662030b810003178a40d4985100884003149404001529001301c1000c25009454aa4299186480d6020120040e00a150050b0b542e40284001a030008208414002d44204103000114850303265092a4800506e601e2915074040040c082150000c2c0c1d01161003604203006080164468441c2d081040c40c1070940c82401d5006414414003007001c94810f80650301c25105d045100718066240e4080d454103000a4070f004004c1d500c060b031403400003402414a025528000b02c222180c00403081040349015100c54042e098421004118440d03131949800f508020300307403e060601c2003003841c901 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 167012724 1250 167011474 167011483
    0x1807120f1112100b0705030301060905011b0314040e04200d0503041a07080a02010f0513080d1d060c04060f0305070e0108070908011d0106090501182004030b060102060a0b03 76
    0x1841d20b510b0030001c00103e400d40c0c40000031001d441c0041001d5281d405a1402070366a510a020301000f084161100245c950700c200242080c081440302c62040b4008199015524254011040101140140070100303184516106040c49a4084c19080303083c00c06181035a5103101201c00000e00031040808007101082000081300c1c1140d191a0704580410300c1090f0301c610718010210020103019001541c2d15806905410045102d0b2181900700f00030f440b18886c0b1400301e01c202c1030040c010801441000d60702d016640c030000000d03041c901c851503100ca0040e9680e003480c4080707074960407401c0e01040074482654440c80e0504090214141000ba0f030509c1000500122040540a4100115280041c0d41103224211980003041c00d04d002740600000005507405048a00c251030002d50f00e00000040c0c042110b02400e8100c2e445541d071451410242d24035140a003640b4800415100c2c0e0b030b00c00d0703140002020780c0204010341c0188440ea0849c180031000a08008001d0207032070115003402448141da40c0c3c041b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 167013974 1250 167012724 167012737
    0x1504090c0f1704030201020d020d02120606030610050d0924050a110304260301060c031b1a090a05030304031d0f030304050f03010e06040305070203070f06020a02040b1807120f11 78
    0x4068588660f10303450b040340a4450140000103140c0089110020406160003811a01c4c1c082103802c0f1250751500184100340c00202c5019034482c01000c0c04d285041d008000920302d000c0b1110012603c90b40b41d440c0e80070b00c68840208181e0144988950407601c0c3c01522030650481d001e01b0080c0035500c050410311109000152010303090080b4400120061880305100b03c1450460140c1c0c50744a6a50b01009010482c440c4026004110304025004041007083c5964211a503c070b6404e110036010314800450b180300003050354066115030115100428010009144510302ca0355691414544545607200340c0051090340e45d01500080c124902c4d00e41c1c01200b03032400d41d10103444000c0105400d8000901500f141402c201c03482c05882d081c0811705d54003c0040511303c0c025012141079035038071114001c245405210b0000160812a55000140703807541040304a04001410040350381200090455401000d5400c1000324681e140300b0b80001e03250f80942080c44a02090820a14140c3d0428415030b20440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 167015224 1250 167013974 167014007
    0x515060a0501030c0201090c0f061101050c0301270504061b110a060b01050d0905010b1c0308010b03250903050c0109080c0f03030408061e0a050702030d0908091504090c0f 75
    0x104044d180c0540300f540501340841c0c01c08410342c80180c8e114003941d0004690b009010000700c2000414400761014080c0501441da5400c1c900d1440e8600742c401d000094110048401c80e0504440382c0303118414900a160145000d80c000003a680c886d80042003028000501842c00e11541000e80c1c0c01110001c170751074034101d40200021440b01d425200481d03480c0b00e01d0034003030807492600c40d400c028400151302860003a20296080441c2e4540e00300c003450591083c0b4001400a041000148030350541000516080304070b01c4113410050000c80305201030b00503040003110018030705c01400c10600004100007011141e00f802c10890040c18060321940340c0b1100c01c4c0d0580a1410350040d02c01c0f645042084038000c0a00d141075686a0410a80741100c801b42c00b05070044002c1403002151000c025441079a000d100d45400642c644880c4020781000b92410100c1941d14040074040f40c84030761215940544c0b2204200451540e4500b8040031000310b83c0d01d036404504000c001c603003040182d0f81180e403001225065 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 167016474 1250 167015224 167015231
    0x907020a060b011b06090605010e040c0303030207020310060e150a0f0603020715110301030611030f22060c0c0201080108010209010c0206130308040f05030f0c1c0201180608040515060a050103 84
    0x309001aa405075a03240722070074803900c0700181014000164806d80425119601c140200c0c0d90382d1412526860090300c0c00f80024021110420000e4003a178001c081d10340c4041c00f59a81900210452001c40700540d100ba100c2e07090034000c200c50040d042c107c14488640c01c41301340303490b203080c980300c80036188642c0540d01c00d26a00003108014070409038003a15010048280902ca903810503140914907030021310003100c1d02801c000c2121212200503064030300c24402c0b40313483d4295940c0e03075903500c1551031303001598228810400704203004905079010700303841d440e0161a0a4074810003807000601c58801607000840750b07403041c080405103a030301034240c030042c1d84c04840b000d07104c0224400c0a040984180d00050207014005000202904c0c007401c0101101c608500b515a9461600c10454486501c1c24285900c2035183d00340f012500301c2070f448060114018940400c44150640c1100f0340800d06400010100e00d00500b00410010200150141241246240d8a0b603040c40400700f40650150301985051546 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 167017724 1250 167016474 167016491
    0x4090503040911131511011109040504060905010504030206090d050306150a1e0f090501022d0705120604120c03050a030207081911010b01020d14070507150203090109050907020a06 79
    0x1125040e2500000302540413101c2c0c44e502c201c5110100c1c218188a40803514540c0c60b496010300604c5074200c0d034990f040701c0a2510441030b0801c001880001c000315400f950b0307404403002181091142c6442103210350010180e03410030f228604c1ca00b05003c4031030130400004000700500d80d15141c901403080c200c6440c40c1d075140c080030a01680d50150480b410b1503001c1800034911040c81d844801ea90103c652900c0d98a82036841e9001241c5514000d1400e24480c20710204048140d800c55583e440c00c00d8410007916440c0d03440c0c200003020315211802035803841d403100f414002441500c82160070003038540d0a001070301da80d596401500600614101105150313021074814184032550040700c01050a842c40301c00740c403011400c0a48000000090000d4640c600003900045500014000c0780c0c031130117078861107031031541d8101031011130380402c804480034000d4520009802000000700d001d2856070f50051070311041910001003840000398802d0344280700c0c4c0810311a000e9000725010441940001c0d01054245 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 167018974 1250 167017724 167017751
    0x301020f030a0b0906121504170406030506040e0f0607050705160e100608010f121103070b07060b010e061b1e030c070504020304031403070c021507060b040905030409 73
    0x104001900c40200010030070160048030760041504400032289884d04d070316010240081180d4114581d61603501068204003400ca0008a60394002c0c4512141004038240b1007001d21190050391100001c01e07181d0060142a1030a4007a12616902ea0402400100201004150303a40310141c41342c014814001042824000c2c2401203017040d240c401d0350703d040341c2d0740c1d9004041e90400484442c3c0c00740102c04400715600e8440c03a2814101d44080c00304900311380c01c00140e2844400b90060494400740b040ca4075003a592018401040240401e0b540c0ca500ea0302141000c00c01d03285150310041c10082000c0c2c4a180e6503030748405860320b60b41001c490704541d111440206160007825041070b0f4014000f5012035460f89000401804c0d030121010507102465034030010300c02a404140c40c01000b04208101d042030040410740515405a55841c1800c4128640d0700410003110400240005008000501c442030003028022002c52003001d49041050301000d49030795880c2d006501032030744000d44400031314107200c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 167020224 1250 167018974 167018977
    0x20c0c1014032a0304140607080c091f050a090e06060a0c0206131710060305070b0319050a090b06030a0b0a050c040e09160605160b0a0204080f060103030e040902130b030102 76
    0x9855407140f48110492182e4021098000316011a1408103400c58070860f10404036889004004949075144035032141c0c00740840f20f410560040d9004003082503224900410240c410a00f284140c5072190303030340082a001031882c1200e0300306c140380c804c0820605c80c20751104412100d40012508d40000005040e00c00911544582c5100c00b06504c02900301280c1c10b00310340040071414498808580180c889060080c05940c9148000341003904200c2e401c020302c8030040029540640c9154116004207519410602150130a4680701030260b503850000f42004500412550080b00c100c00416840b0700c80d58071900c060700000c00045007152281c0214000220404c140c1e000703444903000180040c40c21825255541c104800c0f50300d1441561900040d640c4c1c05001100c0d00401024201c0f2581038190f101c02150550190006245503401c10000a5040041c450362000d104000c0c041d111552460600030003c80c00c0b17542d5188103600c0e00710720304d0040e82d0308000304130300e10076452000c40c2c072040c2c00300001d009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 167021474 1250 167020224 167020261
    0x415030209040b100f03021507060e1e0d110316050708010f050604050c0304050318010c080c0307030905030d050414030115080709050c090d0201180f0603020c0c101403 74
    0x8603103079005100c10800302e6503005124005107543e0704d42582d940c84810390a4400e45c40080d40206d250000c1590b1102154002c0c20328034000c92022030a0002004814500880b20f80c8441d1056011402481c5079801840840241e5809103407210410720904080d64403440380710000d080348000ca140480c00c1000520404000b0704116000700202c281c0c81800d2005010b04403940c91045181000082011440000380d0780669000001581420188031070031240003c0001d0280c1803041c61011440001d803e200109452041d40c0040c54540790a464007030105040c036040644613800802d1a800242d510030140e90480e81800c41500009500c200800c2c010940032506481511381d00c00081454400050740d1011943c8101d002c1002d40d0b108500e0120070f0007054070b61075100884e44585009980b290074452116680890050050b541e1918000000b0111340e00420100c0c0c0c000c180c28102c03100c140070400c44100c0c10340300b4507a00d07050140020480c44817020074103600b0b64040301140130943c8200c103a00b107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 167022724 1250 167021474 167021479
    0x1209140406031109071101050907180c051608070507030809030c0108010e0a0c03020f1801020607031a0d0201030b040507020d03141003080307090b07030207050a05010309051c0c021f11120904150302 87
    0x50800000050315885140a044042051800640c0742491144641170cc0b02e0156542e4074100000b42000102100509038180c4000106000d000c0102d202440084000c40c469805183d50b051600103041c10410300124840c140442c4200401c0541c61641c03185621109400c0f0005d864031004100350024000c00c0481d900341e000101d00245071000508a550a1420076021074081b5a1165400c0301030340d41d035601e48a9803a945080c4114907040252100641c1803050502045130307081e0001280c12603c04032401801a03101504109069415203d513694180d20080d58001c145086086450048a140f0000742444000000191100d12420b41100580f0200b05070664880c1d807130500030340d0380c40180142c510607801e0f090009855030081c42905905031744100940038480e80b40300414100700c070030781204c3d05020504a00303600503621f244030307680c40650180340d91851130143c12006000c070041018402e03079680894070141c2216104402e8a8441c00d080340c0115018119a000c242d8107103603540000d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 167023974 1250 167022724 167022731
    0x901050c01091505010e1005040207020406150e040e07081f090b09030304030816120b03010213080a1406040305030f07021e03090907180306090f1209140406031109071101 75
    0x80030000041c200c00f4070504008410311140c0d032680e41c45042d40c203081d21100031100750510208070905054018120072030000b4400148260f0369100c3d020302c2980907030110b00103041c07050041c080e0301d414490807007001c5010005000d56401e10707030090b41e102e40031141c900000e02d00f01d20f1525004400d4100340ca08036030246481003c0e09000c000355079640c00c02d03641100454040310010b410350342ea112150700b242045640e00405000002414001042042c24894065408115110b10034400340420001018480001d01032040a410802c0d5000340403500c940321a08190188004a031740001034a4005003441c8000d00251200300b0103178900440051040c408807658018084411004005030201e4001524400e20550794850100c40c9489a0100c6a0a00706602401e1020842a0b48140c410314850914207440407c0ca07140c0074181d000901081e800030754200c40a00680340300525040c020303807044d5810b00c16641155a2012030541480b041400782c01d0303400000705c1d1503104809a0010081010081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 167025224 1250 167023974 167023991
    0x5040606080f100e010b0d080315091e010b03042102070e160e0f060d0f18080301050102160f03030305090109060c110c060f030106030203040f0b090a06060803090f060901050c01 78
    0x40352280b42d07814000403214985507510748044c0d07040c000d80b0742288000305000203000310360355041034070f4002400401900d400140303800d100e620f4504049001d161b0304c1f00510b00d940c1c009016550300c2401600213851400003130007884002a8021101380103070320b0401c510444017901071301c00c03031609920383d00500000c0c07030300414003103000113014605150001555841500030011003c0c0500c007818002c0b003a8016008100341500703000c5980c00b884001e050480007042d0b841a049a940d103040300b1090948000381d001004002c203680421140040401010040c00c40714030700110503021840505c4045e0070b040d01c4034006100010300398000c4444a070311902c100300d5070410100c010a00c291302403003240302e8407c50000342c80a28000d8142c0707440014000c01d05243d80e013444401c034040e41003c0d204a83c0c881c103a032840f10010300d810b0082882411014010000c0c1e5289040230000c2c0d4410b6030011b00c058000300800310050f1a0441d40844041095501c45e94521044004803454800d40f09128125442d00846 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 167026474 1250 167025224 167025253
    0x20c092a0301060e0a05030f0d0305060d14010c0801060207080a0b0a140916060c05061807032a0b090105070209060a08030703031a040b03061603020d060806070215010602030406030504060608 84
    0x1c0c50103400c040e982205840d80740c0003810b99407901c2c1d440340140c0d940f060030412109842502f2050303200002801d08607800b0540ea41e0300b00c1075800c01c9103100b5565141c07041400050791201645005100303071320081c403031580307030003d882c0d151941c00c2d601404401000d0300003000943c140d0066580020b4610b0190110f151080e244e075182c840c20821000c400006503c001003d6101c1c680c2d106c451038201002d046181c81e21002120520754070a0009521300403500c0000108008803910503401402c480004c500134500c12146c80425481d402456140030309000c0540c159a0040503076800d183e040e80ca525580e19403400059504034070b940040301600c00082da18040550540000741400c00308544940068031100c10030069071041800c80c0e030581e01031400500d200c4250301480502002c0d07410f0041c0707005c2c8041d050344166500340e0850782c04d560281e4148541154100400340811607501406c02140d41440d030001c0d2240710f42e00c41d2004140d00d82021a040c000d00e60301480c02049608119020030084108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 167027724 1250 167026474 167026487
    0x1e0c0c040e03031e131e0506070504150f02010e0f2a0f0d0312020a030614041a0f040e010f0605240301210b07021c020c092a030106 58
    0x204a02481c200128640410341c0001601d014403000840c10380c00311551201d4940c141c60060440c240700992031750003000319100d00195861012480c3e40c03080401c1e96410b2035454003901402c24001c00004001c2042480e00b402c0307070f540c03030f107007071072402d8450382744c610508074050910a500844a4014902000030f80c0300e0000d04110341409205404007130343c8004100c40381c2d00603040009500300c401901044020300d03010042c00d0110b44241444035001c141c19000000720b0b0064400701010030783e110700a01c03808d102407180526000c400c540911a208500304c03400440510b034103c02c0e0298018460000d0103070b8490300071900b0340710f03610300070800c040f1006c40c5d80000c0d220f14030800d80030b004002071142d1080c03c00040d41c1d00300401c2400982c80c5901e46040520442c40340020074520800070000e100015901800550096015500419100104070440103e00c0340c0c04115a0a5600c6403000e405980c40f0041a198002202c2c5010341d01406030040e50312030340c3d0300004180b040c1c540c00070010407015080317003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 167028974 1250 167027724 167027743
    0x160b0a020c010c050f0f0a020a0c0e06040b0f0f150708070b100506070b010b0a0504031b0305060a06030f1b031b03060b0a050d020f040204081905012706021e0c 70
    0x2440f401880041c00d6403544034241c450858140c0810402c0300c40c20350030004240441710340c41206c464091a48988584015940010b0640c01d4400b0600c10645403e01521000708411140ca10142c400c4800051002d5401c102042c0900c0000c2800c06403850070703600703035171078280c00c10b04281c1e40301082e00d41030518020454100e2282a802c0b00d020805040c000207540085511152030801e0341d082120b002280e030045022441040010032010001400714100d0710400d80d11000c4005440e815485c0903410481c004000d00203a519040301003020640d01c0c02c40c0c8100783c0d04a00f815080d26103c1e00b40c4861040f05801c050701d42150b45040505d0000c0407170058085034000c8400b001081c1c0440100003010390030344903607036000c540e107600031001d46414842171110100080006180035070707400360f071030805041c00e00b03031071107519036890860034800e080c0280001207a810f0b0301c04055441c060302040c0c4610104d10080e1280350301090a800400e075243c5800303103070b01c02490302c56150b4548041069a441508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 167030224 1250 167028974 167028997
    0x1503040501050906060108070e060702181501031a060c030c2a10090e09250504110306101103130e01060201140606030c09010207030f0b040218010608060402160b0a02 73
    0x20310350b000c3c0031541500402d4140d44800040d02c4071941102d11201d4003014691040040180000682d80c140780020409129144211603280070800c054085001d07020142c140360a00c80030502e40011b803440001804022500c0d69110150010300901d5030184038a000740791b00c51402482d044062101d00d000100c1100c041184500301042c00b40000c0c84540350304c400c00300301c0c034100c00e212203513846c0346036070717006501c103040315030703150398104501a405803100c4103200c2154444d20a000f141018060042120b1148465501d1420413902042040c1e110300c401c0c4040044030440c0581c00107051084038007402415000f04249500d501c4650340301d40b02846400095880c0c54840811041c1e54031340240305100052a0a045035983e032020080c9902c000011411802103400100004405140c0d150310140078601e010b085151501c1800300d00b0072002e00440f01c1c01240b82c0100111540200030301d50081e41a140580c581c80004900c090b201503c5400510980c0824100702020782d81e58094549250203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 167031474 1250 167030224 167030231
    0x3090a0f080f031c050403110604060c03060504090b060405100807062105040507180f020c010c02010e07030f0204091a07020a0201030b0a030b2413090c050616021009051503040501 79
    0x184200e1590344d01c00d00113050001140c0b001c290b440401c0b20350002e5400780c000d045c5400c0b5114101c029605005007214101d075801e40d644580d5004c0c507494480c00015000565040118210f03c3c0c0321409440c000810980c4100d4a40c00003c415a070a914402d000703059000072120800e4030f684001c1c0c0480c2c01034044100810781c01401c08281c81280c0651070107907401201914025092070043d520a2068083c0c004116849449034501c83e0032501c000c12003030484000000744403080000c0203094501100e051031065000e0f290a001040c0520a00c003540f83c1c3c11900004c03000074030304d407146c9030303e0214a208500e1103000c41006000d9800ac40c0d9440341034803d0342c040040e5224001000012042c5000152a01c0c00c07800004550780c4441002140d0214206441504a03004400185110221110480c40c180c1c0301d41c4080204007250407454050401121481d01707002d01c40041000311001d03240060300c9001900c030012140b502030020280034101c050803c1a0800e440d0503042011351043c1c80494643d0718 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 167032724 1250 167031474 167031493
    0x9040510120609030e12010b0f06040e01091503080a121103191a12150c1e0703030f050703060311030309092a0d05010602150903160503090a0f08 64
    0x20308608020746032400d00340d24005100d510b50754000e0096050441c1400b4041c1d0300642c1c15990b0038400d94141003904004110700c0c1210050090010b016001c080c0208001e01041c0b1080700b11030b8229040d2811200c1c006140130000160100403c3c45a10203845440005500c04110740e208010605111081d0014056034200e114640c1c880c7c40f04540c05056003002803039401203080141c02401c50407506510303164513580413200181c010f406450001d042548a01c101c4500300b05a00c480700e600c081000e11040c104101032691803880b280045165814800025800e42054000c0e444a00c101d4000d6504020303d01d010f1101500911480c0400d491a400c1c0d0745820314640307400030459000d418081c0450600b526400380c40303817100c65004554189141c0503d04041d4510541c0041c20241c01c4801001c1055494108043e04154454900900460f1104100f00504000004451046c3d00107604070020700700505160b411405081a55030b031150322a200041e01050200400013a107890105a4041c0135 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 167033974 1250 167032724 167032741
    0xa0b0a0e061e0405090a05060a06032003011506031a06090d03030510080a080a1b0201090513020d06030809030c06031504090f120809070b0403020105040311011b08090405 75
    0xa049100c0c4400e04031040001465900b40380d0040e902e01c07180804944180d818000000c1d0a0700d00454503400a50301c1110f154041c0320701041103a40101c000c0744200021303401e60300d0f40c00e44020001d000f0148040d003820030080c0c0341c900354400700711902c0441c100520103440300350080c060411000005140c0302075104031503440c58000226030076030308000e00c560200f01c42580c2c1078000d400c0080504141007424040020261801d000700c404283c401c2507261380d900c2d003400c0040c111690f6500c2e00e084a0000301a89401030342c100c5110000e449003200e0081d407080702c100403440a84104482d201c08a41820000410002c04402400b83d00c6230443c00c0c0c07503841c44000280191030004403164807801000030821050381c18154000281c01c0e001d212143e5103008161034282074007031603080c41800606d070b00041040344e82d000e00004014001203107140e071801d403a40d00000c0685c0035501001d460404045102d4200d6070090511301f08030304c1804a1f0488443c458204149640c2294803454051424500041d0800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 167035224 1250 167033974 167033989
    0x10f0e03151501181e210b0a0b03060f0c041e03020a08030a0c140a0c1e06050405010f1206050d120207061e120b04020f07050709140601081504020f030a0b 68
    0x1020b81044c5212841d0013000302d9045d004c0c5450802031042813001140004015070309042c0c800d040c101c581c4482026180221064031300030440d030102880c00159403d540d8011071681d4002011030724201a50301c0b403514400b0f4a1080c0c0d4855410380340140402100d0269542185045a000300c0300300c40a25901c02c01c590b16032050b100702c0d90000b400540b004000031541d0b0a000c2a0340101c41c202c8592317122039642c49200d11059000391a032020600c11600803003d05d0300c45100527104516201d42818513010000e0000c00c1020f50300000d0142502c4031584181c100da00c254020b00004088801e040141e041c0441c00d68000c43d00403006026070b180c081059802100504042d08003054210003420b18903004a41c40d40050702d02a01558582407184000d42c0c45002a0617005c0c2c00e40c010f1aa80c4030755150862901d9516031110040c4c0303046c14801d241100360002100d5108100b0301784440c04d0ba072415050303c0e8090f643d285d025882031000c00d1055001c0d4110700654441e100711340c010090018110100000f4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 167036474 1250 167035224 167035247
    0x1206260705010807050a03140f04110a050a120f12050306030f0a0506160302220504061406030a09030504120b0402040e0c0d060e07030804090903020c0a080606010f0e03151501 77
    0x309003c200800d243c20302c220020198807910f40b0340010201c1a03288140410003064078641d150300500700500c01403200030160b04200c1d000071500a915035180c07101045070345080b0b124031034503010180101000d0061104003050115488880e0801c944481d0401500940040e00d004e4002c0c0b1800034403101e0b4110019004000b9030b08270300102001c2d030342d1541e81c28a8401050000c01015020b00c194045841648001d004080709806520406400d1005010032a403207980b1800c0d0088144500e0350650721414112070b00490820804502c81d221814103540910842d0f1000303044043c850016030034040d0b0454040c0c01603108036000c0c44003e4060001c140d1300c00c100c9100c17648c0a0041011100003440d140e2101c44030480343d606580d06e0780e0b9603072030308041703074000340e2040c44403c2c0c645c500c1100b010381c144030408041c5800c40e106503102e400e00750902da0703c0c04000e0030f0905102d640e8034946d42c1c07a4040d4038042c9154070010120b840d440628000b1850700d501c00e4964101180d500c2048016540c001c0640e040c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 167037724 1250 167036474 167036477
    0x13170a08040e0705041d010608070207061b080715091b03030206070806030c12060406060f080717010603061b0f1b022106040828080a020a120626070501 67
    0x1e060a1044607050200007902c500c0500c4420040016004042160b161400078421021581580340c10f07030140c0705502c0100f0010454000000c05e11080d5040300041ca20070100300c0250751a10554509810144281d82c405049505c03040a07680004060307400c0316484902c03c4d94018403030f4042001d10b41040c0c40a00005025800c00c3c400103541e68402d407441c90b444240102140c0d03500300d011021682c0048410180040381e089001004103000c0c860040d007000340660171b4849089460b181003580c544110303004d284c000661b6550780c1980c281c000d4000e200a10f401031000c1111020100c0b2012101184e0401080030800b0300c602554064000d40701c2011041c8001d06800c1d0159142c0d00304001c032140400e54000c0740c0081d10815050b1041000001d205920600e0380983e40c1d50380c80982e9138041501c0e0500300d083d0010000c034200d42c40e8490803140e00900440009616400001c4d4252021490901c000c090a4608400040e0f5180c0502113000c0360030051224018607a28051720715140c1089024450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 167038974 1250 167037724 167037727
    0x1206030210180b0309030a0323040209090102090303030c0405090703060b030c0d0212130201091406120604091b1404180201050c100501140a23060a050f13170a08 71
    0x10403076024a0214040d822003150a01007242c0b126400d101075001581c2803c401e034000309610354200d4152150080e41c0d881001c440700b40c1c0e8120700003050310340d00061009000e070601d440801e000041c02d4060324a6220024107498403031070847e040b02004e40141c0306183c86203100c10301188035580280b1981d815100180c801d14a107540d4082100a25030000c00d00240c07460b0b00304013241c0b0078003411450b01c0c0110318843c981910550395000040909100b03130000c0c2000d0140306101507880d035031882100c034565103641c2036035880d5564030001000ac20100e400940310210360110040f240f14240200b006655541c1c0c0e131124181400002c0c003084521001c5071074a0004d002030040c016600800240098141c2074080b100f0303115004100806a400031f81c001e52610301c59000000c2180780c203807600700c080c10034002d103501c110300a40c1100d11203000031003805d802a24006440350f802803286040b940744004081840d40d981119416041d81003941b4031038005000344000c03a00704500000b04441402d990801d10341ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 167040224 1250 167038974 167038999
    0x61707080702063d0e1b0306010e0406050d0501090308010b07030504030b2703091512070305040326010806070509030d12020909280203160e030a050f0d12060302 71
    0x710b07400c81410780360301e03a0082503076201240031904c4866a03080384102c3e8854000f00d468520000000400a005c0120494984c002080740485010650394802c400746003003540c80c404500410000c14090b0400c030303004850618500e0900005410010041d4400d0351094010381c1c1e2102600450300075100010b0010340d00b00f100b04041104041440c0d0004a00d100c205074000010100d81c0b0055149d03203001981d60004681e071690b80c900346444131840c0d50300840103032420940e00c0345644030b0f404c010620010315079580c001c82c052511504200051a80034840c07040304c2c0c0d0f45040d4007600c1c01c03802d20134000c1078403030080090042440313101580c10514002e00148242038031a43d065070706c02c09206c0d2020f42c01e035083c0b14941d080c3d41c810040e1030050200c0000290340a89841201c60400492030f0b40c10200b5004100307100382d4000b0240040406012850190141084c050020f4109003180030084e19600c40c401c2010b188000104942c15551481c0d1901c2c54141ca03030102d80c1d0103581c11484040d40c00074920224 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 167041474 1250 167040224 167040241
    0x6060307060e060d0b0d030c0c0b0306090f101806080f0d050a201207051b0a06120f020414030607030e120c01090c0303081e010807030210020708060106170708070206 73
    0x140a10059a084c049410b0000901155103035420310b000341e000800480e6290b0030711400718040006009220005032451400c0303c081060000c2c041d00480d4200e41040010b441c551080e02d4402c0681805030783d000c1030080100507a8081d240a0013100e9a5014005059511001c0007802e00340b20480e0362603071400c14140004c103540c025a02420344002d034010041405401c9014000d03d400c0c1440081c02e5a01c403030240c18010701d000305910380d00b01580c12880210005580d5040304000b12441441c00a00c6a40d443c80d00e1400b800c0004440039596002050210300e0000c0f00704440d0300810194221840c1d5030350000101c06581c80d4402580140d0414032010108044c100010151a070179040003081d910300d10395480f0a0482c0962060340000c0b00201404074a401c0307010046d680749150341c4215510750400b005140c5549144c03000a00c03524100c21200c00d42030080c45400001c20340481a601290fa441030043c002c0b6101042002000b0303540070015a409010f04081c5001d001e242d03004052660303800382d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 167042724 1250 167041474 167041477
    0x50c0c0409050f15070e100903120504031401050a0b061603030b06091e03010f0c080a020d110a020106062c010c02060408030406030f0c02010c02100515040f0e06060307060e06 77
    0x401d440e140a054144195860108130f802d900d0780d0300086040d4245000e0400402440b00b4140341880f40f1145121482c500303900021003010741e90842100301200d90210400d56461049500080014114113400c007010b000640c00300d442550800400c3c80b454004034100505031040001c0d0200510741c0b141800b0101c4d22980c4560780c50100074041d5031418001c040020f01c0d82030b030445400f0300d9190203401814070b4102030145c0c1d541a26021020300013100500800751100a00500549415030301141c00c500c044480c5e00b00102034081c078004240c0e900c0708100c009002c2c1203203015600c08543ca2140e50106403c1503004030301c050480503418200290000011071342c41d81441416a40300000340700220f074112061004000800745134500103500c4403a50208020340725001090025039161000c0340b8a0b0719004030b0032440824800e680016256135505001007180001e0f80d203950030a10304201000364044907030108070700018480c101c0320f10f9680c01c010190741c0e00890155100041d045040180036041100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 167043974 1250 167042724 167042741
    0x81603020d09050f2e02090f10050a020106060905150307030905011d070b070b1906030b0a0b040b0306040c0513061203020d0f02010501050904020111010f1a0f01050c0c04 75
    0xa00580381c448880c4003842920b000b088141d030300da000003148020103d410001000d00c4030307041c209011400b10180c100300e901044020280c54003030700001c0a90040d5219105a00c0700c100043c04d0084600e8041c0d030003000c070303040301c3c0204d4050342c40c0401c0415094001c0440000302c5a008015040380ca034440c10a0720700b03400190512040c19103500440340020403c1c02004040c10380da998a0008500c0e0505884c50300642da0b2041400b11002c00079180400e0009042c994401540c2c0f404070b00c09082032042d140201640d1b4400360031000c40100f40440861160841e0400000494040c0b2034100d2141c20503441380406d8400500076044034404100c5404d0450740080c00804084000412a90300c030b0692055040d501e204030010b0308036911a6a0041d04850b540800a08500c0200810340c10140422a42c0c100a000071b4144501500002c11300c04094010346481d20038144144544602e01091000c1d400001b40803901c90300c3c0361250107945500c90b4041c1c55403803015600800c558034405003400b00400d40003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 167045224 1250 167043974 167043977
    0x50f0f04020a03141006030b1014090f040311010c0207050103050c0901090e101e150503040b0103020906061b010515030102070f06020f090a0311030d0306030201080a050c0c0a05030405030606100816 87
    0x1807140c045e08508511921008500a203920482890309859098031551241c10500c01c51043c113203000a0303512051419903001000744008034080e00d0f14101514020300142400401c0c0d03003888551042c150740880e426040310780a8a0501c225181c502410300700f80560070100b4002a0100e50422150319850f000c01d0300000741c044a201c0060700c8400490040090301c00c0103090110350042040340b03804e0170003000000203052078560f08500b13050b9108802074606110203407245200b030300460095a59203049618180c960f41c0d62003041030351030900d10b010701000c548054044c0d540b0302100c9070508042c001c603180b96600c80c542c9047d10090703603500402500045407412030b0050610140455880303110071040994001c080340108180008201440c080c04407101d0340415042c40700800042c0d0b0850001504440d516601055a036240c180c14031650140c58203180991095840c154240709000c001032080d51004d500351000c559842e82809038108a0b25900000038001d480080c0704010026405c002c0725005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 167046474 1250 167045224 167045233
    0x31112060a1508070f0e010608010b0301090f0f0501060c150c0e15160807150212070c0510051302120106050a031514010e1602010c0f030b01090b03010306050f0f04020a0314 76
    0x443d240b00c2d181142c0d980202c82c003550b8030001440900b202000b918010f003900c2c81c1c58003680d030400c8880c4d0043d00041c070540c1e44454649440c844104078580000380744541c0c8e43c0041110350381d00c43d001000c041190000b550502d51201c1100c041c06054018501900d01d942c440e80d8002010209209485144000302700340c0070000d10060240420b0042a04e10302401010751507140c440508108101140c140114419244100280001240300302d82c1c03030780c2c80296404c01c80710b40742984c00d07c60700300180101c5020200340381000f00101c1440c0c0311290300c1c1190080e0380070646485541405070803240c450081c9940302d015003101704000340f2a00c0c00c0302c105d10764400000c50307200c44442c600c6074244005c0e040440e0030800c01c2c0420402c6004400d50360314511702d501c024001d44910000c045c0551040d14080010981c507001c00500c60390244041500400380105120340d65a507034140708006143c1558010076000c0544042541001d8000d80d590241e5001010091203034610b075100c0f40d1aa8103c50462480e016 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 167047724 1250 167046474 167046479
    0x4061a12030921010e0105060a090c0c03050a051204060501140a031a0907170c040e030310060e03010e03030405030903060112080313060b0904030f03060501020a03170c070203060709031112060a15 86
    0x1402c0c05107170000803c4d20000b181c0c5040020801c19031111b141c2116030414a80520b080b40d0503848500150526054104240d40c2c0c0780c1c04408640a00c0345c901480d4041103454184002c01c1500c0d48018100d85951802040e586011810440300c4252480080c2131801d1440442000000303080c640c64000040030111001c50303585e4103c000c10752441c03203070304803068000740d101d0380c3c090a160003010a8894458055855450072140425106840307014400421101712486101908c0940c0b0511640d080300c001c90340c981c6454680207949511030030550340240140000000c1c0000701c2020703200e0807580100641c0c15542d4862110800404100f010b0b1540c1d0b8441240c3c54003072701d603c06114000c6001e983c450b04003061f041400780903035100d40d001604640c8200d5020010075403001c040340d100c42d40304c080300025468034840380c4035600802c400079515000d5041880079640c3c00080c0581283d110b054202c00790700640e01080083e4200700303504070054101c0e10000728000342d0307a0f0041c200031101c1502801010b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 167048974 1250 167047724 167047789
    0x1150e030a0f021302190c08040801090f0c0510170406090c030302251a090f181509070c0f0507080d03061802090a03020d061404061a120309 62
    0x8801c814140d400c02c0c00300045000b90f0926000c07200c2c80d9064414207506d000034099503e91010000802d840411001c00b007143d00708481641102c4c000e00c442c0d0001d00409105040c40400300780c60702e100b2500781140345000500c80c18003400028807605244c40c1c6a0b140703c884003003000c0700c07203004000310303465a41d589541000811340059000603501030f9000345844005080c5442c0280c20101c0c004500181100c0c00b0800b0304103049000940d8010020792586031285400407401c01840079007010307403003601c0501131024409003030500c6220302c110340c0810112103a00d105010329402d05491107000149a29261808943e00c0100350503031360301c0341084403210342c0d40300b881e1b9080606883c1404000b0303440c1ca800700004600f000b218210050030b40c0b4214940400704d00000c449018a2000a0181c21543c603d081405443d038000f41c55a03030000c81600b030034605440c203400100402d4030f43c144691480480c10055041c038011610829003407500540c500f04c0d2510421000200359252510000b031004082805417 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 167050224 1250 167048974 167048983
    0xd0605090f04050c040902030d051e160318030503030c0f07051f0b01020610030303050705040801181a100e0a020c010207050a0c0b0c060c0d02040b0a0f020d0e060301150e03 76
    0x1072081040074a41810b0034900241004402d8131414440d038101440c0c074001d6600400c814070b001100d814810b980b02d0181030200851b5860000c00029201c0210340c0d02e03180e001d2400e400c800c1500c25564060303007044800443e1504110b5000141c0150f1040c800910415010002000543d501c00070450500c5090340d11a844c184c0d00009202c48040340e44102951148103005e20300144509001402c80e1b23160210700305030420720301e1102408043d22800400c1155001c0c0c4225409414400001d00007450003400000e4014030559040b200e40c005101c1c0340c0d03142d00f19000300f85d000f0ba005546c544506441e0034456a0028009061880a01d508100c03641110800344014543c132480380b40a4840f110351402c14128422144d8400030041404001c6201400310200d02d032035010300c00100c4a030319884503030045002405160044206c4034000120201c0040c0c10150a1030f020316030b5800c0795a0140e00c00000c0750800b086c849820340010042c0010320240e40c0c840c501030b501110500c0d010b21444242400030b07250 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 167051474 1250 167050224 167050231
    0x6120b0904060b0406080f0309090a150b0903150f0a0b01090504020a030e0601050607050a0602030a11071506081218180c0304030e010203070c050d030c14010c180305060c0d060509 79
    0x4040e594020306051381030a0084a00400c050000740034507405c0008000e032a0b110701d800b56486840c1c46400182d01e07402c4c1c1e6000b0b914092064480391881a200c104002d45c40d40300780c400610a1003440b40943e260303403003250854825501e4024080e001c3d101c030341000c1d004d0002d42c590356041c4011542d01181d03039116840a0f00b00b580710380d6004200c3c100f0440c2018180b48068001034003d40c81008003c0119030002000300961f90b10000040c2d030f039030342d8807055001005440402d411038200004d080d4240300b0115841041e03000750b044204080390b5100019681e8041c6036034200034520f011f03c1107482e403001c0c03200740d894560340203881d0405603001c0c0c48440901c00310444814840351400310a000505600520003907400400380000c62401c0815101c0e202d07945000d101d1140708100752520941098030940400424a9100b442c40280f40d000038495400707800810b1210700090000c10315425031544090b515000c80781c100010300595150000a00541e6114400c1441e03540c1c0c95140c0000c064442d031035014071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 167052724 1250 167051474 167051483
    0x8100b01210e0610090b10020601030807060b041d06060d152a03090c08030a17130f030201020405180103020907030c110a050109020109090212060603060f13060302090c0f030106120b0904 82
    0x103229082400410446c0c00d40c011040c06a004149440c500c3d98001803120f041d80c0c0c01c40001500d0714014907041b00903000d22030120350414100900c190700f0030140400b581107100c1307040c140e900aaa65400348032a0064002019102c482c0b00ea608001e48980390f400105200a00a041040d040178082140400e9100c0c9d403280d80002e6503410703450184103c041044014080d048091841c1c1078192500900301090341b010003202500020104800300120340301e408059070b0040b05541c2100d06400c01030300070f400c58890703107000320580001d90659000c411840e5050380d0b40181100525213a14800310014626605000103001310b80c545104400400c10240e180300707203d0300020a1200183c800182058404e43c030015003d0f0042c012140b0b20100100c2c51640040241d60719500c1e40d03907680c0052419844450083d40202c0b03a141201b01c2c1a83c00d40204043e00e00039290a400d648038074071400c0b410b00c0782d070036200328030711083c4014031282c0d101381a500c1441089490200e049820b8070700043e080d4006a800300d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 167053974 1250 167052724 167052751
    0xc0c061d0d0807020c011409040c0c0204050117031b0712150c0503070f0c0809150301080d0c2001090302090711010b01020c0a060e130c020708100b01210e06 69
    0x840221041000701445015071810750982c1c2007401010703540c0c1d5a0b0359081414449092114604c0a001200380e03074494000400c00d12840c01c2010014000c812800d8041c1d0049051078000b00340034046801c411240803100780110728014984040200e24003400c8000721160081c0580096a5a402120745520900592280c0c00d41c0c410004d104080361807a60f000018000240100214036030040308203582c00c011824080c100143c3c40c0340c00100c80c840ca50b4803940c401c50324800d842c40041c0b5240590306807106081240c2822101800568182d02800c01c028107040c0c900c050402d0348500320a01e2001d404040c1402000c968803030380003503408c01e0204c1d900740000310303212207000540009005207007002c0000e001410004030011b0100c0d4041d140c900a040901030300407000003c40d00c0d59003081080702c9100c1e03800c01c0b4032240901c000f51240350070310503c50f9a10890458000b540c0440c4200866108161150300d5010b60084846506400141010020316914a6130925841d014011988a0740d000030081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 167055224 1250 167053974 167054021
    0x10110a05070f0c0b18030615040504050c1f111518010f0c030b03061005010815030c03070303230415030c020a020d06050105120f03370201050a0509010b01020a02040c0c06 75
    0x40310f8000105d81c006210f03501040a0050b400c40400780c9460708401500d01080039542e608001e0716003601c1000d182d402c0714840c0c0c0401c4000e40c01c100030f9164401c0542c0c56600c0202405409943e0b89242580b0340146502d06011490b4200c0d080c54502c41181b0f054000b084504100d8055000c9500107004100442c0d03c40d900102a450300b4030181c1d40c040d21100c1e554100e182031800003403800e003006100c400c1c0e514500c0300c28041654200554601d52000030111400075032686001403400280e00d4592903070081d0010041c5d901d4044106036015908101540ca40c03114039200114090100c5190140540c0a00340480015844610782c1e58026400f40c480441c041d4500b0b400e03c03003009616509400550003455188907070310400700403941d0740c404001600c9141d4050340307028600414248400b60300802803813101c0f4007030768042d00554820541450100010340da4010280c1c20b0b50700030000701d801a00b162155a00510785079100c4221003010385440c24202038142e031400e0071102c1103251001b0120806c90791 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 167056474 1250 167055224 167055247
    0x12030403061509050f0a0e071806060201050c03040317070e0d0c05010206060d1e02030f15061e031005072c190608040308060103110d0b0310110a05070f0c0b 69
    0xd42008183c003403410030140c500074030b29031010f40c4054a01034609803140044c0041c0d1800700040f50150201800d401340352041802c000c5d00403c02c511440d8055400c250000d006151803c003a280728a030962182c0010103030141c01c000303880d00700416903418410540302402560700e03003c500741d4280c0d214503e40300e01313541007a0002e031038030030001c1c800c5220708c1e155080c0c01c0000e102401c07220484070507107603101300d01c00042c40048c7c10481c01e000c9400745c07441840c4448265110000c440781c0151003e41d05040c0c03c44082d0f1103075a12601c1004015050b5000b201c411601035030300e6001503070010040c90583c4201c2c6003120030000c4d00c040d500e41e462032000c403654000540c1c6005031440400141c54541c003011145041c0014000c1c01000340040d0510605100003009640039401c56040c0240c40039101d80d641d500e01010030018805804400d00a100d26008441d0380c11a0b486900700c3c00a04d20b01d0780b401d0041e60001200c1a6008203812200f01104900c0c1600064401c03040d04054061080c400752601c01d81b200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 167057724 1250 167056474 167056511
    0xf05010e0c010509060d021b100b0a03170a11010608031e07020f060a03115809050f03030415060e0117240105011121091203040306 58
    0x20325041942208100701c8041c0c0e000800c541e42c0036400e494407074440340c0c0000d0444c000e00a401601c0c1c054080c1d0191a8a03a00c1c0100d009000c2420b0076104121141900301071000c20384260000030164041882c08500d020141d401500c00c42c0c1048c50050807004200880d24292511079011f03000652000c80c149490305230071101698034242481d0440d08040c060b400091036050b061188a000740780002d010741e890f61280d00b003404039900003203500d030b9103480207a044910315020036101700c804916103100030920304102c09006484c0d40f1513100b41103248260351204a00c0910302c0c1820035500d0f5142844030003d003013444462051002c020195403280b5107418041c101c044804034818400b40307403001c240701d10040074100711b064030180c030800c1014001e010120f900d03008030841d003100710b00790110f4400e0141030baa0b04c0c1d05062715020382c0c80f030030b811803401d50803a5150401a03004162400c0c400c4244401c000c054007606401200601015019000ca4039003400d59000c2d40045d0350307003038503414051030103407102c03c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 167058974 1250 167057724 167057741
    0x5130503190201080903120c070201080c03040c170a020a03050601060f050708030403050f040806331c0206040f0602010b04150501051b030409020d1b0305010b04030f03120204030f0501 81
    0xc0180110a203000403071182080961030003410b1208010106822510400654001e80d154240010542c00c1620782c202d202d80010388100d000451031800109184082001c7c0c1e03000e581d1000b0140c03140c6041248181d1242c541c8041182c1a00c200104003000d40e0350751301c8101c021400f41c0041c20155040ca00020700d031401c147d440ba0140310080042100003007801044981c4070b84c061500588400030f81c0f410190a01c10b41d401150240714400501c00e1101076111800075602c000a40f0004040344412940e0b0240300c0c5044199004014400100450921010340260f041c0700500d000c2c546511800c2080d04248503800480040c0c0d541d814940a500382440b1303c05010410383c81c00c180e400d01e03040000300340f8402c540c0710003e420340f0088150104c0c001001550b0242040b00025500e80f0740400a890040c1500300c0a803641c610300000e41580d0034023030322955050b0383d00044210318150640e141c451425030014011800c1090140c9982501425840a0b0001e507110b000002408040d600b0064296030111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 167060224 1250 167058974 167058979
    0x120b091c0e030d0219111f02030d050a060f03140111040806150301050408040b090111072903041e0c05040501150f110607120f050406050f150f060d0b0a0303051305 72
    0x1410200d07003907400c6000010072540260300c030f1b041c0310500001c42c42d81c003440142025500c50b042403c01d5101d40110203002040d204a070200150b070741e44000304050305e103684200003c80c4911101031001c1003816900b20890303002e000c004142d1300000a88904258807960080f2a40d400c070105201d2844100701c0000c424013401c4009102506151725802098459071040d03000c42075000680303c1003039000740304108210349081c05a41d02e039581c0b00300c500c9090080c2044505948440a84a00210101070a4a000c0c64201c200410744c1300070070320703002c031501241c010540d5000c0519070f0014917503a66000f150301800e40d040301140a603540d410040e01010550502c0c03c10320065141048118030006842c550100e4203103002d034100010682504000c0c42045452411241420100401d00c88190030040c011455584003010965940c141140b480d2800c02d60250b204c0d480040c1110340f440c0000203084c45403120f03180000e2884161000070384204660307100318080f41e8040342e04082c8d0114885803c0003803406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 167061474 1250 167060224 167060233
    0x610030b030309010804051509030c0f1b0907050c01050a0b130203091507140c030c0d050a0206070503060a0905041a06040b010507060e0c030d090801060b04120b091c0e030d02 77
    0x8100029103a024046281d030405c101d4030b001a003030110410401124410700042101c0780d041c58551035480303030701241e00c02d4603030b1058207401c0104090003d0040319000d00d985205c032508103103c003000a002c802078040c0041003410700464040800c00e2045a004109850001901004a00a20840e000304004101085d40305008001c082c44001c1502c040901500c0d040704001e9840c46801d40c2d126400c48203280740d07004086000381610100100801c8640c1845085581c0c0380341e52042160035208152041005070000d80114511a000b4800385400401c018042818540c80300012001c981c03040b142541c50300190508080341c000380c4000d4907008030083d242480501c0a000000c1c00701d2085403001403001d81d442c41e6081004d0000d00030300d05011402803d6031501030304071400070184890350155103119440e214000070002c40c100100d40480d050030380240182c0c5007a40301d21900d480d00030245503042c05507440d1400607413140c004040341542c682d25000c0828809609051900102041040c00d5501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 167062724 1250 167061474 167061491
    0x3060b0604240519020703020a0512030409091a0a050619080a02090c070606120c1d0a020901140307030608060a200309120a030603110901050f01050a020106050d050105061003 77
    0x2001182c0c01e560710720700c0d11402c4102040040f280391152000a09510306448880c82210384e0208403407045078000c6032902d0049880d1010015205080500318005a100304000c10403146660044000c1390b005000304404101558514000c060040701d0b413000c4669501c02b0080780c5e290044e081401000f00241d001e05060800785070303680d03a0154035000307442203042c140040ca206104400310360400f54429000e101d0942e44940d46003c0300400402202d04001c101404245d101010000e0318040c040901c88946a4540c000001d00940c000300545042258a4914054900d5000c005601070100e0b640c0c0050f52901d89843e003410910017802d12840a81004103d9400b0401e001e41c1d500d10000c0041d00a99035128595542e19045400030200c0345220701050201c110364040c0e1040041b02d0003828550b13104041e0100300041d000c1c00b4000c2980c440742c1400071031940d500c04d1002e0480c4a03103130f0000107030094540c00094070417141c0c02e0044074070b691508100704580c00c0c00c1201d40107d42190605000c90b10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 167063974 1250 167062724 167062739
    0x110109020a05040f060504020d0b1c1205030606120702030c0708060f010b0c1905060a05070c02030d0305070e030a060c1b0804050f04111201080705011701030b090a050d0903060b0604 80
    0x81c080c0b00d80d91207107856040200088005500c414000c5c0700041c000c5541e1000401070300040c001d403031203e41c403614101c155407074091184071002009680c00000b019124404130300503105600f010305880e1b049502800004101c41c91044601e010700c400b074000703544400101600b94503107021504120010b070000c0d07040c40000d100d01c071411419151400001621101101102c92030a42500181010120700781c5c030b59000d001d804120382d8002c50240740c0602481e0750f408401d407103c091a0400a4243e0701913031a041c0018400d41c00190440010324241c3e25401d003500c006071a0290154081c0c5149641d5041202825040b00340050000100403095800381d9840d01c1b0220b0b20301492060901404203201112055034503503128a8a50841e46002900d81080c98407800c12480c0900070074550f8071030640081050341c013034040c0b40580c0801c030011884582c255980c80942801c06070034101c1c948034102c0001c002540900c1050003100d03039a50742030080d0345142401c41c1270310800304002c1d010b510200010312806 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 167065224 1250 167063974 167063989
    0x715020705101e03020406090e06100e0a05040e0303091605010801120201050f03010608160206190e010b1018050d031b030c02150703170c19050f0f0a11010902 70
    0x80d80704603048940c0c0849020140d80c40749a94009140b402202420725001a41542c081c10075160980d9075020b20940b59580c02c220000c041c0c1d04941c0c465599101c12182512030702c2d0009288002030854503500790341d0380100f0181c95001c82403000b642c06c007100300148000200b01690030201440246048035141400180c542d10041c040d40c40301c0490158a0030559010300c003219440c02d01e842c441a80c075030352058001c0c512a0b0549204600710340d8201d020306100d100040f054040d608065010003c100181c1d60580117105c1120310b01981d54850a40c0001d80c3d642c207600988000e00c070f4a54000e010104151036101802980110344500b0400d082040440c1d4401300c124040316010132003e07011305003403c00b91154000d00c01c1c0250b1103400c40d18201c01001c1d10a0240c40d07450b1007612500000310301d1100058441c0700850f6841d590202c240071007589032013085602e43c071445407424868503050b07040801e809603038401c00c0ca0720300f03098002402060099102107100b15129444008200d0482250300103541d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 167066474 1250 167065224 167065229
    0x51801050a12031e050a0e0301110f0903010b0301021801084204090305041701060e061504180204051f020a15020d0204030b071b0c05090c0d020a1107150207 69
    0xc01c81c02c0780c0c0c2041014050013400c510b0800c4014030000f10419510000c20381d40c004ca10f0000020f00911900042e0305050281c491410b1004590074103000e90b00d850004660882ca202640c1592610046811038400784020f1941e0000482808004a80c480026002e654003070185a10203a8540703520002e010504030406040441110300361070781520740009500045540c2c840b55109140c4034100c400c16401c8001081258a003610a00c02c0c4811440e0090880d01c040c81841909416000020002d20b804144d03504410341c940e80031030a0075201e01b68103000144042601016130b41c0014144140d18000143c0e0055000c00c240b0510341d100303000350094076140f42910081c00b410104c01450601d9a164060720903046000c0c0d011501c4966a0804850100040c1d98880114080c02107480099500200c00c440312504960403031801483c01c030030711034021802000d401e4020707800d000c10403101c880d0b80020702c1d1241a030342d503c01c080d00300030704001c0c24142c0300c0e80006100164000f660700d03000d8000c54005d08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 167067724 1250 167066474 167066489
    0x270a0b01030b0910061407060c080f0903040b090d0203011e060806010909050c01180513020d0f06050a060e04060302060d0902010e0102031603080402030309040504080a020606150409050619090204051801050a 91
    0x9403050030001b100b945010b10b000090050b410040d072841c21550140d0800e2064032072483e07003142c0d80c641d01003a585900c150f0144200c1d0b00c0c8200880e00039030400440c060380c160320181c00014243d00c4113180c003d45500c5121109555030700d4800400c41220100030050240c10203003000c010820003966020b9495200e12020783c10711000480f14030340b00640c52101c2e4000c00015100c545240b400343e4210b40250300450700d10510074500b40849100316458032584040d960080e003802006810044162203007141320301c2c0345030f00c82d481d10760120040e00d03003001a083d0f19180d0280454100c1c0248000b51003000c4c40e102d4141150700a04c10800100300001c07600b807083c1e070541070405183d03c4a0000c41d007140718250840d0b8226050400307101c1041990801041510765a6003512031a40303802d03080101c18016050b40108001c000d120501844036160f200ca908018010701c0318121030032941c00241c00001c50b51295500703039808201088030f401d0200d5009040c4080c0041200f8035030600f0001039038034409004064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 167068974 1250 167067724 167067737
    0x5071d0121050106080916060c02041a03030c010e010510050105040b0f0c070609050301050f0708270d02031902150f06130f240e131b0f181a270a0b01030b091006 71
    0x24cd806070b00303503850030120314040d080c1ea5440301501c283e0341c00381a64440356000b941ca803070000ba001120682051094130416540c4a16052400c071011846030020110440e0b8490100046400903508000d458010102501d44d018441c1c50041090300b1100000c00060300081910108603006034019a902c0e0b12440860b84014065002c5442c0707841d03180c29400090141c4544054421250740000190480c0d006c1d00040050002040c01300321f8a403080c0c1050a00340012141c08541200d2405084a80c0328038003800f21040c41917901c0d004415140d51281c544940e5079641043c0e03600d42c54504920980440d104a10410613103003501840340190020300401d2440070700070700202085409032850b5605c4568001d07180946486184a0491811512402c50040e0308299000150002d03801003540420143c14801c800c1d403010002e2200b642c1652448a0a02e00056854014603400c10b10681c002d540301400090450018000901218240c428181c0300b50319007402c20085c20180449001910305500c0c0c0407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 167070224 1250 167068974 167068991
    0xc081003231204031202190807110607060e10060f0b07050c0612010f150203120c0c0115090e070513020d060504020307030f05071d0121050106080916060c0204 70
    0x4030040000c4040610140500b0101105140c55100a0002c2e03901444982d00301c07892022040e80d448414051011038040301c003442c43c1c0858000d1024180440c0110824408001c2400000d0030139806040d00300c4001d0b0f50b070111400d031036408000c0700030044068076040007403908120380c0115611041c4107409030740380005503c1081100510a05801400141040303485600c0e8146891100c130007400b42da01d1a034001032000800480b00c06001800d1850354002c0d500d40b842c42d403d1a940c039007005045a02030300d010440c0450f268001d00c14031040c04a9100780040a034206005001592195441d0740510707840008248026a40c7c1441c20940102c2c41e000180e40340d2309000d4010240c6001d0344090b030b0240c80803040200d9a60103400c0301c0e044204800c8100455a255a82586e15500303000300f40307034540420f00d411140795000d070b42c0000c40c42c0310b10000c00f5030500c10b586008003968000d8000c07500090099040c0304082c6801c001c5901c80d1101d0074100b107041030030000018134a14070014042e02c00d685030b850b03c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 167071474 1250 167070224 167070263
    0x120901020c06010f0608130209151f020307410703050d080103020316030b011a0903240903030c0307080c07020d120914091b040e0112060c081003 64
    0x4480c0710304944030640d492503940c1c00e0520000822881207a010946103030000d03014900d2048800c20b0a64010400a02d40d25914146110000350440c003a4004d8490b0304036200f200e2608040001000103603004507602c82c0d9914141007002d46840605884d0240441d090b006490303a140d04201c0003000b401c2180100d201d4580c1c0b0761401840d540041c24502450343e0202c655039004071154180ea000790b00b04d40ba00c4019811111411080748005462120210014001000c5591581c1d03551000c402003982407280c02d00c0020f08054408081c00c150a001006408901c0300c03072004a503205080d080910704600d00002c00c07000b1484000c050804000d40d00c030014000504010a560340e00d40c015120318401103407850312100c2c8581c0340c03203050302094103050b0009000304460141d078807400000d0150791941d21210b40c2c0403840010034488010194050001246841d84100035900910b600c85c00505081c555042441c00ca5124000707040c100318421041101540c5041100070849a00c143e480004400d801d68 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 167072724 1250 167071474 167071477
    0xf09050a0605060316240206041547060307020601030f0305040305030a08010e0c0405010c110109080a0b04031e0c0f0c0b0409050105100201020a020709021c0509030310080106080312090102 83
    0x140c1a0703031122443c1e0042005240c00c198042d1b03051100094000043c0718080a0383c1d07412085500400c20090301c02c081050018030f80140e83c5030300303c3e11702d0b043c003602d00249804542d5070800e40304501d01c9000c04000b000e011358140d00301144842a05c6152840c10900030003911084140400740c01c69648050010400d07101e41e04480c01140c028042d29120003082c000101042400c0c402c03104100d1a00c00403038034448900d000c4800303c950586031032400040641d183d10340d0701742640d0300074180090b05500040c654828444c2c2e184040c825050452145818500a081143c01e8045400d615160b10300e4546844d0b0041e5292220f42e0301302a140c0c407103030702c2460192003104150304901c0e030562010074000f81403882600100e040ea21300310b40c801e59200034200d00b00e01300c0c05055940c600691002da004c0116030000d0f4000e202200e81080c5000100c80c2c008078101c00e44d00e040d40da00d001e0380c0c400410005c8004032003031000003500c2860020310045180003070013a9603000e071812201c1d076280300300082850520b0950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167073974 1250 167072724 167072743
    0x705040302040906090302160b0a18090204030c15081303110a080a0201060302090604050424060b0f0a1b0302031b100504080910090f030818130e010f09050a06050603 73
    0x20000d10003200c00303207001c90117481c42440440161107000c6103450034030080c240709130560b80c0185501d0b040a000c0740d000c8840d48014485215000409000824207619a0000b03001460144c07022201c15454140040041d41302b0340c2c00c80c03003000341c0c60040c4030503682031049456035250075203805807202010316035940c10240f5100005250000c0081d106038410b80641104c02228021660041c5568618090005036074044a0041140702c8840001154840c26004000fa00002031400109c2c42d440700700c04c1b8075640c00000c0000042e50301044000145030f001118041036240040031954880503a0390296030780c02840801c042950210703074a00c0d0541e01c10000c10110040403101132104c0d003454200445c9680c450003020b03028919417010054400e000e440107004a0b50dc05420550151542d112449a03410209005441e030203404501c3c415540c5180080d10301420050001401c84020502c807130840340d140b16105ca095050107445000b10308040f40c1d841c2e203240c00c040045803503503030078000905090f42c42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 167075224 1250 167073974 167073979
    0x1d0a03020d030e0115080c1008270304030c09021c021602061b011b0e0d03021c21151a03040206030c04050901030303020901090515030a09030905030d11010501090b011202030705040302 81
    0x17600002d15280009111110820255900800d00900150846900c034048400180309000822140200d0600e0300c80402c403900307408243e07410b040d200d60350421807000300d40c4141c070000e0b000b0070b0007452506810140d0904a414000451800c0e040445081541140e10ba020744240c1011405001e024030b042180d1294084100003000800721140e4824450005983d612000445207a440032041c1080c4a65502d0b01d50550024100010f00b2403000c104a10800007040400c42c14070340ca089280800d020042c070400c03410801040b82d590001d0b64400070070440e845003070700d04020b405038007a480134141125005501a03880e1940c0b6503a8160510360b80c0700da07901c020b4100d0381030000041419415809440c00100036603410301c0c5030b0354804c10070004494581c1620300b800d10400204403420380d10352024552910074204040050768510000381040144022000842c0550421030542003080c0710f210301403d881c0804010500700d4900003400203580a45c50041ca0354000082900301e40a201501d00540e0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 167076474 1250 167075224 167075261
    0x110313110a0f08060114060903060f070c06060e19060605041e030206030f011e0b04090e070503070f0e0f090304060c1103100207050f010b09060f010e060408011d0a03020d030e01 78
    0xb035400e20383e52058240700b10385002c1d900c61b01203a0f04d8030f40300d0b0844204440c010000c00c0c2d0b0b600e0345482641609409095441402103c0c0003031030000d8458000c0c140100000740c409501c07032500a0b22003044107101a0765001c201c1c90144c0500c0013540040650307065419030590301680c01a551212002c40601d9000a540301d6408020010707140012680241a41c5001c068908540002500c01881107041d001e142c1c10b00344140010710518000e41e201041c0c41501c0c10450301059900c0011a00708469600442d0b4481c0b85440c0c1409003c222040140d001001280340300d07424546480600d44038007070790280342c040107001214002400380000260484e4440101620301d00c502c2c00400c18025405071500300c3c0c10b8001d007949440707085018464a58100300103804120719030327140340802408244000f08941070141c0514605056241d0802a0010300a03900c00000c91109180c02c541c00c82c3c24104c0b0241c07540d03002c20121000031368042602c03043c101817800c011441c42c1e5801c80d0b060241c1901210001e084e00b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 167077724 1250 167076474 167076479
    0x1030f0303050a0e03300f1b1c0b010e0406090c0f020c15090a0b040602010c110f0604060b18040503030702010b15090121020705010c0305010609030b0402060a02031b060a110313110a0f 81
    0x387c07844030b00d019000b241c20140300f00c1410f160b900500e0050410344030a0742c15180d140d4030b403d031040d0044035802c003051514650040c00c60002030222070240d000645440d54400303540c042140c102030644001c0c0c0340b0740000c011200c05440004c4518100d000300815050740459075181c035407114412400a4000b11703034815100c60311103c0007030007044040c0e240350010b50000e5001095800c0424101200e41015000c0d1180b950b4a803500c0d4050010650b4080d008990105050f0f410391151000e68041e40c070a00113196070b0300b0b01d034600034250f8243c0000103115a0031340d4107102c504500a01110303210038003070138020305031940100e404c4411420721422090090001984900f003080640c0985640440c6440c100510390300c40348104c3c0c0f66102e07808010010601038002c1005441c100c07029150091840c41200c0c0744ca0f0480c205074400741c00d003900e09845a80000c1c00e00041d200940641221011404155400d52800b036062419410581d80c000e0202c202c0d40c0d0403064591103240052028018503500344500b00d9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 167078974 1250 167077724 167077741
    0x10e21040506070f0212010c0f0f08070810080706050715020307020a0f03030906050c0307090b0306010e040f06031b1404020319050603010b0303030c0a0306080106050d08031e01030f0303050a0e0330 87
    0xc280304188c80000c1088c1303c00700e080d034003a21014002244a0395092000e82e2400829205138502409001c45070207040c200284e030010800044010300341e40d907103194488000b40783c40304d5403084200c00c5140031401407040000b080da0002d208404c00c5d400101250302040b0508007540241042d41000d4046420b18003000410345401d001540546c065170751700180c0035612000c61405020548011740003600384010041c191a05800148080504500c00034483d917590b5150101c41c0b4a403034a041580860b04020032442b1100c8008100400040c0d6041d40755240020040d0001c3d0100c440b0303a1000c96558001c071348a91000d40c070011500b640501203d40d00e0070002c06104480e00218440800642040e40120b011801801050126032018007081c010610513039616005400052120f4400081c0344040f80743c213004490803a000754010807031409114040c0c10001c0944200508819049040c40310a84041d88000116035000e01c1d9104060030440b05540c455080225600c0841d803100d000006101d14203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 167080224 1250 167078974 167078981
    0x4110306071d01230702031005090a0309080c03060414152728080d050403091a0304110603150d440a09090e010e21040506070f021201 59
    0x7001d0032880c29900304004801113440d2a1a03450b01d55012220315040d510a11680001d414640e100409885411240340f00c00c0303041340d1045a202e00c03e9440804005c0901d50441c0d0400701800a68001e0010240890086551844041c00041074846440000f420000c0140271048400c400c08101c038080741403000700c001c41a89120035000c0b294940040240003000c0019041071500c1541d00e568210a4202001700c0041c1c601020a42d1815003c12030303000109414803035640300d540301c0c0c1c4807200c2032424071805064031649a0024600e100f410400e00001ca0f00e02d03840342d04518803c46d6603e03900d6a4656618030710040e000301840d003104045500908004800e10600002032a051016084841c83e00700c2c426200c0285d0001c40c50a944400d0400144600100401051b40306090030031980b07603509115021140c0c610005000799540b109150700354801031001c612148107034034085150300c6a0714407102203032145200d030505c00c0e400082c002d820401d2040a02d0205600209011030040104040601a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 167081474 1250 167080224 167080247
    0x2120705010e0307060c140708060103030207080d08070e0d020112020a050306040f0216080304021f03150e011d1e0405070303080a1503021e13060819030f080411030607 74
    0x4202e082101140500300000c0c804200d41d40c6a81e014920f01c4d480d10b8070380034801ca0341000c1000380603d44022030350034030412455008500c41e034010720010789015202c40c204240300400780d081200100900c0078040d4000050040130b482102c1d02c10320000c641c801a502c43c2007031840001440d0001c1412504950814051489801d0031780b010310000702401c594100700c1c450001ea0000c861401c40c0c0142c08111280084c1d980548064060241100010080421011240c0d055000039440b40444c00001d008200b158004055071042c80010754100070300d1901c1148440000d207001090701c0c0016906465442918071454030694070003450703052600b03240c0d45440443c04140c0110340c4000110790004d03075612800e8042e0740e4030350005100034210f9081151408074140803d44240100c030a5901030f030380342c2c8842400d07a42510740c0083c1e054036051102d41041046444441c0304540e040d01080403a420041e050701100d020300e0000c0c0d03250780703d00d08411844005448190540300704810000000d821800e04003a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 167082724 1250 167081474 167081477
    0x20703030f060302032e02030c030a0c020601050a050d0602091f09121a0606070203010f0209180405120c070b12040308010504020c070302150d0e06010e0105010903170d090212070501 80
    0x1032800d600039a00c0585029101c029010760141106881d001650b5000183c1c8a80300301240d52241c00e0f0306c0c1041c0c103a81060303402d20800d400000901104c0d800b075208506803d2640d0014020302d40c5040001801d10000c3d2003154015106051080100308042c1d0460300d074420700a0503505100685207030890071002144244020a00f550070206103072040313000100100c1d602c100c00d104070802c1b464580c0c000050203407489070080001d1000c02c0c0140d07000c2c05488142075005400503124220241008898012608546a0150a80d0601c400303d0720114030300b101c001c41c000c005a511802804402d18100c0903612141303510802185000c48401404034070b03070185d4000d80d544241039880c0c208000492040807805249940018030420060400000400144210784070242c03e0a001120101c02e580154010f00389136040000103104d404d451f0250706014010a01e0110013941c1507988984800000d0b08484540c40800310f404134013181d044c1c0250480e40d602901000c61400c02c2100b0030b0ba40c0c0b0081c000d00c0e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 167083974 1250 167082724 167082731
    0x70305060402040e070b0304110a05030114040210050f030c1e040b1306050a0c1506170f061f060c020607240506011d0405060d060219021902010906110a0b0106020102070303 76
    0x2c813150009441c4040e2007044040c60302c2c5031210f942d41d460a0030961841e6801c40e180b50400203065900303118103180b1481200c2003100c140b07080d01c1040351025036500b241d024488244949031032940d0440680e40c2c041200106260f075000700f0040d90a03008020ba0214040202c0090003003030255010000d071140200021300d5420194480100344c507980210000b48000810300650140800c108100c02c854520300780400080d0261182d040d6094202100c140e46241ea0205a441d07038141420040103512200c0700e03245444160400400c19100e9081c1d1244a04102070300450f50299a00c4a0843c3e179550741c4480e0308034452481e81e25074900c4001c0d4000c81c15010340351400003001e6500581e04040d0320780d035610440c8000c2c91824104402031401602d81d58101d07070341410035000036050384000c141038600c401c0c0003100004211002031402c0190601b01c0404c103500c03000c810040c1d0300035645030305a5106041c800c00040907140c07146c1c9010b040303d201600404007400001500340d011342c01400030300c0c0280c1c3c1c240f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 167085224 1250 167083974 167083991
    0x90f0311010501140609211914060601090e3303060714040b1c15080d050906070b0a0e100b0319050c0f062205010801150c030e0303090307030506040204 67
    0x742d408130100c06184e400020401c508800c40c03901040084c0032200460200f0f40c110603c4108601c2c0c0a452226051052000e001c58420b109801d4003000000052030014016440e028000804802181c4140c04103070207001d01107010000c0703000440f00d030414501401e085041140f507c1c0a126142410214000d0003602c021484080c42901450b2064185c0d080c500c0c5040d151580e58034956100d031203845003415100710340c030f100c03044640074003022050302c184500c003928109240a803c00031507012070030500400304072800c0c050310b54030103460700c05800c24034140315070ba20101c030701d07029014102c0d84510500400005084801140e404030022610940840f454000c00e0200c1114904000302d010b0501c0e400400800824500350040d4003a6060140640341802c03012820120198218200307405d201e4081c060a203c5035a20040b070500521a461074402400c4070007001824841100f803001c1c0c10000300d11601070280d10100101c41d041c880241c212010319949041c85500c0e01d01c103072012407049050603010b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 167086330 1106 167085224 167085239
    0xe0a020307020c01020f07090b2b03020106090e0606150405220b0103090b0412050f07050705090703092d0c08010504060b01020706020304030204050a090f0311010501 73
    0x56141e04003550060b05210500080c04d0455004096186140d0790000b000c0c0212910450006020032441c4041912900f5841941066010180d14107888840c012050512103000750300030822103443e441100c06892050481c2031140d0b020b080404e8240c600303040b482d0140d600c240e00091a0556a80100c1c1c080c400300c00c00030f841c501d805a0005c0108010340160142128246004c005100350790741e0741444a0b00241000c4c0404540c6002107451500510803604a601c42e552643d44481032807504030350b603c2c06400380500440c42c0c038004c01d0210380607010341d007065580842c42c0d600c1c401040311510850081201c0c4040305d14110315400000c50111b00c3c9480c0a010110004107072480d207402d1a4003a604403510307240c11580000010000c6950100c290b4060302d0b4110b40100c0e140e2602c0c810a409807940100c060803a44400041001305504940c549080d4468540284000c0c1e994640 = true := by decide +kernel

theorem cover : BRFrame.Cov 166906474 167086330 := by
  have h0 := BRFrame.cov_init 166906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 166906474 ≤ n) (h2 : n < 167086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
