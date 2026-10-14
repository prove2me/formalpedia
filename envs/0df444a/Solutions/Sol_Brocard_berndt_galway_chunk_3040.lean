-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:54.920814+00:00
-- url     : https://prove2.me/submissions/07a0d694-56be-4a29-964f-f0f18b375bc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 546582733 ≤ n < 546762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 546583983 1250 546582733 546582739
    0x71208030a15050919201903050105010525050d120b01090f0608071413030209011e050915030304090b0102060601021f0f06030819020609010b030a030c02031f0b0f 72
    0x5404114540d544081380e0b0300104070750700c2080011655901c51000b00b5940c1c4442083c600c1040300020202142c5001c1c15880c4e01119407842107640500c403c80803038600340103480c04261300340320210301248030702c03400f4107014151601950b68080c0ba03101c8503d0444d001c11903d0010310603100314041c94a40e4007494822078000e0801001e10340c1480720072050510617018a43c200704003400007450092180710031030055111110081d690308100e52111090144c540001d074041c40c0e824000061010706507030218000d4440c01c0c01030700c0290504d81004020342e805000d6454860b904442000c0959062004000906400400080301a1000000b9080180c01081d260564000243c2000b010342c00d58400c2c4882e00c031800e000198200854188001007500e03800181c40c8903404100301020005050720b13000c0e40d000c59002c070380c01c3d0340d100b40096084c0c07a50350202e41e0300358200040403000240030350030b400c035561700c003e05403208240da03186040c05144000704001c105503190010305040341003100c0c901d09142801c1d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 546585233 1250 546583983 546584021
    0x70906050f01030e1c050406230301140a09020a0206040209011401120b1201090c0504110f0414150c010b1003060f05060a1116060e1f08040302071208030a 68
    0x100001c018092041c00a070605480b00c58071060700b075050008000b4111541030190340a50840c00050440d000360042002040441458001032302082c0a05001c207511040040d01d56801c140c9040120401c035000d0b0b6410401c01800030600841c40c2c00503089220081d40104042d180c2401040008101a4058456050048001c0f202a40c2c071040394206000407540208094202d90007040c0c4040200780811440d52802c0c0d103840030069551044001c54804840a21188018054020301362007a04a01429414100030800840016458940005c10002c2080e40c1c51a100d180f4000e10b03500122442400384d545d641480f4203450005c44404840f070304c514042150a0034443c1140b400c28180c01414440d0801143d20044540b00700320750310f00181c106041e07610b00385641c403010100040328010341000c2085021060030034102440e4034914a04510f80c1c041990031542d9041e100007102410a82c1140a45000480c80d243c1d00710142080501c500e40050fa01d10b41b8800c00c20031140e001e00d00b012030b0f15503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 546586483 1250 546585233 546585239
    0x2030402010c0b090708030409140603010e0312060f040f020a0201050708090c0409021215010f23100c050d0507023607270311121b0303070c08030903070906 69
    0x40542e4084541d94070000c80d070150345605a21910b01503045e44009400c2c4400100070030004442e400101540644042604442d148d0000301800d07100d4075002220b80760b2051103075401035020600d4180d00180080d185da114000c8110100c1c040c0e03000807201645207500000d00d40714080e4240b042c294415410700d0405820b041c103501207501c801e8210702c454807441d21281c500081d5603450703031b00320300c0740c420007088031420550400c0c0d01a44a200340f00b040009000d004001403124200500c41003402c6d00405516140100c10040080030801c1107269410403421503a0100001d104204008220180b80c0301c09403507030810710401441341c03002d105800b41c8800c11070a030f40b0610351400800c491000000400c14090b0b0341c52408482165030000c070b0308405101d11440c0042c5641d00c003244010b0324010000b24205428503801e000c42c54015020040345a8028444227000c44000000c0d42102c99009090700c0c50030690b900c0d49105912aa0404040c0b9000000c511080f4a02080341700018a5068020b009841c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 546587733 1250 546586483 546586487
    0x15250c03151e020d020d020a0e01140702030d030e0115030c1e0b030723030a0c080a090b071d040e010605040b090411100e270106021216020f09130204050106030203040201 75
    0x1c51070b10701001494001c6003c515403481c9805036289080031400454580070070b9000203010050548005000c5916007440d6000259076070104c410090f0090001e000842818908a0080941c0c2080d8a40e555070303950f0111600e40240c06e400f00460143c11101e480508149806c208100d0851060707050044186042010071098001c0ea0b5200302c2e40e0904144010007810803090348001808d0035002d03c84000200600060a43e01c810480000741d5100b4800d40d483c45020003c540c50724802a1081082c44002684203100c3d90341c001c603001030505400007110b20308010409071121161501e40a944403a401d00c0141030601c1000c10700700c8112803400700e80c24030751a1000507002101c415402501601103115030315000b090325943c0e080300071b0705950708458803980f81c0b082001c00c0b0055030040c968202c00004c0c0e0f58400145440d00da41d404071990701d000408640083c00e5401c08008a0b0130100003030f030186141d07541c1c5104900c1815940c1c0c0f040424007183c810030044034816000314050620500601026036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 546588983 1250 546587733 546587771
    0xf2a05010207031103070302060c0d3e07090204060207150c030f030c09030f050604150b0a06180e09030d0606180b0d090c09091a0615250c0315 63
    0xaa042090030701d405203044d012900300704850308040e400c0b10001989101c05600040c8402c10200144e07112990140745204080103540c412141c060108440320f4171403004031741d00594406c3c0d282004115059a0741e10300c1140280c2c0c019602200260304090b00030030940c44c0154a0265002c03a600d40700e190000c107a6406811041d15078044802c060342c428444034450b001c2d02d10340001e150440c01d1413a0b0707200c0510340996101c40854040301c00510304494401c0c108014004c000c910704000345142c10035030808000b1115044140d16140904600c035170700046102c8902c210901031700c850f501956480c0840c640060907641980c0c066020008402e82c0a520007061400280958202d0035049541c0c00d42c141c000c1700a00103c80001e012030790000c000003443d0740c0c00d500c160b084c0e41c810000c01c1110751541c00c81c060402d00480308960808481740d5010340c00c1c41c4642c000c1a804a800194034440c102a00c101c800401301000d0494018646043c244240140701c0f550410301ca11039001403090403d00f41c5014050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 546590233 1250 546588983 546588989
    0x303040608071b150f18020a0b0d0b0a15020f0f0d0c050f06090615061206100c0507060203030106120216060b060405031005100806090a0209130f2a05010207 69
    0xc0d600754403855507416000f52800a900b08200716070080c0c012454900401054101220951078113001d0240312111840964009400402402c580c1c2d00d07040c81e030750a990040b01207501165913004007607039a5440c3d914040c040e043e454840501440030503c064540a80301034070400b04e43c08600300d562851400103124843c40c24502c0d0104442400e0710300503103040b040200000343c80c0039140422825120000709035219903d41e2046148000034001844010300c00c9002c0b02080d4610000020500d04010074102114110b9103003900d22030030341e03445050820500e508000011b1308000010009c40c0d901900400e0821042001146080d030520300b00404d010b00814010040e13921115809000d41e14001a54020040902501c07000a9910740e094000e081c00c40d41034110750001d0f000443c80080c0010454458100c1d03000038003440d441030b02000061200104004450b4010180034000204010b41e110b0307110780700e001d43ea0700c603490404024004003402c0400c030252650078502002207a034002010421 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 546591483 1250 546590233 546590237
    0x605010527120a0302010b1005090102061f0f080312060a14090a020c031201170106150e0d0804090203090d36081f0c0813080d06081006060e030304060807 68
    0x22810010340401c005610501c0398009a006003200c0f036041c560103401ca000c042408417008c800e40c6000070b6068496000d42e420890040e4012000a041d0f400c0c0c030a05242900000b090042440d0758810300101d8035038040d0004800c41c2c001088482604002c01c074840d800c040b0803124020340f02e0078072109030362440112200900c034481da40041005900564101e80d00c1c03040b0354017507964401002e5080100420284201507030b034035000d60400038074101807103402d013602e0680c5050b1954040d54602240e1002000743d04981c4021088400d00005d10752800400090940000150b1a80ba00700c01c4641803200c88160f00c414440c9500d2141c03107900454001801e100041501394007031124108005c400302040360030001d0103100c0e00e00d08803c0300d00e11f401403403e60310049005000316030803c0703004c0307030107013402d959072481440c042c2c10038400141024003800d004c1c5528500010311564900720175140c081d14420178030556a4402061120592001c0326200c200800e03001036240c245080343c000c144050041c14402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 546592733 1250 546591483 546591547
    0x7171207081911240f04050c0d1509062f0301090e030d0603080714010e0709021c0c050c011505090a0903020a0503070326090706051c06080102070606050105 69
    0x80c40340100300d5504180142c01c04c95900190f4207200e00c6111a220340000c10742144140003c0b00c0191443c0c58610859105014020690401c000e04c00c2100c0480c404452112040401040070700e207900c242d4450324050140071450204140d5140604016501c10f054100d001000c002c0035881d19400300c81c115201e9060000325200c04261650031402194070310241c40d42089800814032503001c01510036079000e030302075152007624605558229100f4545048054000c4902007191188680c054240ea10654000032102202604804201c409440c8950b000c540702042039605001c3c00d208910300c1040003a0010202d82c101000504d010000800a0700d4094503032400301d041510034071591a0140d8001c044984030b56140c42c0182c1083e40300030161000e1039001074400320540b6a40941401a4001c10113000000d00f00401114541d20400c0c1d5104417107407584200201c203c50740724800c0100084000180c40d11241d10b8644242c451f140d00541c1008410700800110310702c1d030301540011400c007400f098 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 546593983 1250 546592733 546592777
    0xe0c030616140c21120403081321030b010c02010c1506080607080403020d0309030e100203090307090b090106090e1513020708090a050a0f03030810080717120708 71
    0xd903960711202410700c509101107160b10600400007a44d082c1143e81c001143c1416040ba4150700d0180650004411030720105800b0402090085215603003000c4015021104030b14145c82c3c1c2310030b01040005002804c0744204905111592502c20a402030009103401e0840c1c48441c2c0000b80012b28040003e048021185002d1442104950000000b0078904c41940c40070f16080902600e40c4000b26000c0d400340c0110005500034074440c4c840d0030203582e410380300d04030384940d103200344410211203121034000c0d40700400c9840da180d903040100c10024144003001040680030001071189000069000005010401703070b0a020a94000202c254807000603810035030601c0514001078048900360390005c0403284002400400d01c14000000d01c0c1e04141500c4a05049650344180100b081780b40c460444c12f900c25010a10000c1e1041e002250400e165280c08502d10391108455800c050240d0321284607008103112881911350f0601c070a00308455020849400e0080c50307250071040c1d21414250110441d41d840d040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 546595233 1250 546593983 546593987
    0x20102030c1b0717060f0f0f01150e0411210c0901050a0504030210082a09010c0201020a08030a0219030902030c010e06070c090c020111190804032106090e0c030616 72
    0xc000810700b500e220a4a050440e40180d00c8940c1500c039040301340346c400d00080019214020341e42c0105041070585000e13a07e400c2203884c4d440e011070813040800048106440c10b07662680a0301daa6440c241000c103543d12040c1e2094030130204040307501a400d0346608200000c43e28030384284d4190a000707003800343c0e0701d03010390700708a41c02d1040b904001d60150054100405040d8410240b500c00d003405416070b529810170604101948141901c080143c4004011400895201d041113400305881801100d240d01034030b5441900d1a04110f0b0a54022903005c80c050526204908040e200000300341020000b04d506030300401e4480c01c905081c0c42c1481740224a0b030406803501c0003102c03d00e0340c11500c007000030360315500c0f14006040009402e200540c246a804110101c5210807181d16100b014a410240d0303006038001e0f6103511001b8816024084400214421001107001c140503c0c115030800140203070400302440112a522821400241d118030030a040a890020303556403c850180124116030000c1c03042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 546596483 1250 546595233 546595243
    0xb0d08040611060609070c030c33020c0606010e1c060f241a1918090204050d0b070318030e09070c020d060b1201060603020405031011030114030c101806020102030c1b 73
    0x4180380415a100d007400c1400104002510b401c03401c003107003201ca0f1132b0b03c0a801d03402110450b003c40d0300b02a020a1566000b035440503020701c00540607a4445942490070b441d008000c0c0b600b03407012030721944810151400d030720903c01c01103d040d038a80d07010741020098148144140c010f01d1000381c020307061b814040030b160040c0c544200c80528038150718403400f20000e221401a0820700081c0031408408180380541d03000b5101520303806421103903203240503220920540c0700a0401018180d407a68003040510b0510703102d441c124001c0e269055030000032424040b030018028154004c0060b10340c0e0b408011ba07100202100303d942c0194001c52500302c041c00080002e41c3c220b0000c0341a43ca46140022400d8050f005002202c104a041c0ea46042460118030f054038000350540c0102da07010401405019507800302d04810361009000c0711a060890004500d4480c00000044081070b0717049281c00d540e443e041004c1019005070708c025402c6081000c200b030302c01c0c09803a100300c1c80300c111411215520441000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 546597733 1250 546596483 546596507
    0xe030417070b0d0b031e030a090f0b09010c150513050c010201050705030f090106050324090d021c0504090603060b0906040c2c1809061609031101030b0d08040611060609070c03 77
    0x200030041c034021100b580d603a5408280d96401007114000d001892b10b0019203400708036140d00c4000c9103046051070046a0041c0302c41411100c03410840d040514080051142038030650554601c04000c07407081c10200c0c80e0100c412000c1d411a03040c1020001030319401020382c1e4104000241c1d180c0307251100305400e805004640c20444e0144a071290320390010b10541c5240a213031280d442c2803410780e01d840304001d40f91000d0505503c0540c1c001651080c0014070781c190468840442d00e40241001d4440d15020103445c015402500d80f26150401313501c071850800b2a03981c0140d0100c0b0108101f04140d000581120220325449450f074401c4490ba26180c0c11030300902c00a004000c1c120f0100250b00c0600f01e8080c83d0507603501e04181304100004040c0c03075000d4440f48440300c2d191140100a4503560342c149041040729104c1781003507280d2842032402e407501c0706609401303031142410740d440e0360034004010b00e00103c5031000702e080d500c02000d03c0f601c1d4644019454200205280030180c40d0210304050351104c40c404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 546598983 1250 546597733 546597763
    0x10e01050c0a09080703020d0308100b21160e1041030108070e101706010312091202040b120312042303090f010908010e030417070b0d0b03 61
    0x20040c0007601c0307400400e1500007075141e04010b01c2d100da2041c0d13990b045070300009403c80325540c074242c0403e00403404194000e41426202006d1074036154214002e8116001103200800506051040e404500d01040c0d8080d55440d052070003468007010082524001d000c409001e0304003056046c4116118100115502c00c806030810030890340c006007c3c21b4040b5100300482d0000b0780000c0404131020002c1140d0481d05040c004003061410a46000e00b90318000d49103000d9411000c2c1c00247e00d18030510075100706078110000c0e1100390f140d414080c1904020015020400c0070881c003c1c03000000d6070300031007001501600c0009141c01070401241d511440c2044406551101150383c01918540d11402d91003a40b1500c000c50310b2000320036141507030381c0c80c890340000180c1091060300c034541480544036000600c14507101180c69070f1a0807207801c50311111000c0c5065000000c080c801000390b409000302801e102c074010a25146003182d005001e0240764048080c19469410150781d5075010403250800001a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 546600233 1250 546598983 546598991
    0x1707020d030e01150e040b0105030309060a1101180305130501081e04111503150117040209040c050a0b0a020613050705010f170a02250b060d06060f140a1a0a08040203010e01 76
    0xc5c1000c06088541103504030f898900b00b6001042c241008020354070000800341000b42017000b44001952640808545038200d903585105140001c0049000034210703034040d49455598010581a500001e103480d0441418002040c0c144101040c0c190780302245039071540c600d800c16407502c0c039000d602c072000d8100f40c0b540304040f02d41070b021001082c402580071300b005980c0d40051280d0600151600b0032403d4082c840c2140520010700542000618140c3c400e101e81102242c2d161210f0005482081ca0b400100d066440801c1c074205907030b010032900d82c020034202d020203c100c1595903440c0d0303640d400e800b505040014442243d0304150107802c2c11106413201d502c0b01741c1d49203050b0305007a0080d044007880c0c0e9111084d01880191094040c3c84034000c1c0360b00038220301c0d916039420041c030003202083c070303c201c90365580ca41c0001800074104100380068103545c00480106020b42d410440301314001c1d00000540718200c840e0020414001040f58030050880c103185501e5501c6000190050a00c00c1c00701e8019424 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 546601483 1250 546600233 546600239
    0x161a040b0a020c0708160f0e040f020418050f0102090103060e0603060403050a090b07030518011e0516080415170f01180b0d0c030b0c090105070822060504061707020d030e0115 77
    0x1180c2c1e101c0c01a50250205848101c0c0e503002c00c240c07000b0055274003810340c0c0c2080100350054106504950003041545445d03244058817592050700d00140845480443d035400719540b0f07080d603454065540104800949280c260a00c0b00009880b640040d20050910100103000c80c0c540d401207450000800a0b040b00c0c076142c103464140074220342d0101b0b5801c98a480a034030780080c1c0358018144414094281c031031800161082410a13580703a404104025003840f0900a080006a880001003001c3c000b14080000c208500800240c9403a10394990f003038200000400b04500c240010200038110750005d105a501c0c104481030000007482104001908100c41c2c1c5100e40034070031268071301c0c0d00b22171007a60000c281d40d4900852403050f00498540710300294003003003014082100f4402410007100104d00c5031409810f04200045054038652180010403404941080120f0b08403801c0310403900c0d507020311030040ca41505d00030b4540402100c00002e1640d900003103e43e168095000340782c10154220720100f1151 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 546602733 1250 546601483 546601513
    0x7050f03100c140a0842010203040504020c0717011b08070c0210110c01020c0f1306080a2303120c03070c0503030129090906010c050a0503161a040b0a020c0708 70
    0x1180d101b0707030742007890b13109025450303581003a00c10411b41100e1342686422264041c40241015082c2c007130452109100114003540d039440205100d036000402000d03802d00d00803c3c82002240001060120b900d0222030360101c80c134081141125a2003403401e8003c99032231100903210401c2c0c0303060203900f00c508412041300300c13074001a03021400f02400f021141c01803218001260b0ba0b60003501c0701074004d0348480607013045080c142e9920264140d08100071030441d448164852402d41c58540a54803101c40007950b40411020f1061719400380000809075140051500c04a610410f000d0184180c5407000000960414495a001801031390f22000350b940c5ca50b5103c0b20b0301401140303c040c80340505030000c2c181c1003a03000301d0b044542182e0098440d0300190780d1480103640311100284282c80b54002c8800d51800901d080c00241604501300201e2207442080741040061004010b200300c0594120354180710214015401030369002132204409651228113200075410000240e00c0701056108140007240051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 546603983 1250 546602733 546602747
    0x160819030f14101701111204151104050906030109050d02070f0602010624170c1b01090b06090a0216050709110412060b0105040305030a1107050f03100c140a 69
    0x10a003a003400701c0c100240b85405144015604408040114501000b06540640340c948298081c000006960382148650b408141d010206a20300c104094080204003c2d80d8450111442d1a04c2d508000844044080400b903109900401e880741c2030740000940b05075000d4110100165020094422203040040701a550712181d0040d4a00c00d5298000401c00d50700c1481400c00315541c2d1540f000b0200d011000402c8880c2c0c00c40c901c40c0400044450701e5148042c10100f8601503403c003e406079440d201d82e03034070940c082000c5182780010b0341008403002c04108440543c45c0c0102c4101c1d1400004d407641680072000303200312491401000d9004143d40300f44640030902d042119424001406000e03a0120344a01c01d124900691200080c00b040c041d02280841c3c0c41560900c006050803450151a170701c0702403560301314100030070010b640c03d584100c0c0d06c04140080402032005071402c4c10404e081c0b00002c2d80b00c00c00c0008246c500c44d5503507200c001441c8151501e144d440302d507054483d507a440c80c0300c0084c646 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 546605233 1250 546603983 546604001
    0xb0109050105060903190201230c07050604030f03080c1e1c050907060c02061b010b040c0e010507060b0415121e0201050306040207110301020f090108060d02010516081903 75
    0x14a00030002502e81030020071100310410007409040000d0445507003441818004200760304100769000c4080d02e10302d01d6038903c0c4090903800000d40d21845013004491a080464002d1401083c09110030400620b03461901071945505081c0707000a1396800ba0303611118060a00d50f4420700d020000003903481842500200400e0070031030250003240200e151414141d406c280c0b0807111b642c1c4041c00800c240b51090305101c0406100070041c2d40303880144c80b1060503041c2c03001c44044180e517613002503081c1c40c9060301c100030701c0b0055810b0201c40308181100280140c000c41d00041c1040e5154111018181d44661102c014134142e0045400042e44400044c0d2151807000d170101c07202508252841000ca105a1070707650320f20743c141e4032240f8560351601480080d42151100325209081003943c60700641c2e0a00141008030701c400340311600c4024402c001005030b040585200d00440401c8042d00160343d110f0101c544070560041c0c03210000e411440e08030b4080c401c400703001c4803001d82d8682643d001645600a1910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 546606483 1250 546605233 546605249
    0x5090409120302090f15040e0901020c01020403061b031e09060e01020a0206100b04150e0f03070e060a0e0c0919090c0306030c0605030720160815130327030f0b01 71
    0x1504003500301b030000405400c4102d00340180240b104124285081c1c9000c0c1d070058034500013600308159008020b003680c000d508200c1d5002c0c1c441c0d12540740f84002ca002100085110f180034000c001814544031030b0100e00511101c03425403581c05110500030320760820b0658502e4400215500c030b0300d03400b00a440d02e8081d10501000d0b021800001b621490450585d02518810703200082410902c031001c2d1b890307081d0828001d410800300e501100156406000c004000c100b2070040c42c140c1d00c0c0034030810101002c03540041034070f542e40d2000d12803007005030002c0c1c1380020401d5401c044000300706218442c0c10b811075401121624140303007102d2040c3d5803641082d021280300d1041c0c2d00c1c43d16103450040e40c65010849100d000180901074880360340e0060000107540f5074480381030300c3c107101c039843d26440381c41c080e81c009054541c004000742e142034000c0c105071603011220480c8989000500d941c010460140700f50410381c480001c00c0f03d44613107074200480d031000b1940305055081d4a140343c40c2040312080c003441442c0c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 546607733 1250 546606483 546606499
    0x2d080601020a05033004060603120c05060f0705070506010f1d01062f0304030b0915010b071407051f1713020603040606030f0804030c060903120509040912030209 71
    0xa500014410410b640e00038091801c2c074403c0c41400180c1111850607041e0451442c980c0b07074211107a04e01c3d56005a010300004070340ea0b411800c005200c2140490284104481000c01d0382c0810004035526410886c0c0762220300080d29000d900b1152401014000707099401120000580d450368040c0c40e004594940b420a183d51058480254910030f00b48600400324050203826011310003c44084004c094041007500601000240b100c1e1960b0425081201c40e12450000c0c0310b92044104603800049200c22960314003581440080c4000e801803401c020608040710180039100e040231300c105d002520000d41040041c0018045403103040ba110b0045802140750420741d201d5082448804a100f50380410004c02040710907800c2c4501d683c0000c200307440060f0384002c08800070f0040c514040141f4000e810302a11142141002c000b04501c40c0d10520038020504010400a0b0b9509514903a03941f403400e255850b42c92400210f4045c002440004022203580d50b402d018058040d030140035004c0059074804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 546608983 1250 546607733 546607741
    0x1701050108010b030a020c07180213050a030c03080705151003120e0604150309060513051504210c0b18120c030d0902030304031e0605060103150e072d08 67
    0x24030404003e001d8109128020000125403225030b40052000b03131200400c54107050354038035085c6e44000101049004483c0c00180c04040156241e414501034a400c0b507515110500d59500c84002d00380c3c0d4800200070b003902145881c240201840840040325030001c4143c0c040c0b400c40b00702a080003050208882c0c12901e91091100c4074880c07003c0d001031070805000c251510381000358030940306444205410800d5200c120341c100292181c0505030044c0801044240580d41e24604141407082c61442c0340359140c1800e0802020801000103200210107180c1c6040c0100b28050049641c0303070102d40007808082402007402203118582e94508400c82d03448007915481c0b610005090821b2045450858070341d4024448480c0e0481c507503101c0c81c0f000c0e04c0241100d00d4aa80c80d610700b0250a0180d01301030034422414400300521030103015041e88101c4c2464104004000c290580616041da070256103203083e1401c0002d040302e03005d020f0290001002749951800c200000d0b600210080c101d0341d4440019130210046 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 546610233 1250 546608983 546608987
    0x14010606030c0e0906092a040f06020d0507030305183406080a0c030b030609030405030610120f05011d1b030d05040306020f1608090406290304060b0603010617010501 73
    0x411030003d40100290000e4981008006400c17801501000c14500700e245484024122101d4514002c00c0010000d0749880c0740c214100d038030003d80c0e4051415904440c01d0020019841400c41c1d804d0341e414100041c06454403942d03040380072001c02110901d407240c981060411013000b40e11408407901c2100d8144940d10f0868560b07010461885132001041c0180b000c103001d03880703a8012034195611071a00241107415000003a181803020b86240c8003e0b00000703403d224a080034440d0540c01070320030003450b100034a003100c0c410030110075030b4002d081040041286010840300390040281400d00b0210351a41c0004803000c0ea40741c4080407041305d005200342c0c6410742c0c1e0303003400700705503c20700d4180d21914100761a545800e0040d60180300c00e00d1050030f04000b40361143c16907011a4403042c1c050414142c4a080c444280001c1b44c95941190030100d00742d17030110031140501400a40076112582e80c2e1078580e16945000c1006c2c100204d000340d40305d04080000302c1c504c2c0c0d0125480282d000c0c01c4802c0c031038a903030790801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 546611483 1250 546610233 546610247
    0x90c040b030c0f040509030c0118030906050a0e0d05010e03030106050c070e01030b06280f29090d110a03060b0108010905040c060806010203070203010f05060f01030b0f09060d14010606030c 83
    0x11080e00309030511002c02880c0780550001b40d002c0f9099099030318100c151742d601801c40c0c503800d40c8100820a8042d048090543c04a2072101901c89400c081f0300e049550000a410042c181510500c1186548000801c0180c03c1d000300442d0380390b0004a945a50312540040c1c00c035002030441d650140b18204000810b652018641070403650000815101d503111081806009030401084021080701149690302e1000b61400000c002c1c010015001082030034080c82e40850500c01118100c0c4000c02c02510088002c040205c030350f024412281200b095455142588418801c2c5050305c0c0d10030380051000052140c00c0d000030886070003d03610212103a072035800c40011184251009440c8203600203040c068203004940e01604540d0500442e42001e20341d40c0001d0079104844611050703d500c075070078800305080012001c00e161100f400c05000d1041342d40c022541d05240581c0852180685001107400d540350352882d074142c0c40d005110000300c0200801041e01920340d03840b940c1c001a03e0607508915951040310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 546612733 1250 546611483 546611503
    0x60a06051306030804092403030c0b01170c0108070905090109091202030a120c030e0f28030210050c04120503030403140f0702010f11030a0309110402040b04090f020909090c040b03 79
    0x405141854280f50031007008001002c7e0403541307401807000803440480000130382070045110380d9030034690020703a245c20030040310180e00c1408900300c02d42c6040c511500c007081d42031406c0428a03110f010b070359030002c003111400300325400144c00c40e0001c00003082020540c1c114000310303801a0704401d0703440b9003524209ea4900c1074002c240300280842c6000f1482d00b440c1d4001d21601c0b051481c01140b0f030031451200c3c03418040e4801c50b0702110307407000150480c0810204041c0c00c0c940071000860317114080585010351240501866080740b203542d80d0000301c1c1078103401c00b911b0140030410034001404c0031a151095490380b05071415804284c0b603040c43d01c400281442281d65004903840100e040090316030065030001a03803141c0b02c086c44142c0c2586801ca100410240600c86190750f80843c0c020100d04040300d03000e1002c1415400350340100700600402c8103a00c01c84040341c01459000841e401d510180c24020301582c201e040c1e00c42e5000c401c4c008040c50025420507415011501085409042d000301503071280c01d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 546613983 1250 546612733 546612743
    0x1c050f030a1209050114010b0c010f0e0d0e0a2417060105120405071703040f140d2a0b0307080a20130801020a0503090f0106050d0b0414060a0605130603 67
    0x21030b040b8900722603002910f00521400002c10300c42d01c3c0d00d01415441c0d50982003a11042404540c51180040074040c08030700741c0c110482049130400091509413a4000d10a0000c148481c076801e0702400c0d10b54112440040000d0080619000c50b522201d1b071000105141800c0040c5031160b0200b88030901010f450700400c81611018a070040081c241d001c590402002599103004180300041c980c1000040044022100b80146541e00e0410481e41c01202c0d1a0704030400104006650500307070380380e298040f109260464405c00005415650b4051f01c0c0222a054001c0403001000c000f0782c1d202c1401c0a940641110b4135149055500c0300b0604c02210000816003020f0035442900b0000c0d030740503030018204002058650360f0300f84e46440d08582603038031290404002070f50000030410780210611415120808000090002a10349800500315502001000c2e29191a840104080001e000c07920b9030541c61540981348140760204001006040d5846101d01800d0014551801c6802904c1400140d039445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 546615233 1250 546613983 546613997
    0xf070b15010203030f04050309090108070906060201140f13050d030c0f020d021c12020c0a0203011503120e130c020703020a09060317130512100b041e0b0a051c050f030a 74
    0xc1d4802884001d0f0003647da174081008022016143c000c1c08034040d042c10002007903c940360000740303030490b405a482072003164902854800107810060545403c81c40110100f070141e21104d82d04221482c8455000b006c9104200c208900305400d900040b2000146031180c501036002d50400b078ae110318403210300d40c005030007c82000040048030546041d90600a1030039800d06005520b0002c120fa00000c41070450381c1c030402400d4110b2809005800707400712070700d0207605141d03d983c0c0d0b00440c0102003582103080c4018540c02410b01c1d101e62605c0500d0031a1200148020200307031030040d444a425001c1640190880304010814411078080c2800b12903020580c21703107500441c41c0c006400e40191010120300c14044a00144566a08000e4070f8150501c0300a0a40c074000000100c00310b80400d44028000e60a01c1c031143e0301c1d01040b81010100500c40ea10100e0220388640020742404016008654040300180c80301715120b411311198404280314030304954010343e200703980da03581e8092f0b0001c010002c3d5032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 546616483 1250 546615233 546615241
    0x402010c020d031b052503020a06052104080c0106081b1c0c080607090f0b04030305090f0406090608120910300905011419110d020f070b1501020303 65
    0x3251002a0b0140c1c02480c00140030030036400e06034582801103005599030ba03c2007811010010703c07035107408001c0c20940300c100031080c555400705460140d684110400d000002c980f41c40b210680183d074000150030b0302211038245c0741625019099411250b0313a0942c640ca411004903000e0800240c010204c4d1002c0b4000c01101a00c40822400b0803600420000d03203088013000c180010400c2020a003d0000000076029610340700c4001050381c021035010004c40d4030718943c108200400542210141d0703815181c40b55540207510301088000c2d000c45001d58000380b40c20030004440c00560b00c540c042c0c030080c40564003065041e00310f01d009401800e1195902400d040d4100b01e1642c0642500510b60504403000d1a040701c1319155180b0750100c10350034101c8552644100b5081000c01c0c8159500401144075070b28503414600340050a80840c0b01c20f00c1c80699641d2944441401c0f04026503002986001c82903650703c0281c4401d07525a0003078842200c40030f6168008c03e04185141200b140810700c10780c010750842d51 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 546617733 1250 546616483 546616489
    0x5010f05060a0e030109030c020114040317030a02070c060206070912080306040b031014060f01021606050901030902040614150a080f0c0904140601021c0c02062b050912030402010c02 80
    0xc0148103030710600440d8070300c43d10142ca0030f0040c00d1070180642c440b07074a00007560002401c19001a001c460040204000610006e090490b01d4000610031070001c40d01c0c0e07912949160001e01ca0407601904800c81d01e070780010750a9000804605c9201245d40700b035402961403d0034801002100c00c003c6c0102014070000740c00307090940c4001e08940006040341d81420203044180e0032208100713141c440d11460002000020b0800b15194488190284003d1000380c00c000e000c0f4001028500412003005800290220076078425000305c01c0e6150003c00070000641d9070000a003280c0440c880c02ca0003051103a1001b0071841c2e4040640351640e5150312661170340c2e500d880c01c07603403030a03001844c0700c0e83d0200a002c4d6402c140c03124440e42e2205416400c0030307152400d100c400a481c00c80c2e00c00392401041d203100d860b0340802d58044d01950700c05906550307198480001e201590004a0009501010b0403403400001420840b0303900601d011388252011b0710000700b0560441102480110f9019010600e44451072005003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 546618983 1250 546617733 546617737
    0x906040c05011d062b02210906130221070f1e150c0803270c15091201020c100b060405010c02091f1517100312020118080a0e0405010f0506 61
    0x70208241c0d07175488140a244402c22555a0200075085940030808081e580f8010450014040b03240708402814980302d038496a4402c002051042e078601c5005000d011526a0950060400300c1010300701d1080810410b4195900e040344600014800407403000030b094085c04412801c3c05c0680082c0f9940b0b503040c031909840300c0f040d0b000c00608000380c0491107004a010003010b1f40c003907100d0004c041c016401e25400c00a002c14030171039401031500801c95120456482c081044403580129101d2501c416680f0f0020700000354021445220b5400020b20a0b10310030041010301c1c0c0407400e00b000300f1070320500d041402081e00580c001d150200ba05465034001500e440720209a00145105007440a5003150001b07214100b915440b01501200780040000e8080e040401c402a159a041c0c0201261410b0380c20580ea41c00709100182c6001d07107a841800700c0a20030b40100d001c00d10110349404440400c1d1400b0b079081c0d0310000e00040000c10948060005e840e00d4040c050499074001003400b642420001081555 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 546620233 1250 546618983 546618997
    0x90f1e1003020a0e04051618090602070f0303090c080312071d030106030804211707020d0506040516140f12010f0f0203010905060916180308030906040c05011d06 71
    0x120030240c80010069440250b0f010140102c4074080e0018246403400f0382c41c01c15202039620f042981020184180d10304051f0301d0114854800f000b284100311402c100300244907034000070780a002c24001c0e190602d038241d007003030604505c14880c00140e41c0d524048140c8a00030821841090b005001c040f5000c03601c20003900c6056010f0740204a5441c0d0040d00190071640168011508a000420200012083d40e202c01d000000c040c541e00c1014005a5100121035407660001505000f01203020425900d4012090340855800030455066040604005968107902146210b4240b00c84002050988a0071316140d0000005054110540b4089080240610a07281c4502c285e650303d62155803802c1203030094503402010007200503a654100350304501950401008540215170110500078182104030300200e00030010302d0080700c0900001ca200c41080743c41d600180480c41e001c424001700105c0401c4d02801648945003210840c0ea8400c0150b07159074180244900a42e004690040281130900c010061 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 546621483 1250 546620233 546620251
    0xf07080a0504170a0e040b100503011e171f06060c030e150d090512070b04080309100c02061005040506010509061e030705040f05010302090d12140315090f1e 69
    0x10107000203080d40c0190810010200005c4100603002014101881508207820050318480b030510004180600b40e4401807003074064801501019401c8124143c296a0186c000c4442150002d8503001020b951360780707140806070b548181027028a9400945200307550403100320b91200a010b8240ea1801d0300c0d0800031040d402c0d0082525000c04100390071a070028600d00f404c1c20300000d1012000c1c24034500e802200c0030588501c040400004010641c802c005562180d4402c0f8215070340c0d0b507140c10150070000445207103a0646c0c20000403440035500403903924496000710b54290f08282e501d0003040300740ca1050f51700c603010070800c010003400d41c00c085000704040b2025083d1074000d220b013010544540e6008680303150001303070040790a01c074540b035040b0784000620302440d040d41441c00340c200144040e02c44030002030980c4803850035214803d0141d001c00c50701d00c5416003400e032280703458010350401103803505006108464600c0001d0104294102c024001c1e10303800c0361140d031008154010202d0300c5014245030340c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 546622733 1250 546621483 546621503
    0xe0109260a1b030b0a0228030b09010b0909150a0b0c010b030d0e030d03020c0706030e1005070302180307030515041a1303200a060209012607080f07080a0504 69
    0x101003000c405940618200c4820b0040300c82d0b1030343c20b01541200e0043c10503079907280104815850282d5200a48030386200300030040d03030350701c020f01801d6005040001d4490b801c00f00280c0001415500d00015041e03100e402d03904000300781d8600c4044920050f99040e4698030940103032003030007609600b44c06009c012503000000076540358a48002443c0a0701c920b1030380300090010b602111a0f080500c108111421207080560500014015903600c0315505c2c019002010350302c0200c8030201c041007203510340707070041080c00b0031150030714000060196000c0301a44d1030007502115400080e0400140c0401125004400752070800da40e40d064004901d000b030819910f080c08540c00c0ea035401c15901c10710303002c0e0307101d0074581013422028503010701069841012242800740048442c0a00c0c0404100705207010782c41320f0700503030710420340b001a02c01c2ea070601c1e0204c0816852101c1407161481d6200704c00c0c000c07410303034960311199983c0d81c0814801110440c0c2d61390015000e00d001c201c6880c91504150703000351103010400c2c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 546623983 1250 546622733 546622753
    0x50d02040305120d1103010e041b0e090c01090f05030a110d08040626060102060f0901110a200a021f020a0f0b0703060b19050c010e010e0d0e010926 65
    0x1031030641401443c0c180340200060341c101c0c0c0c1000e480780c4c100c1000d905900078119858042d1980c14101d00400203400004403050340d81c0683d000d000c03003801904200880003ca41070190005580b4449010b5050100300ca460740410000d082032700759002c640c40103005012044c02941c80c03101d000340302a40c031504540d074602d003d400900887c0151014080d941c0d21b9440960800e0510420f51404059041c4001440e01c284a12a40c1c040740c03443d4070914900d400007154070b80711481030041c01042d000c2240d840c1d000c64096035103031380090240c1c00c45151031403803040c0382240b00c071082e29211030707620017075010341d4030b1601040300761007006681d5004c1031a00640300c042503152610070400710440411190444c40c2d80c2000102c84d0540b1030000648445d4102a0810070360b20201c4034041039100c0c0ea481888000325180d0001c0009400026280b4040c0000f0f002030400c403200c095980120150400202c0c00091200702c3d20351042c20803801701d03003030903010204100d080141d46800c0c10a01e8056445030150295031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 546625233 1250 546623983 546623993
    0x70b090402190513090c09030201030b0a0f140108090f0a1b0f060c0519050303070c06061a0c0712030203040302040c03150f050a060806031e031201030b0109060b070c06050d020403 79
    0x4249148041c0d12007980d215101c00d081a1364002035001000104d242c045041040c40d03000c0c808034250ba5080c24005800240c0400042c0d41e07072400d902000702c000c8182c00104014070408046c1c0c14540c420389070402d140c1c8520b410503407601100c80034800035a005924003008a01e0070020207400e40c01c48000b803100c50392107410040b420b00305900f02c400412021405001040703810000c024000070a11110480101d1070760340c0a0b124400500b0840c20051181c100c01c040c0f0006502c0703440288095030030019040700d242045030490b0414400c4e03144a004145c400614044486025000c199059020350b140070704660822000b85040040ea00c00c0683c0c0b0790141a00980000b903002c042c1c0f00a0750501e407900d14120400852500325002202005040001d00095031400250044c5415203010030f900c082c02e10300011851070145d480380c040345484600001091000144c11a0b050710280d400c1844120707151120349010b27202e004001002188101030802c14144982c0c054201d03119040409461301d6540c0c0c4076 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 546626483 1250 546625233 546625267
    0x40b04022e0503160216060e03010e030304060504050f160513020d02031e0106020d09090504080f1b1c172802090906010809120d110316020f03030108070b090402 71
    0x1d580200b40d00005100d44820a1500300008102070b1004061100800964001555103485036005100c400380004900361303820741040302021044021207840b03140c54100100503000070385043d1041d00455001d5030301503002040300b1001d0844140d00415552903c0e083c000c0c100921105e080301c103a4284024500d400c1240001c2d070181e110081d03103401407202400800c000401c1070b03201005650000c00d269400a81044060046030715071070b000916584c035800c10701e8242c85000301d02444100001051390010403405120358004603d0021200960f11008014215a00c980590008074400920030640344540f5244da6501152400d4000385207141c2c40742000580c0d40c40c0b5424210070303401190304811414010f0342140e00c664240b816000038241440313000d4480d060a00060904440044d10805e080500e8005c201d16244079900c0c19541d01d081c5500c03800f800f40000000c00180280c881c83d13544401c0c00401d41e410b94442c2c4019050721071502000038a1640001d5401c0d0300a5006e1040c00221810960307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 546627733 1250 546626483 546626569
    0xa030c08060f0f090712020a0e0c0d0f051e04050c10031d06060d0227101809050d0c030c0c15081b0a0c030309060908091503040b0402 59
    0x424141c00c0c0342e8002c6a46420040032100c4129562041007144000018864100c1310340855140e0110428004208041e6040d005070f2020040c1400b03020f91051114002c003040b01d40d80500700b01c03602558090070300760344050303622211591100d1090094000c41c2c0c0445a0020312810031100c0038881031020510b0b00e030f0001206800301b560307138028041c00490030003500c481c0c2da00d030009803d00e8500381001400007940c2060180c001e9044601822103103c8210f92011380160000851400f40762880584245080740e018545d500d4980403800e481104070b50003a090110703440300140c11b04200c0030f07101701c841845180054041203100c01e8401c01180345900c9150281050090f805e000030404200a0300d01d21010300000b00b1080c1c1d0510802c17101d43c0a1045e168440202e10344010815098203040f80a4000d004001d08102d00d040401c004006940f8010b0528007000d640c0601c081c4c555842c3e5180c10302007220080e180c02c81c0c0000280040c5404981034a00101030300381c400c130507540c1e20082007074450f00c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 546628983 1250 546627733 546627749
    0x80c1903080601180312230c0109060609021812010f110409050f0907140f03011509050c1e0c031210061407030f08190c0c021c020612060a030c 63
    0xa000403540d0205075080d1095030002ca4000440c6140d850040d50718a0800410400410a43c4100d40561f045103003407071900304000c8140c0314041d954602e40245941c0100700c130b0503840c00e075000803024100d0098400050100c0503a004841010041c00f0a01e221300b400c0d2040b075585c54640325141100b030310501011803000301416442d103080007003100459002600751040b48898104000703c00710000f44081c03c0d41d444080a44840c4c5440e00400d10340559076030855070650030005002c035028034200111007102e503070a0043c006902c2d400c81c0070300513116a50414846080030a005801840f501c8010200c8125000440b842d042541d460405000780980b480d55242c5418601000103aa10041406c03610441c2c1d040b403481c2c01d0b07042d070740901030400481d043d40c28050b90301e00140465074a185805150f500052080c001d901c10058004e10000d9000c80c00c074410402d0b980c0080030180303406600c4801e00d50240000340f80240d0b01026101142c8014030b010340c003000d038080100010780400c2d5520b0041c01c0305 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 546630233 1250 546628983 546628997
    0x140106230c07230d02060d090221010905060601110304060315050d0503040303030b2205090f030a090609090b010206271605030c0306072003040f15110105040f080c1903 74
    0x95001d03100090f40302c800d05445100c81c1d090910141e030f1150102c2c0e9030f1001001000aa0f544144046011001d1181003400c941c000b50380611000e40c2c3c10f401c1904024420020f5850a90b9000700544542c4109044498164001c0c04103100c602c3c0030f0f5120034100c045040403c0d00703056458000418080701c05500311b405410200301002095014010340340700704000c90b0b01c1007101e1010903c11141030503e040d4542d08617141c2000c42c00140c4103104080f009070350740d025a952020500000b401c0e4004502c80c0381d00080044500092010b0301d4071a83d0301003401607000e440b258450002121035201205070400060410300032990160001700025903003008200c1c0b4803100981740400301030410354146510341c00707500514104804240e00aa481411003100700c1001070044060980d03910b0360003190010062804041c40c041908042c10705003114032100c0d65100141901e60020f242e09854007590000d18044c245410000054a401c02600d450b1700307407500311905c000c2c1c42403811840c0140040103a01103044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 546631483 1250 546630233 546630269
    0xc06070f0807080c090906060c010c030b0a0e06030307121e0f081305070501082814060a0303170415020304030807030612030801150302070506040506010801140106230c07 75
    0xa251036000c00b007402c2492540c54080c544a20b24401e0701c1c180381c402d400942c0002c069640b0803080e1180400c0c00c0b8000c200701e04050780050007c008024509200724411500003d101c194240f0b0b142c424400075011310306103151b5542c0c0070b082e207691031012014040c404924a048018103581c0391100381d00ea949004c808903040501402c4040041d142250a6002640c0d00011400025a40045540c203107444081607842c0406e010440706090003484170034540842490300c4002c0da8000c0d0070525110303070b8000510f840b00b00422201c0240c62100401250300c282540c640e6100410103240d00a000d0b10300c03001d00c800e07858001c50483c0e00444086000c41c000d6014824529452303c1407401170000c2e03c0152429039015100585003140510a012440c910110034980d001c1c401c0c1c0560f03802c00d07400421a2400c0c01c003854015100c440c24060780c07c5543c64540e01700088000740e48454100c0d02070383c8076044003045c011150903003000d44541408004100b040100207043e8100201d400a080003444946c0c8052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 546632733 1250 546631483 546631487
    0x1f0801030314070503090d11060c03071106070f030309031701060203030708010803160b06040207020301060f030b2a030921091c030509060304051005070c050c120706140c06070f 78
    0xc2100b2400c0c0b08007082c8551400181c0000840c1c260050449910000210301d00d803054100c0d01e80c00090360401c502081116842c00e001019000c0944190b100140208015041c0034150160b490701070400b604c001064000b0a000350710a0030300310f000e80340098424580d10300340d40c2007842c02c4c0c2c0041c0c0160b10020401403201d40c41a9024054070440001e1450044403002e120140008843d015002030480c00103d2041d42e0396030f0440b9103c5901400910071156210040c00f600b0119110a030780c102c0108002448844804504908055401c0310000b450092503041031299040240398180c144146282ca00540d40e1200718002005a813840c0d05035541100b5040c010f0000c45030034290189082244100c0020ba00001602d07403040c81905c10303a03100d982d6800d000e454062003400071061585440140960280d11082d032a83c2d140c011000c60700450407000078440c42e60410b030210640354012102c2444214800c00f5031140c02c1500c504600c2c00c14000007041c1d03060440079104403010032060345083c25120707 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 546633983 1250 546632733 546632747
    0x91505250b060d210e0a080a020117092a09100f09050c0307141605100b030f0a1103030403170c010e1519020f07060501241b021f08010303 61
    0x10509990804018100f941d0340f0801100702c40001a9103590402580d1340076105800c512005040200819081641c40d80d139980ca625401030180e001841d080c0c0790344144204c5200050144003070750000d0a81c1804031500211403040401d1200740089140c04040842d0746801010703000d0b400f040e07040c05c0b9551038083c521100ba001070b40008619400c017000c10211441071002c0e65800b54490922000030312040d41c680e1001d101e0312807503500c0c420704001e03038a080c0100000c640800080e02c043c104101890002019590038002d0285030450f0b122080200014014203003800d20003001404407402d1940300c1e600d8001d030300c6000c89686101100410270726050082401510141a510b6014102e281c40780588107009600040c031100e60000c0c00c04860310564040d5040340c8441800603040c0f40c0780c808a141c0040941000c0c407501e4000441c0e0f0314030202d0102c0c0c104010140c0c248540ba0700b0701081220728000c910401c20304c2c007030ba4042015082140074a84942c0c00b01c01c0d20209555081d903e60651801030000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 546635233 1250 546633983 546633991
    0xf05070906020c03030910020f060711060703110a0c020111100911010923010c060e0303160914010e04060e091c030501060504030204020d0e010e0f12030601091505250b 74
    0x40d0301000c3d9410042e240803084801d8920141d440e2070b5144204c1006078540481c4081e40070b05485100204a4000e501941c1840501510b609171780040e1a096011003e8402c2d0301d120560072982000803008039400340490194091040c149040f00c07003420b81943e414520031f80710a0081c1500d03031084504000b110904c41c01016802d00b0b280d91034a092400c94150103900120300c5d26035200c01d00c1c0755009a8011540d000707049501c107005020703041c03520b604031f9221303041918401040480212110f031303118000c2400800340c4400e21300d0400b40307407031220044510034504d4144030340040e6a41c601141010001550364443d00d51140100400c40360100884041c1040d02c500d401094606001400282d5015080310b084940488000d030f112807052a05030010000c909070317607086600c0c1c1540c00d1104180860301a001c681c13002e0030380301d1b0507400340040c403003c1c8411509a0300094040e441800000541719107206912000d14026052002000c0b0140c44000360342c1c4407286045050010904228a1800250340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 546636483 1250 546635233 546635237
    0x10b040504050a08071104180b10140103021812160f0620030d1d0709050c09121c03060521060a0b0d170c1204030c180f0f05070906 58
    0x545000e44030242c44020001d4011311000300050a070050140011804907003100050080050480070303040050120301900f41213279070702501400506079a088108500486420103440c03d01040ca0b0700044000b94441088100c00c550303400c0ea4070350640c40300750008045521490007002200d40f0011a00082c07481507100b0110783c0c030f406405010a640c050b4544040d00107080c2c4002c24041c12590150a40c00307290001240c0e14988000b030450102c1409003200c07841c0300c0070142c8014603200ca401d042a900704443c012005070b0104680031050606c035048103001d141c04415940c1310100010565481c00d11018409c1c0002e8030b6a50074803a80c50302200c202c1c040c3c4040c0500b290701490712014903484001c0185040841d5a0360b0710086216142d0803100165280d000c42200da40482034180c0100c517401400c80b501951060500001140d1050130484080e030350000e00a030a01ea2170320019906815000c0c00390550a600e8000284141140340a00d003c000700c42d0001245610781980c00a2210b80c00d5880001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 546637733 1250 546636483 546636491
    0x4080106051210020310030501020315041506020a1104090b09060604060f03051b041b121b092306030403050c0d020102040506120c040806040302150f0c180406180c02010b04 76
    0x144032000002c4000300d0745030918001d45c5070f80d603010840d0414003981e480036220754000020080c6000c0020049129000d00f11420010382c403000c40791800c20400c41c015000503030b000540040c0442e034022428010903900810202c0c0c407081d2a40c407515070703040a4400301100c3d0720103003c0c4841341c9498001c41300940088000c0103900e901c0e507140c281d03440d0b5401c1c44902e040d0b98841c42e0800c89441d0368000c0c4c000494000c0c81580260301c1008010f144010810032030501510b006024101240c000c1c4904031b640c02c0c641e0f10204214180000405210102100b1460300b1201c00381500954540b007019601c5030313010b510303455100c0305103040203420940000702d0343c021640b041005101d295100001d8071820242e0025050140d50f80118640d0b26228035007102c50740e48100c0c0100401c041c1c1c00112480f14003e18031603920f070b58035103e40c5881c044106640c19615180305024100c0c000c080c0113800002ca01c001000800c1c2140e4401c18282e50a481d23034030128555841d0b120102c485d0f902409a22a000415a8208 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 546638983 1250 546637733 546637759
    0x1103150412020303220c05040501140f0334030605040b0106080a06060503011211130e21090907020c09040c060f020309060f03041a01120303050f0f06040b0105070c09020408010605 79
    0x1a0050907680784400828200e0b030383c805c00f07008040e2488800303130102170420040c558488400c03a0b9101c40c00c802c440d207c3c1c10171034600809410007042e04001c6421010400203500b02c00030310480da01203481809440c11201c4200080800e14038010140100d0060401c0205941000b00c014101d17000104243c000b00e0410101300166640101100e0440d0b1072200c05521003420340c81d001ca440030340414207650003211406c925010385041c1c2c0c090441d50703840000b1a0500e12003443e5890418281c401c0e0540c90000c18400d50645081c0a480c40340d004ca55481598010140c08000500c0d441c0292010754615181e4117040c4815500f00d0201c609401e07107400110308241c401000100e0610540002404142c400301c0800c0410400c00559070800241d400b41c00650f6031501d00049a086c201d501c260000703428078000c945000384c0350840034011001008070030580ea5402c0180001340809103100f0741084000c0040c08042040780c00c0800c0a46415000581e0b200e14002404c3d0030b5480c10f40140b485070914000394 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 546640233 1250 546638983 546639001
    0xc020607050a0302070b01090c0f0212090607020a080109030c020f0f0f0d0303061205010b0312091e0303091315080c06040332031908160c1103150412020303 69
    0x11548503280303180c1103554a05030b0304220702074001c08200030301c2c8544500020607041900e07000f19050b686503941c2d010341ca08401500b02c0c1d903401074441d08011448104181082ca080000080c10b08a0020f0700481005907545030140c21030380e018000390001800020700c5021850300000a84480c03030111a0a0203105481d80064030301001036014030321a4038039080003003c041c06500010001d00121300d860002120f941403183c0a0024048140e00c039020300b55010016103a42000d41d803010b180540440030300e5034218035103001c021080003096407510040c03182c1c150381c5d90381c0c80f005d5000540c02503011806040180e4803500300c0c4a07c1c3c0000a2a8010418040c01d42d1154400d440c100c0c1d400001c008080104100c0c42c50303104030307881000210313254080d41c2c1003103040c400402400000106c0000f036a940300701d00000c84c1d90000c00d442c083d003058801c2c1b8019008a1260402c5a0454010145030010100000c0001d2804005c401c0e80e1544094400401c0140407020104001800c002c0c0040e40c9140f0f040540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 546641483 1250 546640233 546640243
    0xf1f050a0b07020d0609150e03041a0d0b1512010e0610122715050106050406050a0e0a080d11061003060903021c030b030c030115030201262502010c02 66
    0x103001410318022489100b5035840e00c1094084641107130040007500840d00b40004030b525002c00c3e0100483c100500c550b001340002045070219072f0540101031480740c54154105242d0720103402c2d90b18190b114110340000d070b501c02010303050059604529940c1c0d980309200020710204168020707201c0000c1842048203a4540e1954049492240d1074074188440b030400c59440140008080a03a03040648106072000c2d54079043e01b040c002c1c3c002c24101e900e08048600e4941035850901030380c070002d281030004201150007034014140002090170105c0d00645040081101803d803036103c0d080c04d900c5680441c5889030480c4140000411000141c00540741c00140c0181c046400e04c4000d1110f59222402d40a0510a1184002496449442000010040000801800008100c20720a0080120792050740c90144111b840c00a9046141815149950010345840d00350500340e44042c0e48054002400d02c000d85400e500ca02080c0716400d03001d40014a00208007104501c4800a42e85011400c103102900092 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 546642733 1250 546641483 546641489
    0xf0403050708120a0212160e150f030c1207051e03071e0201060329010b0c0f03040602010e01060617060904080903010e1c08071d030a08030f1f050a 65
    0x40c15a51000709103400050340c89042809001c5400301400c2c8014590b40781c000784050f00c0d4080d140c413525151070200350096110140d8402c0811802d0480400c142801000d44800340790710040e041c107144030382000c1101c0354001c4131803500d9820001031203e1040000301d82a82c100d110b134506030b810002c103500c40f0b1a921003800e03414460701c00701000003a8400e11a0743c3c04d40206402c240301c6500c500c21b015029010346a40d00044070b00071a0161500c07000201c2d21008040d101c00317600308030342d5079103000c81072a06640000b03050085409142c550216402c820401407000b06000c0e8000a941c0301520003050845450750007170030400034650052190351a075030010740d800c906d0440d0309045503192032a0961151181d842c1054242d42131911210400d1004103020780720005510004508040f00d1208954200048880d00042076080e2183d01c2800c4180402102602000d002c071503092a05441da5200d941040758582c280b0502001003045c2c1100e1400c94111000711070280c49503950500002603001f2061340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 546643983 1250 546642733 546642737
    0xf0b03061f030c2711180409020604030c0608061c1103151306051f170c1f030e0a170d140f010503190c170109120e010f02060f0403 58
    0x20900c80d4032452510419009607400b41c0c91520311030713565101070548038407130103071a690300c40c40903c1038401030013400384105100001d41e2191400518400c42c2c21841900700d2440d0f0869521114100141c9501000b0000b0350701910309407904070700d4200002c00c0d0f024000c1425000b40340103102c03078016108e002da054076001d60104005010061003000f00c1c0c50a05045a842e8001c0001010300c904107000308503402c1e074603000320400c1c4040da855100003d058038204002c020410b1440341c0400c9441c1c2c015120700302c1c2910000c190786900c40c084000a05411002c1d8000c0e12060850f68051002505841200d68610303d004c00307004002e441da12000915022000580c03000240099500c1000c44194440c00901450503a03004040c240442c0d40707540c20100740191402840b40c1441041035044141100c2800d551141d00b44e0031240c1801410309468580c450214110340d00d0b00038801c001191400455544e45240c7c3c0d072000e6000882000410342c4000d07000714406d5401200902901204525559034455014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 546645233 1250 546643983 546644011
    0x11112090c030106060e10030b09010b07080f0f09010e010c020a0e090f0a1103150c090d02120a260a0504090c050408030c07091505062a16090f0b0306 66
    0x24000150411141e4030550394075529100d80462031607040070800400040944980307000c2000180c040c1d08541c401c040d207070fa2006084004000c0c50044400802c03945202c3c1400c03030704210720302d040591181c000c1c0c241505079420125102c1c1070742d44c0c802c0340d06803200701c01d00c0e200109600680101d04208141e01138000388620b404009404a14100084010315103407500f214010403907414151301c450943d03420300b4468021500200c0c860b803040c4101c1e50188a5056030145815020410071200d80c20242080342c00540c0b800c140d0310509010711205215a004450740d4440a590000c0e05840001c06412102c10306801d00007418034990041c00d407810740703d6075480042c0c1015801400d60b06801298051140340c0b20010354084034413000300707c810884d09000428441e0140b20b032a28141804540200d0340c01c80000d01c0050148002c506041e41080740302501002035100880c0d003642405030602c8514041d10b4080c10801008680b4466a0242c1130911030403c600c904110000342c035024040e094200300005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 546646483 1250 546645233 546645241
    0xf030c1106040807030606090e030406031e05180105061f0c1a0c0a1b0f020105030604092021070314010f0c091e051011030f0f03060a08011112 63
    0x1512848050a005124070b40300c0303980c0c61070b9a0760b808250101b29089800e28400007010240340c0a02e81c3c50415400103941001c1c20640102e0041145410701903514410f54030096440b40640f04641c040c200b2502c001c400450008000d5081d550701520b814014001c000c98400300f000c94480c21808a10343c0e05d400c1341800b16500b40710501140c003458003040016084140072503015090020081034683d6110510500354084049030502c40d41800a8030f05118152001d00541c4076400465100b07000810005216001da02c0c1da4288049aa0700700d4402010440703281c2040c90309202c4820101043c580c440701c0900f151215640b12001e80c80014250751183e0005070030250207410880e00c030b041100040007024202c12005215040c1380c414004e46c400744a00c1c03411402078000202064070006820b4000c800200c4004480141014141d840711740014803440140c1410310f0020801a0300300482c8903140d081035010406004207690220030260300d8190b40c1000a03100b003050310b4251520300014603160f99 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 546647733 1250 546646483 546646493
    0x304051002070f0812032e03050f12030c040603090201020f061e0601020105040b160212070609030306050303040f03030507031205161d030a021002010902060301090b0f0405040f030c 80
    0x14a800450340304424144440d40c95500003402001c0b1400c60400c1604a81c0d103d002948584241496508221041000400205000345c0e90180702c1070128141140c4460f01080900000b01500116280e030040039001e501340408010b0507410f141d4114400d403031401c02c140541c01c2442181306042c2450348841280c8156030082c08001c1160b0090826901c151078030303400d13130030031056041850b20300902440b01142040d48144143ca114a901c000240300c0394864529480d0514280a046000c52155009859020324241c1c050164280b04031800300e1032200c10701d030203004da80c540d0b0080d07402940244420030925030f035014800116505030900982e24400f80c1011918183c07048140c600041c1044240009401468000c00c03400800c1d907180c9407000c2640300b28809200c24a04215070650009080102614140a86151080007800002080070003030f804220590402d9124660883d07a030289a176150034602a140c4000204803410801440c0c569100f0384544030402001d0100701c4c4c0708900e081008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 546648983 1250 546647733 546647737
    0x50421030201151e06080705070311120408030903010b0d0201021902060f07030507110f180a090c06180f030317060a2103120605100507210c0618210203 67
    0x4a02180703114015868113103a02c10141000b040003501101c0b01c1e00000d40134440c00019005840300e40e0741ca0b1800718507440803501640b5148a400e40d500070308005c0d90b074002ca181c0c0240700810a00e0055515a03654500301421541113100c00f07801a03140f1810800182e174003042e9800e041824036002012805130f4000305003180640030001c030701010009103000516030040d0140440a20820703d50f0180f10303603503003031103a11601c525161750080d4103045801c0c01c81804080140c1e000380f00381400100c0030026114503960003034070780c044004114110354480a102c042030702000a00b078200c4095805e00c1c0b07180d0340200118282048402000d403a031000ca81d6a42e51100ca4000402204c0d1a50340c1c0d5402e40c2004000070891018110003103200e54142d031640703d2241c08ac1c9011100000e211a00301448540140e13010703800b10f14104c47c1c02412480c043d81c190b1079070269407012061541e41c5140d4210310b192070402c564088004072841158039000b0300020b0702c020207000e03416103005c06020200b44517038003c0c0c0c514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 546650233 1250 546648983 546649001
    0xa081c180b100308030a0c050c010f09030207230405060112050703050711070b0a0e030a0615091d0a02040b0d0503161209060c06021305210c01050421030201 69
    0x460801880340c00c005010324a5184041c0242001d40c042e484078441c0d0401c55010303200c0181184000d000064000c076895004080401c0d0300d09015182403000714891f070844407a003451422659a821014080c19810070142015084d0030a0811611034190301e1440007940c55040c1910440d01c410000700a6403107041060a61060703000148141e0400d054064040c050483d000000504081c444000c03100c0300080803402c6416080280f880c003080d0803812100002d03115003154140c0702d1040042c2c0024114843d01003c0302d501c90400c030b11107007403c0b404c400350350348404600c072a00c144400d0f000301c80d400418031650300e83d4110b03800190010078170086050f642603008003030b1241c00301040e0030001400c500c017151a00392041c1030b510052081044d0507039a048581c00350000040e80d01202800040040d4003c20354a0a554108440d00766602c0009041c0d40c0c40420850305078501c0c3d01d04000d5003c081180c3c14004a00f400c110b410f003414105c45c0c28040c0000710400c0080c200d000200b00c24075000394407903030345 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 546651483 1250 546650233 546650287
    0xb0414151516082811030a0804420b0603160c05011104060509030f1908030406110a020109060b010807020d03090c21050706181401030b130b150c0a08 66
    0x2a00f500c2800d2039101003840e44013030000c500c0c048410007262002000700d030400441916103003c242c0301c640b2840d20b00140329911942d000d40040a2480c40314407541103010a02140f8880f0b44120403a88100060381c0c031145c185800743c501441403044c201414170986501d2142d07450319290390040703130a01038054580346c0d0340350480d000009400308078240d000c070080044200507412074107202850308180380c0e2010700c508030208642400d41c01d24000389028000f190068060a0f002c140a4a02040b8000350744c40a896403001d0303959203010008115a50041500451007400c1c80845ca28103000069210000c000c40c48080555a800c02010000610500c0001e40b401c01d0781e2b045560390082c424441500c0300803080d26548031303110000171468401c1d100c400602800d059190b442a25101200245d080c0440900e4141070b01e881e510070b1141c0360031882d03107507140700141c0c0850748484000c2442403540322080f01259100d403c002c3d90301540400500c4011071540420459542c2c600b0201d64524006400382102c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 546652733 1250 546651483 546651517
    0xd060c0212030a0605030c060a02030a1103430b0112020d050a0807030206150f040c2304140409080a05031e070215090118080306040b041415151608 65
    0x20f040010740d00900c2992016070403100d49002200801201340514400e00006a20802c514000b10380300300061910a00310100301c07420014402400c5100c01d4040340c404c14034010f81383c500e890f20960b8041020040756035045003645505582c90b280141075050040c4600d4142c0d1900510842d102e40f030060080316001429559081400d00d00344c100e035804514150018400c2e080481c0b04010800c1921000c14001032200079010940010311006d01000d40990f030500514000c00c1c138501c51080050303001540e5201c4425621400d1090281c0e1102400c425240258540000200018a1741d0200c0d01c803c516414919260703516410031050685410131401e01d410045010701c50b1003900010508940070003401e0034441640d41c60304040c203d903080020051440b145141030b9000c907442c040150b0304400080c3c808a00c0000d000d01140540da0208a018402c0c4100381c10000440c190780090300c0104011541e140000e02078070020401c500590034081443ca070a0813240c410001b420086511040480319102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 546653983 1250 546652733 546652741
    0x60a0908120c010506060315010c0807060507022a090f0603070b07050d1b12080403110a0807060e0d08040b06061b100c020f150a0608013201050d060c021203 69
    0x901d81c014500c500703201d6090401040c107500e014030580384a1990f40e00d81d004c0421414004645108401c8000c0da6890002c01030306000c1484c07401810b104105540080c8240b4030b030180414140f0680d056500140b01c05120304079455500c9030403e07500007010650000c46a02e07602c000a0604220742e0000518610004111080100110302d15401074001d4545c2188800e4654012610004504000b0414606051080d09203801400c41c960840d0003031601500b0a0b00d40c180700c528140c1c1c18141914001e0010840004100740350042511030299440a4401461070b03410243c61880040c000809100c1043d0010306103803240300035202200201c076542020443c501600948031540c00001c14a014107250240003403038000a80300008002003001415107181501580c0e144a40140040e00c00c0b68031404002400b030401d000d8066030040070f0343c0c4010340001e0490f0400c1d601488808100d40c012030880100020b9a038010300d0400d0b03680001012a00091260b400c134141428045d00c04500c020100c240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 546655233 1250 546653983 546654013
    0x7020c0409022107060816081f0e01080304030b010815010501210c17060f130b03010605060a110d1b030807180f090e0a0c090b0604090906050a111602060a0908 70
    0x742c1c0481e017068450fa00103840f2517440c41c000060081e00540461040400314030b114003850030b00112010b802000003440e54403141404805242039000030300c0c66002040501c2030181e602161401441a5802401601c0c4480c00c0130210300c2c81481618103100f49080000c902121080b15400e40e564950350410800b0340000010f880703c0103903003648070503400500c0000c019041c04954807059200041c1202d0303102e80c500441d5000742220b1301c10306400d5520340c02e000625031200409040740344a81c1d04d9241240010000c0c00d480c4c40140d201240030000f02c014103030311818549940341d1103190545401c100b03590310400e09880300034200d1049049103407000e40020b03109491107992010b0314030b8500c0c01d01c4002e14400b0155652144144c02501d05108642c003002002440c0c1d0142c4182ea5000e8401400c1503520a1410101e03154240c0c1510b4050321001001010091885076034031741d107840700c9a1410600c3d520a0800d01400d41000207014550009021785054082c05210009104900071910700440c0c0d07280e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 546656483 1250 546655233 546655243
    0x1112030c0102130806090703170f180405070c0b01031b180605030d020102040509060603092805010c091206050c090d050c031e10020d09020603150f030607020c04090221 74
    0x86200003480e600000c1000200480e9171070041080000511195065841d140003214a50022441401040000c0e60401042c00013030249504105014003403100548107002c29980c00921010401c01e554a100c8006200c5a00e075074156a000055148003130090166560150b009802100410b00c410b01080400c8400c3d070002c500b51107056003507071603101d850b200a9082c1e00542c09203c0e0b00c0401280046ca446c101130001d10f078840f03c50001c42e0001061885080f4404402038a2080d1024490041c001031040c24002d404c1190030614140301254030f45003204c41c1b2036403040001171549481d4030200301000440c1c01540c410040080c080b19003000c1d01c1c58515915854643c07400d01900601160381c101c0340581240d500300f080c0b90000703001c400d000e402d0980003e41c42150340c12402c0d075030390000c3d00158840c2c0d005103104011103085007407200e413110104904020b8140c2c0e80da200754090820412141e601140c5404208429580030441814600c00101014801c80220b031f00c907526046070810300710b00024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 546657733 1250 546656483 546656497
    0xa0b0a06032a060503060307090209180c070c0e160309030c051f0b0901050a0b1e19030b0904050c011d0904030302090108090102340c0608090c0a05030a1112030c0102 73
    0x2d04032a9224070a03295400304540d01641600800c408012150094008100388030b001028205071840d103089015500c08143c400142c4d1140104102c2c0c200b080407080e41000d026108440c1c4502c1c03514200c490b0a54190000740c0042540300e56aa02c1003500a14445071082d42c86010703a81c07207030110841c405001d03520301200000603082c4a0f209030703e42031440615040e10000340892140c6410714103450705a521450c084114240103000c0c1c0b081d10301c40000a80040b00d040c0e4038040c0318110480d402000e454056130103074490702d0044188000210000740c01c0509071428203000ca900400c0004040d2107901000c603003900a200700b001c02c801c0641c140d004042d189000d1700e9034695511104aa2401c034003650344c2c1c2d400c400392404441300c210780a80c07550410800f1429488203800120350744001804051b584034002042ca08000d000d1802e6041c05180385586042d1a105041498140042d540740c0c1c804401401000200d069002c0507141c0490351040c4003541d00031030755038613a0070710301a000754080c2c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 546658983 1250 546657733 546657803
    0xd090c0b0a1803110607050708030c01091a13140c0913060c02060403050403030e061603030b0a050105160206090d0b130b060909030a08100527010503030c0a0b0a0603 73
    0x70304042c640b48119a841c1c002d980d044000603588250400038480c0940c0440d409448600c9481c50000349031004000805000d540d1500215a4041e140340030807079181d00543c0300900d0b003d1070f01001192441c0f40340440c0066000385c25214045030064050f801d0004e03405101e500420000108001c60185a082125161185c40200705588031480c00703d8980e503007650300600140b0204004c0001c40e1140e440500c0c540f4000b07288625240400095000041d040301c0c04501007a1510a800074610340030450f0310042400b801c10034500852510600b8180c0c0101c00f00910444020961442c5a03c0e100001c054035984024110b00078100b502c154210b8007400081100c10046070300004900e800c154500d02d01445a0100450410a5160f815900b51500501c05603d02c0540e2000088030307a220140b03078240c7e6801d2101640280b04108100040d5101608100d000ba802080036108030f240014900e80000d4210b6028a0647c40705001400504460382c005090807100b0400410742c0340c3c80f82d0a0800002c915 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 546660233 1250 546658983 546658997
    0xf1903020307121a06031212070801050a0b04051e04050108061006030b0d060903170109020913020c030a0503040c1203260f0621030a02031c050405030d020d090c0b0a 73
    0x11a1840030004125038004e100e1500c0903c4070080c1c1014014031a00454010140e5041e81c144560410780c580003242c5da00044289241070003021134000c11241e000d4041030319640c000a09103540a10b00c0e115605c1828001c4002c030404008000802803a64004e50b40104107000c5540c0d540b0615030749040030307504d4041400c6884400030b8101c1c0a44985040d285024051b4180d81406450340401000005001d0f030500050051381c0c012800584e400602916501c00e0043e01c0309440406d1110380f407070161074165280d00c10024240b03246c40000994101c2201441c00a59070b5940f464902c607062040c0e4090446101c20700240b50402d90005071b1107604402d03401d034036007451000c0f6074000c1c1c0c1d450301035880d011038042241c04103010b0708103c0c55a00602014000e0401c9103510b4040c50313491603001c89551070060304040f83d0100701e007864503c0078202602050382488142420b032111600e07482000c4041e221f5513070002d40041c8610050300903540141c3c005603c00c220b00c0c0d0307420304c001259005003e440b00103941 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 546661483 1250 546660233 546660239
    0x10b0a120611210c12040209040206121009110304150b120d09060329040f0b030604060b01080c1c0b010c02040c02070e0a09030206040809121905011b0c110f1903020307 74
    0x401400e40700d01d980440b40c0e16425842d9a02880711509020700241d0300000100124041c013004603404600410621081e10246460034ee0361801312a007000c0030000d06c281c10001e001c0418110a01e8000380c1c140c0d1103001403039403d081d00040c03108155003240141e5004050000c2682c076004050707801110040c2d1000c2c8542907896150302001d070700000c0c1040c8c040c20503c0190b00c16041075401495100346c80980050080c0900c0d001a107456800c03642200c00c203490304082805c95a000081542140c2040c11890404a03005202868a23202da00714580040e03450f007100c005a80b0580007201d81c1c03078000e00204448820400025101c1c041400b441200c4650900421101c050b076220b4002c0b1182c15a0150000b525580d0b507520003948001e4840da4030202a0b00ca101c0b54140601804070740d0702484101140d00c44441ca4590f0035038080000311100e120780d0f001e1118002d03800842811009500108480507010300e40c0000f00c151084109840d001580310b401c510664410040341400d0702c2c000c404a640d8266 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 546662733 1250 546661483 546661501
    0x705030a0c140d1509090c03050d17070c0c0b070602030a0b12030405130204091b1701121407031506031407050d08030c09032b02010b0a12061121 64
    0x1204080720000c0150401a10200c83c00d20b602a1304081c84030226024150350701d40d408401e90b8114107081d41d9441c0041b008104200003003111003451005400c10204c03110707664014080275100100240f091000d540100410441c48000540c050481c0d81e8032162510040d0400e5402034004451038562145040041c002c2403400c0c040c0e000c41107c210340110311382030400061151036101c07241d000210540902c0041080c030320a0180581403816007010b04606068841c1c001c2a0070980e101d115003140703140005120300d5280341b2400308250340140c00c800898136a500c41d10300e002400d50014011104100d08405450200d401800440f8040e26010403010044020a62501224461142e0100d1030452840000340c440d005540d00450030b0b040c042c20141000042410301e40b05202c5141040c250421244401c01024001000da60041c8020803200e82c0d1000469803042040c01005506e00c2c10b41042410440360783c00c000d40d410313103c204054840482e0082c3e0703004a0030052442d0710030070134480080c404135 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 546663983 1250 546662733 546662747
    0x231801050a05090c18011a0706110c070603110904020901051210081e0c0d080c0d03090611031317070f0503030f090f0a0210091d0a11040e2205060705030a0c 69
    0x7883d25000c006181e444c00c1c02ca451f5001440d02c071102d407001d040c030204d401301e1070038820002a0003211030959a100200c00009003440c3c640c0d086581031614103003681e00c02c55903980580381080350544005980c0d295010040e42c0c0c1e0301409103c228851045020406401c09140ca6001280d02e07103070031207400005600c03a117010110074010121159209990050162420080325080f00b80a44405480c0480c20320b09a070905242c1d604090100351185089010030502d4420f00344801c0f046440e6504500302000e25000f041380c0494068084d48040701002d0b4075519144c00c564440d540310080402102e802d02c2c003680c81e600304441d0a4036220f401e200090000002280841c0d030030310010b001c2c04a000c4541d0030043c1d030b601d5036501070781000782d00540410100184400e0400b00c2c00410488580c500e0b04904d1142a50314580f80c0e003081c07100a00080086814a11100b60094031041c0d01c581e0b90b10031076440c0003076030304604400b500e58070a5a0505c0805a00a40194020b4403201d005004069100c7c1080d5a20 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 546665233 1250 546663983 546664009
    0x30603061503050123130c0b07030e030616080411040e1609051602070303051c0e030c0705060a0c030c050309040c2613061e0c0302040603050109231801050a05090c 72
    0x841c03007017000039890080f0070030005a0184201900e40000307846800d000f000340c010403011000b040c400b4540c03100925041260035800480b2100210150706450302c010003100000e44018503c142842040c0c41680c1c030340c0c205800c100400300840701b5000c100c0c030700c1140600140c440d905409181801040c03c0c00580b46012100211310307001464400d107555000c40780c5900c1160352401c07070f20b00c802c59031001c1c00180c0246a80b2415600081d038440b10034281135800c01d840c5522444c4140c8080003524042e81d04502c1d40754a054040c200886040c6083c00c00c50300711706c00c14091030743c010f00e05540380503400c0c0c001c03100d804000c56801140c1014100f101031b80400d00f0b01900d000d0340604070304c2d8424000641c1a0002c000d01110904017041c1e80500c1f541d0348041d00c0b00030390074002098005c1028049581d05100302401881055030505c501c0c1e240c850f058082d007030041521650001030200041300b140c44c0c401c0c5400021180b070000c006620f81000391200500e401c2e50340e6043d0380940d981c1d00354289880c0c00030443c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 546666483 1250 546665233 546665291
    0xf050f01030b0c090301151706190e070801151a030906060f0609041104060f050301180b030f0303010f0911190f020c12060426090906010306030615030501 68
    0x40d900750386440312889002000482c1d5550200510a045e0304c0c28015906400c8450854420850074424001c0c600d07610300c01d0200e501d034025000c104003c0300d0b4005050001d5490840062004803000d940ca0034081a40c100341c16941c02e1543c0051829552007025044070281001950711807d00364590300184004e0700c40e0040e691000c00442c0140c5402103040c8040302000b00407030725041e00440401c0c20788402600c410460749001c40c04210751074000b1910700c545019454854503560400c5012680300d0003118224800e2582c0301a0110140c03010032101d0184c4134000c04480d07c2c1d6175503c055400140c4030340190102641003011140d1000c2e204c1050b1918030304400100410302807010802c030703000e5810049807004c61041c6c00c4510701c21b85803e130109140300d044102810591030281450a02000702d14000c040342e00030010140e40281c5003c042e00c0e02c2020840301d4403119244d01c0c004270082e02c201c0d000900a51b1500e0950800000200d00c000300b220f200e0002800000c814001103d0342c844c40d00c40c5400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 546667733 1250 546666483 546666511
    0x60a05031516110f06041104020405090c0c2104060f0507030807030528050609070212030703020708040f172e11041e080114161b140109060f05 63
    0x80c00c41030300b011680e00c14045142c418070501c448043e803440c00c2c450054201580e080402804248020f000701c43c03100000c01c0c2c030194a400e16000c08164000d80040c00701008690204110705d2141041c400503000710079111118008500d08034101003e0f0340300b8800c950129122854456040d4051002d96021035015141c1148070f642c0c0745000d03400740800800c0701c0a20480000d0b50304d030200030351100005a19400c400000d01d80740410500201c03c0c406040f04080d50300940461100038034107000c603a440441850f000d80c4a41061420440601075030f000b9000e0603035800e101107030210401c008801c00e01421030845040c3e92990041800301e00504801d0101c00340e00062003003281401e9005203200710080304c03031140b034141e07200c2044043c030b041002c00711000000e40c3e01c10004884240106600c0d001004422080707402e040300c9c09440c0120742d20440040c05100519151084040764002003030f03540120b0000d0b00303c040703028820f00174440a00101d518915040b001880309801c0d114940c40ae81c0c940101ca1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 546668983 1250 546667733 546667741
    0x190f0c0b070f020705100c02091807120804120311011d030a0c0312110c0f06090a06230a0f0e03090f0103020306150c07030b06040c0f030507120e06060a050315 70
    0x84602c9410588041540700f050300016158807401c84000c040c089603550003030b2502c1644104a603c21024000002800d02d00c207002c1403c4001043c420215540d82100003803011040c60603c10a002d581d100c4074114400c051140306240d041000380c1c11114160008001c00c207102a80213400d4500d419542c007040c0e105205c3d07208a540189000b403403050103400c1c00b200c8540c140b11040c0640c2e0104222050030040400c800c1c0c1203181c108070034080c20404c40050a0146041c841c003583d00e016402c2c014140a403103c48400341d29029151180081e040c030945d01600340f401c0e0300c10402508824040d00c07043d901c0c0c80002d0034030341000303c1601c54189008154800440403c001107010750005010540c0c040040200b82510681c0d1100501880c07071b00070090401c144c6103050140001c00b0007450203001d00d0030f1649002c00183e004001c0174038511103040000702c07512010701c121041c5001202c2c0d00425454401d100a4240e40011100e1050604607003103803805843d00e0502d6120f1200e444c5040c10024410b02007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 546670233 1250 546668983 546668987
    0xf1006050d090506131a190902060c0d0315060c0206040e04390e0105010509040c1b06050105040c0c0201050319020f0a080411190302091308190f0c0b07 67
    0x2425159103401002c500840d01da00c07203a0034014291040d41e42d04880a440104110b20148041040552a40b148031b1b01d00c0c0c02c00e1a101c0040c5502c0f00750740ca50b603503030050004550354801030391096a0100110340c00c810300300f40c000e401031414214070050082d11360740000d4820300c0b031400c040c0090b034040c02c080d060070f02d428107000c2c4000b00034000300c07080c1c0e01a02c220100c181940304000d54203145440c201c3c0e05400c14a1016010b28074580268504148100040c00243d801904503076285100ba40c000640188001049500d00341c02c1030030030100b5145001400502c821504035034141c2d0011502009110b8684009441002c49040001d0114500b800007411240b100e4400c8640380c4040382e00549402c5640080b00c1e0b40d980f211000801044e0400b041c00280040318024902c01d490945040e180150070f00c042c0100e4030078134440203100d00c08080004022004075030700f0851259200070391310344480400712490104007800b01c94200051580c850601c60a00ca0044800e940d81c00030480c407080d485503541 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 546671483 1250 546670233 546670237
    0xe0613020702040e0f07090501080111090d02180112020411070512030a060302150304120c110f0307030b09010b09090c060d0b180a0b0f010c1e020a0905070806090f100605 75
    0x59921581e03ea100c1d130100300007804071009108649016000c01d908217003040c1c04441041c4c006442d540c5c51f050300443d50304100000c403030b17940c04112030740d2103001400d20005108052640c0c0c640800d48002c000026807152004046000c01e1080341c06011142e86100c8401090082d454058116846140c060700240003400040d50440942503000c01c0c501d440380c0200300c2111188001044032140002007006022070030a801520b142d00f46419102048192a514081844c02240d240300300820f06c0c0f24900c0d41d604021401c020343e0321401d40311051528000c91b600130502c880005001d1000c0d00002440c020b404039011441e42801410039041003002403000d00240403c02d5515085008035428440e101d61740340500344590b0600c0c0010590304000c0d81400201400b240c0e126040c0030710003580700001141990302d0500400180d020805540740c60000401400c06a0f0044114901d04018050031035800110248544000d864200c081c0d01e45034a25500080211445882ca4191103424400e1a1140700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 546672733 1250 546671483 546671497
    0x1030b01051c30032c0319021605030615190801060906080c1c1112150a0e0a050709200d020304020a0b07120f030f140f0f0106091503140a05100e061302 67
    0x206c909044c1d031606500000c1402c80c1400000d81d120032440d076030039240c0c442d2410180c0002e80180c8000c0c240401c6520ba60360804200030f100e001e00c100d4803078074484160280401010020001d1041c03580e10014040103201500910350706000700700c031030704642c1000c5010121300d8900a05400041a00d40c0b14420320071402c00500b80e2003000081604c116000030002801061030801601c961401e080b9191405c840905820101c2a00050700b0b01d000310b100410b9403011690b0a807004204c280d15404518084c5040c0c801018240f40301244000301d000150303015500ca03510a0b10140407054441c002a1054040d00c0700c010014400d030841c411005d8410b8603125518502810042861204454000300381d849910a0003503480440040060361250ac07180d0540282d50b00307000400550406000416480c928007a5810012640464510b600d100e03030712090981c0000060361ba41420140030400140c0360580341c1d140f1500011901080d4414407201041c003400c030003000c244c00c481507012180d001c0e4100d00e07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 546673983 1250 546672733 546672821
    0xa0c05120d1b0e010e01110f1218040203060a2102060c0a02040f1b0804050307080f0d0e1513141b090f01030b01051c3003 54
    0x50200100d2104050300344800c4040c07020907040e0440207400d0203080d1800440c010400580c00d440040d0343c01004802c0040001e1074440c015640d40c20f10a40b9018240003400c401d0f10407881d0b2500ca064200000d003603a1b24962035001d82c6d84070b9182c10002a408255250b0b544107210880030804030302e089001d00c0080e04280c901000091003a0002007081c0c0142440c2a05604914400320844c40c00380318841000c0c0c1c85900030450041555181042c4105000303142d0140002000820107214040060b118030580c06003940703640702d40150b102e0449810507252800c86608060450aa203540030400c2c1c94000000c4500121b90b981c2c030303040105404012281611044c01d0b500000100d52018481858003800b0240000c8a091a48051041069000303000100090b0b2007001800092010800d080c1101d42c110b600036003000303c03400a0341c900701011200504230059492512030700480f0074802e6000c0d481d44501d5680c021f00c504020380c01d855040d41c032030702e003940304000701c1300180c901641e408006404030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 546675233 1250 546673983 546673993
    0x6090f0601060f020f1c0306050306010b0706152c010b1617041a0c160e070320030a0902090a090c0e071412060901051005120a150f03060c090b0a0c05 66
    0x40e10001b42000b1b0300f510054040e80c0720030101c08000b900748c05031000600342600100001e41c03400e40c070b040340c902442100418494550215103d9044503000c0c207405005100140d10102942c040c126a5141d040c0b030b0071540c8da540c01c400003e201003101003660740250304000e0055041580e540e4040103410344803ca4104550184404079950303040d20400706162000080c110365070207003400000d1800350151020a050314040405020481454040345d030020f6260030082030780310316038031001d40180300c01c8400e0f003140201000304040c0002c160404900d042c02610552026100c624190040c2d13031034070102403c03840001c401000440c148800580d400429490320000300c080341310b444202c50740141a400c1d0104c1400c0d05107d164030b090604a1b005280c2211848025264080068502e018203034651000d6180140080d055039100c1c1c10460b003000c1d451100ca1121a111451042d10380582e01040da0120301d41443c4c0076585000e1540e9105071420008540d0a10350b0101d01120b08100d0340ca0300b00c81602030707 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 546676483 1250 546675233 546675253
    0x3090204150608011701020c070e06040b060304081b0f0703030e182505091804021206070f030e0d0e0607030c120804030f08010b1c02130803090306090f0601060f02 72
    0x1000c000a0040d250b2581c070440c09526140e101c482e81e654544ca0110164410801803005610000d5414200d412048900c000c1d0351751100010300414000c40b40c25001a4004200820820024001c10309248803c03101071103085842400c541d510942d2442914580c02040309201103405071800c3c881a410040c01c561020086540390132804d00300780e0781c1030743c03895882035210961028001d180e9401242d514246091440d01d000184800c1007000b43d111038203110801050554840c03d030400901100d981c2124024248030760000c141e0104440b0000001c1d2400e0503210740d00c00d021038800c5170f01040d540c0711003849420f902041026880503100b1010b00c01036010150006010543d002240d4882e921102602d04d03180c01c0180420b880c1035402410003a40000600c0b86503041010b030b401c00044010050307480410648000001c3c031a059000115001031080050b5106c00003006144803402070b0f0981b15030f074a51044496171807a14103004441d035000200140681407140d116074500300203d204407003440030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 546677733 1250 546676483 546676511
    0x8041703040816051e0d0308131704090609060b04142d011b05062806081006080a050d1b0605070905040606090b180d082d090303090103090204 63
    0xc1d99003900040c144074181040146000340c0c031301440750034100e01c60003118840c8000a9040c000d1030401030620000c403000c40c0c004080c0d800c0d070480080c0c0c407880cac41e03007030400c3d8003c0120182c00a00c2a0bc602a003803d20106203100580244403c403007804c054039050505002401c13040401804015802c02289040d61012650403266140b40f810102048140c564140c4001005d2494009400c04a035443c1c1840c400014400540d00c2e601080038030001d04a82d03551034000d1041920540000030450410f4804204000d010543d804031907880d000400070b0035601d42800751980f980e464040d003a41c1020f54507240c9240500c00b00c90381080850070300c0f21034882030b0303031900f00f1075400b681c00000054621805204030b003401e03c562006080340b0305040304c4c0c1e6441c00305000c880e8421140c52002c00054404944540c1c0c8030402011002ca50014000b074440050000c12003080d0403280c640785120b07219520507159041c0890454840c0349000d0080c0d45445851070054024007260311080343c21a55030184600e00701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 546678983 1250 546677733 546677743
    0xa05150a020f0708030f180c090402060c070b031f03020d06020313060f020304141b0d02031e06090d03050103030f112802010e150403020111100501090207140a080417030408 76
    0x148200c9104d074590a02540303142004800034450034040c0001003004040f4400082c0403103100c3d00840b52000503684034404a4414064810b103900316100d0360300045240e902c0100518440d0499002d000841d60301040001e141c50407a120294105501130000030109190b500210341c0800c00e48104680c641d913603601ca004541d10900300a01c00350b03001c41400100300c014010b694940d0650401000081c10200c41604200340c2042c0c55803041520194840440d14180070312846181c40c009441000d41000c400e56455890440e403051460041a03c1d6103e114082d00c141030603a9056954280e071a40c0c20841600e130200c9181886c1031612900d80e41040d5a50245c000380101c03200f805400f00d09565a10001d40514a4140303224410042a11000502c2c032400003074900b16070302440c01e039260990146a035400c281560320740c00300090810300045135041071074006141d42445010f0401e4050002c1c0100342c0c0711501d0480003801104100410010708402e40e002c0b100d03110119040d80d18003580c5082c0c01e4640 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 546680233 1250 546678983 546678997
    0x1205090d08430318020a14030a0203190c06020a050c0409020f13021b03040b03070c1b03110a08012903070e01090b09130506042003151005030a05150a020f 68
    0x16690010070b584605500d8011035503402c00c0c045102109001540c0007841d000e0050140380101c0c0039000844185641c10007a80104a4000d401c2da6011101c40c0107580c1070314100401942c441c001c2d80702c005299480000c0c0c00744010b40001c05041c03e462040108401b07042480d030180d030702000ba811310804130790740c0c051050121001c1003c016a1544000c0004034024003200c4040c14980003444100940708803d02204d900c0000c9140450101d8082d15010840e04d451f100c01e100c00721100d481c040100502d1080e0702850070030455aa5241541e40c0c0300c118281c941340259080c40c9500403039248001d04107055202e480481c01000d4802c1907440b06d01e0501c1020f003d03030200c01d902d9250840c014240c04c0081c0c41c2500a240c00403000140c41440e11100d07034903000504000c2041003003e0a10748640c1c5101002e28a000005041e908604101070605019080a54000522110043c00040c2c03502d00042c540001c9076010015001500c02c25910045040c4001c1144003c283c080003045070060341c10000f0004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 546681483 1250 546680233 546680341
    0x2010e030a0203040303230d060f0504060e0c030429010e060d020d0b0603010e1213090231030b1608070f12020f090301090309030302011a060415020f010c1205090d08 73
    0x141458410440919102b607801b05015900d012030038004d44124110550f1b01065005c0b01c2680c0392a079180003521040580c4500d00c000c04c805400d940750354007410140e41202e10205041d1800c0d01c5100801c0100c1c0c0b400e0200030360040110a601c0000f544203402c00703911100003000040c245d540720340740302e0402d100d2108007000908002405c9502e0900c00c4100e0014040e01c81c801c60400041800007046907008403112214407201c140b400d102c49240c00740840145038029071300c03036041c146000622440c00c050601d003000303d030040001510042c411950610490b24030303038400d22084401d1040e240254030912440130b52010401c20322045460902030801070b24440c1c2d40d10100300d895403d000b821240709850074050391020810460180e62644151016600108501c190b4100016001d0f0702e044c005004030b89442d401c01030804003564010a412541d50400442807180f96204443d42c1e403107441ca50703201000b00700030b9004505c041144200d000e95a4100c50f0f03c40960810107444110f0b48500c680078115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 546682733 1250 546681483 546681491
    0x406081503030d0c020610030503120c160804030308160206060d020402090910051f05040603020a0c020a0e090f120706020703090816060e09071709030f040801060602010e030a0203040303230d 84
    0x43c0160b410072a45038400104075203c078a01e408d43d501e564a0388200d0003080310210314000818900308400044941c040c00c200300380603505080e0302c2c00c200310340c02130311003500814201400150500c13881c4603160308991041d0301400441d510403003080062880d4070b0003603800550030301c00103540303844805800b40100400d0403540c2c2810700c0c203420801c0030014441d07c0c0d07140c0350030b011806084640100c00d46003a281d081c100941c480d500c000003110f400030101c1c00654402954a0001040c1c2c0003003114501810512003580c02d1172120444150303441c0700300180319201c03d008101400120300706601400507184249441c2440f155180301241c509011162100711000c0c000300100201c070380200c2c400584c58002d607221078191511020160058503680d008001c407800010000300b602809000b10f03061095a00d40c51a02c6a8848580328000c1c0264062500550302e00058002c0b2082c1c004256203031120190700440c07806007180d4040b030b0031046030148800201d01101410b41c64200c2400a0040c100601c14005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 546683983 1250 546682733 546682751
    0xd0b0402040e0321072a03033b0c150c0d0c0503070f060608010e03040503060106020a150c030f02070f02040501050604062c030f0f010605010806060406081503030d 72
    0x7000316840994100324940c420032641c048190702c094034000e40344101210844540d5001d82c1640d2500b81521b5040701c41030300a06102855807059030100500380656000c0040711410001040840340c1c1040340c5d80c0d9030400046013a07503030306000415540e0740e42488c2910a0034984502055100314000c03191045800085000c1c0311103441044800640c0e80703203140903144460700751111a03d0f8072502c00040d141c0078a080740782044c0310094020400401c13422000b0010b0f600303e4260035841c1c1d0441d0044c0c2d403107401004000151a840011145520707504124803020340703065a00824010500c42c04100c081c5612480e13200100c204520242100b140104d5a01c0c400e4103030742c41000111041608098444e150901052004c10b51049442c800360113649010b401c41c3e0003180054014046007607541e0f40c1480f4902600d5103000020600c2e0416480c004003d1100319254070055505600c2101c03caa00808280010403902d03200b003030456080380f00302024110341d40c03009021078195481a01070922043e00c41c5150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 546685233 1250 546683983 546683989
    0x11206051005090604150f080304061205150d06090606091e0903020615150a02210c0d0f1209062c0a02190b0c010605151207050d0207020d0b0402 64
    0x6a0010100e1000908541040b0001d0928100946464041da0f070381c034003060100035aa00090301400c558103020300c0c001c0d84d0340f5095a0300c0e88107006a4000541c0745000001012850207124001c0300748011301c5032002c02e11800c0c84000b018500e01030f107200d030311131030100c01045041c415500600041d07100401c13401182c0422507a0104030010000703080303181018440120358041440e0750480540e140c0d04c0c85480b0800005100100d01500601c40c001c000290090841d800141114000c2136008084030445813400304400701e801580440e40140d00800926005c0b02e2048801c07142c50030540c10002e88010710201e007174040780d000030342c115001c90f95840302e6640c0b500002840140c0c413900840f00107660501c105015203c0300d0011009000b0410700320070303100854103061844040c00030010764035180d06007401c502c1c1c0a4507680c45401d0250120510b629640301e400400c49480714407401d0f00700d0003500c0700c610480e00b41d440503100110280c4d0a11021005a4628541c8000d1900584d032240180c1418010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 546686483 1250 546685233 546685241
    0x806060a080d0804080c01020705010f0504141f020d02040e240a051806010c0503030a0c09050d0206030f09031c0b0a0603020c10020307020c130905101518090b011206 73
    0x412580c0b020b01c2502c109544185510341c4640c2c404401c42d200c244e81c00350b1034064041c044006019500b000c5e00010941200d80c0290703c190f010318506144c0c07521710420603844030b5071941449420b038500340e5000c0c0c0d49456500140300c1d40a01c800e00518140c1d4418501140725015541c42c2c103042c0e115001e29042f283e5290358100c1c40328085a030203801510b030800094004c4100c8a480e484400b00100207401d503801040c0040da000d8100042d203543e49001034030200186044209140032600d080800f1825023003150611800b1940074203003030b1441e1544010100071140040100906110400520180718401e081200d001c03140d00001041d1040d2010403c40319003403079001001050b105220f0390a980000091003c1c044080b42e100503900d890b80c10080f400d2494121880da08083d44d0840074484454992000e4800782c01041034a442c0c0f04e1140c0100300b5a229455601c01200040e0320900083d0700d0120645054546440b002036803e1060b81c0d050903c00c800d0340031622041c80590902c2c140559405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 546687733 1250 546686483 546686489
    0x30c14100606020601051c08070c030308090709021c150b04080318120d0c0312180312090803180f0607052d03010603021605060109020c0c09010e0414160806060a 71
    0x2d041213605140201c1e0038030480c47c00c8400318201030b40300b00050240c800d04540059401403e06000b00ea228100a0100340741655a04440d100300c1d040010042214401d03207061500060313060301f020469a428030b01504581105004040f0621000105070026000420040604d5009151500030001c901081d070f200603100e0320700450360951200c00d11341001ca000c0141039403a04000218510f2424104d492000100d07420800a1610b02100310f05150701311445c14892103651446922401f000366a0b050780c00600c0d00400ca43d80500c0490000e1481490562018181d9012500c0300c0c520440198544030701622018007240e40001c0201501440c1a802c1c0f030300c220403440c29140c4903d070b0b14a081c05d92005104d190200742d03000c41c0c030002032100c4d0600101c640742c1000c02c8400c170b56162030b020300084d07010000b01d960301d00c01d80d08215110b0620020943c1243c503407000c408000d503610f441340407006184145d011035501403030350180c0c4207040402c0208054046040203200d01c0c902202030004240d400c6d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 546688983 1250 546687733 546687737
    0x14130e060717271c05042c010b16050115081501080d050901120207060e211c02090a08010b10140a110f12270a09020304030c14100606 59
    0x601000480f441e00d030065911a00e4802074803c964a001c0308660408400070000c075004641c04218a6080d90b012018100707840110314059007005603540c128100540d80c088680d51102d40c200100320061400c80074200c00e0403501d1441c0c441e114169151404c4503420100e0045081e0105800e2107000b608102c05c02e4440c070a040c00ca0030550400080950340c044c4200c540082000010b1001d08a07485118041e00c07100e90001d0540d03c0c2c04451030000d008d400b03003540504d480d1007900d0701c018014500d030010000c107624030300740709280040c0c0f00490080c130b04c11064041c5038607808009014458803180e401030001d0201000005218007458100507094800d11810300c208090701d0400c689140f2110122951203507103042842c01076200c24070440c140401030581503024014000c0004007000800f00604020704000c0421006042919036032401840200d145500900d01c1c807818400c10711542e00440d0024020b040003504012203665258041480e92509240f58000d4910004601c50707600480d030142c4054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 546690233 1250 546688983 546689027
    0x801060b1b0d0c12020c06031314030a0504031407120b01030c080a020a090b0a08031b121206010f0c02040504060603030206160e010c140d020705030709021314130e0607 74
    0x1280103060762400c1202811440491456804d1603008003e4070141030f40c0908119281d14005030454141003142105503103180035090090405200401240d4081034540c0381d0600703050850312444d10030b2080d41070000c02c82c855054040340f209a8a40c6010626104444207109503041d40380c2104a18502c1d0f004000d240d10503400f03c40160b4541c2210400d03500145c40c0080d5903200000091849000c0e5840349000303005c00500d121288480c050b00d00c480b018404101c412007030040e182e4006c54420390302e210024040300c0d40403c43d2507101d81d80c0400341035614581400d50002d103400207400c584003aa01100c005640f62020000c164040c00031903480401c561780c0000200c10031201500051a040ca001d04000c4030341082800c11454240010740c00001c0811540000a1403401035239450083c000c3c14800d102c0c2600010f15031351540200c1c1c44e101c200c10142081145802a0051131010b01c0c4074490b44070071403c94511116142e8403d0300f019049060007000d0070300706030b80080c5c007401400c510404803a001e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 546691483 1250 546690233 546690253
    0xa0f140f0702040914010b040c0801030b010620010c020312060904020904080c1603050a0b18100f091218090606080402131b09080d0305131502040801060b1b 69
    0x4801600d0140190403600da94482241c40080d000381400d0340300514401162020002c003500c1503000d110520b0b001d0358200106a802c043c20381741160244002011840300000500c20540700f01c20302070301500540080e000c5a034011542a080d0780502651400580c000304e0310001207441d60111540160082e00c004100e400d05402007240300340d00820150040c030b000a40c05481c4481080203007118102d10550310011501c0385841b9455044c1000151045881c84002c00c0c4070540206580404840d030800a2041680020460000d80000d0350482c60300c980d40e50201010800302c042c160001c00d0181e807806403a900d02c0043e0b0490580a030000c01442e480d0400078080c036a041841d0a4205404a807480d0f10410130030b51941c0908904a043c5080c148105d502c4406175030440b00442c1600c42c0746003914801448140110101d480443e0840d81c6100440241404680040d1905e00d00780c4880802600e440d440f400f406094030511f07803004040881c0014008200d00c044580c3c01904070140380a8014941 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 546692733 1250 546691483 546691517
    0x5010f02100506061e0309010b030d05180a090204080c040507030e030f1303060213031203091a0615041e0f270e0709020a031407090b07060b0a03080a0f 67
    0x48900c42290881d41d46001c034806513510004d43d05030401520407000482c4000b111680650001e841c20300107903080581008540c6030108802480f411107035101030030036902c41c041072610050b00946603040540711b840800c08401c1c0340000d001514a41c2c0040c200c004240e01844102d6400401040802d440c0c101c0030401c20078040304517101005a0000141c07034500038003d2000170314040d0300040045100140d03825141c4c0880c2188000c880c0105000c1c6d00c00d080d0000150180d480000700245503807106c4203040150000780003256085840588103035030141840f0f401c04999030140d00100d2003891355903004013603800070b514000701415044280d490300a10313280520561000d03583c010a2480b130460301150070344007103511400a14140b00111041180d840780588000d40c807207020580001e090122414124000d945100e008080903542c40c00700c0c52030006280c0254001d030f00308889440d12543c031542a42c1d9003055400207140a845015034035800a1805094200b00300c0c402d1080c0450302040994042c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 546693983 1250 546692733 546692743
    0x110c03030a0302090109051201090302160f060c0503120702071a0c12031306090b10150207050402090307121a2a0a0e0d0312050604060e06060a1404060807020705010f02 74
    0x21841e8103000d81c0b5200268016500100315812081d004a042000c1d44030340b000541184080030b01a070241e420f2448019038060b141c01c81e030301a007400e20071180000c1080c14410300300015103034020703800e5900701580341c8400b4110b0001547c8110040e40110710a01ca0071214030507400c40e2038031000a103482c001c01a00792980301e060301100901c84480100000c1d0461411034a5012542d900c014100a041c0c100e1034042c0ae07024040d1000f000700150380002041042e940301c1d1810180000d0380051035128a4102040041e501110405401d4018a0800100c80a00600c452091803203604d020099040510384810100401801d601d24000c0d0070708984105000c0021149480c41e01c80d1900b031f40e541c00110140c420140200d0b09030303080400481c000d401d1541c4802d071100d001465650030301054031808108416200c49001e400111203600700815858907017080105407080c650b05002000c1e0003132076048905500168803c101041d41102085a290303410b104600c041e10702401d00c0c1500380c08c1860000e540c1c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 546695233 1250 546693983 546693997
    0xa06020a031b0f12080a06060924050c0706050705010b0315160302130602030306040b04050601020c062a03030f010e0f04080c120406050c070b18090a090b16110c0303 73
    0x2903410080d6070300c207100940001d00c40c0d0b160050b048030134600d03c1100003042d180048443c564107d2401101065940c86500c100e42242d00344106402c482c0d43e8108d07099240c652030681d13902032000801c04014a4001880382c10010060354490359107907140d5050440c00c1da02c015020b0b5110f034114480340412600c45c401e805070089005600214101c0701c1c0b9a06a009102d00d641d8040c0e144030320400013030201e44c0000210302c1117000381d505200c00302c1c0290600044e607000b0b440f03240c0540c0005d0035008240c2401005031030030082c1d0f40102c21200074102c050420f060141c015a00460304000b04005128900c110a50300500da90170000201d8646210316147d1607801800040c40620005400d6010700d60400201c07000d0a451018a655544c0d00c0034064840c0e070000000640b64003440780c0008403402040c040d5058000090900101561210100f20b2420070041920086d00d41d652403803808202500d0019110700809140c0d17403e03034000c826010741040d4400c0000101a800000091040d0710080700343c0c0c4a03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 546696483 1250 546695233 546695267
    0x2030c0714011107290c04150c0b0f0105011701060f08150a080c040e07150f1e030b0f0d0f02010806011b08041e030c050609060d09110a06020a03 64
    0x5689003070310764003400104000e42940720010403c40d0600c002c0100d82820540b0781d04103041d00603a02c00d02040030380d00440340000060700c284010481c121450b40705583c168018900b14885044640e072362040850265543e600c001000b400602c9156041b040307080764136459100228240d85001001005c40c100030700c004c0b04006c5101d020403044807030103040240e103400040c9003034034407911030785d2040e520801e0085185c407039410b09003a002c1070500480d0303410982e00b000c1c2405042d82e480440c1650604003442181c0200140104440c503010f640c40044103006c44a581d010948088a50030801c0a001c0c90307000740d202d82c4442c404a400181c0510101c40202d60a01f00004d03640e03142001a58021000c3c1183e65200d40e40482401c10481001e004100361034070b001c00252a20000070410700c0301da042e400300030100103600c8010b01842c9029000b8140e076442c001c081314039101501201e18207490812508a95140308804604140e02d4400d000c613000d800c0c5031004208008107030300c0080034000f5140312800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 546697733 1250 546696483 546696503
    0xc11010c03030b030d0e0102011a0d08090111060a0606020709021207030b030304120f05100b1804080d0207151a0d0b06060d09150b03030a0c120c02040608010b011202030c07 76
    0x4050107900812240700005050743d0101c014085e01406510781c3d440420300652900d41400d2034030501a5810070710400280603400c811810f6514090a680030180e02d605218072140304402040041001c2845201001000300b80c035490042d01a00d407000542062102030300500980641c06a0321242c280d00803110f10780170646e0358000e00400d047d480b0ba40c00202d0f001070700ca80ad0301c0900c00d4560090600302e22035400c03071380c0801070301141808582c0c50040d007562004064508881d02107a5401140e00203010340c0c3c030f039440c000d01080c04004a13404054125058441d1414020041c8100d10513140951803199886940a280301c0004081c1791802400030300780031b01880412803c0d25850b00f03641d0b4600c500001000984407900b042c827080c0100c0f0149001203410068861544d040200c2074920701e915030f031100101c165107aa15402022680700880341003102c100310203070140c6c1e901e009440c01002c82d0400091009500030004140803409482c1c0046180104207218010381c3c0b0f00d0866907115005040f1031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 546698983 1250 546697733 546697757
    0x50a050304032106170a0803011502010e151f0b09040903032003090d0302041d070309050601030b01090f0506060f130308070606060e010e0102070302040b0f1302030f070c1101 77
    0x750350b082c1010002d900400c00000310496001c1c0750740c844d000b922048070303030079001c4401090007640d10b8440c820014110402800104040c0050000c445500c070304a0001049006414600d80d16100402e135425000c82d10403400c0c07020302032401010440300741e00b400d41e412080c1d00302203003004103205004403240580d554281e00340a040c0700368007800441c4032070841c2c0c0c00001c60741c402c1ba1049810030745400005000e0207c80643c0341d4068800c541c11100591210308014820a1510001840080030282415250718415001400c240010740c0a180700c0c25010f003c9505040403481150410b06403608181c0c0f90000b80700c2c0c180d8030701042e51911100381200301e986498180139a8a50308e0103070310050a4100c04240c12041104a4000c2c1054407000c1c1e581840410700000116582d081915109002d030300320100500140c03d050b000000300038000741c2211219509800481e810b0b8400c0321000e0107207680441804025041d0707005094105030380307141501403c19031341c071044041d000d100c18144c18030104020308 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 546700233 1250 546698983 546698987
    0x201305011b0b16171009020702040b061902061008060619050a090b18011805040c150203120702070f0b0309070f120b25030506030a020604060c0c0e07050a05030403 72
    0x140078594810909807050074804101d014200381c40b146800440e0705010181154908000f45500c41c0c102e07035a0074007645203045003082c001d5024000231781e0042e4441e50040c5040c0c9030080103011181c290f039000b0891007003029001b41401d20240800b8540114148204803001c0d00103005a00800d003214110f08840c10310b45106081140341c0c0c03116070040c207190703000600002a0342c00004c500b401a00c0c094030300540d60313071070b0003880ba070902440910404403500074501007039a0340004d42c0144a000700703110341c1c0c0c2c07185e1800c1c051458030215071006a100050705c00ca021003000c40340d0341001c0a0700040003207d0a040084803000e92034060010068808400604404000c004447c002c1c106040c6004e0b042d61599080140079250a505803890210340000c07603100000c1000c8840c420103050031102800d400c25004401400b005410701e50301d80b00e655141c6015039181c80081005050b10b0725000c0c0300d104145098200781040f6445080103551030020003050307680150441c1d100e88544c1c90407a907a6501c0340784c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 546701483 1250 546700233 546700277
    0x414180c060d0f0b040c090306150b16020103090615050f1804080d090206070c150206010f09020901020a150501030c090203040f0303051e0708060301060b0403080f0703120f20130501 80
    0x4002c1c0d0007810f244080d101b90b40c00c25061b90580c0c1c0185070074403400a030301464180e4202203125040c26003804104407808210340c034076400fa810b4414500414804269107420050300c1d000c140710f040c07010604208010610700b8500808040381300ba10840c0170740d4100c1d030172486050001400a4111a00014150a8034205900c40105e80340c3c0104001e40340c2d40326040030440c034a101d014034645201442598070b0350070300018605040304e04403008900428184a68071700650421000755040d84980b41001001420f4070305882c6865640a500140c503614502f0401c001361001c1d440020214410018040429000f0007001c3e900358042c1070104043e1669110b81022400380b500c10228406d4072428801c2e4070f81e0082e140380c05888114000d0224a40703c6900c81468070a07440001d04080d02000300142c101c1c41c410103481e0b280c0c040d00703180d11960000501c207800e4590324805415000e980320321600b100b80b5214890007102c20403d00e8a1b0502540841015001b85580100c0741442003100c1203151503401c00310703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 546702733 1250 546701483 546701501
    0x60f030a0b042604120b0105120d11072301080c0337090f170f07120306051c15020301081e0f031215030f060703090f020414180c060d0f 60
    0x1a0f119500d03656900c1c2c00c4800c8118010450b4201d40c0342000040615064102101034003210010345a008010003045e10314100c1d150840c001c600440800061200c6082031500309007070942c048100b40560000018504800100060350091050040c000741d2552191031700310001038090312106030008080a581084910182013405505004142040100c07a0a207508494031940501320700721050b000d0707010741e402140d100071402e80040c0511008144140300f6015400210b081c00280c0715100c5020070401c000320350001c0d4480c107c800d40c00c001c22103a0410b12940306a918402c5003154100314403140c40760003803400c00c0140e000b03440e0903440fa48401e01030300c03d0071107042c006c8130354607461910302da604510100c49a090100c200224008241400b04d4070000c0302d00114017074001d40e0340c1c0342016401400640f2043d40d8400c40c40c5119001612940f04560350041c07081c8807680d540c90a614a011501c084a440703045980002c10000e6098456505851094801c2d43c070110701c4413840c0e80e207540103021121b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 546703983 1250 546702733 546702803
    0x7090b0604090f090c050a06211b020a031403071b02030c0402040f03150c0c020d05030d110903060a09020a1202040207061416020a02031e03071a060f030a0b04 70
    0x3850140c8a980f03164013a0410078855205c200f045a5910104500452035101e00004201c0c0111898480405104032680307034408040300169030310011200029801c908074800f00503030301c0013584100303264101d04e1074008412140701d180d20318600701600421242d0507560314180700b0b07102d0036181c0441d0741c1800f521895903c064401c40d145d47c0d4030401310401c3c40107448141c0300d040d08440c0d880188403050003810310400c0180c5034440900e0351030b030038000d449995500c20b03603d6010500100307204802070700031001c607044054041c90321215020100350520308060090141149000102e0006848a00c034280484d11000b42d0b13401d0020107400442e0207031189000081c092032a0800c000c03078222202040c1c03802031a0712950718102c5240c400007030b40c1c0c46030700d8a00030f5410f510200c207014100103c0300e500507080c040c2c03506580c10040f0720768840800b00e48201e80211411415400c0209a00345110f1544044000318001c180710400ca440d031041040d4040e00240aa103140400f1181d02c82c910031480c0740d105820 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 546705233 1250 546703983 546703991
    0x90c0c0311210901030b040204030b041101050f12011706090a140106080a0614060604120b1302040c0f0806150d09020a0b120103020109090b0306060409061b09030b0108070807090b060409 82
    0x1802d5500c4056026150644c0030a10740900c00c88281861b1098509803a8010903008894940780c40f107404c0c488007088118100b25080007031240c06901c1c503000e0b2400e039400b0b54004182c8e50500d02910040800004001040e40c007400800514610000d41c039182e0f240c200d0034082810708000189805007056411145c00c902c02c00003001c0130802288e200400030414400b10300740302d85500301000400d10481c0301c4d45a8210500c4984004540742410b42c41c0c224820740d901a415100c20384c04a4103941051065034081501c0111754030700d071500260103c1d40400e088a402c200d0560b0400950420700408000c000300d1540e840055085443e03c2251030003408a070800142c840a0030b0f40c00c00782403072090104070700080055100162444441c00303000b1026900a02420b1581c0e2540d040c0002061130003401c0d41c1c010340341c5406003500395292114108040503541c4c0c2c8520fa43c1503080000006c0d506a110003040e034002f00040054960201c0d0600a41d0f54030f6002207400304107840040e9aa0080790011081d103807030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 546706483 1250 546705233 546705283
    0x1903710708130f0305070e190504050f01060b03100306150e0115020d020714061c0623030601080a0b0a020403060f050a0b030105430503070207090c0c0311 68
    0x10030002c0c102210007403403401e076081c2d283c600c0b94281040d40d100c001d0050b40200b00510030340d0740ea21303141580413001c0710304050000441c1c00e00c0300549206440664294005201c000030030b08083c080d00d00a00318040c2100c2ca9810020002c81c0e905800744006044144d0f24460320500240095400f4010980e20070880403558441c9114680010607000d51405481a003618025990000c24801c0803514294904a001000c50041c02a160300c04220900c18210b041d502000c19106403046c40302a10f1060348009a180001000c0c00460307014403803140c42035009034010041c0e841b00292800c0516880f0b80c98681580303c500c8810b01a020307a0700b00504242c200112a242600c55074051031007051100c030b060000d80c02c8070040c1401c98034141c54100400540c2c000c1c00081828400203880c0c0b1150301d801143d2100303d450300c0e0080c1001d403061040c0005000100340405a80d0400140025180c121810050b51912040152103186030000050501001110024201c0000d02003100003140d10104000010b40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 546707733 1250 546706483 546706493
    0x204090609121b0201120e0c030a0503041a0408100b03030708030901090209010b030712110c0f030d390c0f0302070305010c021b19037107 61
    0x1110207855800214064001c1c09856901c1d06003000f45601038480340c203118918140c0001401152589020318820340c2c3c651103240d00c0401040708094040d1001c3c5440c0c1d814100244180c0c440b030700001c954044180070510581d038005c207216016240280e40020f20910500100c6d0950145c04006000d1140100402c4030040c41900400d5500303201300c0d020340e980c3c1c5c0c907040c00a001d40419610f4038001000051100c10280c590b034490113081203620520360070300c0c0d05407030101e103001e8141d10706481e02d8001007550680c500e424040c0a1603503550041504000802601c3c00c2c03100e5030002c03808108600040e00c0d50180a000740c0704292400e8000011088510341414065610403180c44100c62039841c0038a002040c51010800340354242080095207018180442080b44803503066140311075403500d1410010006d80361103402200b080404c2100134042e01d402c10004012003e0340b00f00c41c61080b0310000810441401c10038400d82231000304845059030401400906100e40400c4620245200020b090042c45 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 546708983 1250 546707733 546707753
    0xc0c020a17010b01050307020a02040e0c060f0d0606030b13150504051614131202281502150106180e010602010f0501080c030604080d29030d0f050906070204090609 72
    0x98803241c020b029440b8104011140351004407103c6d001a0080380a64006290a80040100d08040b00c11103184140010001d10070703601030325140c00e0030707000080c000c121103032103005542c024085814104107480720305001c40c1e0001d02034845070010341d9490310ba412100341e100c98000007810b80500104000d2800007203402540d240440c450002c10000c009045011306484115904840b0905021707146030300c1d0180314002c4200d001070480e80003c41e07044000c3c0800c1300108050741e9041c82080080d0103481d0588008046119001d1001150020883c0a8580d550080341070704459440c9084422042c0b0003000c030324403034600d0700080c02e151f039890000641c543c1e05400101c04d175038101c01c0030030030769a0f1480c02640e1608803900182c1c141d001800010041100100a400c10710448000401d50b01ca8500c1485140001055890101e4045071100801402d0410981c0300038003450600382e0131524402e4005d0007038016085110300c950782c0011281e046448a07003003000682e03403042040c84000b82a03d4024130350 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 546710233 1250 546708983 546709019
    0xb090a2009060409050c06090d050d0f20120906090306010305030d06120b01170a05070b0a0f021603122303150109030803040b040227070f0203070c05040c0c020a 71
    0x14440720008a801c910301486100c80c0c0c41d611800402c910340f1868180990b64014110039503211403180d003020041002030014010341552903031407181e40b41c030450700602100322045c0c9140541c0388034407440200610010b4460041e181955405483d448036800041c010b21a800c403040c3c1500075500000100f100c000054031503601c4243d4140600b548424014010640a00b0050200d03030214004202800c038410040c40140001c60542d0084c213166100c080c07800c2ea8507445260300410002d00c6c4403259a00099440110201b80701030701e5036207240080d0782800290b5000192445c510b6012040710140504081000d4446142089003413035002c00d01e200807508100d44504000819031025021903120704d40704816654800f00003421a00c0d903481d0b554030703044000d00c00c80e001030b0809498440203503410003a03541004400a0240c991174a00c0005142c4400c4078901030940d407040c844000000c24060f140020f0b0395055400084007000205e0440300781242c1080030303410064004001c2840070f0200c1c003d15807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 546711483 1250 546710233 546710239
    0x708072001050906070602030c04050a230a05010e100203130905150a030c090203041e0f0606080127150e15090a0812270d110a08070b090a20 62
    0x803418038401901e02d40b1640d0f0750164800801c11620000131034a9000e150419a2440c1d0390b42019100c0f40401c03199043d64002c1d00200304004820000c0458441d89140c01035025185511135a1074030002801d44002524041e2280c0c01141d51104a18402c1040d54500600d40c903007021010f03a2000c4e0301c0010481903d5070094540d91004081d03040c2012800391046a50102d00c0c050440c0c0340c201420300030f40000d04201c07041c54911506003042411400d00c102102e0041143c03428181032403800200f250f56907405603569906140c07600c00c0e190128050450200400b41e01400e46800c14517241648030406140c41080034a0000d161414080c0003402c99881c07081008250303000d449103a260355a41d401500c00071b00c0060f08201d05288014104016a0403510381440c0110003c145210070301881c01074401541150301c928581490581d100f000182140014005402e07100c40c2c0e5201c42d01c0c14441d07688050906518003010a466500c10006c140100740c1044440c202165400d07070515041c2004c90103144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 546712733 1250 546711483 546711533
    0x52b0b01091a1503070507030c020d030f0e030c030309120f0111190e1026071211161209031a0a0c020c10030c020a0c08030705071d0a11070807 63
    0x140b608001e252100d1041d0480941030543da0f41740c00c02ca64950101c2011010800840204801615515030103c00386109860788003180798044c40c000c151100c8600c0f018402d43c000c4000c100d0544010089a82805096600d4490001c41c0800980340440412600c1c00b158030b0519111003c1905101a101c1581480450a0003021030401160340e41d80045070f4661094411205484181c00384540780c0c0d8040e04103101c041240c8907880f020580315021140280810a95014880840024032a0107414106d003005036003898058941c40e8249041c000c401420301301c1d030032201ca407501d0260591000450b4051802c201d00d0f5840c0703015403c101400e81300c408116051007040c4045d2400800e14407070f8034101034500e16081d45c1ca5142140a40441c0b2854000c0d406031080f0310012034151591540981095002966582e034545009882d100081e400701d801e002841c1c20210b00071801131000c40c0c12184101001c12000c074801c44503a46807041b030b90010300c80c1c04006040010811810701c074500f0024071564600c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 546713983 1250 546712733 546712781
    0x114130e010303020c030a0308071b08030f10080304080c120304030f0302012f0910030f0e071401050901050d020c01020d2c121b070f032109052b0b0109 67
    0x2554900e08084008d0100b1004000580d43c01e200710303614085407502640500c0320003916222000258015140e44031140c200c02c00300044500340440300402014203030300941c0341c50f1074054460303203e0388144105881489507038504c088142c420010344010710b13045103034407015400c0c62801034028450310b90070861200c180f03a080161b01550071108018800303402e80c01d5280884800400c5095079521182300181a41c1e40300c0b03020ba074146441040b2905284400501c40e1505000d41c2607407401e14140a0740c1000800c0000d01c0541e640b10742562101902601d01680b00d42c03c0350940350190050701d1400c40003600d4406850340141600c02e00494540042480c4562f0188a621390783e242c241718890300c0c0070040100840c00e011440c01104200e100d83c0c5105542202e51980d14000f8032000c04d90058900c8030407a51a0291203d050750f020761806498180594004e20300030200703540d240c580300041412003016641c1ca081c090030550800030903078010074070340e842e40e104d156290050013002420042004242251 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 546715233 1250 546713983 546713989
    0x30305010b040b0a0e011e0207050114161205040803030708190525020f060a06030b090c0d02060d1d0d030e0312011a0d0906021902030a09050114130e010303020c 71
    0x182c00f6200c0300000546400101c643c250b94000080c15510b0400082d03a0003100186141030310251800040d50180680c90319150004080d41d9000c4442000100200402419102180b00010b02c06511a4070129114510300302903407d03004a60150609000c00401c204800785e010681c035201e07407028410800148030814092045910407600004071051001c2c041b901a4001d20b0b042c550280b15204460990380100c07c642c2c20301d10160303184004551201030a00420401119031544590007030005e084110710704001550020040c200680180310000700d07809050f907035030021400155210260124148000d10f919520f0031070f5008000002d20b441c20b03a041d451000f1007140c0410405648107400e503400c0400382518131098400000c40d020040044150400c1d2500a026865000c1c400058171508088010910110342900c06e0f400c641041100f108142c0d00101d400090362001c0c64440c05480e40030189645c20b100d800307200a140a0940400200c8100070804207043c0e0303101c0e9091325500c0c4118818 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 546716483 1250 546715233 546715237
    0x120904061d0a020d060b0403051c021203010b0d1116021c11040c020106030512030624031b0c070e091603020d060b010c060e0607141306030506030a020a080a030305010b 74
    0xc4038504481407000b0400154440c0c0103070500e018062400200d681c1c1e91a4201c0300c40c1e006902c106c030142c014851309101c4903928041e45c40c01140074005444881e400051280d540d102c14010203019010100301c4007092800d60b0720008041081802056803035040001e510140c0a00f460300700e1107410201d411440154242d05503188159215165503640700b00c0c0820840034041d04e400c4102159a07804001020800810402c0038004519000c260740382088014029450030814031b003101c2c0b440348030070346081d804180300316503000c2000c500c0002d13040c108000000c058402d40c100104a40701e5039201040c2c4c101e5164010740210500c03001c07907405140c0302d03907440c040604c81d01c0080d40c40740d402403520010848941245440260524090440024590343c240c101c031120302081b8000d80c440801c1004045d00120780150220207080014189401a17024000500c0c00d40501c1d02015200c0e0040740c01a10200506020980e008040708130381034581c0701c00b80d907d900320007096002a04200c0005041004401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 546717733 1250 546716483 546716519
    0x61d0127020111160321031a010804061103090706080105041109010f17040b0610020c06031302030f070305010203251b11040c2309030712020d0512090406 68
    0xc590901212640041d00c01c042503840c484410302910b440c540807160294085000303144260600031403024040380d403021115050011005151508000c0fa900c40042d05909140318024a40032050f0303a0780d86881009070482e812000410480802030050b605000700d100e1003512956910f04801c1d13030b07a80c5c00300003d9940c501f030090303c2c140080004100c00e51141c0b5021204c20440d0500008209035400b016525510454098030310f1100304040c41224035000701c800f507c0200341d00c020700380004440e002034060301c800743c8444410a411509442107440c2800468240c0000c00d0598510555034180745001c1c1d0b00449000c0c0a48407030384a92580348050300e9002c03200810586c0e8040511002074048690140b180400b0355203604d0a04091101d40d8550003102ca0303841d00703035807214003100c201c20402c070480700324000da84016102030000460356200064080c08a6810620300034043c41640041580d25000c03600c00341c2140034451000303c8102e2070b107004180d200f00546040040582c1d40026100506402c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 546718983 1250 546717733 546717791
    0x4050d170402093d030201030609150e060a08031201080c15180105091c1203181112071403070f082e09110f03011b080a0207061d01 58
    0x8030118480d00c440207000c0b010013080e54a20400c00220491190000114a4265122040701c1c00280304550b814040e180040c48105402c0c0101e440e60109181c0303200c424000d0284d80e5040c000055426a142c0d0f14410007014080207903030b81d070701603040080c100040034010610745100e00c1010412908140c0d041e80344030569100010300f0000b12103900b40310030040c45001410880d00340032490300c51703903103541485000e0504a032800324046c680c9003500d9010b0280f0901021705107031140b0741852031001e600000e542ca611506c0208503800550002d000f6860f00c28004a02d07104243c0081501061000c4d14900850120100da00c01d996440216900400c94010340b5400d4111030907110000c00004e5800b5254007401c4003890280548400350000c8400e500c3d01500e0709a016995003000b800c00444c8206204815402070001c24109504450405c03808030f00c3d001048802e40002c1c06007007056040c2c400580d8084000d00103401c00d84030610300010214184140e9510b080a280c01294816140d4203800c1050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 546720233 1250 546718983 546718999
    0x90a1d0c03040222110c010c030c030b03030d0f15080d020f1f18021002160f1409040624051002150c0912071214010603020901120f050604050d170402 66
    0x43d0706012840075004440842c1341c0c0d00c52810000304c08101000d480a00b90140001511508800009040d2001703a04a0000d1610341008103071203480100032641c2c0c0810f0358402084c80c0f81152424030044c0200c140c6140364070752a40020803001c40215240e034148480d0f500b15102010620384207600c9000c1c0e1000c01d0740c0704426001902040d507560700034a10005c00d85038004841c14903a004516458030b0614039900581000080600301404c400004019009070b8010022280c04d01940403110207650340110b206004200c00902041103503004400d9074546401d074403040c080c007003001c10803150359406000c5c8102e86030b81c01c0302d104910000f8252000c3c5440aa1000c160b00c9104101003164059040c00d13400c0344a0007000c02c0d00344410030040700100300009052841c150107003804500c0c0e113a44148030070141d04018003040965211030b0b85a065499001c6800404c81491402990103a03540100600340e014031810001406800302d90202c8820560316000000722003a450300b1403082c01110001c5d4000d00d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 546721483 1250 546720233 546720259
    0x90906090405010f091b060c050a030503192a0305130209060402090612010e090304031a071e0905120705010c0605181b0316060503040611090a1d0c030402 68
    0x40009080d07045805080006401d418070f405000a4440b2400c0070358602d0702d1070300030039031380d44030716a180008094601d00340b955090740350303561510741c806c0c0341014080210100108840012582d1150301034004208104001404100c0c100500591503003070350282e0075070907407080e600b600074015a8441d41040f05280c15038441d0398200100b016019103c0e94211f03900f440f054015031250002004c0c00350140c41564a01c5d85010342c00040c0f440010281031040d0401d000800010346005c1030001e620f0754112072001c6543c3c584604445d8481600b2942c00c485008031032172154540c0284d4200d083d59001d68039030b07185030b060448540d540c4485101d0300b80040c14080040020890b154003642c2c2140c400400c0c08483d48002c50040d241100e141c4e64214040c0c89011100054234013041203604003100c080144941130303d4140302411034040140060503090311060f507805401c51450840d02d076510b005040541454442007a4025002c100401208000c80000881c43c0310f0455003d80340700b40c2c1d00a0210303150f040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 546722733 1250 546721483 546721489
    0x10b0a090e0636031c05060909010902090403030e0a0f060b0f03010612030c08040e0906220c050f010c06021801120e191401051305010b0d03120c0e0a03050c15090906 73
    0x750100c48070030f9010500c07118140d008039519000140344688008141810b00d1010420745841c05451003140c0d81c500500103005803503011340d055106170142400590b0f0030030002c2403810046003d01c001c0001a0281022040001d5940140020841540d1a02030b10400c4001d01d0708888842c042c119424400080100020b8800c2d032a940c0c01c1840b0380f11141c00c047d942c000d80608010103441c40c15050704408100320a0414500302443d40c0007101c00c1005c001d80d003540300e1921309545405224050124149a241503900031100c0e807401c2e6600941c1150b84800140012041e24545d4000c1c5000078400d540c4200c0440702c50103070307103200300d603280203840c1c1103401803c0000380c240e0a0000301d80c8d4030160806c142d1060028410341c1d1040842c24861180000140b40480c21a14031014051040c82c10b500b00d400800d030701040510040c007000f034000030183c00390a0152840307c4d101c490710341c1c4004c0c102c42c08010090041584841010242c400480801c001d242c046224041c4403c0c80780c001d81d9010000d01185 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 546723983 1250 546722733 546722821
    0x150108030d0c0e0301090c1503020403020a120f152012060d0c08060106030c09050d12050310080106030c0303021c0221120a0b090601051c0e010b0a090e06 68
    0x14210700f4583c40300400a0042425100707403c009131385c1c01001c400200031466003044000b560186a1908525082c15940041c20780031040c001c187d0103110b030045a1081083c145460b005050b0841645803ca05d00100c0c030b000a03058140e6080d56040a407103500060300c0d0043d0030388243e40d6202d41001c03002d640e01014021003010494042e82d0510b8074001c0003c0b80c00081c00360a010701107a90300454403861046000d421204964480d502481d07130ba0800d00c000c0307076007201000040003a81c074005a69071039410940b00d8000c03264000c420340e5460194000100200034440000300d0b80301e502038a003035451540b4a60011a2050201009608103000241c281d40ea114a02e00410051740300c10383c10712108080040d003402e421698882031b6591070000d104140ba2502c02a503024600b46002880c00b480e6440e4070104c107400c61001d04109886500da1959200290404e041c0508090080702c0b49594418444015102801d08203000740545c00200321818656032034203190403c000c14004007900380c00710849801d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 546725233 1250 546723983 546724001
    0xc120206070b0412031b0e09040212100605030115120803040218010e060f06041809020d02040203040f0c2301200102041203092108031b030408030108150108030d 71
    0x140e020018100001c90032100180504e00403280000c619502c0b070b4018044a01d85110b8803031981c07901c049030010716403094071703034280d0482613034071003440e4a4034800301d150048141c8286280780507c0d45017440c1c0b40815400341d012600c040703000340704800d80da414059400340c80c0d008400310100e203aa01d40011843c01d000441c1c01a03c058142d004100844c80e821078400e400381c01c214211070052007030100c94541381100c01c04941085400501d054030703000207a41c02980d4485c8031182d0649038a400001e641c0d543d1481c0310696000740c815540c0c0c1c0341a1406006820b000720080744c00d072101c040d0101d41000111a102603200051a005940340f0104e401541c0744800c02128100841c01c044560503a61001c0c00580b000b0444a01107003c0140c2c1464003a0280323640c2d4003d5091810301800320030340080e52025101100d07400114940d52903d6001c0d540d070039064128503441c00b41c040001804200000040118104e403440070640d428072250b0380400464850038810801e0a600034082e0a081e20000d60107440c2c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 546726483 1250 546725233 546725239
    0x315050d0f03181518081e030903190b0c07050703031b02042f13150216030c2115020a1110021909150806041d0f01180c1202 55
    0x80900c0903103c010042d00c82c0c020400c045440a503541e4002d400ca1110310400c2c00880070410350310300f4601d0703081d685e841c0004419101402c0440106078944144104d900820019040d00c01c05c0c2d2070000074a81085080e40112242201000022545400325040e0b6020b0741e0f1040c0039080c82441c40d103007260613680720a0442c2d0560071140c0600b005a403203204281d590380440366080c80814502588050740020540b0074103002c1ca0411611b03e00a000341c044105442e44c940720020000c410100c203d00d400c5400004045281280034048280170400c0c80c00300407140b4003411500300c11034a850181000712440c00051003000403842d610310807c00b580182042c40020320b00b004105460406891500c0f01c50300d0300c6442e0980c0003034000c400c2d01d2080044680c51405050080b00300d07150140712103601d184002440200320403800407030b109079031303580001204490070350780c0c800780035112110ba0303817144256107400d80150320700005086d100000c6411025003035000504d5031080d6140070407540d50b80c40c4e09070701241c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 546727733 1250 546726483 546726497
    0xa02040504050403020a020f042c071502010615090b030403080a0b0607061d0c03033009010c030c03050105181b13030c0b07020915120712030315050d0f03 68
    0x140c0c035116445024403c90199004150341c204034014090343c0071803404510f009904089079845541e9402206050f40303820244500d10704100c2212280c00c0c0285504010000100c0840c0c2c2c1c507000b80d054100800f5900d41400341030003816010f0042c0d0341181c403441140300c0c8800a10000d000f20f8094040c943e48085003020204040307419400103a01980098002c480c05a0346040a003481c904066069030703c800d503c1e0003005945144c8000960764000c480c407001031032407541c090800c043d07404100c00549002412400d041414000501d0b8080d10150100340002450035000359040c6110707020f4181240c8c006000c0e004403e6849491800501c4010480074102404032400d1854040b010018103560304001c00340a802402d40c0740c5640b801c0429400b84294610a00c49100585d48a035040d5030810502c2c64064122903070075011a060b41280c0d9400c540d2400f41d03c80004e40c41c20094041c080b0701e44681d80401c00d0300704040c0c004241e04001d000f403d8011683c0440301c400550006001d403515802414964 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 546728983 1250 546727733 546727739
    0x12090512040906090b0901120f0f050a0309080f0c01050d0905071505130e011a0c0f0d020601061101110a14160c050103060b0702010e0f01141909051e0402030a0204 72
    0x210761055102000d110b55500302001521124420642e8040d02101c0000455242408030244100d0024028010040040002041107007030410040c90580c1309054603000025400c02a2200e07440d40700f50700e8036019403d01040314040c0480c160110200503100c450400742011088002488130340c4044541d44192640030030412003100f0448400480d5555641c1d552180c0650b586003d00c0d654081c0d03540300c8a0303000502048070360034180358000481122050300c9142800e007841c9070030048210a5514094002c480c41d0241d404503c0d0b506803844c5448031365070702060024960072103100c1d1009880400043c81182c518500c00c10313072809038910604006080c5019030280d101700020700c1008440e400307211682000a1350301400b85000400700c80d003010742806919000680002420070107a40302d1080c0ca240b01d00260702540144400012083d0f002e038070bc408020519040c0f0030140510303400700702c9403d000185440d020a41c0c0b22361118103409912010310700306c00d10010f0340010b400c24804580906c004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 546730233 1250 546728983 546729013
    0x120a080901050418050618040c0603021c0219081608011a0405090c0703030b0a030816140d0e030c0f0604090506030703120314070e06070b1312180b0a120905 69
    0x3132621509426000a55050400410143c803000c0801c11100da40030b10300704004980002d0303410302101e44900b4056916920860031101130a01c101780c2d14040c40c404a103500f00c2055040f424640380d005900c1d46003043d02c0b0070b01c1d40403520101c62701c01d00005883c4001031200d8180c259545c4403965081c107000c3e007490340f80d400140c07a200080314081d14060021550409040e85805140303030200c005e079403003100c0504680b03c04c045403241c0b8242c2c81341481c0c801da1690403c041310010003800b14000d402e903500c000450f07200920313506401904a02c00d20400784240824549480410400c1000401d040e10b003c2c5081c031464003801c0e00820071a41400f81d08000404281c1b074555040001d80603580008113842569030182e601c140241440c010019107090902c6a501c07820115404250070072220381c107036a9121441118840c03c40380042683c242001401c100d2500003481054440c410fa80078144e4540b210684602d50007044100c1000880001720001c0d00d1001d0b034442d0040500030002d0343c007040d00010030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 546731483 1250 546730233 546730259
    0x13061404020c03190203190f0c0f0c080706090504060e0c030402010c1403030f0f18030a051602061206090a0e030702040c0c0b07020d0f0e1810090c0f030b120a0809010504 75
    0x3603136000d0f8100064240610252810310020b0031b1890400582c00000401d006101c28900140186240300145420091100c03c002e005d00418110342218440f584540c1c0041c1007460511655000d1030418101044070417140c2d5215201d0204200450308642c0c1c6c5800440f40d81e80b240700203441085502e03040c1400d0203402d0009521640e001e4000c002e0900345542143c0300c2c80740042080303040560322201d00070503000100884814a1040c600303a0789803080c894110383d4030000200003d6001500240c641c07000070001ea000740c0324840031200c0036040c2c0c1c3d50034624000d5278804980c0855580080000400500c0e20b54400c0c0000c3e0424580351080c203440c3e40e0707906044241138962001603889800743c51079441e40119400f904100904c0c0c03028500d0044400308048400c1d2510035002010300500140341100c644406000401203203105201c80211010701030800032107401030f4400242004d5200f010350400165201440c10382d0402000040d003507881d0101c082d005801810304015003004000b60651003040c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 546732733 1250 546731483 546731527
    0xf0409150504120f020123150a090906060821071e0b0901051e010b090f033403050606010c03020f010627090c0909050a020a09050613061404020c03 65
    0xc803102100c40304141c05071103103401c00000c04c00c6a0614448580c09014000008a1011102080441c503112040922808441e08000c141c1124038a840001d9440302ca40155000c6801041e040200d0f544071440035450b0140100e9a8080201400490024000c1d44c0e0080c003145006003108a19030390b02c5483c80c0d20442c203200341900c5010701070040c0030848500707105e500d41208491059090f0718041c0a01c040151005214100421a000c500c40311142c8030009030026000c4020107540d00382c1038a011b0f50304a50b40701c019200d40d17602142c259404001841c80140c1c140c98004006190940c2c0e650300444204203171260850441c0184285a408203400340601d0002d00100c0403903060540041d500b00001d8141c401040c01180d060071008004200f5400c1000c0984030034a001085c080f00320b0420f2464075610310002500322540f21800111800c450784041d010713401c1200c004110011078100b900c1a200d45004103540c2588501e90310100c2c3c40c0c1a4000c000b6042800c00340c070305103004031030032000c1001509 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 546733983 1250 546732733 546732743
    0x9061206031204121b031b0e010b0f04090e071a0c12161e0215030a0b01110c010c020d05010608030408100c0801120305130f140607020f0409150504 65
    0xa01400814681401000551030940c82801d040a10b000c135928080307604010003600600159200c454400985002e4202445d00221100040c0a81c11300403001c1000394820061281d950388008910b080c0c1c00f508542c1d03040501c0744c4180c1000c0c141345010000348501d4100140d03501c05e000001949414082103502e807901c88468a941320948030f8602410b0180c580100c1c1c140190812024510740074000284035000d404c1426564012290300e10000214002c00c4044d41c8850804101d14422403080700451143c01d80c948244142e80c850070040d01e1107c000042207140b034004034101c1100d944140103030740702c1d940001c15400040c8840c0e210710742182d001e0740090700180c000107014000140704100c0541009200e6000304621161b030fa000500b0b400c010b0144001c174585400c04501898841c800761894954010020b044240e0344070040c4000c2d00d0140300e1800c3c1c06503404c1d01e542192500c8816144035503000303001080741c041e060081000400114004441d00541011a0071100c413251145605c218418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 546735233 1250 546733983 546734017
    0x30509031014041410050405030711012d0216030f0605060d0b0106030506010c020303120f090109080f07020301180303020d050627190e0a060e010c140c030906 70
    0x220605062403141c81c020422142004440840500c0d07503030303100341d0103500030001007854000c0001c000e0420144000715254941020140000d0140220050500d248240b13150700c2c02c0f001071001511802038058001c800c54056010040000308101c0041e04050150310681703204c800851041c0d0f8155440341c100b03407a06903950b88007000b04107580c070480c1c4d00088100c50714001500140da030401a00d005000380c8003019100c0021408603401107000c800b0403580102030340d0f15903e950314110000c1d00b00712401300c3c0498070400414060709043c40360a1031990812401441c10991000c6c10a45a01c41c000c12a050342da2a19849080c1c0342c00144450901e101796809030b9a0034a40c500d00095400241940340305032241d807042601109580c0002c1d5140c00018645846070341e0300105000c0c4103420401c5d04242c030b41040301c00314040c40041088008244900010025010b1a003946422a44121050f40101c1c184c00d400401a621440c0a0111030500e68100c3c1d03d04014a40800e50581002113070249260003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 546736483 1250 546735233 546735247
    0x10c17041131060803030c04120c05130504050705010305060307062303010f0f240819060801021c1a0118080709020307030e1209010e060d05250201050403080c0d14040305 75
    0x125003d0708009110300e000440c11410000c1c6041450310a9220f03486801e5034090000c82001244c409c520028000205040000c5401030b1a450240808480880b0320307008a200c0402d080d8002e101e0580107240181c02400640d040c03003c1a952400c02131000b40c100d500b0000f4007031a0990340001503000c2d140340445a20700601d4902d20801402040d040401000c07603082081c07100411080214201040518000f5190745075050100d0792141700031411600a030a040000c15281070540003800c0c444645070f038000d00311405420982c2150850781051958100c00c103944042c42d03204030309055110020501c040140e9070745000182c074000d52036100c680c2c1c094010040080203034051080359401e20304803004d041c0c9a00e49440c010110b101d202803e40c140401019000095154403080d02c00c0400d40e04410070150401541122100b1101c1000c2c2e0381607804204030f06040d41c818003d181c09941c0c1078445e41203d0311006c5c5804100c4d00058540402d142d1348441c0000c0b6544810000360085002c0e4a0f4946d136505 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 546737733 1250 546736483 546736579
    0x1d06090304080f12031b070f0c06090e0f07211a090a0504030906050a0903060221061c06091103150603071d0a09061803030e010c170411 60
    0x1603003008843d41c60308940c0360701c00e4138200b203012698014030520010707903560310340030b0404403a010300d0401810589400102d2030403c0002c4801400780c500544031f541c0d82540e81d40d40a00b0280c02160f0421244c25582c01142c01507020b003040e000d01d920801c3d55140301c4000300a2850854401d034969454020312081114500d00741105840d400402800c2d0034400b43c54261009404000288656020040000390701c07203089200d03032802d00107590710030001c0d56203240203504241070096840904110020100100300b0614040030a101e140c52242201850180e4a8903888010b021120069444010030250191555014400e5243c9414030400c0c0400b142014424503241c0003ca4010702040100304260a8840344840d00007544003400080200740c41710b142c5043c0f006060a121080f07140b0149001e020109a0540c00041018078072130004c208800b4030001c11180958100950110540c06101080c0440d6072400803030310124003e0081060340078139440300100f1044510201e038070143c9070320716070300805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 546738983 1250 546737733 546737743
    0xc02090a05011a07030c0b04050c1207051003140103060f02130e0f0708130206070206070c0b0715050115050309120a200601030305220509011409060307060905041d0609030408 77
    0x2254404284d040005641e40030b800301d1248000a04803940d0302c0c0c00181081010802d00e044070030050f081d0f80c2c0510f568584107644100302d000f1244503165101a42c0f015500c0b80c42104501c0c040c800e101011640307140c5500c001010100c150f07201442c1c08000e036001130802c0d08008802820b803290035451501d8007010102012382d0107000301042000c40300901c00800a001d82503080550116611070307032060b503031002515510a900e001400c114082c0c60010340c3c4800341c8007408000b0f0041c030b05566501c0c06840240c0840e8001d00078207089045900369100f4803841030000c0d560054419084404402c3c0c0207262794038941103030380d82d038000880400340d0340b40e050441158840089201402030005504558000e4094040c2c4407130514031a0092100d00b41c2e000380d50074060f0080c80003521410382c0b940c480200c0e907040408503103901d00910207078000c03c8540c140090f0307000807569a99a402030340d40c180750410004e45046048505456514908050000014443c07140200c4154004507911840c01406d10b00709 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 546740233 1250 546738983 546739019
    0x70c05010e090f011a070506040606060206010801021e03040201030905120a120b0a06050903071a03040b0c0a140a0210150503160b0a080a1b0f0206090703050307120c02090a0501 78
    0x112010b4040c0149020900c0880e81176504001c900c030018030420f401c00041c2c0c0a501e00c05402807007228180818000c141e400070058034038079400e98401e61380700e00500f82070740f241503520030008501182d10742080780800007560300a80305150100700080c0313071b03102d1030310344030641416003908a80005c2582004c2e0f0448c40c0042100c081140c140b0580541000117803280c0c1d040d200314814014000360019403982e003030001b03901504502c070b8a0131140c8554070161116802c01c0b101110b103215a01c01185100384a01c090360100d4100d41c0d1203042d0b1140c2d000c140c2d02ca81d000004000154850052200034209050158540c08285174440e400043d150070100351800751070180080f207a40605400388a81c11004017125000781d030905020f1095264000c405000301590088405020041424060000e0340030f00030654601c0785c1e40c2241c0040c2c03200c04640e0388901582c44014015801000000d0004500e0000700c0030107212400e190781c62240d1500414103001e021200010b14664540050042c0d01c619840e070703001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 546741483 1250 546740233 546740239
    0x150a0e040b04061a1e03090303060112021206010f050d0606050d140405030d0e0a02060c030904050604180f0501140112060e0303010f1707090e010b1c020306161202070c05010e 77
    0x1c500d00d440050110f8007005070035900c58804c009003511035482c2200445401014004003e65246460307003906403240c01c1071310381034001603191001c000f013100c2c507000303840e0000c1d0308000031001038031084015a000341d00d00b13010300c0034801d00780440384a0034514810800104032a0715503d81e6a50308421110031100400380300c00da2860f8107018003022407000030075900c41d09003004c40068007101d0324980c81e180c4070240700025403000001480b03064115002c000342005010664061109440d0f203001c000c181c9800450b040d000351400000e9002180d23039000103032000743c0074000024400300c0c10501d03006070000903044083d50410401012080180070710900085001200c00303141554140084110000c5661042039000032030704014410441d42417050f0802400400c00c1000b20001c41680c080c060300340c1c0010310b8850160103804621400041045e1300d9043d500401811003650b488403100341f541048889101045540d00c90010324419500c01031860902440000e41410b03d450001400705003030480041c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 546742733 1250 546741483 546741491
    0x1020c0909030f22060306060813021e0f0904110123040315020c060103061a03060105060a08070903080a021c0302090a180212041208070203030f0411150a0e040b04 72
    0x68041c1c08800d031200c41401d421102c0d0344202c3e1107030759a0240044080a0261009101d00182064260340108119240c03500e461071070303035030724040045420480b840183d003022001517412403c1812602c6816000340007032a403448251040c0104001007401c54048891038004d042805140da000703544840c81e4082c228910707442050f0a80c0b076002030b00545c40700800503071862170384d4104606950140c441413a201c40c116125581d59041c800c020f00703a0038540034803c0078449141200c44c1408181d01341a2200540042c0c64030b10881000c035600c1074000c2c051010401c1c00c12003c00081d101c00c00601158103a42e0003810f8880f9400110864010b000c540c000c1454030400c40701e0041d03118800c1c09800c841041c102c0b00c031900348290702d0801a2190150000142902d141044200407418908031000c0c00c07a666520126602d40505903502e110541d00210700c500c0c0140041c0008050300000100c00a0151050001d41041d00b240c2041e50030004055001c100001c0703c40c505800c051181c9241202c0840d8284 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 546743983 1250 546742733 546742741
    0x606190911090918070b09040e16030c0f060516050109020d03020c090a1a09040c05030712170301120602181309030e03031611040b030a290408030109200d0b01020c09 73
    0x160390b41c00740d01c2002c0c00c041007ca0500c1066171181d004136240e2aa01056480c00310501c034100c003504020f0b00044500002c05640401c8075060b040c2c580d426280d42c3d4507034501d04400d40002c0888003211510880e09592104200d01c0107807214014140041c0c8030390000d21000c42d1a90401c4026080140514603030f40c584a0100c43d203c401003507080050806480b401385545903420b12280e140510707001070780c0500c03034190009080f280660024500e1340c09800c18801316800440c8a00c0310303200a1089141022105408901041c41c0d58001c241c01108215595005000e0b4404160380c40607600720740c414039940d40010310505400403c114644070044002d94545001e148401d0031010105d0405000c40d800f00c28808240d480e1984001c2c4042c2c00101100d00c4114640b801c1519a0b5040d00c820482e54140c0718040300050300881c28a005036480f00401d4216828009240010851442d003031405481c80000c5401e00203900d8002d045400a00c3c201080c2c9140950001e403a010035401240d005000120400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 546745233 1250 546743983 546744031
    0xe011b090b0a05120a060911070c08070f05100c0c09050108160e0c0d0e0601030804031403040b0f09061303150e1f090c08011e0612030206061909110909 67
    0x159031300107118100d50b0700c0380c0300e61107810024407446d0001100d2034038008070b02c0d03031800d24440904090f9104a1582c92043d40b6803003115200e05180c410f9075000035090704140101d2410b10007000d2200320130b20301700b04000e4894a8440c4200d00030360140004565a00061010303110501c0142d010000b00c000c0300c1c000341c0c901f084c06501c03c1c00052460700c0710240450512610101608002c103560200c900311451541c41c2d0806402e5507020340300132503100c800000e490030400804400d0b01c0031286003021860800d2050707594a162a0320903813000342c1c041010001204681c501d05843c0001d540501d0f40c80800d9003103159210100c1e040f400200c4010760125a0105415480c1b10b048a4174400003500401c600d4414a00844180d010390404141d03942003180602e8144e16004040240c0d2004600500c8440d03903039900300d2840303480350401400580000d0001505030070300345043c5070071340081c2c11000c030407039a81c04080d0101c0741020b42c5c1011140000030711390010319100c1000c94000e2900c400c0c1200c9201c2c503c0c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 546746483 1250 546745233 546745237
    0x80109020f060f04030f060b090601020607020705010c03050c0a0f06150515130e0702150601090518091c0503100e01080307030e06090405040f051507210e011b090b0a05 74
    0x400e92081e000001c0c0901c200d40c3d0351055034000c2d03030b01044002c012851483d0480c05407070f02c400c6a41c0181c0807d00000c529602c0043c48a02811582e005417030301909080044981c03c100749415801d0160400c84008401800c001c030201c0503000302c1c1c00c40211501c92400300c0c166408108440d6542d100c0c06001d20282c0d6a2200491081c21409251550341c0000d018104410b00190310120800070b4810070071004540204800c06106944000100c05a442c0401036500c48503a009007604200091590f4080d190808801a000f1101208a80201031103001503001111805070007800108040244520950680ba64001030050032040b0f650700d40c101603c031592409809409000c000c07103001d03000d06544600c4200c2d446074901403c00e104600c0c05040a040031050144112103521901205003800701503030982d14082c4c005603991881041048659a2400310320102400c1c3c400d580f1050751610316000d20811002c0c3c20024401140d18030b43d49409808050315500c0356101103420440c0d00380696104003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 546747733 1250 546746483 546746509
    0x2090c0c1002090f041a28120b0a0c030e030d144008180f010f020c040b010e0d03030b1207060f0c0809030d02010b1018030f050f150a0608010902 64
    0x100003038105100c0c06c0e8024040c00040182d038000c0b01e0f0000c3d4242d40c445420354450503800c000150041151380b03c0d0301400b881c001200181a4a03088804200d071030b60b03160045407080a003481c0101d400c10031043d402d41540e0050040c8984141d46070312604140110b00c0d5540d60140c0480ba041e801811401c21000e01394500034402034401e08001030b152a10340705142050000d64121744610380303030140038901000c40c80e42451a03510510b088940021158800d0000b0569000e555014020ba00d116000740320181404114046c1804102180400f017a280c0a50b440541400707960007140c01e80020050240031000c8580c1c80d0f6040d00700c00303024490076030400000400c139240c600d40900c1020480c180f00c206405446000d41e0315000e40406542480c2e030541209809a0085548440ca140b900c0400c2c0da000b1100034101c40458050751040002c91400032000d44100d0095080d52456400402e01c0350400464803803541c4850300790400d000c0b41c8410303031003001301400b62500204080c290700d800007910341c18919 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 546748983 1250 546747733 546747739
    0x90304120804081b041413020909010e030715140106080c030705040b120603070906030203060604090809030a1b05010804052a13020d180201090315020702090c0c1002090f 75
    0x30405000c004070302040310003e0004a0940b002290035040f40701d40c00042840c81d030310841c10003c651000c3d1400b0b0407118082c8402685c0e5a48507400c650900c072445000806026071075507242c001c0c81074018280010701c60284941d400040000f04c1301100400c40d40b5043c4906000e52003c0d005011042e08082c40e5038000300c0010b46a0b481e6a02e110080356240325a410501c0413820100d50502d5519540065900440048080d18603140e195028041225006c2c40080d40c958400c402050150500303034080c250090040c2c02c0c8902d059803036000b19240035500a0111001d0240a28031007080c0120301c0c4801c0905024a0f10078071904150700c465940d040d401105036100c00c030f058500080d01c0b005844040c201d4001405207103400303d40c0302c140d03070003500080200c0380124284441c080184002e28010340c1e280b94140c44044689045840d05648600101000d00e101e9500304000405aa100c55010f40300e540c0100420759280f10b42000681230003042116841664018050007625a640001648401c0e00a1b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 546750233 1250 546748983 546749009
    0xd390605160c140c1c0b0a0203070c0204180204140403020d051603110a1202030c0f0c0a0e040804090501091a040c021b150c0102090102150402091314070e0604060e090304 75
    0x400d6145007802413401303440b075015440d480ca0300034101a060282d04480d005a0070914595a99028001079100456a0b903002903010401c400061a00d503002d000e170619094900400c0981e203a000c5800c8809a25400240c8401d4000704004c25070b0400031650601d2a5240240c1000d40907140070120303007141ca00040c14458038202045034014108510107105410205d23017610780342ca05001030345030380c00820030145174010210340402c1c00600082d00320744543c02800104025161001d07594007520090011a10f11004000001e580410360240038083e100324600020814103100c1801030f80b00130507000034002c80c00e00080c2d58800d0340114050900b942801d03103060b00111403d000030b00c500204003400c451220049042c0301c500c0c10550107050118020380031501c40c15026100b40501e40e104450007548210100001100300c4600991710485a21820403545c918544000c80b908103883d5400c8421a5205002040041e2030a03007c0c10000b0315071603059100600303110b40304c01d48030f1060740a028109000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 546751483 1250 546750233 546750263
    0xc08010b13021c0f0e07050306010f0303032706021c230705090307031b08060108120a03140916120b0412091d0601120506030d390605160c 61
    0x40f4a00c00b82e4801a00a04002c04014644c415004000140e1181440e1207041c1c00800c05d402d001031a20b05841c80d150400c402c444c0340d940e040300034155103002d15000f0003a01c0800342c00d4901450b20100581c1c800c00d8050788940e0f0054000581d10012144600c1c003904298003000d002c6a04001042c0c509a0010240003e41e03031103805480e1b03031150a5401d600344c03141c01c2000044c081041050380e00d613200c1903c1804e2055481c407030030f170b901d58081c00780c40040e0300250b600d2500c0c40d80040c018030380203c46040100300c040e607201601d001e0301d070f00700c4141c88139030011514849080b1004000d2809020901c1d100b900710441903c8411101d0300c001c1006080c3c04400761100c3d400c60240000c40000c0c0074542c032138803450f1503034480740400c40401d99003103002c150b2905111103030000764000c0b41c0c8207030f60140040840c852508011544511905040000818002018074410b411022040c03040c09842c0d02c403110b61120361416500f1a80f0003400300d610080140000c0c0081a40000800da02c26003104180310700d162 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 546752733 1250 546751483 546751507
    0x703051b01030902010e01112e0f0b0102100b0a03080d020a09090c0e061305060319050915130311030a050408150f06150c0601031410110a03020a09080106120c08010b1302 75
    0x303000c80c1000c40801e03200305502d044801080c842c0c0c41c41440080c040c0000d440455660f0283c514403031107133000d1380004c01000f0301d0034243c0c0c0c4000c0c0c4a0070000d12644000307507203855078043d9034054903840c0440e9800081140086412120308401090098020401021800002001381910704411845100700065200a10390340c060351401500c8010012540c2e400c00c44c2c8802c0c1c04001050300e1821346420140040d8120202007071541d51107894803041e085940d00c41c0d1281d01d9000c202081202440354101d864107100c1c07001c1028000c0c861003600e51036950b82c1800c1c40c25151056002502c1c1d1040c4145040044c40c8820400c00d0b90005801da81141014625042e4240341e0b028192101e52036104020001080c003003101c1e5485130310003064054a030b0140540600d80142d41d821941c61920100400c000190075107c1d81c0101380340103286c43c00380401a1500005429508142e00600c0c4040612001d80240310070307036103410b00400030500200070a211440201d031100140c1d40170111200c4d800321708104011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 546753983 1250 546752733 546752743
    0xb10030b0a050402100932040e0105010614041404050c0c0106030c0f0b030103170903190302030702152811060411040c0807020a0618061d0609070b0304080a020109050703051b01030902010e0111 85
    0x407006200740310780c40149c00e406000307120074410783d0700003002c0c074060b42c3d105100790007180c0c01e440d03056a82282c4480c100d014000a000c02500d00d20794032000b00040c1e640c000003072240b80083c611441280103118940f4140040f47c1a0540040304110010801000020790840d80d6030415102402e810f0340314040040083d040020314116244024031b4070300803000301640480148440d501c05c884101850360307007081d55a80c502078000c8001e054403c4046602100d034000d100c2c45e8180b1045d29001c501c103004000c0e035a050880503142164120004000328074249058000c20720391002c43c5c80d12072070b280380003d0001d42c0c071041c800000d0109982d46210358180802c02e443c2c40c0d44a07030810418012000a1030403400321000900080106019490215125000104940c400c8841d108038090541e03c0e542c0307605044d548507214007425590307200340c8030f00010f400b4001080103500803c0600f807450004120300429650789038140c1d0405261400010050b030b048039000003464130038602060b0107844000c0301403604c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 546755233 1250 546753983 546754079
    0x9060d09020f13021c0b0915120d0305011a0309150406090b1603060b2b0902041803020d2a03021203010801060807091103040b10030b0a0504021009 65
    0x54064a0f440c0f020881c5400619800c0b01c0c12481400d00b941042c0d8030401c032a54010125071150219000c11113440045204140152000f000700030b40d062014982450403440500c2900420b4607200100700314005210f046003000441c901091941c601601c55686400043e5481c02d1031981e030303102040034003141c0e501400705a03030310000128031400c000d0f01c200340740c242845403840000e007056008a0403100780400e40304614101543e003079201c2c65846c007101480521242e0344129580d1281c080c0091780d0f0700e00a0841c8a013100040405010784c5080007410440791503140c43c05e200303100c243d8034000380340c022000b00300c2c1a288076640308030100c0303150403820400f01c10380c4100f9481c40400040b402c5c02e41980110211408001100c66207507464005e00142e900514a6100c494814400074010412061396507030300040c079071100e80800d81c0340c0d5075680c600b0f01c0a503003050010b0744e6a001c000860401c6c00603611150b41c0c1d42003021160740340c54451b110721696818070070210f00e0404450f0900c04003210210580c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 546756483 1250 546755233 546755239
    0x309100606171305030a030902060f0307032f09040c05091f0201060e0f01030201210501140a0b0c06060f0109380310050402160818120309060d09020f 66
    0x10541e03030780d00c005180c0320820403009805620070011400900340d40310803146582e800760103182400501c4c00183c005048100050340c00100c104516407002c1000c9005610900161302d00003402160080c601c4416414884c1180d1491002080c00c01c0b0001604195503800e401110041030100000c503044034903001e01305426410041d05503002d07028110761211002c60038003640c020020039960701d0403205603420075a980c00d1103000200045c005940f081c990100c04004090709042c622008980b00350485909911003005440c01200000280c60300c140d14130018040441410309184840310341944403400900018425402d50900c0074040e40110b006c2002810345035030003921200d5184080c00e581550178000e4074001910300030780c05106a90400c2c0d030301458000006a11503424001480000d600c51000f40044c80c03074203c001c00001740e51500401c40110030140c1e004e071990300d0341e06010001f002d400e40480640c10038042c000e1140c0701d01056400c0a0900440450f5044160000c10001c5603803506042d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 546757733 1250 546756483 546756491
    0x209010309050d271a0c071802090f0f091302030f0a0f110406060f12020f041202010f0203030112110f151b060402010f03150b19020c1203040b030910 66
    0x2800d6070b04200e4403030807410f2940f00c10080701c107260704c0c603202021180121608500860522404d0300c10341c4020301441e004003c1142d51183e105e00c1c410000694036084c424420360006107481303441c20804420301c04034106940c030003019002c040c00507401d4074004000c60040740028400788255a420020034001c0810f400a0351602e070740c64104001c4d00000c820f01034800e0424650346034401c0c2014461881158003586c0c0e540c40413403803000101c0d90656400040c85c0790035020f010b0842c50281c00701c0140020300c0c80111410003030701c45100141081c0410884d0006640040c0010808002d41c102c510000c50380c0200c000340840f080d000000da80c0c603032034503105806c060442c240d0f00064580ca00204003d005200c491081d820b007a0014036034070b0404440081c0002c40340110701d00103d00a800c60a0101c600c022a500700645445d402512a0800002652000c620115010000b41c05212103d4419415162120642c50a0603041d60b288140e11881d01d40031f00001c0090403c0d2820b1110078040c580c4039400388 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 546758983 1250 546757733 546757753
    0x13210207030308010503060601020d0c11220e070503100f060e270606011b1e060203180a0c03080906070c08030d0609150905070207080709050a0513030909020901030905 74
    0x25500c4005001c22000320b5030b00400410300346400554035200d0401640144103101c0b048004076540b80510301c00300d665590b40a450001582c0b200e100c0385a803610341045017a6141a2103032036040da10850040c000d130f40c00074001800704da1004034401940d070a12850102e00d0400b00150000280704603408100000040030074030642d20003a010710002c580c15502034180c066560b01070103844400541d11540451303140340800c43d542c41800401c00c4414055030640c0c0c5244580000d80c0d10440c2e10300f00880c1c00d181c2c0041044441d01000c3d4040b01c605c0710b407070001d203000782665580e0300c0602c24601000d00240390200344050399a40d850125584154014050a409030380c441c90a5501e400051203208224244000460724010a03c60728049110b0041005800d51425269500400f00a07090004600420901051a580800054000b800705a10001d803514040395020100d4001400d6031034a103c1071201c0402182d4400310f040c0550710700a90059540c030340c11700142d00501354584001c00b24082c405c109 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 546760233 1250 546758983 546758987
    0x180609131a010905030d12050a0204030f030e03060a0902090406050408130b0c01110703080a0903021e15071418041e0504030806041503061d03070c03050d171321 71
    0x254400e12080e242c0c02c0f00c1e16102c0c02095105c1c01d00010f003070006050460040000741e0150030458000d0484000180780907100e0701c5060780c41c00141d8003500459078000d411a0b45040c200302840c1e0100504504001c0000a81e000680000000d80301030055900c80e00802c7c184100704c0e08540915552000c2c5a86890b0394403c150300980020900303280d0b40d481c001102c00c001d280d503c1115081e0740d250341c80003140d5171009448801803440701300960452043c841c0c03001a4165549118021100503001002c03103081a944591854000600d40707401c0102103180200c021021130251100b0040c62808010018507140106000341181d02c1030300380300b00107032038045000303045a8011030045000c0d41d5040c0c0c25030340e000e05210940d0303080b40404180c4116030383c080011400d2a4030039680342034000c00514420915407955861500101c4048d9a0004905420002c1250803c0089011000c904129203982c0801012002e82c1d00b000b82802a0b0b86002106201080002050313402d400c3c04290080e107146400f4040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 546761483 1250 546760233 546760271
    0xa06091407030c1d06090126030f0c01050114030c0d0611030c0711010c0c050d080d021206121605102c03010f02040803041e0e010303020c0f040218060913 68
    0x1d450f4030710fa28080544c0c8000d41103413809100d07a0000d0400e0486034070f00790007025245d81c0c100d15044090008031680071410400c0c0001c148020025500645a10754261a03170b00716441030340503201c60756030340c0540036403a2804a220310710700808a0301d62003502128144007014109a140e50070122600104100d8071a5803480509001405000b240c001141e02c0c1d0015190b40100320005000011541c0040001c0e1174031080310b00c0ea0074400e14a850910310300c0c50f21039060303820009000801c0000101084424249441c041c9400302440006040781c2800b00250b2818030307994000c5038081c12980f006180054000c101d4108610300002c1d40c10849142c5180a172030f0605411003041c480d508018000304c1c010703c03d0007914150b030301d0800034600e001e180040c0041c41035100d00700390350041110800080c0e030103000c0200c20700a600030307000f401c80c000550b0100180d400714824541d100302d02c144244210303201c00c0028003002000035104550b41e28041c40026051040c101c440480140c140010b0323003c1c154007051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 546762589 1106 546761483 546761489
    0x3015010c150f060515040302010f021209062a0604061d0616090302150301030c0b190e1c0f051504081c061a071106040501020a06091407030c 62
    0x300b5070340c40560348104180e0170b012408009650b08001c1c14100040148080c4c408610302c0c100045003400b0300b001840c081c00c4045400d1081350b010b41c50403060b2005441001801c80c003030200385030b51607070b04540c1144c0080c11304d0124241d0f11903144041d0100c4018602608465803445a03004030718042d5489001041204440080541c4840c84034504c1a8251161150750791b045041401c0720641c594032100100c84100005540b81010300b514008505440c0b1705030b002c02c400b440000c3ca041d0300383c0ca0042450020f450003001000100300030407035010701c2034050704d08908502588601000c001c40d8040d108100400c902c02060210310070514a25401c80000184191154045003100045034814502c0040c001400700c18000d080c00410b001c058104d071614600360600000030344031046254020b2216844e20024401c000c48500713a06010341c4504d003210007103030b901e042180d942c0b44544 = true := by decide +kernel

theorem cover : BRFrame.Cov 546582733 546762589 := by
  have h0 := BRFrame.cov_init 546582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 546582733 ≤ n) (h2 : n < 546762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
