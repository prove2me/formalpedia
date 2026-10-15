-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5196
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:52.434995+00:00
-- url     : https://prove2.me/submissions/f48c9c8c-8e01-4e83-8c07-8952bb9451e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 934352517 ≤ n < 934532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 934353767 1250 934352517 934352581
    0x40f050f1507030c0c030b0f0708010305032203080c031c06030c060806060c01110307030f0203090d030b130f0902041b080408092e03061205030f0315060313020306 72
    0x39074004009a07030083c10204900c1e441a81e8115820390254000d640c40071049060084800e00164156005846031410b02420350550b00c410740c480c070440100c10b2003161380d24000031a00708d010003880c00842e00705000945901100c1c040c6030b141c2d4001d0b24640c00c2035101c101c848943c003106229070002d13030703030003555a04415046c620f0580d602c820142c661940240f05000102d40700d1001d01070184401c81501c0d55a840342414080035081e034082000b100e041c40d005104002e1184000140056204080e10b4003180c1d512400700410100002c6122480d0104c3c20403408182d4034500760003000c1040e200707440400004041109030040c01d4235268030b07980001e08100204010034189400340c2002c42009151058440000132001e00e0b00c2d01030910f00014441c0b03801d05c00d00a54161280703400030880c016000000d912a5034031b1a40382d10460030003601c600780100101c3d0f101030f8078020380040c16101500c5a6543d050100d60111071950700b03a022407180c454800051514107084003101550910348903004800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 934355017 1250 934353767 934353799
    0x30c0204020d0609090c0311040c1706061c020c1005091e07050a03140105160203030c071a0a0e0616090e06040e1204080708030f3c040f050f 62
    0x6540034520b1103a0b081d444420228035034901c2d01c503040001e48680c140441d01c51031072501d039100d1194036022500c0b0b185820381d10724403290440342440f481c0400c0c5007000180d40da06800194075001e016849038058200c0e20581d900c029480e4010301850305000100d0b0040300e0102d5400055138000c4a054006402589038010007203900c00d05000d02114004c151040c160701d8402080408510350f0040d070385c51a1039034400d1801c41c0207110303482c0c00001c03d002403c0062581640a5074920000c1c00c620901040003902006214681c00480c08286034099022050b05011301e4600c081c3c003d8441d0062140203110110303064610680d00308081c54510740311050010326189460b881c403d0000c001513041602d030407082800043c10311841200c54a103d0b404d64031281001030300381c508046a0001d05843c0d10410100c00c001890a05032044160f0310114510701c030549840001c140f0310480e40b0248841c4440c07105210981561002e00180c0d00c4603c0000b50f1141e40790100400c0340300e112219070b040003400d2030444071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 934356267 1250 934355017 934355021
    0xb090a150902030109062d05010302010f050307030e070b040e090f07091a13020c16060e0d0524070e0411070f0317012603090a090e1005270a030c0204 66
    0x20071400240002042c0c0340584400c0103a407446403400000d071032004c0081311541500c50819529036041101003050313604681c00600300c0c66524142c01c0c1480b00110004080314441e40000100c804140c065a10712580c070895503401da0094003441407400c44110004882c80c00000d007076942080150000c0800d64038104440d00100b503041702e090401c21084051020750340303583c0403401024600002c0103a40d03516104006003850803406040c2c000c1c0c00c040104001440c1d01441601400f88200c400c1070070044a49400d9140c202100401c0014880c240d921080c5902c4003040e00f40710701215180d400e4140401002c0108407241030050080304d00b03040c40500003040840c1c12012001d44130341408111481c4c404200802c0090903445441c8002c0c00840e60844102e0450004241601c20b0004600b01036014002070348480d46801041e803029034500ca5a401c034107007040719200c0c0c00000c0c40100300c1c03400e10f8400c0036042201c66001d041c25844108010701841030000e800f1204035095518441600c030182c0c20880 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 934357517 1250 934356267 934356281
    0xc1b0405060906060a052802120a0e04180203190c0906060503010b130b030108010c03060905060904112206090c02060f010603021c06060c171e0906160f0b090a15 71
    0x402005000054400c0315000703ea40c2015200407e2100055020380e0080c0382001c04606119401c4043c404100d04907000b8410a640da6400c4a0109101e042c1c20090300203108441d001960610600010752a002e80b602c00c1003405034003540e00d4860158895045a05075002c620441e000113008000420840250001400601c640211038054150f5108216000d60700281c01c10a0582d40d0740441556141d014030410f4002c11001c607081c0070310701e48000080c51041c00108041c4c90a4640881e103103455483d41208100794085184101d0390151036180e40d40209114041c0d42603107442c041030501c41c0c40c00012400c2c4108100d45905107181c0c20008120301940020345e0305103854465040c0c80a881d5000e0180380080d241d07540d640740103c0c0203401d00c01d241c1140c070418100130020401480034824410000d940031001140b16903540d848180300407a0ba00e200c1c1d0071819810310744c607001840030402110000c88a5501601c03c60241d42c444d800169161200c04500500032039141c0c88401103400b858000c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 934358767 1250 934357517 934357537
    0x50c0102070c03140129040e070b130509090f0a0807050109020d0308090607090501021b0a050402070c1701021603201c02100e07050603060a0306020c1b040506090606 73
    0x541003074280da695150581940e00120341d03da0300c8400b00103209200b40310384040105010488100160081c2c11500c0d03e001c250f40050003241c0300c042131580d0040401038100241450031a07140c1c0d0756640340d0b07601c54208640c0034261069829901042c00d8210008013840c42140b504d0140c1858034040d918101583e1050004403069525a5005c030b000d42d542ca03410700c0035180603032104581d9141c4500000e0030304000130300700004d00103004001c1c403060741e0000d440005120f640841031080c07904100002c02e4020b0742e0b0300c4a540103000244c180c00f08051400c00e0803c40381d003901040c50144084800714240d0095160100700312003560050b41c0402c4c45031803071070f0325026981c20030031001518070225410300d456501080440070100e50301d070045642c1044452424960014100304064180303d0450700e41c042885000d20405010020074a01c5e91a1002d40e0019988a034086584d40b07111845a6202c1c03d103d8840703024403c00d04082c003250300302401130740d1013244003c0c0320340d0041d5203400401c0b445030060301d140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 934360017 1250 934358767 934358771
    0x3010603090f0f210309030207090f0e1605040507020d0507150b1206010e090f060a0c0203090a0305060609010b040e04060c14120907090603120507240c180605070201050c01 76
    0x20501052100e003c0e1014140034000d00c1d540f2000205418140b003e44104400406143c9000040840c0d804180301e8156034200304080340f42405c04400c10082d120454117540c1c075000d090009901d5140e84a103050464000b5a810301c01561005002d076107c0c101200120702140f030410072080013400c039440c1040082c100810012761403402d100416035003150030702c51b0911503104500500c50b05100c550116401030768000144901c00f40ca4080648440700902503020540c0c588000c414010f00a1041e16031401c0e020300441d001c907690b814030a07a0380d034080d11824001c0c0b80190000c18003003111000c0300d0942d00d02c038901084079100c9a89000007403c4020000003000543c0680d8200b512609005190140b8a0300b04a0034a0501385c000d07600300b580a138001c1301c0e16890100308100041e100804400c9420a03420711588440203410909824100c0c00c107070104820b16582080e482c00002d501010360011f0039a1505d400080404999088034441e02800010030380900101d801588524010b0905541403000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 934361267 1250 934360017 934360043
    0x60f0b0c06070906210f180213020306150c070503030f03100b0a050a0c0c180c1407050a0318030c0e01080f072403090611040e070306140906013c090b0301060309 71
    0x40720704441f41c80c1402c10012604503c0541540761101060070100c8041c501180355043c0900003400b00c48224003440080c03c008101180b09800c1449164000c0c000a02070380c0d079a14220307404c40860343c822103004042a001030030210340704590700e00341c842d8080c00e5100c142c5410300c0000b003510301c1d40c4007610440341c14070200e2010580381080808849071540c4810085440c00000402034010031f6102944031150009004201c0440d400140e031a135030fa40c06042030060500301503044500400160000b0f00305070000040042e00c0f1015503802d030304a42070001070351421154805859142e002e54801c0c400b414410507003000070304405045608106010781400640348590380e49007020348000c2c01072030320070342c0010034208184403c800326030790b126615250400000381010b40c0c0c110810843c07100345004004040c0044c0d10359002e203130740700144240030902c0b407644003072945103070704056403480ca4900b4170003032009010803140541040c1069a264003503a60940c3e0814808400a20380e94500340d40700e02050398 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 934362517 1250 934361267 934361291
    0x91a15040e3903010218040203040f0b040309030303060b1207141e0703020705011e0318060504060b130e03160501140c12340201060f0b0c0607090621 66
    0x30b86070580401899010800c241801d008a004508810070701030390040000ca61031004520240035541021140183c403921541024466880c1c01280281840000da05001c10325170401070900c100ca2007660180500d50312041c00d00854000da9100c00c0000b40d00d0808a11003c0c020baa141031140303030002a2b9810080c07510741da00e03d00b0340003540c01016003100068550605506000c0200980020300302a001081e80082c843e83d070b840c004c0151020076903200312040a0350032004a008240307400007824000e90805080540040a010b504148100c00e034411025024519010301e41e8080e22640107181446044018111003400d0350404913a9075580300d608a40c0781c01100803090042c49600c00780d07515a16403007111544103101800f4203140c3c02240020b511401d0b01c1d041c030060900707035002c0543c100e0040b03840140e01624268004550b4202040320105140c5040000380c00b0440705c03901112066142c418059a111070700307001d51030000301c4411803544020140d0800b0600240020070000c2d078202058 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 934363767 1250 934362517 934362553
    0x606060c062707090e100e100b030a02060309011406010e010e12070b1c1a0607030c02010e060c0a030e10080615120f040525062007030303091a15040e 66
    0x28211000140c5d8560b00e40c05456004c01040c044903801c0c0e00f04004070011121840c2c1c0d03400b402c54003501d03160740fa0041c05415880a020f00d919146e4041e18094503402c100d00c600f03001c0c1801402443e02c003804240020850340c030503c10307001c8002d01a11020740c03184c8023000344412500c9800b1002c10600c00d80000040c80883c1c1e00050080101080c0740302c282d412440c144009540a640b200d2601d0030150031646080e517241e5044400c803951508000e19040000c2c070041c0c81030003000601d04d60000c4041012100c3d52400718600f005144255511900e60f101c4008201044000c0c0311b5120000300c840c80080c0f078a04014008504202d0742195150070080040307079401e80d01d40100d40311000600c6040c18801000300800070303414100141000020b40040c2c145004030b60b1209071180741e0401401c8150070540700d4510001c82c06a00f582001c3e0345226441c5e003005809442c8800c1e007141c1c28070040c150b024200000c011618001c000b10051000500341903c20000a00381026009a503809480b410749da007080700e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 934365017 1250 934363767 934363769
    0x50a17071211090f06030723211504050607081e010609060906110606060a0504030206041d0907141e1804060509190615080d0905030606060c062707 65
    0x10300c0544010b840800900007440c4018024080400d442030030300491355404a0000306403140c654100d1042d8000d58103401e403900035040555048038107405007829983d4032044c0358486603455400c803281d40d40b06030003045000c0c80c1100c0141c040d0b0041d401040c0610700c21443c0d0b940082081200601c1000160920000d80d030003a440000030529041c81045029005240d04008020900300759a008000fa80c040361242d400a200d0b80c070416002070312007182c45c0181c09440186401402d03a0751581d8a601c81b00c503001a6115040070328442c20b10004600c12000506c0b4001d881d1130205040c03102a0b40d0042c8500c01e42203440f40b8170400030041030403016448034040000b05180782c2052191034241410701c101296400361042c01c15401212400368800f0784040820303003480d03210500044650001c1c02d426451480750b0800002405005110303e07a03a68051110f2702580d07011400d5130f440352070301d47c100310442c811043c400e0580e0304102d00054020221080c0c404a4490b6807408001401940a480e410450f00e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 934366267 1250 934365017 934365023
    0x603011d010f05160c0b060102030d1a03010f0204050105070b0613051603052203052802060108070503070515030405070837020d0209191b18050a170712 67
    0x940d648081034520385003c0da54009000b10522600c010200000038055014020701a2540e0400004101d050b4030130000c441060038004402c101c0040c010203580c0c0508a01c00232288250308100c0204016a1030f482100d04680c016101e42d8a80b1000780e071240343c0d00c20000c0c180b0354415040c00c140c2520800740e0144038401c1c0814100f80300d242e0707800d0802a0450350080d01d0315002c1d031103406940c40c07942c150b0190600007a4160400d00e0301da010760303440e000c1a00c1c1c040701c46215212040e6050745402e44c00280007416104080700756440c541d200c00900d81d980075140b040a50001c0d140c92291018102000150b030040d008005840c0c1c8542c650b40300901c1d0004207898034000b48084070682543c00c002c00170080700001c810b4403070200300b00250000b580910300341701c0180c410700104010071541c5080c140041590450100d042c0030100750101143c0841d14103040e0307603000c03890503070610511200b04030030003061390b400600c540700342414a040d680a0321140010008648519180415001040450400d060388 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 934367517 1250 934366267 934366271
    0xf0307060b1003060f0501110c03162c340207170a1208092e0f051003081b03031003021008190c0e120615030706050403020402030603011d01 62
    0xa10a070500c604074404856120805181c40820310014050314005811500c0900c3c0c0150921901ca8059043c00c1d51215600d6051003030311031300520034000c02841001c65900382802c1c0001244108034102e0004000400b12040d22a10000350300720242641b03a84481080c450484c445507000150001403901082c2c92501507400460104112040e0f010102c5500c50194040d20b000410390340d400d07400c4217540c10301009003c0010002090403004010328058107466940661000b0688220289944aa402080b007035a007400030f2660f039000300e0301845005001c21602c1402031451034945201310741050100c07180701c103840c04046500d46020401345000e100c0310007011441d5407852040080d90303001482072009000d11340301000346045408101403000000f40e00c0c041400882c0340d0003140c040c400d1399125540600b2007944250203000c0010301311301c152041d16228802c2070203101091795407081c521402000403070800c428401400c00d5005960000300c0a40041410344222078048582000359141c82c10342d039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 934368767 1250 934367517 934367531
    0x509010e0601090207032a080a050304050d0e031f0609020417012406050706060e071701060206061021090f0b1b030c09030c0603090d030605061207110f030706 70
    0xa0018425503006180c400c00441c45d040c16994080d080d0304460b40c4031000e851400c480c3d40c0e019944c03010308a11481d408013281c3c0c1d8400d0200d20240558000ba10262030501c119462881414002c001031501c41c80000d0081c40840c40e2030542c40b0001640307120071000151143e400140482d0721740064005440c40130715a02d05400018842801c4a030f422003d2110f502480b107241d100d20100500b02c82c19075019140861303486800c2e00b0240e002d014654014a42c40442d0000c001e003032030340203030180c03881c015060b0713501e56a90365902c0490b40d90b001680c541d54040040c9079095a06405494800d0280e803110886601d07a4000031800d8007200c00b144000d031085050085524100030746000b483d43e2004080100c161040e802d01c0b00400180001000b288540d00000780e4002555010031640c828120010032a036903a140040120f07850b08040711842c0081703800d09001007400d00e405019030303909070040b51400025985240342204c20700c4040b09242c0702070040459218800c4004d000811081d4003c51001c01e03c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 934370017 1250 934368767 934368791
    0xc0912063d0513110a050a030f051909031806090e0a021303080f16140c0406030209270a0803100602060603211605060a050c1216050409050901 63
    0x4031840292032962075400a8403240d401c0c001810201038800569400312044202920240104a500348a02010700003044101840c1d52280041001d0680e640d401c1c81a03202d01c03030545007035a0080d0781c0c103022412843e010300a044c0295110b0441e50f40a0710b0200500f6040750190b0060141e1504454001101070310240f01e03945038642402d40058071100c045242030f13418070f840b036400b00e1103000062001c20001960890b404902007900d082d610700161ba6100b0200c1c515000307202082d041403035402030141220108552402c1e204080440760060300c2600c0540e41d0703030150909428110703030320080c624034100c0140f03122108211010425100b05030702e541d41c0c200b1070907940d04625181d020034119844141040100c5c0c0740800c810007000207190110490368a00d102c00302140c041d8200040e07403403002000c0c040500000040150080024441c204080c2d241c1c800c0c0000d041c80703841c610401c1c0c0300b041c002262500d00101c01c0544090010f290950809489418200907a034042d101d10b44260744a80814082c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 934371267 1250 934370017 934370071
    0x80309030d0e030c190201170708040501060501090b030f0c0f030108160f2103020c1003140a09020d080c03120f1b09031b0303160f1a010302090c091206 67
    0x40e07403810021401d00c91108600d680d070b5a8202070842c65900e18480071760071a4026001c0b031502070a0350a000d042450032090040083c2c20850301601c05608154000541c1d50061800b0810f130b60408440a1030350740c8100b0741c0024160040c002c2610a00204a20782c115610130010354007030300103130000c5c240300c142c20052030002100e280c100c400c5094440c5010003010600480003000120007001100b00004503040c00c1e0b0618084d02e1030316802013807126005c50440c0d0300d5448a26004540d580403d03207034554400748411542d8130341000f0340005510805002240f00d1101401c182c1c3d504608880c545115100d0411686100361481a0011098020304c00300c00c400914100b0740300801180742c4e00384203104000030340e107001e6484070045002408001c0601903d0500407150b2802d440d101403400144140b4086080e0b1402031429101e861403140c180c00c81a030400c10303950413031390020400d2190303841e64101d203201a0320076107141c2c0d400741540c0041140700c007052180307a00c90401e880d0150101c03c816250590 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 934372517 1250 934371267 934371281
    0x1d040519062310020f0105090309040f0605090c18100c020301050601021539071704030203070612090f051b060903030706050c0f0705010b01120c091809080309030d 72
    0x15121808060119503001019158020403808464508443c08007000503403c0680c0e160300821254203200410448aa001009103c6040c0944040010260381503113002101d420b40100b90f031025161011800140304640075102d01a10100841c1c0aa849000012222009001c0e0039010592844000d800d40c50284112a0702c1304003030001d0020311030900390186217494020030080b8180c0f00402c85030701220b80058250540650402c1040780c400c20301602d201c02c0c1d0003c00b4101d9000000a1b4130301100607800007070380d045990203030040c6081410034400b6240e40131140c1001e01419919003650002c912011507209055002d40301a20800143c6c070001080003800514181c0074050800c0203804c1da0701e0010845d00d003660444c900160310b07110007880c03240500c20392500c410300890101c0c0104c180070065200415281e004d0302c0340c44024442500d9003080e200c50002c084007049501d1030070096450183ca9001050003d2500020807211940d81c501c41c0f0f4105403980300a036440880e8440018031036100d546 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 934373767 1250 934372517 934372529
    0x30603030e0f010f03181e0506090d140d0e01091109101406031e0c0d1407300f050103020f1903121707030b030d0f0207061d04051906 59
    0x148201c07140a0000e049071340c0010380c0904141d0f882d080d140100f5010550141201d90040900b186654000319100c20049800701c1550741e030213144040780700c5801c00900e81c910345115458100d40b05444002d04c0c0515000500311181158540140c28800c400a03c070b151034a0f80304003008140c09500d03600303004882c1001410100a00d0707a103c41805622820300c00e0010b19102119459035031f689801d4414003880c02d078410384950540040030f01c1040321110010340490149114100300300c0c5904c4460603001e1005642032404508505082c40c0448404514401442a884000526422000058070464028600400c0c80c1603543e40180114a02440320444528044072600a600003290540764120350398400240014886260b218100e402162551903040005080740300b6482c00e041c020340030f009152102c6102c3d00510b038072200042d004150514102c1e000d9801402c2450420000b0b81c0c0c540d060190340d200000544202d8091030380c0d140500351040311812207000242d90b42641000540c0c005800117 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 934375017 1250 934373767 934373779
    0xd0e06070801091a04020c0c04051e090d08040212151e090309031f06210221030301060c020609060a020f1b030a02060a050d0f050106020c04020c19020a08030a030603030e 75
    0x44810b8000000011304010002c440051b5100c003500c00c00c0e813620360403035251030b04181083c040000000760440700344802d02e094032541d4666030ba0000b203e9104c5280208080108030400d000c9405420269580940d4040820450f507030748084141041032440115212000300d240142c80e2584540201407031900142c001004504141140001a0b19061a8a03c0444000c12011044644200d5401060052402003051000c5540e0940c025440c0d040315035003603000d070a4000041c1003020300300500400c0010040007850a5900741035040380d03510714890040c0e038007260a10202e81203945040083c0084443c82c0c00074210002c00500f80340c01c24044088014603117070720780d52054558402003960320788030380c0c101c0b070540c0d440407040c01c142c030fa9000d020f400b280c18074507000724a103003444164087c41c140d8002d90200d0346214040ba0070032080c1d100702c2c444a040e0b40c0140a00070a09115040c203001c4031840109800301050b01ca41006140d81c01503081c2d00002a200c01b0100207154005580d4000e10f01d01781e0740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 934376267 1250 934375017 934375031
    0x1709030d0e061f0e010b031e0c1305010512060609060c01050c0301050a080d0207260307060b0312040513052809030e010807080708041403160b0c0301030209040f02060d0e0607080109 80
    0x22403130034041c05114100c8811000030014817911980700e000340ca98501c502c0c528105040030341c410700090300249458a042c00103041c0210329980118140d0310b1012000a070101c140d80e41d042848440d401c4206031075003000c82131145901001d42130080780c0c450a8042549600d035031601d0b0030001400625030102c00d1641100c0c150310041039001c5041410b40d0390307188000002000c2c1c0f5083c004c41e080403a51390019800f02250340c60800229400140d030803402141200c8010f111090411201e00c500d216031503000f070890f0020590040c00b900240ea00c02821000700486e408954030701c215469841b00c4511507181d4503c469001c05030083c4480a20036000c1c64a10700030714060b40302034006240988901c0a100c40c1c080001c1c100850003241d01c11041802d4152074540c5c10040d403a1001c0e5500b407204445100204001417403450100058078100d0f0740042c00b1070f06039152607c0390800d10b00144016a0001020440d903904100c80e03009144840b25840c00410540c500500020429141a00b00820081c18800c4c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 934377517 1250 934376267 934376279
    0x140f01120201020a0f330b011115040204110301030b180a0804140d06020d151205060127050f01090c080610141c0b030706090302011709030d0e061f 65
    0x3601281081c0c0c803485540c00f00e13000c0d0501110701001d804503062003002c10018412601b0303042e44d92500d802c500c0030062002c04c0c240c9006454a40c0d2503110205c9550100e541899084d0044000c507822500181002500c1440f868520215a0098100362441038000c004e2164200c0c50780c0f007040000c051034029220403001c0390364080b000d219510490014090484003448550707141458040741c0d035440482156200d10a41d8580c020b4018a5158a6001e1141c0c0340000c6226040c06040100c552180180107903a00f40f500c070081750002c0070910690501304039418042120b0a1144d0350183c41d0030300c541d03e200c3d0b00d002d12800070385200d0100c4104210300827050259640701c9100980b08c900c62414400f00f16551000e03c070300980100030084144206101440380403106540c8400145030041c0c0c140c89505454074010b490400e40381c0f02c02400200c00c101810b05101001c1000e50b0001042c1007568a8183c0d00400607040c2da0641c007048040b0740104081c840c800201011030844c0002c000e21030030101d89014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 934378767 1250 934377517 934377523
    0x40509131e0201030b130506040b0303040b0a051c0204090f0f0b0a030605181e060f0906070503100e040c060e030d0215180a03080601031a0d0303091401140f0112020102 74
    0x7014801564000c45219421680a9004000764004c0076110011101c1c2420074140945400d42c1c0040c01a03142001d070040c142408004c035015101d89507400c41c42c02695145c1214654401c1406951420805090070074164a500092000340540b22001c0340f88540001c41108489603002d0100005151002c0b84683da1500715052040340d4108100013440d6a490300340c43c1754498140101c88d241c1c003491203038205e8100d120500c030703900240350011100f00b5910b4940800a070030054881120300d40c4010005400c8520410042d0381c494291040840340543d142c10040700500213850441da211b40c0da44040c8500c1c0d6001e14400410340c005c4009004080380b0312006900c818078861555841049000040c0000c400310203040c3e00805894200e5070540c00d0b900f0020490901900d9181c00a4100042d82c0103034a071240900702002d0000348007c1100340e05a41c00d80003011000b01c11900d441d2b0300c00c01c0311581c44080c480c0d03500592078440304030414581000d80303420b820380503085607407601001a501001b50343c1c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 934380017 1250 934378767 934378793
    0x206070e1311040b0706020301031104051003061802090108031e160609081e03010618031e1b0603020c0c04090c1a0c012a140d091e03020304050913 65
    0x4400003400b032070301c1c101d4012a03c242d801c040110440029000704219880c3c0c01541240c1c0606d00d8181003401c007c00704002d55a044e1480382c050340c1282d5083c80450780d00c0e80101840002a948607414213041d5020403a041026403102d1825003010942080311030710301002d1034020180341125454610700707a080300f805941e107a00142c1881e550b03242e4082040080c0341259003040310744001c10bc0c81140400c030004194424081c0900041d501c0040340c180703a9800d50080d0540ea4040c005075500c0300403001c40b81142c5407a4800383d460341390090103065503000740f107141c00243c111698050b075100070300210149004018011341d40541d03d002e010707001180706400040207440d42c56580c4c902c4e03034040d6841d02e503040c00740d0207000c50103510b01410b80300101072808000b40c6039908030f02910800c0403580740070790704030040320f0601088600c2008071200752016a48205c40640c840d01102030003c502d24844101c1884038034044025910002c0d041c0203a1605240c0c02d0b500030900020f4104038611681c46014a0f009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 934381267 1250 934380017 934380049
    0x13060510020d0f1101090f06060305071e09020c1005040506010f0b1c0914030a030203010f0506091f0516080a03050c0a120b06121311010309080909090c09070c030206070e 75
    0x40100c45858481c000c2d0086142150010080c1d131407c10b4a0a000700101030600c03084a9901c10300c080010003921603018242c0e507002c034000e00c0c0c10252411200001960051010341e02e140640c0a00000c030078442d1042a004074000d000409041d810104001c20090281d0041401d81c48140106100c11405001c040c000d48484a004140c0d1401458100001ca00102040ca0280004103403010043da15501075070480b4001c2d42480300c0240e41d00e00b072010300d03c2000d900c3d54018203110b1091440741c001c028444e6031a0040c1c5400c43ca80340c04142008a00b4001e41401c03502400002088200170798540241500f01e030100000354900260610041e0011140c2c25048108540741c04511103155505816074404002803c018409441c000400017407030860410100c80c455003c03a03804000313502c6445200061540411010324000d0f60004000301c3e0400204002d116100b84520100b943d203800400d5030103450306403500b402c0d0306100e19010303060540040c012810009040d084090070780d40c011204080a02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 934382517 1250 934381267 934381277
    0x5060f010201151e050603010303020d080a0b06190e06040b1b06060102250e07020a1202060c04180603050f030705060a11070204020d060b03010b04030209011509150e13060510020d0f 80
    0x2036018140c1015130603809982e0007000400000185038021800e4822246d0b207039903041155495144810448010032174060700716038140700412a0f00701c152040c460584c514145004040e100c0000201154400e800001c1d00c04004a404200031f07000c485065400300b44072001d89094580000000e5440f1003414900703003902c100604200031100260b03e40e00107030400602c268114585900081d582c1c66403120225000c48010f40d4042d08640b01281c0c1a0086203400c00c1c2516040c50303e0300601c04140040c0d1001c42e80c5595500000c0011000c01c00d130303001a12000050342c4c81e0140c41c2001c60510100404c026141c2e403c0c241280a880740d010111000f443d81228016100c0e0704840c41c4100401254111004100d4000700124042607104040d1007100e100302c6a251040e80c0b90400040c9241c4c86212520104e013820b0010b00803200f031000102030fa02c41a00d841c1c400d5400d264001110409203e0f0500c2070140d8401051006040c400c182d48562401d038001840080d6004d00700034004202041c4601c00c100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 934383767 1250 934382517 934382549
    0x21501290706090c082415120109030f1d030307020105030406020c1f06140f150f1809010918080a021e0609061b04030f1502030a05060f01020115 64
    0x40399a034151031200b9085501001000510725003006002014060508a0311408150805a00700341450318000443c10a00851548883d00340070009035041042e107030b01c140158080355007103400b44500c100c0d0078026600c0150100240d040540b9680340f0310701c06080704074001c00da40280d032400807c565400d6420300e8095501c0e1f0300c60421800a0041c1c0600c003000703008110101101c4480380c103268032707422050041042026039400d80080040069036115401c0b508129000400e031500304014250544c029050714940591000d0708201584040d80350b103104804520302c1210f03803d007898880c1c09440004410084845140000c0c904030354456801803800d0400034882d01450701c2031000c80b40f10402c07091203a41d881a54480541c8800d4216a0800f80b842180b00042484140307142e45500686a4081c4600d40341c20350b1078484402c010303400b00342e031150031442840a2080c01440258450200b071714001540c1d04007901089070302d1442d002d0007411a030401c244040040e100051040440b950002d040c041a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 934385017 1250 934383767 934383839
    0x2d06060f020708121321210e060702030f0d030e070504020705250801110d180c0b0304081e090114040522180f060507170a0b0d0606090c021501 63
    0xc00d00c0da084180241c0620150b41d020343c2c881d07031070704100c5c2c0e00c2101910112200556030407d0074076401201400110b0750b6000a0362400c1c01c10013446014009401c3d04c01d407070222056030345010400180c62001039510a007a440c124414400b010150200f26825460900341c0c0d01d4881e0b443c615000740b100c0300c84040105c140c1249140202e035004001c0d16000b41b11020514002c0c030034a0701b2001400c64000e00749842e0808a525107070541320712507403001245032000d0070142c1d501116000108102c50222041040c8280c1a580710802e00c0203480c07a4034000d58900c03450000400001c1d41d02805c100500d0203100070320007030b5900155100e564075981010305a102c88600803401a00c0c958000c8400041d2003d411400d111501002c1c00c4c090340280707424081a10780c503504503602c400ca40c03180b5402100c4100400c00c00d4209400c4407440c00002002c581041c4281d860781d40c1220a00c1e0300c1110002c0d03035400c0d2003120a40601c00312204a488140c030019a6152108490402400100c000e105041b1072902d8101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 934386267 1250 934385017 934385047
    0x5160e0c160606081e0303090d110a05060c04052103160f02130510060503010509060631080f0c0d12022401050103050a02090d0201032d06060f02070812 67
    0x1040d42c0180c024002e441c0d42d80000c9403100001745809080305050407070f98080c941c002080320b000b80901401024030f003080c00002c0f901c40f28480340c01c0041340614850140818010012103009001614450741e50ba480d100802c80846945c02e184a00c007404001c0803441c030b07103011060304c1115000448121450703c0d2440d0a1224a80651009500182c1c5001c0c200c1720b0851944510300c03404031680c1c2e000d040e584818054035035010134480d080e840b0048000062042c20040050300314030315400d00203004158038020f04184d44101e142c9607c500748240d1000c00000004020f0300592040f15009004c0851810000c203442082001c006480764517482c40a0715220b208006204055402403d440041c180403112583d28040070310034203000070708007000300e04160703914400c0b40c2c0718800c01070a012404000743d0040d40a4001510b00b52000c810710640d140c0310fa10100f030200c030302c651010000103c242c1090300141121040301460300455001c1e41c81400304440004c0c02c80029849031500c903403104058080909 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934387517 1250 934386267 934386307
    0x8130509130f02270a0b01111b011209120f0e121c090b0a02010b0108061005030a09030306051203040905070809060c090409061103090d0305090c1c05030a080405160e0c 74
    0x1340901c1c1c0c20200503240403254015a40050700340d840f43c0000403039080c4240d80b56000401e066210640307a114003120b60048410b0a8402138500300410800c0b019100c010644506101440204680716617240c8142c0d407000c00f01c03410400403a00b40c01c2c481140c82d2016500d810400969100601030441d0f02102e50040700d000f00200600700b06031b0354039000b20030001d0207000c00c145154003003151640030461601d01088905014111a510745041d5070310001544045c2240c03810540905659a00103e200d0315800342c94001d543c2d01e000199581c510b011028422a0001021501001140c4050042c0038001040640e08020540f00080d2980507500c00240145131381e901c0242960700d044150420303801d601c0e0107144603203040c0b03060380d28050074608141c050b500100c1d0601460b0300400d80026071840d000b401c8981c3c1400001d241c0c08180c500d40e40745469584109055004254100104070801c2401c001050500c50242e0380c00d42c0f580c0c50100d10f5004090003520300003c151002c144881d46145e0710b00c03681 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 934388767 1250 934387517 934387579
    0x60b0a12081b0d18060215130303060b0301260f030f22030c0608090a08040b0a17010b12091501051017010e01060212090a03020103150308130509130f02 67
    0x1840f004590201900c030106001a000003650007010000304d481c00032440e0000e0f24880d003c0200c2a54400d00c002e02142c9500070201c00b410b68a46001c140c072000140030f503001c1c2107440d2041220f8803400f14042150584042a0f000592020103509000c50000c0b0035076009400440555807503558a0b03500c1c100005210f110366862400c0301700e0000c140400004034100b01c032515200c4240b15100c089540781c5a4050400152000c0c50410081142e0707818030008180d0340726640750000791940b08954001249900783d1260383d240704003088405e02c43d60302841c8141c020760080004d1400c0c4080b10403c2c59490030501c101072040e413005240d40c2c41240500c04048403110301a403519403560310b43d11007101140e028010b0000512881c10710203111f004000c225642550002c1c403080c040340c90341e40110080c2c0f0003501a4148004000c0000000480003000b4120003400b40160030b41450800b8184050303480c1c010800034030144550128408211349100d56070a2075010b075032a03402852681130102e041d0344003643c48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 934390017 1250 934388767 934388773
    0x601171c0c020a0902181f080118180c05010f08010e130305070f03022503050a0b060d02130c081509070c110a170d0201050c0a03091a04030309060b0a12081b 69
    0x101406c00100c00080b090b90048440062482d400343c1c0c0d0300e0b0444150360702240030819482c01409200048030008082003c000e0011400e4144000816041c241c0100d0481d140c50302c4030b0381807000b50f8104441ca00c40c00e9051526403815071600b0316070780074400e0160006184900e580059030a0501c14002c4130a8541c01100a011004c1e643ca4020b55410030031300e03080110b1176521512240e03100c00e11413080c1181d030408018461070425880301080d0607005003a40d41c0c4100e01036089130058490709026200040c0c2c4890003d5140211003000e0440030000380070310a950064110391070540e88541e03645401c00340c0d525000d40007055a18000d1a1143c80c61102c0d5070000f03d481c0300041040e028001c0d0204480b0301d40903a062440b10031400d83c2661000e0f10200400c141c02d00024461600c80c0e800000e2944c055200c1010040005042050f072801c151002e038006525542c110050250b1f40c081c1e03400350740e002d8400111013031402c540344c40a803c00304001001c101d00001d5800030200324141d4406000d07007040035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 934391267 1250 934390017 934390027
    0xd020f0a110c01360e09061f0b0d05102706050d030c031407080f18030c030c102a1505010e01060f020f07080601171c0c020a0902 57
    0x1d4219048801030520301c1c410300c06409442c0d48034034001c040c00d0010300459401411440d510034081c802d07000303c0309900b0204660014001d80104009801502c001e030281c042400d041088051810184650316a1100140030800811300c9400c22514a0400ca040c000340685604440e03818120595104c400b45c2c100440c00c0519a0740c42c080f000c43c11724407214080140d1940c0d40180f01c0a05031031800a4081000d0308400b00100b0700031001d5015404007841d40c94646202c0e6a240503c1d034000102a290800c00400c100000e1068550010318000301200184280c00396000001e564400c030280d100c0c0076036420021403903c3e9004002154941c0c001010074003c101c800290820444c1c0199000d4805402c0b00a180380c00990398442d481c145c07441c00400255613800c000c0240c0e11004100011000c500c01c0c44004c8680c810300740004406810341001074100c652601d034180c5150380c40c0300443d580c40d030010b405880c1c890008119003050319285051071018001580002400048282e00200d041800022 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 934392517 1250 934391267 934391287
    0x170a0b06300c04171f05180f010603060c050c1c030207050a15050c07110418020d0b06010807031512050705030a050703061103040f0609050115060503061503060904080d020f 76
    0x1003e042543d4041034110320988107040074550b0358440a003840c5d204091410351080420351600200d1303210318420100d410b540104d0368460315003150f1003440da06c02d035503030b410500030040c2d107000d404404021450901d0130201a07401d034235100c0c9507070406442812520079108a4150187e015502c2c01c80d0010305503901d120302428030f622054002550186da041c80c02c80040c606460b003000741c41182e500038482c000140080403e00006002d4059100c48982c1e8240d0350000590f101ba0080c00094032a44520b007090900b44000341480c81d001c0c00e10710070705060410481ca003a0440d240b480403681441c01c0a404442d207824803d04000c0c1c0c81d0404c1c0d4150140c03500407428005d0004800049a2081300308100d1a40c54a98034003190109480050600700c40f000ca510106500d0707085a2041070060000207020b24140300c401d82c0000e501c0d030001012900200c01c01c0103a2424a00484ea007644900c00c4500d90b142800004520400c010001000c840303012400d00e0b08001e0707c5e4180e40040443c0c1c0480e80d40d44030114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 934393767 1250 934392517 934392541
    0xb0d050108070e010303020d080916080a0212120702040b0f060403050714012d09081e191e0305040810060314070317180301020406170a0b0630 63
    0x10145414034455008005000c83c1041040d42c102d903010b60190000e105001d40840b49050b0282015045100349030380c9828203a1100704000040400303000401c035540452062207040c0c0c4000207800181c2d0004c50142ca0000c040000312070030305a0440340000e1099504000546030f03120300e600305802113000319010003041000220300003682c1c1e58010300c07081c81e256440110f03482c02201155440c0010040d2380d01c00504080c40d000d69081c003460500740042e40d15080180e2030b100c0e6002c0f509040c4d81090380f02c000c2c554028045442c40b03a81c10614403201d000c06494100810811280040c5002480c400348020306100d0300c04d0300c02510080059031918411155040b0141c44140002d440c888141e0340f941c2c40700600001d00404483e801406800700e002e501d80c81000380e07008078204041d001e62405200703060390f5003031004101a14017602d504160070f96003010125009401880010743e24500300161009980f41004d03030303400780c2136030f18156035601000c14001c111105051548081000309810f1028200c008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 934395017 1250 934393767 934393769
    0xf11030c07020109150c082505060621060f041a100302120d0e0603060a0905040f140d02071e0e070c1209050d1502040806040809040b0108070e190b0d0501 68
    0x7684c03044a0181c5035840902c4640c00301d40c41c1d0011580180c04140017803211009482051174582c2d40400309528090072881843c0003c008581c3c03030704101c08001c407600e07100030001c003029420035008036000004d10076070384c1d03c2e1005407900c5e014183d520002000c1000d48000c00140c4403151042d4081802c0c01c0030400c2d40991113000407441841d5124004142c0007000480004510a0781d4030010a0716420701032180540c005455550002c10454001c90000d000c0d020f5140198814180801d104140382401d00d2000c103a260b4400c0f040d040302203e0810b056001888600384c5003100840d0403c403044000500c1a404207902c00301c01d820149081000c11070b0400f660234192801203e200b25024003401c41251103600300d004003580030f1440e680c00c034080b030a20003041c902c4003030701c0074010320301621041d4a074a84241103c00711130080001483d40c5d014203060050000d02c803820f0074071183d641007058014002c5031a0700c180c98092402040c1c00c21715130741c44483d004010554a403419a40720b80d0100b2000192a007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 934396267 1250 934395017 934395019
    0x20a0816050d0201050d05041103150f131502180907050c10150314030c061003150c05041716140a0503071401050705031201090902042d0f11030c0702 66
    0x46540009054104a82e8954019070705079101c500c3c00004c900300380c00070007006c0d0041c1d400c540560300400c1c0c030341c4007044800c10004c1141096541444c20b002000341c8504001d00344400c080c08148036a00094004040d801c206001030000350300e6207070b00e00c04543c5043c4030000d56035001d4043c8060040c01a00302000700ac540b204101698101c0d500e8500717460586161018555003240c860704104040368422100b040d590030040166868060904040e40c41c01000361a003d00c5404041d10400400c850b000210026803068142445100c0c640b00c0043d2650050341b041c000b503101e003920070000d052810301c030248070341c00300c1d0241c40030958075001241c4421600140c250b000300400c00780885d140c5000941c10701160090880a0700034403070640115100e03040280d080310701d0300c01813214084144508480301d020f0b0011410005000c3d5160040200307403040c030607442000415240d840886c0c0c0303004035041104072629100c0440d0703070540c0070340c040000d1500f06010b10554101209000b500070fa100024845240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 934397517 1250 934396267 934396303
    0x31e03011d0c0d0e031309140112050d1d04050a0c09120f080a09030c080604330c0203120c03040605090f0c0d030c2406060e0105090607060207020a08 66
    0x852049181c0008030641d40c508609405101e14405031002d40c105280f40700e205003d40381046004116860601e01c50340003002403584a403603101c05000c2c0b010314240148044d60318010018415140c02d92038007a103c80190400c0b5010301d60400400700e0380c00501c0f48101c043d10070485807418204000c001c2003e08e0640700010600d00b00012045803440110402c50342120444000c0005aa02d0740b0300e030b0703001c2d00090b410300580b550000042000310484c41c00a040040140000d468285008451101c08480c0810050500711400c0c1140300504400c602c00c6008490000d131014810000b030f40f45005500340300354669015020001070300b2030180030714051440744030184030b103440703100d00c150300d42d89001c1c5d400005a100d80810302c2d41e07244c6560310b2007585020303040c14542d01030b06403518000009005100504130802d24183c070f45003002071240400404c503602d409001d0b9014540000c201c1e1045503041071180070041850014401558102c2d03001d140e0060030038004a90303550b103d80d1110408805184600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 934398767 1250 934397517 934397549
    0x50f03040c09050c0703090b030622020c010f05010621020c0f1e0304060c200a0923070210090510020406020708240433020c06100608010e0702031e0301 67
    0x13880320948030801c0d071680f41c6c1d4050724140708028005410084c202648404511490814010455600382d1148030200000d03035960050301d070395403d40d561008006031091802004200860f8400348401801d0f40091205241d62071b82d04070640680101c3c0050200c900582c7d00e4102034a60000f405c00c1070028010021202c070807500f02e132a85a0040c0c1c440d0364040b9120484800c00203100f486c0d0155003e0b4922045041700081c040031480717564854111030211596500e0302d1040021380c8040c100d0a1a1103180e01d001480c02c00300080d00e81c014441048030f0240c41e4240d032820440b05011410b0319124941d4119200c90750b892000395104030300c0c8524007040c000d01041109002d0540780312803440701e035949016440d440d5580c0e0010000015483c404100000889480491411107003462409080030f40168441d0000d0035182e0424001500081307020b400c0c1f400801c0341c0c1c0d400010345411111403032f515084650f00c2ea44160f01b148030740b032040154481500c00c41c000b882d0020028605981c2d100307448010714 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 934400017 1250 934398767 934398781
    0xa03080604110f0703030f0f062306090103090f140c010f1805120f010f0f06050619230301080a14011a0f0402130e0402120604120f050f03040c0905 65
    0x100c80c0d0b19403008080c101007005600e2244107074010120b0b14800c2c940001c200740000c804100300d564020b80751003041d0701c45a040100300207400a422502c0c0c04c09180300c9010b010040060001c4c483c001049040c56210b000702c4040c0708894102400e510b07081084541c5030103000f100d81c1d84941140c0c41c2140461450f4004510b82440b5103420181d25a5915964850b075090004121038070303104404c4110b003841b904409090b416400e00450f10818840324002c954988014501700c162401a00028080d220038803940101949aa2821a5480040c00d2411851009550540002c1416a41c1c8598207200000004079000009400c5403094080c0c80003040c9100c41804081c207031180302d610403c94408010014555291402541c0e5001900400040c6030240c2ca00e800020701c1160351000c1825500d00003000b00394107084c40e0483c02c114643e4050203243c40d050780c900c1022040e080e032190402c01d8074003040c6000c0b800f030011903120140300c1d541b40d0b8a074a01840d000c225580c03a4042e0304480741c1000302103a95 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 934401267 1250 934400017 934400021
    0xf06020a111c05030a060306020d060f0b09060706020c150c0a030515030a02010f1b1a0109151203050909130302120f0d02250f0308011a0f0711040e0a03080604 70
    0x100000e55190030300c00c41c2d2442c2251160005001c0403c1c0e16a03c0b440000000c05500c002c060070200114080703942c1d0b2500d244000c0c4059154009000c0c8001004084040da072400b04a40441d0360144c4010780f60b0548071030717061030b1000e0350641d0350a0b00099024491070021410107040c0225841d50144442c5da28580c607074008506090045406a100742c20710001903018200042a400c4180b804a07030000b00501101c4850307541800969107481d0036010b4401c503070000d59400d409014945400d11445e40442c0744100252624403440d101c20141c00d61070b1301058480c6081795009207000b0540e1100d810a041025100e035150710b0110054800d410003480c2c60300003081601e01e1030601e5400302c2d003042003801404020750302450310098245041031050300d44401072040704d103e0901619019074085030380c1c9000b6001d03003010b81040e0360015501b10282d5104c8150002c490f44424030403400ca88408203440e000c1d0000e07072101d04003980320381090f440103c0c242c40003035101d0442c0c0c040e40d54410315481d06428002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 934402517 1250 934401267 934401283
    0xc09030d2a020a03060506010e1908010509030301060923090117010509060105092e030339080a1209050f010b01080c0306040902030a0c060206010e0109020924070f06020a11 76
    0x3d000881c0c20790030404500c540c0e1280350f000c481814280c20080e80c030000100e4064280c4041c3d84806030a20040c081200240b00d200e920000c00c0005501d154140304014000b00960710a5400164003030b00100c4556034149070800040c00090003011003940c50b940c85a035240b00742a62007207250300c0c0c1000a0480000003c40904072403000d000b100240d11002e856502c0300c2504010054288404212a44002c0100099000640c02035851900001c2e262014069828800040141070f100c2d54140c24198200d05403040d540b6a4801480c90707a444105406844000c1c100b8000c0d61610310f88206e1005101d4045090b0011044c414020003440a0120054815030400d82d061110390200380300049050070240c0c4802d04503030000b012644041400d5413016134100c00c2e40c11400060304050010042d500109000c24007621460f9825030405079043e021904800d40032501e21b400400025024401c0cac40340300d007100c000640000c1ca0000004050401e50b020758040381d0b1074400a540c610280a4052020036419 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 934403767 1250 934402517 934402519
    0x15090b0403050903010b06030a0209010806030d020723100c170403030503010e13140a03020c150a0e0114040f030b01062d02010b0a0e040c0503030a170c09030d2a02 72
    0x90115191620211042e8101464403501503681d06000041d030341e15440a1071040030202c0300580d40f0030b11400010500c10b0040c042038000e901201001d404c960700418164140c1d00922100c07101700b00da640b0300d0f10740030140e1f03404032740c106040002000b05c59a010010000071405424044900c1d00c441d18954240e0ac15403002138005201440103202000c2903a00454100181022880c01e901450f15800a00c45c186210b8002070b0740030203a0301e4101501888070010544003219100000014104035080034425500c0391400c000c440f00100000f6030040b844215041a0f0f440241d440310385801c030b80c8850030f480d40411f4840340030441c00007440c0c91245c070002480b84d2864480232510001c000b20340881d07241d040c0d1110295501e0703080f0b010340f68503401110402001c0c00705107072140b0300b0103040c14a170358052074119034043c0d0820800016038070340048694044181b01d102000142c0d40304d801c011124010b905420340e060282c0180c8200d4181c0c03181105400d0041c4607071200304000300c82608004081001002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 934405017 1250 934403767 934403783
    0xf090b1b09032e020a08190c05090f15030901092001271d07030c0806011e231b0307030e10030e01060305010c0e0102012c12161509 58
    0x601c0244030f03a03809900076100f1905144042c50000450f026130304510007030000644c3c018100a50369210000740958a06d581c0e0701000203080001009002d07104184000b409544180d0101d21036484100303000b444554003098994507810040d110a0191012400a40c1c0c03988a510b10f6001c5d22042d01c880c400302e054144c484034145401c0e502e05c01040e401b042c104422140140d0f04c001050b020400d5040e610b8031100d1541021032030400c2014044503168060303d0104480c0c0400c020161b6000980300c46100f0201c0b415484207002d0044c22140007502e50022401020802102c0108040107406400381010201c1c0354810f90074140340e90b590341e0207914000b0700080c9880d4924440350620188210464a0510340440c1410a4115450079146140d1040b81c55a41d0f42c90100e440544c02600022041005d00c000d1100744e0b964a4845450798040b030740c000707000e0b480c1c0b07550b400c01c7c400412445c0398801c01d8002554072688541c83c000c0040e400c0c1001070300c200e241d0050f0302910b80d90502c41d87c4174640c1e0110750 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 934406267 1250 934405017 934405033
    0x10806030a020409080c241302130509010e0a050309040b0108090714150a0e13090f140a050d0806030601050603040548041112010311040f090b1b0903 66
    0x7000090f04c407080b415240c1400401c511004580244641d008900ca440c0b0408980044000440803026005015400443d0b8000ca20b1006940c4c00c41d55400441000310007041036282c5185441c01080204850455481a41301001c1080000300141910300ca04803005c010321091400150b850b0311003122007a0503508424414440401031080c0a000054050150345403540791600111582d80540130308404104031484600082c80c025001c985140704110060000c608256900c40602c0340a0500500420000c6d111214210040040380350300c0741c2110072100c041601c80d1014004c45d0040d01e0300760080c0a42000410705080c00c000b00c0c3e0049501c4002010404400c10a00909080502ca08072002d5181500c82c2c0190400c1c0c8480000c11001d0030b04604084404401c010407a0003910305500b54040602a510014840700541c90449030400300a040402d440d41c0024010905a26010724440ca0310440710300780148513201a01c1820b2405000380104a550743d003c1c254000d85611a6040e0b110140d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 934407517 1250 934406267 934406269
    0x190f0324050618040501150806040b0105040b060904020706180f060b090c09010c020a0e07030e010f0c0206071d060f0c0607080108060c1b060106050913060503070902281d010806030a02 81
    0x4940c0180105d000040011003c02d0106644c05641d010070310680c4101c00b484148940603541c21300400c82204c04010319803e81002c12094050080024496580400d20310244044c54200740000f00030201c9040395401c991802c06000851440140c1d0038918000c031010701428000d40d894003403020161170b2400c11111400440b03004540c1e43c41280c01c00b402540004000c0c202c0c003541ca02a050319180400d0b0340341044041801c590222501024160920100e1024541c0105800b5004503051404c0c0000140300960400035100700c604040c4c01100000780354040468800142111180d0030041d264243c46c1c01000b1200d081c028007801100350041e0700410400c4030a940100035009056032500340e6000544400c5041980036030018001c10303000201c16403180b50400c110901845201c50070881c86003000c0119548102c640034a031145076000a0303101c48046110343d0110a0713019004184c40b05025050010200100c4000b08551140c034040d00c04020343c000c0550780c0c401d82000d001002e008078250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 934408767 1250 934407517 934407559
    0x152101060504031118162d32070b0f041205090d0501050420060f19030e010f0c030501140f060d06051002030702031006060c02190f03240506 62
    0x404c65800194503290504442d00401d02c0340c401c441c02010103030341031a243c0c1c003d800180c44d040841183ca1141444521084c02c8100d101005400340c50070410080002a1210070340030215120060b40c000780720701603001c4c5420401009114450950301c60140c0b21090720b03050f0441d09480051012580e908038030f01081c860170261800034001040b4024200003621621b08441d410740e81601c2c003851450711000c0e6090040d21010f00108255491440e20004035080c1c010350040b04c2c1c04003210000d03600016040c51083d0818440c545408000f00040e9009005c1d81004041001d0341401107400c040000414210828202e1424400503148440f41c0e01c09908010340759101101102d00196a00b8022842d61620300703104440070125001160358117424010149042a08040d12142c03d0600781d0078010703d0b5200b0300040d1400d9054400c8040e009000300840b030b5121058001400c510400c1c0d03c004203209103910180c01404402854030480d840100459081e82c004940c4030381c000c0000001d420001880c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 934410017 1250 934408767 934408793
    0x10c0f1b06090512121e0c030f04241505060f12060406090612060e06150906040f0e010b15070c030f050718020304020306100e0a1a15210106050403 65
    0x1070300139181c01980c541c100c214a40c00038101d9424030107510040080100340402014800000194008031a142807180c00c00c0c6880028030005161884001003005c01241d40300165131041d010404640780c50700454000c0091000c50f06c001e19884881200044600300041280d0b0640c80501c482450244c0c040243c407031707404000e001107802036030741c0c100058241c1c0790340701e80740241ca1040411000750003e400c284007a03690004040380d10390007842c00c1c00150711031035902d4a09400250740c0030b80240d55000c0000c00500701c8040c1020b41358101044804030020640c00f55604032811540307003c41145001c4000c0c6540100e50004002003d414418401720389820002200355201e01c0445d4402512000c0e100d910444c40c0080e401c1082c0c0201c148000c514082c0402c4d13034480e249801c5411410324152120808000240880c40d106684509003042e110420440b0004100c0c0540071003010350411480c00003992003140540c3d0840f83e182d90000e0400c0310502c034581243c4117941c480e030034541035803607071000c0b6403103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 934411267 1250 934410017 934410023
    0x408030a0c0c02010537020109021801080c01080c22150815040905031b010507141305100909060806010f06050a050d1521050c0402160f0512030108010c0f1b0609 71
    0x12281000a41c040746400c062844d00705174000309003410309e0700c1403183c6004030044000050034980d00500047d1030006a01c41050400d103000d8807a078071102601c1406d07200c4c031300516508200340d900008058803007100381e00866001e803084107108010a44111030341c10f015902100c203030207800303000c191601d8030360051211140644252841e162914800c116a6040c2450396111070351200c0030050b8050300603000ca4800419040076038980101003141c0918140075000b0503214100022031420b07828400e04d1070f42e0142803c000d0802c980d40d1038980345643c0701824882c5480183c3c0240010420510130400d03207910400c107881d030505040d116103003d8042c1691902034840e8144448001419020140310b128120345100002c02d91001c0d42d050641c2401200300c5514080d80c010030410070302c200400441d144690b04108029400061840c3c460b00b0040c5042101d210a0004000450b02500651051211000544030b01008a689050668141c1c0c000c01e80d0202e107110300051040410b0803500f10b6048188 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 934412517 1250 934411267 934411327
    0x2106012c060a0810140c0c0a150b0409110306150a1503020712030219030c0c0f080705061f0f06090504150f0b040509010e061c0312050408030a0c0c020105 68
    0x140703891440f07140c4400030320640c00c13142d10b8074010b003041c89202891580020300400414039140c0c2c1c000d68940e0ba1107400c200201944403910311922140030644c0304d00040c8400400074000092641040c0d00c002402c1c4186a01c2805410049116403201c0c0404000d0707203001801e413032211031606410100c4070000c541c45509240c1c00300001d00008030054403451070140552070050315a404a04614001d110143c164003c2c94074244030b001080c2c0d0013541001915902148070000b80c00145081c2c2014000c885004106204440900c43c481040d001c89035016040313003c180d950569103651007610884a0300c00c0c00c01290a0240600403170034141c21200310040038402c3c084169582d29141d80c4010317041c0c0d000d0460f00388042014452803800a04c400c0c014007002c20084458100480051014000400c81b1040025160341d0a010107000d40d1201c0c3c000076100c4801c000e2441c01d030074100d059600884e03041040303c5c680050500c0403800f50341c0100d03900f50180d40b100d0400b81c428003e58010410b507079034059400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 934413767 1250 934412517 934412519
    0x1180b030a030c2307120201021501060206062d06030406090f0b01260c010e031207060f05060d030c03030b01110a0510060e04080702011d2106012c060a 67
    0x91810005200301e00d12940c0c070310012030a242441c1814244143c02a042c0101200340b4802e0618001031403000d13200151070051104501d0f2005038940280300044041c8280d100f000000c0003500420554400d030019540d11a0001c00c24101c1a03010b10014031441e11001c60a558158609000c2e0103541d1051003a40700054151440c1c072204426412040111905003900b00103010032007050880140034298024a40a40c0150001064a80c1c1120121604000b4108035400d03850ba403c01041c0c00d50a00d500c51503035a425541800b1010f000000501c009590620010503c9800c000401901c0c51741c0503600c403100000d0940c0c0c01ca0181c1072220343d40781085440079031140040010f0100d405c038188102c005104400c1c0054030803003a40d0066001012207500c3e01c04010105010100b111b0209609103008011640503503901c26140c0c8240c00829040b802156201d54080714011508581c540444102c5171756030381c1d45068543c00c0c20340458540036050103144060b444a80300a94540041c00240060b52007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 934415017 1250 934413767 934413769
    0x303051b01020c100c2d1404060207050f0d0b0601110f0114090f010b0d060f022502040e01020a0c14070317210f16090305011d0106090204050901180b 66
    0x1a0704402105100303904004420540102d03640304030302d000b8003a4144188090742a40b000040074030803155203590b900b1140391038503100341b01e038021f410003074450041503444e1038480800940d5003e49004080c041c900ca808540014601000d540c0c0e1103550104200b4415030341c0710f004440390b251006020700e507440f60380381c0c0c1026114203000350134144840010b80710140c98401aa40d14000906001d41c583c1c0c2d141191202d890749034007050f81d800325089000400d04440f420783d030301d00078490402c6429104000a02012501900340281386840340200c50500c40c4100790322205080344690452007000c58041e040c840300043c02944101080c2c000d04003610740d02030743c07034640d801c00f998114400e042c04500082c00044031344084c1d01008680d0410b490001292612940142e011180a410184441172500020030890711524440010390f5201000b444400c4050000602c07450000b85251500c0d400c0c6140801e00c040e03144203843c21075500406849840c0d04e001c0346080c258140340c510020860300c41008241c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 934416267 1250 934415017 934415021
    0x30902030f0a0b010909083103121e050307030e01020d0507030b09070201020405061b0a050f030a090e0c04030b06031212040c050904020306041e0506010b0d05010617010303051b01 79
    0x65040450042d05030401c02c1d190a200032001604000f0f90b00345000c40d0f2030040346204042e101d008a42c5d40301d0144d40240c1e1201c40382c1400751040b0440c1402e04150740402001540c0c081500414003d442d0343c04c104802e40419400f0680c941c002000080302800000c01d001c1c4130341c000c2c03407000c440b103000185040440c00f41e11080e1360045031a000800c0d1200d84a0079282003041410350b00000500c000c600303050508001a8030391060481c4a5009c6078520302403005c0304418008420351507400000c40f0f28204031500310507120303080b02e038096000c11244000043c18140651199120380d88030300c440c9181608555400c021010060710250301880f41e00c0c1680440511000140903d6044100880281c40d041c07409011400450f04540c4c021842c000900c00181c40004486030015488602004061490b1000304000303c107006019203103204140000800000e031200400f5140901d40c0c0a204903a240e0034280c2e07040200880000c0050220030041012078403c03000b40181d2070b42e40c460401c20941e00d10005007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 934417517 1250 934416267 934416283
    0x30e400902012a08160228120606090c110607020d0210020a020106080303040c05040605101d0f030a14070b04031211010612030e010207140f0103020f09030102040e0108070803072103090203 83
    0x451700780d018140c0000e5103400c565200110104c03400e4030714100703803513007500d01d640d0440c0c420b0444100c0340d02d1200003003000301c3e0002c1c800b0300700034032040101d48181880100005107a41c085440b501810021600d800c0c40460707030603000c980300e400030060030200c4050a802503201c007140200715580c500d004a50458240021401035000c3c0a0041081e41803070100800c4a109601140c400c65006401640084c1c1005440400e22208589000312200c400082070b440c1c0750f443c20041d89406030105600812924801c40c80201c5210403c1350203d13900c0f0000d099803441035000140826000a515142e0301d8420324009000c030301c0c5e920022501c41da45640c01401504a00c80840118017803651490302542d041100000038200780c82c0c00d1044042e84000b0800094611140504041d00000c0850741d0050032422200207044c060000c542c0c03a603484403204010082130281c2d614501881c00c0000c0c6d1007171700000703652900ba0080342c0c01000d17024058940c1c130740041c2c104007081072541703800308d00303015035030a1003201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 934418767 1250 934417517 934417537
    0x14090d080c13060f1101020310171002041d0c040b07080a0309081c0e060606250b101d15042f1909080604030e400902012a08 55
    0x1520302080c1d20050100e400174443d0808507841881003042243c02103011500301cad80d1240801c80c1c10791814a40c0c9041002d03120901c828036000117000201488203103400c109545032519004901c2d11240b0740040240300d68400c403410385100b40f240d140440c0d0254000d001c90805428002000c01256486485a4000b00c8102c040404440b035400d8089802d4069482d0007000e0300058006880c0000014100f0b008075100c015003c06032100124020344580c4245079240e03080b1080d40350901c0e245481e902c000505024440701c1a004481311003608402c1e64529002d504101c0392601181d1710314003848010301a0800c2c0e03c0c1c14a688010340640c03401c01c481d10344000f401d8492003550300c8001002c1941200405d100d1007040102000e800c11502d040815030981003130f80352404c6000b03180d007140001c102108030810100c14160011178104540f00c038141c0310b042011000c504200110f0945c2820044a0b803000000c0c1c0454075070209041c038180403030303c0024030315040e600805041d40d407521180e8003500003068407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 934420017 1250 934418767 934418777
    0xe060c01110901031407210204091b090f03110904020609040507030b100504050a180902100309062703030e0f070e1f0807090c02030409020d02030a14090d080c1306 72
    0x220141d5641070150715003045100c5e16040c1e160400d0304004241c0b21508002e0650320703c102003200082d9007540c0407a0028840c0c0d400902091128240c0343c0d03240c3c111300790070340e0101d80d620000082c07805110400d441100d40106070a90b4000404d824003912040c01441207900c90350401a101107580c5e03910a540c06007240e5500021201c4284c1e050040b00740130a40c9100c140002031004002a507120307122281a1402800c3d41190450380311803c001605030020b00941c44102411404030903036041d07008080c1140942410b02a0103450306084003a0340028052012041030803140c0400b00740603400641d541d5686000300c694a081d2000c40d0b504004142d04030b5034944c3c0714402480410304000b035a1a540040106510000c549001740190b503820a034410b011429884004182c0154002d0007a00d004000e2440c05550300d42c810307044c0c4002584101c039058411883c00b0405681002c00e0b14555100301d035003038003d0a000d0310700d1701c042c3c8040c00003d104440f108401c22500b0040b4000c02c00d140014a126110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 934421267 1250 934420017 934420027
    0x3030109271103010f1103191e09050f060c120604150306020702130510051f0203070f08130e1812030105010e0d0602040e07020f0f071203050d050906060307061e0e060c0111 76
    0x4600d0584007540d824000142050027203802c7c018a90f4525403400014100083c142001e86092070421044240e880b132140507250401400401e01401080e0290b10b402e007a0b5620390340c0707008100484681100081044030400b400f440003d510b5402010190700040030200a0210b45115500342e40c4100d41e03909000080c0002007002d400d10540c84d588010f140040318590010041e4001d54030700415101500c04480341c050f800506c4140e10441c3d1a5140c02c54507101c050307840740c0401e003008800755402916079200407844c004886022074145601007080001505e183d281a0044505801d580061540080e541c460b00d00041c0961000704000d029003e801070751840c08400281c102210f102e406e20b1140c0090110407207084000c50380d4001d83d4198522089541400d0804461502231030415858840c500000d0012450001511900c0b4003001c90444c0c5c042a1142c100b07c1ba2066060704000c04494165500f42d0442c5c02140105034010f00175044a0810aa5180240c207482c5071084140442c030300094 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 934422517 1250 934421267 934421281
    0xc0312051f0506090d170d0e0c01080f0708012904090c0305010f0308030f1801051305070501030c0207181107110109300c090e03030109271103010f1103 67
    0x1441c0300007003100300d8040303051140082c086001c035458018021b1a24081450780802d140200701a200480340d841400c0041c01070792601943d940c4405810071b800b20326032200250700614203400d414031070f00b10365540302120391074684922b100c40081000000c084607030031044e044020042000c2d0008047c11100401c04d40c0c8400006421604181c0003191000040d4009002280002c0c00304ca03040605110b5418140d038511408000344800200e4540c1c8035400c1c4403e01215000210302250f440380030f9425510259a680010342c2111491414600542c206080400000000b9100d100444044060101321004c8844207000150f20a1704102c440b41001c2c81d40050a50740034810b10081c00d0300106030189840c00c0d03201c00c0042c1d90351508150001c0c01c0c591480e800c1191206071030009010519051121035102c404541d00c0f908240920303c40c880c6000e501d0680c60312403402c034801c502e5540244020381c2d800784c0c0360720203654814007081da01592104100491304006201d8080058000004031f074a0341407400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 934423767 1250 934422517 934422571
    0x30a0201022a0d11210d140709060c050f0715090b0a0915090302150d0b0604050d0f1a01180b0109060e010e150408161a030402010c031205 61
    0x11201c1809070441c0b55981001240c00180c003e1a4440b604201c1d00c40782c245441c2524104010307040329174004403120b00034199001c0038003412030310403e14410b105030600544540d0400108690304800150049401c2050300d01581d010002140144107960303404140d88030303261414410340d12091511180c600c145a11507803201c01031000e01600b9183c24a001d4042c3e8006045940e1b5020700089403007140040b444030360240d124003004680c06401c8850715600c1e2443e1404131307080380c0304900340f250400745904190710700101100c05944000b06004100310305500d030b80001d08512401254040c0c208400400c010745542c8019008004042c01c15582c1e54400724031009032040245400c0c14004e95503020b0080d1500a00c255030070100a28001071000400800a44510408072040b01d00d4400050b0210707002c18082100d0300f204005520b0140b0344c030740c0c0700050382102d24042013510364840140040740c01503200d00c0a0706035090007403801e515094110a0b92404844064076000f0519010039458000d01070b40c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 934425017 1250 934423767 934423807
    0x21810020a030207030311031c02031e0f3106061503021e0a0c0206130509090708070303080c070203150106022a04020706020c07120204181a040212030a020102 70
    0x80c4003801000c0d01540c0c01039541d15680c0001024050701899100252104100382c85100720040da200e0b0b918a94100d0040007580260391b8141c21618081980600411104442d40240348240959082d40c2d181c65a204039840300c03402c00304101c446507600d150300f1806101c001d100c441c0a01c40004400c0c0c5001504c240b04585050190103241c010300442443c108016010206030500324000780d9140b018080072202d184581c2c2c0025484030010842007005a641d405a00c180c0c2c900740c03480c10031511020a0745684840c584650010b680c4450400c0c00082d10424038140c1040203052014104600c9030300080c00c0480100801c21007100c58801000455810010844850400c1040c1c11640c0d00d00b21010300542c5641400340d01035500044d03c0c804001d50350341140c0c20403030807000b80c41000d0f403148007034240c82003c088180d04c41e44c100010000c80c000003102100391150310045000d40300e440069014504034009000b641d00c014902816004000c040c001001b00f910310754001030b660703800c4100198042c914 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 934426267 1250 934425017 934425049
    0xe0103050423100207080d0606090e0703020901051603030c120c020a0f0f21120b13050a0f021b0f010b010e0603040602131401020f0d12110c010218 65
    0x4080611010405400980c8000000001c8140b250186002c8807840c0c62000001a44080e10004968080c00303151005041c615021803030a0020b9540c590303003251480307641d0040c0e11428034030b4000304101c503000b0750040c102c000d0181800c50504c0c0100c40c0c1e0b01c3d060400c2d10000d80c0813076140e820040d00581d01901c01c95a1665451041003800b04200000355504840d00c4018101d03501c541141062140729081900c0d0745511111210412103074072000903100c98140c2c050808580303000c1840207050030600500c4509240609520585600c034080400a080d000d80b210000d56900c42e2402d1544075180003c0140c1030010a603034040004203180d0300d02d4010340c0043d000459151021013841683d10031846d540104c011202a5103944407402e018009101d000da811900c0760320810002040d0b4041004020000426002e4821918106442d940c903842d41512040024030b02c5007980c01e41403040d60016041d0100d0b90061414018100829400c9a1045002401c0c10303d45681a1000d440c0900410010a05d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 934427517 1250 934426267 934426271
    0x403062009010f03020c070306060f120321090c08070f0e15010309020111010c1e02060702060601110c090c030103050607050a05030c1e0a031a0a030c0315090f06050105010e0103 78
    0x811034406801409801c403203a040020508100b039400b4400e0f01950901e415280a0301c032030075507070700d0640010840e0344180c280d0001d4241001801f06201c6405203941501600c915a00b2901e11601d9a0071205083c07003040003540c0c56400c100420f143c480420041c00c000c0c0011f001d07450418035039a03c1910310382d000700170500c640001c00c5030350f0307a84c040c00f8042c400081c200803803c401144010b032140070500d121a0303801d628006038641425440078102c18402210840741d81c8201c0300704400c0f61103010848841d0050380c0403202150301075105503090a4120700000607900c5072035500c40050522002603850840d452004801401401700c2071081e075400072410b050a528105904601410700e00004029014004011a05103554644414048000805d2a01040c3d65001d041e802a00526024440101240d40980c170001c1d90f040c10004502621780008000c00481d01c1c43c1d8458545075541d0400b00b101c55140c080b048001103845114510892003418081039660601c0001000c115550042070704043c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 934428767 1250 934427517 934427561
    0x601080a030210090201030b09130605240d03030f020a053a15031406162109080c0a050a1407060c0b07020c060c0d0e06030601170a0b0a0902040306 65
    0xd800007034008551500310f601140e0590a400103900030100e8001440c3c010100c03604204502c01a100c804400512500c000c12050300c03054801220922003242160f0107003041400c003007207441d0030640e002a01d4400e00c0c000c252805146a4402607802c120203174030220740c01160a1071074140c1102d08a0012000200300000303000f150081c1c410a084800070388014a903281114500c21442c1c0490741c01441d0070009000c1c80c0032106c41c00c5a56220102d44000700320108107101100355100e8901001c406c0800d29101d0106510060321500400180400703c801210800000600e46801d00441d200d075401030010f020705013014107041c0c65050b09003030354048507000b0050038400746c0d03080400c1c216215009150200795540d03410050340f602c074080501e194070400100310384ca85004001641c8441010b140c0d918402c070000340062000d1800b003606e101e8080f42c0c1000044241d0080300c0241075103c10001c10124100c01c100c0080741d595800b03900410840340d0001424024004a40680e50092240c16481c110174 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 934430017 1250 934428767 934428773
    0x60809030a050a1215030305030612070509010b090102010612051f021315020a0b0f091504051c1b120f080405070506032a03070306170d140403050f06090601080a 71
    0x2c0d2007004a100140f100f443c41901142e29241d100c4030160003c0b45c04682040d8403801c020708640c00840d1460b12034100704542c01700481022038100d04890024042941990a02c840c144103070b002140520304640d80e41000041051103050810550ba000700c01814618100ca002d5615460700e60003402c2da03484c010005d90024081020012040390300d101c03071502c504044210b003207042070452203000d8011140ea40600201c02c0007844040d0140901c80100c0e1101c25103c11010322490046401400c1900304240300901f10001d826038000010706071403c0c050081e04000840c201e04032000081e1024406005500780b490b801c1116066950068204100c55142654402c0d41d280d4140c05524000c55000c4007003000101502d40c01403842d00303440000c1d40000401c43c1101c2441e0005c580c0308000a0510b000081e0000114121019800b402000b406810006210640c1c008642c100304a80644c0708010000106506021012101800202500241c01c207000702c10700d80340c01a000701c007240d04050b10142c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 934431267 1250 934430017 934430027
    0x40b060c0705060d06081609060801180f080c0d030f0614091305100e150109020f07082a0102220f060e0307030c0602060f07030b0d020103200c07060809030a 69
    0x11580100c0da07503035072004040340201c0a00000d41c04002c1074442c7c3c0020100c1c0c410003080480940301c000404001e89645c0307408007801c0e60b0800c070b0046000c82c4040d9091010883c0e603042415100e015201507450170b0102d00041d841c2041c418264400070f039445444203031415050140038020840402c0540545c4a42000110032080103803d00151030001911a01042401d2100740248800704004220300711008041c2911a54620380c1844040c205100209110b00c25200303482a41c4403107425503041803817a642d039050543c0850034484000b00003480c0741c01c440c4501d184401000c58240c002588504960010713400c80c0754580804c0c0b143d041d05103818003000c0c0700307562803008540c0b0510b00b4014600e030401c003190501c03c81e60006012041c07202c1c004a0425000100035010710403041411000382c0c1e5186c82101283c0d00404101e6021503442060310142d0310035000000029103007031001c00c031600c41c21450780c0c0c10ba0045c0281020b640140c00c04019041c7c0008036a5400178280c07002e180b80c1510f03944002c003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 934432517 1250 934431267 934431269
    0xa0b0d0206030a0c0917030405090a02030c0a05070302070b03040c140109060206150d050601060804050706052b02360609100810030804180605120a060c050c0304030f02040b060c07 79
    0x543e5503955100b4548040c8280c0c0403400801011113070900030703400005025144d500a001d0140110b0900001c1200700e1401c0c42240d110b9402034881509206000780211a20b03070242c03070150114407503440085843c010440081d0b005030700c20104880c229244c0041701030500c10300d440f038034107104a224080220315004600d4a80c01541480709030307084003400c0000b500b103000740340c809081440380e0000810502e8004a4003070240c1d0041d01201c0c1c1003aa644411182d0340705071044807641850300320340303e0f03026040d000e44254280145400036080400352030f448103a001d1b2f0034598089207420004c0c0403e0700c0418040200a00c00141c0d2000e29012480c40030940c1c024241d000d2604014069001640a807141e90b0050050b5510055240d91140d58134603040070181e01100d003d02070740c40c1400015440c5846010040390b45001e5015000c1c40c80381b074490030300608042000e1801e001041041c688140e07000d10061016600c5444c200c8a000b045005000c2220f88141c00c503401803d04001d4a002084000b41c1c500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 934433767 1250 934432517 934432531
    0x30c081b060316030f2909060a0b04151116030b07171302040209061c05100312030b1203071514270a0c120510060f0b21010e0a0b0d020603 61
    0x41411105680264011b01101c640c9030b1190f910000f00d914008039500041a92204c2103070441c1e5141c03584820032040044a00c20000b014504200402c0008a2101640d5a5909909100c0c0c080101400b615040c24080108894110101482802041040140e90340c010700305141540c1c0b4400903228007140140c01404601c00c1103d404003038070866941d0f070101c0e06103000c0505090703141c000c03440040f4581e49609110445681c24a00010f20b5003850b06070001c100c0741c1004201d418284031500640042c01a58401d50300103403a5244003440303200400003800c2c61446802c20226411001e42c0180840d0f810651541c00381a410007405041000040300351010700c2e240100b03d07003868560314120724014480d4001468803451003c000741d1100c039020048011802281030721040c920101000742140d40900490741c58420810b41444042c8450b400b8200d40c204241640382c03420b01070b055540144800360f03c05400d660055040008041c114010140e144406548034150000a6800200f2a0000515071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 934435017 1250 934433767 934433771
    0x106080c030718091b0305070602010b091501020a08040605040801050a090f0209100504050a0209031920120a24090803070503070e0d060204080c010503101a04030c081b06031603 78
    0x2104244003c0d902c082c0581c1c0d485101e9454142101c5c0e44442110042d100c10354031401045400103e00d4010f000e82900400c00a044041a0752202850668201500c0c200c60451003207a91b00b4000441c3e4070010300c09400c00e600c4450300c0b18605006035003951001001080d4032402c0c261480006401e03941050520340d030480d003d005544d9100c0e01d000440744944e002c140d202e800c101c10702032400d0341c0364010004082d041d003c0c0d074100b8804810880c1c8403040c80303500900146840401486000607000c200508401c002d081d05000a1110840380c81d02c03040013002c0e100c00e0a000d4100b1300100c60b1030500f0703010a50013a024010b150007078451030305c94080100b00d50140100007001400b00c2d0b01c120840131a4ae800208110000c0559040c150025040360050304902c0c030940c06030301303403560080f404d0381c0c03041c0140301000c1d03000d508045110744004015101240b01c00000c2c8030110003d210300700d9241c00f8000388001000c0c0b5140841010400302c04c2a50007034001e030003c106001e41034000002c0025043d9080c100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 934436267 1250 934435017 934435049
    0xc10020118081b0709020414180109050a0204031a180d080f0c0913050f070e090c0d02090604060f08180d0e21160905010803121015110106080c0307 65
    0x442c16a101e00f500c1e40014902543c030000c80c0c10550355014209a8034001040e5040e65100808d010860305c40d0549000c800d8118001040300c2005504450341c03108130f105015081560700d90712038022184855001401c0b060754420030400606000340e00c108441954000c1203010206a0301038494040035000810100042e800130341072004103011a4218640031305100c1c0b14158865a00c1d00601c0144c603007500c41c0040e06d0115044510444d06c2d0200010010f0140e141ca0b10f44401030718007a80032800b0001019001e0003202103603600c40000d04001d0074a0344800c00403642901004065a030024010400a440c82000c2c0741003030000900c00300d0785015400c002c01101d40980000e030041c10014900b492100c85144907404050005c00d8082e200401c1c8076010140d01c1d12000e815040c6c420901600d6450791080c0310703040c01d500740540165089000100c0d000a0320b500c0c2d040d00b04401640c0600c02c00803c00b49985251040001d200c0e100007404108064100b071107030580020303107901d42e5103c1c0f51030351104110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 934437517 1250 934436267 934436287
    0x6100303050f070507210b240613050406030b010f060203130302010818070603060e13020d0f0312090b0603060610080106051b0105090d021e072c0106020c1002011808 73
    0x20a001400e0020b0240c6c80003011000c1c81c884c06503400e8011250a020780000c10756580aa0003a5100c000300880280d00003041001408106c1d001185400d141000420000510303482d18031411010b14010307443c8607441e6040c25501c001c00d0443d548a07104562040044402c0104c0d509802001d495091034450450303115203240c42501101a2140da00b140100000041e45640540c8100c0440e000310310440c041c0e0b83c0d2407800d042e03404400c02001e0b400406003050200002c00c0040c203c81c26500c03d00780303c403500c1128400c40c400c036400c500040300c404800e142070064902c1c0810240394040011100c1001140e00f100000f41410418415482401404030711100e00344940110740d400616190020441498088100c1c1c1e6500080740c1d01e4009805000b050341503070602000820000080c4800400390586044103c0c080050303c04004918020214041c18580f101031079528028a031541c000e0001000c40360402081c455601458019a850060355a10b000719035102d200c900c40c0c00a01ea00d495943c00e02d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 934438767 1250 934437517 934437523
    0xf0702180705041406040b03070807020a1b2111010509060d29370801090609060630030302120112030306140f100e03100207020306100303050f0705 65
    0x1082149040105508100c1c44503480800303042100d21104810069404075001d0160500c00c41c0140310f0f03180010400210300c41d0280785000c0e0400040c3c81101d01c1d41429403a412205030303007900d0403840c10a2440d020885412403500008804101c6480050401031560300d441d4400342c10420300b418007002180101c426924103060751540e2003190380c00d100a00c3d0005c81070501c0d00b0503007042c82000f00a2800c224003420200c004c0d00380d41414040501c900f1a003404450b10307050030b909400700e849086d801c011910410038010719005a20542010404800d18036000040d0b0304241c01c0f120031000d0a840c031132003a00c0c0400c9000002444240311400600342e90604074041d100702c0a8a11740c540d0007100005001c4500000101e189020b03036802c10541c0c0d1120201c002903401c510740c40f580248404040f10280c80c084096084803900d50901c2c0c1c00c0d0807101004a420840070844040840303602080d07050a40c103091020720b5101c0308249000d0760040c1550780280a9000f04020b5440d210310101b01d0600300b00d010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 934440017 1250 934438767 934438789
    0x509010509100e0d08030402182e05060a08060f0f060a121803020a050609010204031a1f0f060e040902012a08030a0f0f0501050a06030e1005390f0702 66
    0x513181e800b00c03040e5030521151a91040e10101c2c041c0600346290303400700500026040c001c9071011a04c43c0344085403004011040b0f00c0c1c00710601554030845001910b95506802081c400300962a009480c4c0b50403001c1041101503031001c0390107046088903010032903982c581242d8411400307040c02c2420b443c14540f5800103101e000e580b1810040031041c1c07502031680014841e010a40b1400131900c3e16950310810a00381c7c0564803000b80140c0c0139498440c500000c182c0c00c0d80d8041000e4410012041c03609510b1801c404890b031111051203140341c0d042c041c803903210b05050100303001034609000e20006a0f0000b0803071084a030b00c018603003000d00301403020b00d00d60b640710a40f03141d049180c41e0313202e00f01000d5401c01008600d500b60842031819071070036501905800384a048440c01000c0f072200e245000b5056000d444010900000f90240210a00401e0340e548207040c0a40399480403040f01c07402c20340021402008085980702c1d111100081c00210003004c00894400c0d0040f401d865840f411144003003902d140d08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 934441267 1250 934440017 934440019
    0xb221d0102040f0e0a02071104020c0f0601060e12010509030d0506060d0603061a030a0f02010311040e090a0209071d0f04020408100b0301060902281716020d0509010509100e 76
    0x20b4000740c0a208400300c4810b45210440840076500c64143e00000ca01c9034900042c4104004a00510750b403405034040c0440101140a407401c40d8191904141808002d8000b807000c00c001448903030090820b03001e548440003130b40000f0481030a0080981c0e0340c90042a01f115529502c3d0000280341d44c6520081e911241c144080c140305007620fa01e0000c0c0500700e24407806c0d4840180c13080a0031030349000103000a1154110039a604091403d0b0011005414954205020103200f08400510004461400e51148030301e28041c0c00610280e01c104002c408001d000f02e010024200105403d184401100f0413030f100044800c1c4a54a48820103c1c020317000f20307881441c450180803010f840c0c0c4907040c0c02440b080d05003240208403898440c40c0d064101d010303002000110307029149080000500340c820081d42800b41d4200070403020315420001489880c1211441486c04241401c41042a0104801041c030025801c0680c00d01641c02c000030402c0c002c1d1810144581c40380c001d000740751130240f0220200c20304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 934442517 1250 934441267 934441271
    0x6010203070f03090806070c11010305061504080a060c091a03060a0e0a0905121305010804020d05070b1b0606010509101e0201020c0c100c0f060219120b221d01 70
    0x40c03608024060242511544000d40030301c03000151918411061050b48d103500003072104030740c840e090044000b00b10080c4140d070011140c000d00d00300043c10384045e000070002c0341c00030311214100b4903100b400c8c1d482114a080c140b10040000b40305052141d01c040c007949030603001503500c1e55114070020b8260002d41d0300c040e0720315004006101500d0a2500038032465802882101c10551703000502c035075140f140c1d40c040041c41c810b41405000540c8282c1c00d21350003500042410f01d100305651941c50500145910640d15204002188207107003d0547c001840084603102804403483c045001905600c00d01d20340b18850021011000c1c1d80c0342c0510b040ba003510341c0c41d5100716100000880081e0007984945184c903130900c10148880080d01e004041081480500d030390f0035060702c045070741c0e01000100c0708000b107130040c1e0240100121041e1410b04101090301030750364201d08500640300b240442e510b5400081c003428140c40c2d42c1072580d150054090180010300c100241107405000500020034002c82c6c5000a94 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 934443767 1250 934442517 934442543
    0xf021002030a0c080f0403050a05130510020a021201020405031504020402070b010303021015140d050a051207021203030f04080c0f060907063207020d060f140702030a0509090601020307 81
    0xd02d95100d25048801c50700c6801c040d0311881400c1c3c5624104031030050000301c0400c0341155861045014008800d0011001c42199031a80001141c1c03120081942005a000640140c1945045489039403110f10340c9008528050801c00400c0d100d1101044100100e42004040380031504c695044a00f05078002200742d106584918000f916075580c82a00740d0841d00713001110b41200b0821865404485400d24a80c80c100041c8041c132441861704001540d913400b80903142004a90280700c00c00c40c0b51440300ca05036503079181c2d1040210300143c40303404011907442401000b0010283c60749080d0001c1e00481215215107001c400c091810324020180d040c41e0240009212244100183e07072010b036503e5454a03407403039603c20000c400609440f200e2100d211409030454075152900d60080c101c040c00902440d0703014042c0d84907041620740d0345251400c81980c66801c14003203a100da04e41e6401c500540302542c41c0c41c0c8910b07001407042c040d91102d54420214000842c12980c020001c031100e003948003403014500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 934445017 1250 934443767 934443781
    0x8060411120a11040b0a0e01120c080f030c010612050d0309050c031b130e030a05030c0910050924090609040221010e151516021509040b06070b0105010f02100203 71
    0x35106210083c2d0003103081180541c0d29180c92813100f02078035101a04144070360329101c8103540d500814441603131061840700010850b01001d0001030103450443d00219581c00880501508550040c3d102e105c5002000290b01c0008801003000140b00025180c041780049080c10a58142101c69010981c5480f03050240013100342e020007101d201c20400c4070b8405c000c001900710705040d10b0048448035865003003000781200c40d5014001458024540880c0e883c1401d4845010a0b005100000e40a010650100c4c4501140c0791a003618524101e00000d10080d00c0075420b0304121900803803d10f139100b00c1c00401d2500c0d80da00c4940c103507124407100c0307150901400340032885100640000c2c02603881c1602c2910001d0b140d0100020020703088038024003500c104c9001200c1100d020b4014021030800340ba00b1021100c003583d102100904180c10304100325940d54403003001c00086400505190b4003501e0184228070100781c0305200c6904480f02802c06040454842c6000c03400c1c098586078550000e4030200902c403078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 934446267 1250 934445017 934445033
    0x50f130e010c08090307030e1e151911070501050c010902030d030917120403050c010b13063803060307030b1312032f0f07140105060a08060411120a 65
    0x141055a112804151500c80d1440d45a10600d06d010380424002c1c081c07284982000300c0f04880103c0103010011b00c1c00c6030003000a600148280e0400312108002c02d8500c040d4804401403410441a4100049411170141d0001d4860401d44102c030306104000c45d40e101610300039045170010590007429581d110b0812800a0010a6000025240c900a0045800503c038420048403149141085240c1c01a515690215020381c0203170050900740d5250385c3c8001440e1106414212507003840321003c20100d007402031012044a44082442c21081c030b03d85645e134002500c0070b000c02c8010030150480d40e20b50724100860b241c90100d40c4014a81c40f0280c0070000c17000c1d429490841603034403980525405018044084042c0c0b068032010880c03084100070030908411280356000180b5002d0720800d41008945520b40c5070a410040095070844403204420f00c41071000c2c0304855100904a441d00841c1d400d10344000e0780c80302c0080c00205041019480e40720280d03900f45403051408100b5048074440602450700c612 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 934447517 1250 934446267 934446281
    0x20f060708040b13051005090904080c010203070f03200f0c1e160522050601140a021b0907050d2a05130f1d060f37030c050f130e01 58
    0x1405200c01401700700d500d070105221055400c036654850525940004120181102810481e4002c4040080c08040c0900b80081d40c41303001161907550f5a401c001c0d0b0082c00fa0b41c1d100e907840811644414013001c95140d4041504c40c1070845407241c9842d0540c45090500d0141c2d030380e03c075111074240ca00701c0000b80e140c00030300c1c03207180e0b00351081c44020503a4480600a1600c5004080048200d41040c011151038050340100d620401c1403401c0c0384060202058880c6d10380c080800400140c002000e40d00c03190344105003c90036644191141e800901d8241c0d8001e01500071300b50f0304040c0310340b5800b003451501070340d03c0c1710150844d50005c1e15252040d40170001e030803503000c500104582c0000301000a0382ca0400e000b500c08890303488004485411501141600e6090001c0055500a0002c4011492a140c07891030841e00654001c0003c03415540221040205100501c110401d410b858018000550141c01580443e84282c5100080d82c85400024010001056102e64100e02d0900300c1da91030801500401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 934448767 1250 934447517 934447537
    0x50f010608060925060f0e04110c0f060c0304030503040f05161701060b0f0c190f021e01090501210c050904060801020712140f03040b010509061804020f060708040b 72
    0x250349207103213402035980035845072488503c0c512158030030410706000750500380c0004098607190f00445445800034040300d16058030051005800b00391030b6000c40040041d00380e80140d000c000c00307651400864074009440024001000c100e00803011074200515928814000ca900000b0384840000c952550344000c8514420300030b030541000701a011140041c400c52040d506a006600c0c0303054090006410780e641b019032014840d124258542c2044443d400c12840318901c1803010207440071041c0108400b4030941404280d180b90310981c0b41e0501d0386c0045203541114001e0900b1906c2d200d0140d080042c001440c1c1da040d0000e400c1001c24209a03500c100102840c6108660400503a80c460303541a00302c2c0a0204010320703034581d20815000242c060210814032080320610249003060400d110307200d40d04191411225001ca80d401409146803c007007440c5c0c010400d0b07a00014010f640c03042c0c0f00100c20007410203030040301c05200000090301d8040c12144102c3d0010000390382c550780c0d0034442c180d030f500025400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 934450017 1250 934448767 934448773
    0x6080a0b0612060402040c020c0301020d0c030605010503070c02130b0d050a0c060509060403060b0d0f030504060f0e130b061303030e030d0c0515130b0109090303060504060f090207050f0106080609 86
    0x214039140501c064102c441d454002010039a859a0a000042601c0a120030542c82050b4241450740d0f000d000500d1007500e0b028020620040302180035050310070542182d0706000d0140200a84540e0003268580c503ea0115000c0180c0000541440000c002521549801000c002c0922041c464001404099107124003107a0b41000d60303401c000c50740f43c0038611000d603010004010810100700150400f0514100041c001c003580700c00d580d0340c00460a0400c03022400300d80301003420082305400c98400804040f041c18080e002041c0c01002440303907000103100c1f10348680d4519074400603840f4941610000710304e0710700100541d6142d0070f000d004900c1c80508540f00b8801d80c50b16864180c80792141940c01540b00d40200f070010042c504070080c44500500c1050540700050301d05000c9101081124001c0000400c0042ea01d41c50703080003801d5a059800182c01a814000108880241900c100c000c85075524130058840d492464441d003000c0c0403502d207407600e41c00c0190125586a0107c0e0141c0103034050744c21 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 934451267 1250 934450017 934450021
    0x4060c12091a0f01081009140f100b040504020f01050304110901140a080a03051209120703270b1602060405040c020303061906200a0c150f0329030a0606080a0b 70
    0x38030f05000e4403d00841d2096004a010700038000b40c50340220306194850840b941d240500668114034211140700d18a81076031007481019440c007841d1050401c658402d94080c483c071f20705500861540c2011070461810000e00200003814840c01110314050340d14010408911541d440203205480300c200945144180407d8034000f40b0001c0000e070160132298151200707424510005e07030100044100a240503c03a000d44411802c08100003030007001401c2c0b1030b494904102008175001c11035448034411681c103d405405050110400180684107840c103020f002a000079901c0c800700c0c0540c02240c1c01190000e04042c6100c445907000b0010f584543c10036034034904c4080c140d180303501e00d852040c800c0c640407c40d080720007051180100012100082030070115918201d050352002c910548961128403800e4559801c50010b51340940407080860b44c5181c00d1040541c98003170180001c3c1d449055030404581a500c45003591018080d113912160804410450260740d17040391030700c0701c6505004440220302440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 934452517 1250 934451267 934451281
    0x105010906181e1508030304050312151503070212040e04111f0c02010c02120a211b020109030c0f0513020a02100e16120b0702011404060c12091a 64
    0xc6040307001400e10b11061621103d1442042c0100a5140d0060780d00e18292004075801c901000114003540c0f0a00c01107984d404110308101c0c0ba100c0c00b51400c0076420341c40548840c980d131000c854171901c4006040d125640c3e15581e1041e4a040f241d4514000c101c4c40120780001c0c110200d007030041c4298003c9041803104403071101008600d4201803d01c02258505c080d180c082503204066141c0c3c2244103041106184415030001010794880060802160b030100e42d03510200320102340d1004003007018589141a0050506000c1c05011080f001122210300603034245065a200e804148021500401400031150301d0307118598031406e00340100ca01400540710b0042c007150544c405c8503402115036010300f4034910000320742c45c09040a825402110701c11210b820807102d200c070302110020302400e0741141c81958545031a48860308002e143e003066900d000c0c0c04600840205250591140e0302403000144604600d409840e609000000e080c01e61b4034140c0080d080150007203001421a582c0035180b015692615 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 934453767 1250 934452517 934452521
    0xe0106080f07180e190606121203060b0910210212150a180b04110c0304050111060112141011040302040f060b0409110f070b0402011b0f08071103010501090618 70
    0x5004e0344095010b04103807074000985003803500700c880c40380c1008904140d882440207080e080345001650740c10b2803a22440403068162041000910440510504102c00e480002e003030341e8542540301042c4020b00c0341c1038096002c1c0500140e04849404800c40d10744540743e0a2a07030381c50040b01c0c0105080e202000703080c0c60345041003914040b03503690b28517203400780349035103481015081d0b000886e50420345400800b1000d00c0008003424800c1c8141d801140c5643c50000010240801e15007052465005400148544112210744000042e000b0b038800c00b5842124082c540f810148190003101289064443d010b409281002001240d0003200c0601c00c03410203402803011560343d80706803404c3c0c250400c420030041d0301c50b812a0004d01901c0c0500c0d4140002c200d215507003544040c1003101c0031003140f01080110f60b04007400c0300003802610022120101a5614082102e0009034041c0507440046034010070060b49084a40359120041d00074091565034490450180040e400795112242030140d01d20b84603c2c0b14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 934455017 1250 934453767 934453781
    0x906020607140403060c0c0c091a0f060904180803130c062d050403020306011d0f040804032d0510110901050919120c0305071a030a0e0106080f0718 65
    0x150740c00d151501c0d580d80d0358000d140c1b2052940611900030304850209100300035140080516101c017084642d01082034005100318030500e14810328004600c00c41640315241541e4444500f0368001078812841c840c1140c03d60389102000301044000070400602010300441c3c001207070311611032540d800340c45d00001c1d60742103010340000d07000400c11001c400035003065047d10a01c0c2500d508155180503140c1e004241400c40980000c1c0344001d01c0c2d4040c0742c858040c0240540d200b000405a1030050809950f141503501c603e1001a003042d0a000e4001d00c4100300740403101c2144030014019005542a29056031248140001c5070f20492900207510a1841c80c04201c0d06003a00513910145400c042508000b6800c0c22052403070746a0004070300105e039520115826040c1d0a0042c3d4070411120b1039440c150346030200c1500003228194400401410054060080c0d03504a40400c401058000186016034010b20283c1e100101034030829240e40710b00000414114103454080d681414158a0203030b500c0291517103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 934456267 1250 934455017 934455047
    0x1b050c09151c03050d090602040e13080d11120106031d0c0f010804080c01050c03100807050d03080406092a0806040503120702030c0a06020d0506010e0a0909050a120906020607 77
    0x1001090790308129140c60b80c1c0302090310905000b4200201846980212241c9100484540303600050510585401c851002d6105034000d2220340c0c0915595030b0a14203005002509001c1a12000751103a00710310310317040d103829480760b5009009540c0d6810b001000752101c3d5170100d00140d420710104e440c1c914007141100301c003000580007000080b200300044804910050082c0d50b4404140a00300c01c000080c01164000d20030a00c85903160b0900e030384180b803060702561110349941d2048104228503202c141581d10503c4d00340c04e180495a960341841c00c050940d03084020171190100b201c6856192480f0b4a80c01030060966540004545504400b070703641d403081d280503203103a01c1801000c41082800308031541c82201032050368140b12410708254603182020300112407103138001ca8242034054440c400c1c1c0f54018000d03c0d184101c9000e034000300b551010180100703000d00f500c0b4447c0340d092000800651403810f034010a81303030ba010303407280d03004202e030a00e801802d005004450115042912038404c040d402c0e46 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 934457517 1250 934456267 934456279
    0x80111250c1503110c0a1707050c060d0e0703081b070509010911071208240a14030a150501050306010e0121020f100c0303110a0c06020a1b050c0915 65
    0x42012200b4401598101c41c000c2015240c101120090340c15a0240c2500c1110a00802d14a5143e14020414440d8000590b29418080c0010700c0894070005220401382c0d000d0300c1c041d40d9841e84051481c007510503a40e84a0040c4a01c8500004105c0d0b007034010f0182c4414040c80001c44268090425110502880b810381c1c07044000c0014005404a41c2c80032201e40031103100580341032039641ea25030104405001e4400440e07400410404119a00000b0800680401072061440602e1a0002d01e080b0003070301980001020502c42c41c2c20503207080181000386900a1050300c101283e08546030094071090041c41c2c001e01504c0000200d00c80895000c030f05942d110001d00c0c0506060403883c0f002d6940001e01a80d1003036030301e0041c2c840d540780c0100c520300b0b1744016607864842e0030407410003074191201c0c66492441f00d20100700d4598243d50003d40c00310034940c003400150ba1151b408504568003d8455a40030650a0101c1e11100704071001a404c11031130000d40b4000c05d25941c03600c1e0700142c0c492046010360011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 934458767 1250 934457517 934457519
    0x501121404020f0609120303010e070318032012040f080105060112050a0f0603030c021e01050403020409051e0f010c08130219090e030903071a040e10080111250c 71
    0x86001e90442851607000b401550510302d45d10f00103401482c008202d1a81900000018001c2010f1080070300e0388441c03181410702403840a09a00618020858405030402c11401080695005003926601120222404580c80d25001481c1c02d0811b510a1013451400389a00701e0001b400d02c1c041c001e4500c64401610f44a4030020403e240701c010f081d000f0240510156603940090002950b88100405103020366183c0c0f1805510b407050201c0040814801c801105d001d2441c4200350303a0081c102d07030680c0d80c1540e001c28140114600175150134400812190b0f41109520910f0031000002045035110f13a81200a1141300d01b900000c2d9070702242611f2184080000d0901e0102505214250f0789000905181910407160f498000e031080f110700c5e1144461a8100142d40c100e1490708000d4400074150103a0000d000310891599021a40300798480d90b0b840a800e9070002c3e0600c0c2c540c00002c070080241200900040c4c110551090341644541c0c00d12400011f42d820940101201b0920145025446042c80c2c3c500c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 934460017 1250 934458767 934458769
    0xc0905030f120705010e0709270c06051303060c0806031209060406050702030f010c0315140f01030c0c0f0b1b031302040e0717010507020f150f13050d020601050112140402 75
    0x5500400f000e030b9456485182e10080034204000c0308004102541c800070304003509a010044031511401c815940c4080b144074440440d481415a0040700c0c0941031865960030110b1400829855951000e0142407602c0d04181038a07400c403c4962085900304d054800d000990781d4080d0300c07401204181a0011410f0106021143c003620090440500040840e42d22403450700c2090701355001c00e501003000903261100c0e035615011011071000980064860311403507a01d20f00c085001c00c0400102d43c0e0400d038444198a42c00360140010529898102c000d541040c541d9081c403008002040d24030181c0c012461070412810030503202a6801101c001d0060060100f00d5000c00c00a010a54901620b6006144000404060451140104d0719034100013080c1450254801303800c040c0d240d15100c89540010300303108043d8419138250365100544140344211500c0316140700c0000540404000c1c02480742032960300e0b510750002000c5049441c00d907180c2138021b0000865100780d13185002040c101c02e200b00041001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 934461267 1250 934460017 934460053
    0x120e01022a12011a010e010207081f02090603070e130b060a0c030908030d0f05060a03020109120830060118030308220b0a1503110609010309050f010c0905030f 70
    0x26400410b28201c806201c2d410741c0c2103610540c2545000e40c002c0c10342d9849540c020f40c0d01640303440c4c2400a061306902d00441a900c844208107a40c0075108403811550071045181c4c151502e4580142c44c09480e8603003072102401c00c0190524031403298119440f0081880d1280c0501c0b030700e41c18083c00071404c00c168850190b40404452400301d0910851100119542e001000034007411242000c01244211260104908650f03010b441580900c614207401e00150740c004030b0701d60464042a0481030715a0060802881c140941071010180120342e0800e52003066200b0058510b500c40350100304c0c0c0684401005544020048000420050f0090400c00119001b580d645500045210b5503060b07030090105c101b80200019003084600720603c60031300100d0030840c41242055500c5001e1b0241040c15a150900400d503d901c4a0348500000500c0101a910a40184241a074040125030b8040c1e400c0041d9800b030007036000002d0004422290000351403400080d072254103180070025203c501c52458180314 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 934462517 1250 934461267 934461343
    0x30c080a111009031e060e0706020d11010609050f06100201200c070f0807080615010e040b010509040e1b1503011712130603062306210103120e0102 65
    0x40c050b80803c000041580152507540c0002e42000041806040c1d10b003490032104600207011a07070340444e0042c4882c0e0780000f100d034010b01305400c001010b05104050f40f805849150002d04100341000b06104050164808860107250111420440284a80c1040f42200e84060011118255110044074042c20500040c020642101c055581c010f4a0707119441010705c140d40103840f0340e0b00c005010040b0301c00038020107030400300e40c0040003001000d610008103c2c0300c0311201a44101c0d41e40d0b10000290380101304891519401400a11508040c02e00e51038070b9070f2041548065078401c0700418400c0b441c050f00703100b08145044000500303613401c007580250a40d10603d003800007440750740c50308292150b5034006418036140c8140144915800d00070006d080e0741d50341e0b10004001810400c02c4e07441901c8125040d541c0c000655155841d0301c01d41024200d01190103080052400b0700800100c1030016039200d200440c0030649603030010403070709001266103040790400d0340c02c54988801010541d5940b1003041c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 934463767 1250 934462517 934462549
    0xe030a1a060f031504080c120f0703020d0f02060109050a2a080a0b130b010e1903021008190507030b1504051503130b04030e062703011a0123070c030c080a11 69
    0x140c401190908d400d1742e42d4001c0c0105d54140c00c000c2415000c0550401c01d030745c819a81031404118018402d48041d603980c01c18060702074040e0301e484c0011002d0006610001160701c11419003520600000d003120307441c0440c40c42c804002020400098090102802041001e060241c1464004494120305d0350003412115425030400140609071003060f5240c1c03c204508202020080c1c8042d4618410050442c00750140002406507240402c05c2140d42400c070403000602814001c22076980f0305000320014054540070344c0d400b20211034400c2004280e280507006a03841aa0500540a6100c01e15000303404106c40c1202084842025140004c04613641d4682051080c240000c43e6850741000800b140c002c000c107090700d4041c10321200701e00d904e051441c11035080e00394000c00620710001c042c00300b03225040c1101414080c210a1840083c0340b03001a01c219895405e4500d51508d0f910310f040c061104003131000783c03221420f0060114150f0300101d1007100e40743d0702006800d0030b080100240044d19420700341c98 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 934465017 1250 934463767 934463773
    0xd0c0312060b032d0408030c03060d020303030c0408010f0603020a061809020414031902010503060f0604050301020f1902070e041e050601090516020313060e030a1a060f031504080c 79
    0x82c68022510180d402242018400c5240c1c0c0c2100780b03807906500d01407a102100018401c20711000c120120110b9820052110b0791a40c2c955403c80410086201480025014400002081710b1104140054415622004024030003c607401a010090301c080c0d0201a6120714284001c0000c00c0c01101c030003020102c2d5200b104180c1c0d990340c1c2c0c1d0604a8120307034400d402d41a0320b1010b0181038507040c00030300c1c803103d000300883c4410301d00d0f80c00003011030000800d00b81c0070707581d0781a0304071480e55540c082c1d50040900400039540c5603421050b00e00320303401000a10308110004840300036001d0010030b0700801d450003501440780701d85d256100d10380e4031130610082c6008410410700e51004241d0a00441c2c0c042e1244e204080f4003814980c0000441025219040003107400138032404512146005a100480c0c0507440d01100b960396040019040a5410000a0411190f20041e02d6401d96900c0e0b05d9100c0c0100f1103010204102a0f820326849002e02541258140303a444d00140006400401406011420f0412 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 934466267 1250 934465017 934465019
    0x180415021c0c0c210905041517010204080f0a0302060718090e0604110a051e041b020a0c15080711070b040b120604060b0f0f130b0a110d0c031206 64
    0x25801100c40080c48a40014800e41141041c40440e44d40c8542c51110028a4002c00940d40c00c000d200c0e04240c02500c0c4a10b480e809a215602d0440c0c5461024140003009040307285070380f000a50003940244a9200903000d415100c0b06203900c0810107086864050300a401959505a0103c407085203050409440c840081c2c1e010891015601c02c0c1d000c4032001e440146030b141424100751001e915032101c4540300c0c01060f5010311403900c415a081d40c00f0300c1584070b00d0510101c0100040e02400c800c004445102c800149107032910b6900040c506040c5020b0002d031008a511134080c2c5e0400b845060800e07000c201200c02044c00c640c8500c00c42c103003040c501c2003515482c0d91682005140340e84258409a50400080341c82101d440213820460340002c011101000320514103808a0700e28052100c01881642c8041038003041200103008882618201001c4c0f8400141c803913610100703a0700016500d600041c0c03146101c83c480c07040003074244c8250100e6120130400e6100da80d0105c1d100341402000808064031414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 934467517 1250 934466267 934466317
    0x50a0c051c110c2b0f17040e0108030a17090c0306010602010e011a0a180e010204060804050c0922020604150503071701060804030804140a060b18041502 67
    0x4907446400260b40d8075102038410980c0032518000024440c1c2e403140c2c81138408844480f080440c50902d600d2120a82c600c0012641005840d8041141010b070048460701308000020b04804024400c1d55004a0b50041c143d8850b076003607540b40a80e8510700007180917a200c0441b00c0c045805141d40c0021580d086a1140300d06001190510300c080e813102c800361303448807000302c02c000c0c00b80150242c0b42c41c0a40041249149040040d00741030b038620400040c44880f4180a585006541154004c40940b10082d5a80c130b9450100400310780c2c0845081d540340c05003140b080c10710700e404095a4061943c0c40d6000740b03241c05140101c0070981540340d003264415020400029032085000c03003503088800640701e480d100c1c906544058007148010101e0a00c921042e8018070410307412259498005405190002c02990f55140c100b08440e601440381c2814419044140c04004903504415204d4100765040d100c540403118030304200c03100c2039500400d07030540c45010040c605402c2c2d0251840d4807100a5502d0b550030014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 934468767 1250 934467517 934467553
    0x9031b08160308011a0f030115020717100606050306030615040f180c0b070512030c0d050f06272e08030a03060b1602010f030204050a0b070b060102010606050a0c05 72
    0x6072086012030030401c010005002060100c0c10501d00c01c8929601d04111469003480902c014068404260110052074a00c140308122040240c513039030320106c181c0080d60003942d913a4080c0c00b0440c070001f820000c0201e4640e102c0c00c103130b03801010090010f246580303644088044004074600c001d070304199503070920f04207404c143c0100c0d072146540c508082000b912a0a02140701c00c07450f04843c140701350401c440d01c0001d500241130340f06400e044070280c0d142e844134100c0407007900c80e040e100c18040b403c6c130051104640c911382d8040c6c011581214444a241141c3c02403088109180030401e18010007200003c1550f400140e41c0c9603001c040b40e4080030040c1d8420800070700381c6c40765080040c01e54004a2822a00d81e058491074010f0030410706480d0500e84c14450000340030505910013030412207011081c0944602a40513580038042c0140001c1441d602c4659102164000c0c140a40f048500d113000310711a9401842180d00b83da42c0c0781e4440e450030301388a80590f5105408001116144940d0409030b0a66441c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 934470017 1250 934468767 934468807
    0x100c031e0501090608060f040f0c030c060201050601090f062c0409030512060406050904080702041514031e030304081b030711030c04140a1a100302041809031b08 71
    0x324400115035040c156840120f82d00c1c2c3d042500e02d940300300144088041400701540d0303c1940b04001c05800c0d4814074001004801ca035100034442500b0307940208220743c045d003159100b0003080e602e00343c03081d0352482d0300b54481c0054030808011075003010040b03481010b14000e0b40007d6071849600d03e01007444030080b6045030100141a000a0400708100703442000081191340c0107542100c1c01c0c426a4240300000361316907030180004013040c3d0002006021506e95030490040050501d40490f865650f4003200320003180d10f500d11a1190140c81700c42881102c00c0c420241008001c2c0380258216582d81d42c4032501640890030302d101c060200c03c0340f6400004104014102c0c58810070f046070801c82a08281403801182030840742c81641441454542202c00307004460303102c901108080f130204000c6010303c1c80303441814042038002c1e092030001550a50141c005004031040c0d1940402d41d0b200402c032500c05c45455aa0060001d19041107004a00d1504401c42c20041e00541e0214036081030403900070840c500b6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 934471267 1250 934470017 934470071
    0x30c0509100504230f010c05012301050f0303040e01062303010b07020112050603100507030b0901080703020a060228060b03030d140a0902150c0f0a0309150504050102100c03 76
    0x2000074280002d00b580c10800032034000c50030b00130101850880006107903480c1d185d05141000410034031101440741c01d4100c1d05c80d1000e2007440080c480802c5110344001482402a1802030048003c407112500380042180c040b0384072082c0c914126400c0441c111410b481600b103022141e28000c1044c01c4800c1705100560080110041241d036491071403001424030b040034024844068a441c040140645003c0340541019841000001d51551540010340080c407400d000c83c0e0300000c00c4800403c04010000e2118240c81c0225181000203541c1d00d800c176624a04a00900c2c091200501c00000400d0031405400040e440b41d44040303100350304200441e141d508209000a41680c50746800a21075a84140c032641001c0c200d0800d020078241a0013081e50a28280d21150302c0410004100700708020a2010f0400800b1400c16219500d04905000b010f0f020107014105840c4100200418454010000c90f0200c43c3d0607006808507205a02c542401421907108000a07d62105181c041d1449010000d02140b90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 934472517 1250 934471267 934471277
    0x1303091d011e08030307030f1a010e0f13020c06060310090f030e0109170a02120706091e0e091605090421020c09011e0806010e0414030705030313020418030807030c050910 75
    0xc0c481d08c1d07000351000c440991809003168500c01e10140d0f07110b0000081640140d84100389018400f0100d81e11280c1c44600c070000394400701e85007400e040f01041c820300a0f001102200c0506222054800485032481e2005002e0544000410000b0303019030b04070f26540c00141000c4054560380c88034141c1c2c2141d402c6014500b40c0105041001f14a4510300d60001e0060038030040c05140d040220280914081d4054000400c6404000200c0e50840100d2040034118501c60a821420a94042aa00c842d410b142e14401d541a4a01055500707007900c040d482190400611b030941380c0c0451913102c9044103a594441180a401c202c55030f252126084940280000c01c2000180b001d502240c40d1b0355802d0340c00004c4690400001006404140300391140c11503080040c10803801c4104489510b035200c4e07028000c1440c0000720401003980c1720751520101080c001c0e0741c2070080c13080c00c450000b051028030388024007040d080d4020400b40c03486584107002040c2c0c68181540303010300a50004000401418800780060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 934473767 1250 934472517 934472531
    0x30109050403180f170a050318130b09060f010201020d14060103110c1b0a18050a05160f121410080f0d0210150e1303091d011e0803030703 61
    0x359100915280c41a04050f20000440c1845041c071802c144600c42d035081d00800aa6000c034040d0244014000c644c0d100e800c803680c410144503c2e00c1100c0341002ca240c46003d19981c40180030913640544070711800024000b40c0039641d91000c102c04100e035020309904643d401c0c80700e603007002c0d00c9120741c10700e581c00c0d070308030900c3c1e0b2908030001019200b101c0700c2803107241c609000344014140e000032240074000c003600c18458a141000003242046040c3d42c801800034680031803c2c01d140146900403406208a0b80041c030003035a81d000084040252a00480700003038040800018591040307a41d0204440a020013244010381241314140c0000b0a8803003805044003440d0400c0010001c001c1036010b008103e000d895402c01c00c0300040d44a800e915080c6010a80300d0100e85100c010322402000138040d844035254803403c05200c01e2064a00c0024100d000c20090000424611f40a205980115980f50f02000440c3c4c00c01c0c0c200008052810004481410041380114a041c414405103100d1415564001517034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 934475017 1250 934473767 934473773
    0x3041e021914061222080a0302031603051e0402151c0501060215130602190302090a08011107080d0209030604050a110105070f0b1008070b0a03151d0a110301090504 72
    0x16007074518156103c2c203402c014500d680c138000612580e2010f441c43c08030560038000c941c900c142d0110b0190017010b9200000d010240c094141e4061f40c0076109020076030001008803102501242c506076011091120b07625500c5a4440d801c0d1112948244003400c00301600c1c0e40c1490804140d049036180d15001e0710340244039480c546061142c0303801010944001c200841428060403002003001e801e004035404841b4510040c006903404440300180c0810b000c00e902007038500300800a4000c1c19400d403241d254040001540b500c140210780102c02e90011a610b40320140e6628011640843d1504c48400c0d002d000b154a02e0b6400d00c4038511890280d405491100168030f00a550920ac1400c907a040c0001170110b8404110940038a01c00316034171091180d05c507284c00025041c11051680150710f90f20811a010841035400800b030824031030251030a220205440001c0040481c3d50300070108000c03207a0903660201d901403185160030004544000074041c0d42d2582d140d40c19802600700744003c9403903c040c0010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 934476267 1250 934475017 934475039
    0x210f070e09060103080901110f072d06021f09020406090b03120f0304031b020d060c0e01030203010b1210120507140103051501031109190e06120303041e0219 69
    0x4800c1d0600060000ba41c11561401400c0c0030300b0500b2810000c403140074100d0030004201a0000c0709840c022210300d1035461100704541c2d80d0802c0c1c13009c0b4040440b00c0b00030851180031101000d0316502e401504040c00065005410030110b407804942c0315446084d21405601d441c495034001e01800e4901180c1741d64800181454480004030b00d10703081000b0480700016156040139241c101c0d6142c40c189058420a040c20014400b0004020b5445200c5a03890400c006565100e640f0b12040c645a228078443d8400040d01203000174819501c00c000c00f04030760f00340209030718180f039844640300035101a101d8440b43c40800425007000111920303400250207000200b05041d0107001d010302481c081c8010701d03041c01c0381c51203001d0b00341140c1c0c145030710b5540114803141481c0a8540007003000d45a580e07200c4801007000c2c0205006c4c89081c0f52864400701003043c5060044c0c14030200c0c01c8500065140d910366585110406511410413004082d01c04000d03001603440301c060082c9800c02500c151591407c0c00030000c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 934477517 1250 934476267 934476271
    0x9080f18090412080c0f0a0f08060d020108040b0a110d0204050a09052205010b06070b0f0c2d1e120f06030a060e0111070c06110d0e210f070e 62
    0x8880c4808804100010310f0004240040d05500e241c0300c06107483e490721002460190341010500c140000c5000713190307203034400007449407402c00750b0324221300351500380c280448d100c04030718007900007005100090089090307100502d40190086c600003030104a03070000148550420700307080300380303940024040081b807400c011410040c1032074000c20082400c0115640c08640d00d0030003003007500c200400703103182804820352114292610140442d581d0b0011440c180c8070512044902580c00096800800e0034080034034180c40b02911140420009811a11303111240b403440009401c40c03281c000c000118007683d540611440028000c0d0f185a1580c0c1d40106280c0c40034801003038241c1c140d20308400c204950b5000500d140e40e00c1d82114001070003006841c40306002d000300f01035424440c040050b0400410083c1e00004046500b01d40d54074111007610080e980c3c64440010740d9400280240211021030303d070140c0d00d14140f6240212201c0300d416100e0419007080c0306520081c1458101c201c0401a0b0309502d01010b13 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 934478767 1250 934477517 934477519
    0x60a060608060f0409020f0415050a12110d14070605041412030a0f03020403082115030607030507051303080415140d020708070b190b040203090a030f0309080f18 71
    0xc070185050008140e04541c05000d1034840c90b1105000d07810754803110000d0101e00d0018006009406105019000c49115449518040d05c002807000034005411140d0f012032607400440d0203507068015040211440e41c460040c0c5a407840d048507072a40f607c0402000c4014950f03611011b40b0703546400d000c18900d1000300ca0300b0f405410394a0440e242014040211a000c038080d040411440106000c200c0082c000c80d0401000220002000103150100e0700c600000000c04000311580c0359544403000c48240c520782070058043d40701c100404c0b0501c0c0241c220a0307000d600fa01c0c3c5a0704084819074007840c0d403400c5a10a940c2d1460008041c0801e026100c1c600e40460b681382005030084869414280751440b13078078a403844950340030a606c020044103008440354541c0000c0c0c0c5503180e080003940e00f080c101c540e0f908141001d01d0701c04500000d04050003980c1c4544110703405082a56941d03181600c00d04104103a0030304141e5124a9240054102405072180900001f80300f51a030011410001c8180307094000b403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 934480017 1250 934478767 934478777
    0x80d0e010c0e10021005070215130507081f050601140a031401060f05031f0f17070f0e15012001090b07090b0d09030306180203100e09120c070314060a0606 68
    0x40c10f40e40d000111090004a81c000016865842c024100d0a00c0b0000700d00e011105800c00034880c140100c0d80410090768041c000f070300c950a5942c81400d5840c0701030201c803c12400c00c240c1c9903103030020984c0080c0c4d0000d4181401e02030b0071b0440038405100e900c544000d1000c03030755400b42d1251a03000090350901611040c20031503000c4200c4000980f56000040c4660541c480f40c00820025030070400301d03500240048160711405985402840740c011245080041d214803c00c2c41c00078207294180c01e10030441c1c03010791206a494480005032540008400c50aa050105081c0e00ea0071a812283d03330b103003414941e4000083c403007000d4a02a40c18440250080c8101f00348408240111884401100d607900c03e00140010310303d40c0791130203801030000c561010300710001342190303140c0d022559001113102e11514419003c244e0703100c08100404041c255199030b25070740a0302c0445800400c080042c81e10000f007030110b0b002d003071b82c0755140007100c1409421851150410010310264000300d01801e0007508090a00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 934481267 1250 934480017 934480039
    0x605060f03031c0b151207080105100807171005040b0d23150106030c0206060d0c0605090a05060d0617192909011d07050f0d080d0e010c0e 61
    0x203560303019a1014003460042d044030039000840a51140c900b03c1c034080e00d042d040c2042200d4601c5c0c581c00201c07698010000e0345000070340c000d110341d9045059482c0202000403513991002d0440303620313500a2440080c0710603440705840394040030a6052155009410b60004203040000740021707500003401c0b50303005401c0c0c840504001224410840b2004a800301c1116284207410b002a2a01540319169900ca2410400200e419075041c1c1000800f00c61a03002c0741c10581b03c2a041c01700c04d81c100280504004c4080c0d201303000752803040c001880003c00082c234010055486100003902c90380b103100c00320403c5a80380000c00c840c4008180c08002d0344c940c0c0c4040e0440301c1c0c1c08100c1e07a01c80c0e20a803800825442030311500c04501981034948112651a14034481150318248412038028000d541d01c3d0802c190710307043d00e95161100060740c042550805484041c00000301c0c810f00c07602c00741268085a901c0e0b018068001e10041612583d42c000c0903032400401d00c0d0241710009420022000b16040c0540c0c01400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 934482517 1250 934481267 934481269
    0x110c0105071713090f0b03120909040c03060509100b121f0905010e1014090d0c080c0303160809030c100902040207080c030a230304020907090909110a0611120703050f030f040605060f 80
    0xa840d0901c09c144c0d1300940f160b60714640241502520b4000a1100d03141205000603100d0002c0c02081004009600b080488040b07001c1110680e203904e1042e079180c3c45011000400c1d849801c14044034084100301007150403041d0380381400c0d03500c8880201019402a4004210421039002d04411400da400035020242440c00800ea121001416160f003030048400140f81044a40001c4403915406c1c80140d0b900e0741419903902d41d0400c001c01203540003071848000724030820303000702c21981c03c03d81c0c0600034480c5452505004d4040d0020102c02e0740c3c020340c01d21080020500d00070081000ea29400d010703659803800b0800190044039003800e002c007a007000850b01e80c3d411010304101c0350419012038092102c2ea1303a0340011504030700650480d649803400c001e016020011b03402d002420310360342291420852a03e4003003c95078848503100c017010560094214085009402c001017006900a250183c541000341401500f60b60041d140b00c5600c500b40c901300010302c0610702c01c141d007048003141e845c03244c941480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 934483767 1250 934482517 934482553
    0x250f030b040615290403080408150c0a020a060506030a21020d02070302010804230d02241b160c0f150e0306070e030106050a06030c110c0105071713090f0b03 69
    0x10124074513425001c811400390001d00a55006543c4441c820750740710344640340785131103200d89855480c04031000404900607820034001c0d02e400302400d43c01440e07940c0030b54a6110180001902e42034140c0140101d07940030480311145110f40c024101401c500d1000e621000070701c1d042c2911001c500315000352005000607070780a04019001508403e20120800e204070961041c0882d10400e241d851046912100d5070380d40104420070012290748101c0d4600c400c070009007640390003c48503c507c407050101820403182c0c03410042c2c00c0b4000100c4c440f00c40c03030610780d484c040300680075003281e0821900b1200400c4039100085c1500c10300000ea2508202504c0b252011959400e0098060343c2480001a000100c6440c00d60280d402490014002c000d655a00c0101400a00c107200007200090405003070300304a4840082c140b8446401030b550b4502c0c00c0d54a03180c0c0d0030240900c1c4070740d0036001001c0003144201c4400c82d1140001e803224000c00181e4880013401c0790221080f062105d40250403c62501500030004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 934485017 1250 934483767 934483799
    0x6020607091a030903210712021317030c03030709050906030d211103010306020a09051002121809150111160311010212070809040b01030608250f030b040615 69
    0xb0300310941e12a214841054110301800074a280903240310b095851101c01e41c1e007105400781c1d045454001c801c0c0f5413405040141e02c64192448080f4110f01e078104026440c072001030082c030581c0300a4a00304544480e1103419903005a90540c009242020244194940782c0300981d0800760450080c001c24212a401400a080c0b80301c11540c02d40c2d116040510180c10340d04a00011904503844981d80d603107a02d07000c00250401741000d070001726004008984c1d07040c1002851142d00c00d6400410b211111103240c0300c1e2680c81100701512030051b40c2440700e41c9890300b00b030843c080ca82d00d8002d151403403907001c0014065128010a40c80b154042060400c0c0034904142d810143c82e00034681b003a01d5212000140e02d03141d460080400982c1c0e00240403424000900c0140002da038080f038007403016524040044040d142107014031120b03a0003149080404548400d980407042d00070030322419160f50348114200c1036a078603500071b40d0b000c038003d410402040060b110b10300300808105150402d00b400d180c0100c4030000c103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 934486267 1250 934485017 934485059
    0x30415091104050709050a06110c0604050603130611031602012a08101a07290109020c01090501020c0a0b4506040c06020c041e0c090b070c0602060709 66
    0x743d41c0c0412078441c42510880041c2c040031304003a00d0030340c1d00c0c14000c000c2c0303d070403000e00c1c1139009454500c1d00501c0e0100803141101c030700800e06821034a50300c102182e015500d0030210380311030343c0389500d20700b421811010710310484104001e5900200301e010040c0c2540e80304610252180340e1a01115850201910205414038240c5403114603a85c0c0d414a05000c204290000b03d00c2c0510160300300c1e031000c2000000c1c000144030b03408102c00c4d4070505440d000c8203217556141d81c40f0602007000600050070701d58060510002d4100000c00d0443c02c5440d07180c22070703002d001490410381001c044901800200c05007150451203400611180c003080440180050180380d0686400440b40c0c1c0c8454802079624061018552501d403d407403850815240403000291a449558054006d041070001c851a003031003039242503a1181c0e600700007181c01005100040141c80070f080188904204042607040307041e800b90445522170420400c03d1400c004000c0d140c50740040450040020841c0c080c011160260540521442c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 934487517 1250 934486267 934486271
    0x6011103030a110d0e0f0f03070308150f040f020d0b060414010305090703050d02060103140609060417040906090605030613211407030801060f180e2a030415091104 72
    0x181403c0306514070408a0400c0f4890070940284d034410408100100c034a41c100b401c640c41600300408a6480f40076042029000c01c05020004504401d15407a149028100504202082d03a40e000080c04440b0b002c00144200d135808110f01c6006251486031600c42101122428205850080f100449039a401181410562038001040e04910200041005181c0c028240c620100541000942d42c0b0001d100560b42103c90100d000c123002c10220340039020b110713100064040c41e035807a281c800c00f840745418117400a04007000000341c1400c0c0c0784a014003501f071118001c00e0f050302e44000c1500e8804051f22031141e4112030480000060040c24101065025070116401080c40040041e50104404405400d02000005001e0304042e44801150306881c11030300c0f000e0440142c02c90842e6000074090442e0305590b0007441c1804640d649200c1d041c0e000700c0110f8149601002854892119040c2c5250352054920100a10042009010440f41100c9490364104030030030194030394061100541c40d0a9008603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 934488767 1250 934487517 934487531
    0x80304060c090308071104050a02090d030c02010216060804022b0f0f08040306050f010819030507080d0e030403110105090a090b03010b031c02190c0324061203020606011103030a 78
    0x60050320b2100041d600000001d03195851303801c1c1300d1a840542d95280344214a490001018180caa10035a0035050010b0204508210650342c1601d031009030310b1040c1e0551249450846042d620420080060210390b41d9940740d9081c00c0c0306004280e2400c0d40b141c000d80051210464800c00020ba40010860b08004200c0d2064076900340b901d86204a03100c0980201d00001d008070922107990061070103501e071460400026130f40d42c81419111008929403d400e41010402c100c0440e01c20005421941c4c05000d096150a1101c07980d0f008903002d0350300c0902242c201041c20805c3c42001c1c4503a0601c0300c1c080c03c203940303807540241c0000d1440125010700b4510b072ba514030081d030180d102503103d01e8172100f000c1c00300d9803d04000c504001505140c080d0303820040c4581d050140c240140403003142c04096000c112004911300719910300118a880709900301584100c0408010000d0850003002e004028505505401c59101e040080c00d0042c020545810310914400d001d41d0400300000700d07540852425030000d050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 934490017 1250 934488767 934488791
    0x1409240121150204091a030624040209030604031809020c1e0f0a1115070519021801120309120c03060b01050904020c10140405061b04090f0617070308030406 69
    0x2e0300849003102906202003000700b80d018075507000712040001000728070b00c40240b03241095520b80701110340040e030020417000e040c4031290034890211f41c00002000076082180c290701003840d00380125020380001d90308002050a00501005840282052200035854816000111a40c440c00c2000c0c014445230420318424208006225400c260b400c0c50f0140c40340c1c61064140b8150b110007124020744144140b040d00c00503411098201c80e0050791110140004007111007a100c0c1d0301602e0141070b07030816030340c3c03030944410038419150a010f841c1c00504000310222b1801d0003000c1c071186820404070517406182080210f03203066040d40c00c403a48041c001c66103c00f0300340101e070980640c940072a041800403e007081000e0001c2810341c0000c00c0084104810203418095501c500015207014110f40c106801041c3d50204a030056005c01c100c5a40706890940c1d80c16000b0211a142c1084103001c555401c0300784440c50b040301c4450380402041005080c0135003103860300c100f0b07480064001805240d0322401070b204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 934491267 1250 934490017 934490033
    0x709061b080d0501090b0a0e0105060c0a12210b031e010b1c0b09071d0919060213051207140f04020a0203030103061515080a1409240121 60
    0x41a404803801d52120612607a181c0548400c0c001d851002d4204a4851a241041c0c040c0700115114074120a20603481c1805100745030740a210041024014201e40d07802250b43e6a40b007200f02c00c03050341d40756140f5201c84111181110119001c0b10514202101c201c55903400007484440140d02402c10b0f01a00c490000d000c1c0107060320303200c1603044114003861200190f0b04d0400100700320b0140300188065a14512103984824040c000e40c85400024044c11a1b6613000709807441c1c0c8410b51400301d1795089102420025038010440084800359000610ba40c1031340c40b0500003070001c1506070703031141c0b0001e18120443d031600200c1c0900341d13420525180c0d0002a56500418406150028004654681000c03400945950007404156405400d1000103050303400700301c00903821a031030200d0118041070210b00840303c5040150914040c141c5a440f01c841c1190403050380c0703000c0e81d001001003c0304003805003000c40c00d1180310b0000d02c5045070070313004101c443c0c14200b00d80381030204e00ea03c1c01e001400310f04e01582 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 934492517 1250 934491267 934491317
    0xf0302041a220e060906010b25060209031c02030a05070201200a12021b0d030c061406010905010e0a1403070e04050303010f1e03022202030903070201030b09070906 72
    0xa030003603850120740500c1c2c1c2c090054501980c15094140200b81d0009202656040b0950305c2060a9211000400c0051a0140a050340c001500d606003488803140b80036035000c0002100642d036141d800502030354a454100041038041302001b0100080e0f4034a680701a40703e000e400fa0640601c000010b4500031607100d00c880d202007034900001400318404030600d80d5030746e0119443c200c80c50f402c0700e00109001c90000808400b4019644501207d9807070301c1c4180002603140e04012424000010301040000360340340074064180c81c00341407248203851305000040000350207502060500c1541543c6103425164100031000703540e9a000706090301050350000c00e20b00510341d40408110048101800b00f0080040000c43c1200d401e0310141e40400c0d19200c120000d00c00800b0b4600041c401e1000400060504940305480c07084501c180b4400c001220300034000740d0f030007241c0146007600001803c1085680500c40c544103098240c0d00700c829898801005884d81c9201c0c0510000d001e00441e494400352600c1001035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 934493767 1250 934492517 934492519
    0x60305060a021902160302010c060b03030d140c13090510031202030903212703030703080a14011203030222090504020f062502030c06040f0303080f010f0302041a 71
    0x104185021035565000f50004078080440304901e4001d0004280300140d48042505041040e036221403555005483e2609450300490f90350342c07507022020340b650b0240040d245904107223101262100840c0d4500c0704034480240300c1080380009000711443d01d10003650342401ea0380000d83c000f440b901d8124841222441a9100a2a100c0400e200b210905d5020001d00b9412100f641246c0c54110140075a4807440c03010740910b000c4240c00e025103602e20207241001c910605c0103034800d01406900720003003070449c0e01007441503010902000038040c0b2085c0b0340c81003002c10740c0d028907045c01e95410011905851025100058105900803170300c010400d901a06203d0a900520a0107800c1070742c2c1d10800c00500700440e0103034803680e001d10051132a4140703101241c944d030200d481084149031070000540e417488103e400507070709885004606550b0707840e0800144041e0030700203108080c1030315602e0001c012450080c0b10b446082c45007001003040300d283d051a08262070781202c001c10110304000e41d0020030410a9803003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 934495017 1250 934493767 934493773
    0x151e071103030a09030b0604051504090204060f080708160602030708130e01090c030c0206040b010519030209070302120106110c01050313060c030501060f0e100e060705120d0605010e0a030312060305 87
    0x51082d0304d030010a240112446800028001c1e0b0321941040704440702100d8110360340079115000d410a11701580316031095440144005007007a110310f070301040c1041542000c01c0c542d00018040c000b000c3c0820441400c00c4122804a01650506900944a000b058001408a400410310344440b106564101019102c007222036030341582d540e801702c00500303010a9001c01007403414030b8134911a0700c0404c4061046400c8951000c2c181d1030801480303250200785100191001d071200c0c0120044e52102c0c801c1c2d0007175070140c1c0c0c0540c95000720700900c1c01c1aa8180c0c006030502c49200003001400d580403c0416010409080481e184da48240503d080c3c0760060f0380080005141c40104410260594441030585038070790f0f10f0702c090b500300340c1c03058a070402880303030003a030101d1128070700c048862180007500060000900030340d0501a160b42c0e401d290800050303d041d280301011500000e903119602c5007074001c020910300311403c001c00002203070404110780000390811002c1c1800310030b40840e0390040c800460b801000c07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 934496267 1250 934495017 934495027
    0x60f1c0906020a1205372d0b011e03090203030706090c05010c15020a0306030f0321111902030702120d1b030509040e1204260604151e050114151e07110303 68
    0x200440181004411219003003800406001c00300241301e00080440d062b1244d0101c1821219988010301e0a900d800b01099203844181005803014405080030a00c9200046280300d26494801d044011640003039041104000100340402c3e04c00d10388840c40c81b0584401030361510710036422405001160009000c2d40740c0ea5580310f013010b501142140701c210304502c45d803c0355030a043e9000141e03501d403d6160701000b000d1000b20001ca4079084041c141c004070b401140d01e007141650100b4540c0803221b401d400103400440c610a00305801c400030185010004000c01d80001499802030421300030071222a00455a07010160891b0b04100190002d08a120741d0710368a480c1c0e201000c0e0300c1244010417504219080c41d807200c5104100007074a6000d035a00003612130300c0d4496a0900c6009021400749e80c03e418440740f00c880c45482eaa03201d6240030b80004e05c08041c5800d410b074103104448514004150080c4810800c1c40c46102d02050900b09200c203285203250307525054140b0001e081600c8444541c14040028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 934497517 1250 934496267 934496291
    0x2060c03120708071709030d050f010f090b010801031b03140c040608150103021504151d09070207060f050d05070503060111060402060f1c0906020a120537 68
    0x805808006911481c000c580d039100b840c12a458002920103001041150025100080c1d20380c1d0302c10790000b43c45045a050000d400c0404054420a6542500b01080c000c018484000c1e002c108402070300080c1e105020082480c00000c04001d0140320140244041c1141001d20415464034003004541110313084060f40d028107441c54981e2141c99250707200c0c42c40c04500159001012481510fa4036000744000120ba103541c09020025171032035000c0302051820000821111403010710b00d10698081c3e51200d00003a01515500c0104038a40e9403207124000300d60801c0402e90340090300744243c44403868056601c1900c2941907465000300c14052480e42d0919080044156000c80503510a5400360f0740e5801c003640781c40f265900c1c2c0000b50340107908408204005120720441070002c0c00418114a171030b0056104040c01403085507038645088035541d0b00028000407881d880040b100010304801d00801c91070030890904180940040d0441c3c03c030f25200903180039024038491910710b000ca00d000040c48640340101e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 934498767 1250 934497517 934497523
    0x818040c0509210a03050307120906020d050f0f0106050a030b0303161e03020c010e01110f01050129070b0c0421030305011403030913020d0c0309050d210c020a02060c 73
    0x1100d01400c3d048650007007a81d2480c1c02002000400f0000d088000300030745044a141c0d00003030011050020107aa82c040000340d03403249040c1d4034091480141c440341510354403425958003074000280c0032460303000d2120200346034018a04459403030030913541c0c0e40c0c000c9106070050100d0010391a0300d4000030440c000300c0d007451700c0242c00c006d00c54403040100002524039440a801c0425000d00180e02280451100394000c050014072a24141014441020021000c1e8641682020b45048994507200104141407110198541103025164032145400d21204098200e0050003005020f80b419440071611000040302100c010340382d02c00228610321500b940803c2202340060301140021301d82800081c82558920303490301d003104020040c0d49800c11623000c01c42007446009002600c03035802c0000f240a20400e10440040281c01c2e280814006100d05005080ca4603640f0703603070140540401c01c49031168480c00300c03960340041407000154083d2041c0c42245055506a002074000d080090181c81c0d444c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 934500017 1250 934498767 934498777
    0xf0b060c07090e0313120203160b1c0605011d0a0915030b150a03030c02030709020c0c040b090f04030c08090d061a1207060309110604060f02060c070c030818040c05 72
    0x5101807219980440d060344e900d00c150032225540740d050500501040c280c81503804607150004040341d41c007402d50841521120002d80c441500d4100028209811981c02864916000c000358400c000040c82c00f4000307802c4c6041840340207565401310000c03140c26951071000602500900302c5c200804940c1000700c452001050109450301a050000550201000580304801d40e0018160319041c41c51542d0a90300c403500080220f03414002c2c0c10002c1030301e41075880640407282c8418020441e54400710140022100030a03080b60242401c14100000000803148a58005a041c505800c02a8031401d01411500514a02d1030b44401000c502c9028800c1507080a00440301d00c00101618040c05c50030009141e2503140359541a4014140800c0254000d502c100d0119004800d40e440d544100b40008029611580106e00402c4d103801c405c41c0500e40c1040300603840840500312fa4506405a162000d405110744130040c400c4100107440401b01071900c03031100c0c1411015006105900000001a10070b07044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 934501267 1250 934500017 934500029
    0x6070e0901090b012006010f0f1d0402030c040903021b0a1d07020a050a03090905011d070503130506130606080f1902061c1a0607030806040c030605030601151205190f0b060c07 77
    0x70029010400b610296041c904564ad000d004500d451500303440c55005040003041607a140c0a2840c5200d129211801569100c91084d4081c0a40790482c0030306041002d614814203024140d808801e0018807005c1d000070b4502540c40750015015079504100724505859110000c18074040c442c009010150805030182c19030f0030303881050280743e0700c03800700d9020b4180d100303400300c101242800030894640c010310080d600481c0c1040e42c4001c0c84015280c00d0300d0300c2c0058079078082c40c0090b0510001800514400c0c20050404040980700600380c0350700d41d035544c81c0046100346d1480701c0ea08058003150396240032a80c010811411400f40520307040340540052110a01c04803d62841e81414150381c82c00303400b12002d1603815110580306440c0d100c20302004000c0c4038114030516541d400082481d40d010003490f80240700841400c000310082c0c5000400c10b002c00c00c8003a4032641030600348205426030300340350100290007000008840c051105048064016420b800d504103034009804840c010020a540080d075038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 934502517 1250 934501267 934501289
    0x70204181b061209050d14220515041203050a0c121d060910030f060b0714150708071d0901080714180103020d05070b120906070e0901090b01200601 65
    0x501010401c4c0d0f8141d240041c546d8220049006001c0c3c004d110480c480c24400300c5190401d82e640b42400c1034031005041e030702c542c110800c008004074030b0f00c10000101003108240c440e0038035180400d09420070440403402002d0120204410400c0c034440d10a071141c142c1c01c00380c1e4807009801881c01030001035401a2010103000541900b1107541080c00031260001e0000d4a6000343c0051900110010b00c138552144c00d66503103d41002540300c9865000e003140d1401001041d5014901c10b543e517141400e64030124003400020010400000e40007100036500c002641010380b507985020600c850fa2145c42e10209034008101400030551400015003d800e4810b89006c124461100300c0c10800300c0b030b050006078402e000c8200010b00042c00c02c0c20b00d100d030291146c41140d10341501c031081c00c100c4c0c0d001403014a002006450030401100c0742007200c0c0340c010605040001a0302c40031404a40d02c2d40050054244113a118145560564405d150310764842e041c411500c2601e11016100603101c100030312500025078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 934503767 1250 934502517 934502537
    0x3020607020d050d020a020709060e060909010507230c061602160807090b01022802090c180603150603130c0b0f04061b2a060c030203070204181b06 65
    0x900015061005281544443c0d082c080b0905101c2c0103540315590702c1c1e0844c098202d001800107882c1c0104406002041140809031400c041030241002008120f80749a07070501040c821215001031100760602c4410b440c1100c1c2c80401e40401ea50341c854103071507030082d100d588100300080c01001c0c007400001686900b915552002e554101100c24141d0045c422260803010702005102680d90203000300007010300680340b603800c03014258032103e1150b10200305a44908035003541107103840b299503980705280f108000c6c03c00f5400018002c078001c1040149015000000104005081240070706c0e08442004143c0c3e5a0f03494420b4039001c20001c1d003d401c4414288404000c202e0703aa40601381c400d91b543c00c1c2c2c03080d41003900d02001151700d1200c880004003070703010b5045401d01142204000692444180c210420100004044c40024041c0ba9100b142007165080520740025404011506a82d80444000c0303003a103800c844000040c500104c000706242440595080d0740c50007100b01c141196aa51a914106 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 934505017 1250 934503767 934503781
    0x628020106060206010513090812060a060908030d1a040906020d180b0a1a120309090a110f130815091605010903061a060f0d0f021809090a05010513030206 68
    0x41c400c00e0250b040540c001c00c2c010300043c10130890381d13001c117480b440700411120020f071109962540540b42c1c0c00c6114000000700103080c1001004a8002c0c111480d14a558601c0c05a0307083c0c130703405a0504480c58a403542030941c090f40c006558901891001030080011f056540f0300000251b0201610340700144c24441c5c4004d80c1844500560f334072a81120f4060a0360761456100ca00401c004003070640382030300e0440c15084c582c440440301510406100c0046581c0e0401c030040111480f0010705542d0b07003604003208440d030751032118280e40858140b1414181c0700c1d098800030000c030700600c0c0c209084500c00c44503588201091034401600809800060f2005c000443d45503000c8441c03507000f92808100d10000c03c00c00104103a0001c0c0c103820302894101081c990000005140f644030059254059002060400204506200e440311080e24003800b186001284600140c00d01e0600c4640c40c411a281400182e4201d07040c008440c01652000081100c1d160840340034128001d4007100360b0051060000003200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 934506267 1250 934505017 934505021
    0xf080a0b0903070317071101060f0905151c030203040504090305190207050d0213090c0e07030f0203010f06230705070608010b12161b0b060f100813020f06280201 71
    0x98580c060b5518258007012555445c0141c4010b8502c004208240801f981c66000c280f0541015003468040c000340700d441c00454074151070000e0712125007005014042c44180d511409200424805203002c05401c003a507040c03e87c154025540050b411a041240100070180d01038018584902081603580c159044120103d903200c41c24021244c2059502150901510b001c03400b01b42a2100340c030340821250300d159541c005428a640c4260000c01750403060041440e0180207030726030098011011419589007101c20b900580403403040c01d062001650840599000b007a00c80000521014017440d41c5008504d00290748000b20721542c40010784400000c5007502d44401140ca050301200c0c1e581b00300b515041113000404501c2c2c1305205c00d00030410f003509000101141070000315401500222018a4108140310200c1d2000c00d2851280d218500c0070248580c1001920307400448100c2c62000600c0c0074400b086e404a003841780d81c0c0d8454000701d80c5c55070910b44000c1c070700c140815182c2c0b0312407014a1448143d003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 934507517 1250 934506267 934506277
    0x10e132c1c0906030911030f0f0f0c03030d0e15040c05180105010503040204111911010501050306060907030b130f0c0f08160806181806010f06050f090a0f080a0b0903 73
    0x4001902c2c1c00003005143d1081e009507041d140030703103244030102051500181c84c224038a9030754409904035894000c0b00c00c2c2c00b8001100030203020303000303000300161410000c0d03124800c00e03600d030b200c19903900c1380c1c2e94000c0420050440000380b8290000910704103030400b140a90030501c65240f00ea021040d10304100890b40035114125101a15400c1c10354443e982088068101541101c0b09904107001c3c003c81c540441c0929140ca03045502d0b20030010941c0080d00d800e441051f00154060307804241445415160700c815a9840781c4507260024103c440c0c2000980384400001d00620001c0c2070000c95050884190302554546085445466003455281410b0f034204108940000c10410300c00c000003030442c0034040700f40e1300403c0100341c6032a540521001009180080d911020007003103c82c141c15404d01c0c10441075024240000d242c00030b240c5048801007442c81008801d00e030711030001c10303d80c0c13a0703444038000c041c00307005550441022031361202c0c070040c1d6a10300c1e024183c0e030b0071402502040c0d520360007100b150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 934508767 1250 934507517 934507573
    0x1707180303110a0606090b0f06182e0f020606100e0d0c030209100f0909150c0e030a050303091b1e13060305010209090c09010e132c 58
    0x211545286840541d04211500c100c19030701d009406201000460798815080030f8617044400003100300704007060044040308565401c0c060f080420141090756906401c0c24004c81084500c7c5c00d540700144814a101640c2034110200c2d1580300c0c90ac41c8400e0b0b003200800380c402000c0e5003103034116565941041123408515803490013140a107074015645080c0035012000c4075001341d0000080075a01c2d0b000c50030000007110346100d078404c2c40d01c09009040401d000d41c0c00510404406004208103a100d0745c000c5c0e84100700309600984c3c0c500c1c1c0b1b83c20b140c0c00b8481241a02d02c0040644260781c80504140351250701c115030344626801407003001d042000010301126002e08010b0803031520403d0308414011800c200d840401e5220990a988a80f035626030f00820015500c030704000b45c1c41e4102d030310a11115140140c5903905001e03007800854110799000144001d01e010071145400222111018003004051540c1c0e40c0d007140103034502507891045034000040340222003104039041c054050504000ca802241ea0340d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 934510017 1250 934508767 934508807
    0x7020114010b031807082b0512040c090c0c230318012003070302160e060112022529010b0903070f080c01030509070f0611030702040c1707 61
    0x14002912040d0181d036005000f4103504884068601380d1514055803a40301442d142d00542407210342469030350015219040154044007120440034002e442e5024041c07803240c0d40f00041c0c1c00181446119880b2500800c2c849104200210a8542c028001c5802041c280c4100003401c01e2185025140d600c2e80c14500303c0c08002d10300308a071030405a0914002c900c800350420024004005005454044031101d00d24800300442d5288403510b000b0781080b06043e480c80350300c1c1078034a00b0000a8100407074294480c2091030000d49c0f00d5282c180200003406903c4601a249105010841c01e212003841103100450189041e02d09a000700946200701c0c030440000404492000c40040210121001c007400158000a0a0780c0a440d103c059013100c41c8990340c429406580f000c40c0044aa5030141f03e0582c2207100000036101181c02c00f511130001d150248190b808002001c00d9038000c42000744160740300f980c0c2c001e00501083c0348070301c8024000c407022007842020115010100e904540034181c12200d0750215200b07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 934511267 1250 934510017 934510019
    0x21b010c2120040e07030605011e050d090b010807050102070b09240d020f0a03050601091a09040207060c0519050c0c0108130605090105100e060a050603090f070612050702011401 78
    0x1610024104030742001c044075102c01c86404502c0c81c910007420181004807201d0001d031802001c02419213030142e03c41414045010003541100d02240d2000300304800c01d090140d95000010400300c001d1241d100c0103410754210000201c1c244801252940484001340d08403040e45884030320b880250b02c03419030207503481600358014094440c01660010000b401c01e90626041403420b03060441641c0c0b200300000d0920500084101140b50988103d5411010070310f418001203040c402d00d9002402400c81d0802c40d8000440d0201c03240d80c0f280c04171050315601440510803a10040b0025103103821041149400c000c001ea820050070344244151041d0703480040090004041c00001940c800601400f4090161074803204003010a01f40c0c0500c0d4010b0036620000265031030301d4a00c000e08a0b180303808c89000034200c0f100303000c1c40360340e07601521082d0f840c22151140d883e11003085081c81c011740e50120080c0b5002e04440060529003100844500c580c00700801c2c419030303031030300c2049080381e4030000e10018007556040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 934512517 1250 934511267 934511327
    0x18060f030f140f0a0618021806150c100606051305060f1b0a030e0a03030509100c0b040f170702010c0b0403030605031204050a060203040503060c07020a0504021b010c 73
    0x1441880d03400780c034200c80c6103402d64490074107011000b20000c203190320800a02c02000154071a10103d0b045803024511052030340e500259a06002d0207446aa030100034010500c1d0707985407590030503910303003401d041907940010445e582e0b104c1071008a1456080e260034400074589006000b100c1800303a041c86089a15400d00301001860b41140d1010080000140600740c0c00c0441d070071209068107000001003032404001e29000f00980c0d4840d03907185c051f0803500f108000003a0071006884414600301c07407124181c0d11070b1030304030f41800940300081c00c982944400d010a001e0072004482c0300c2801000c21004e82c40c0030340b9a01038030348544480240041c1403610748038007155608446070f0b0014400e14010440c60b0382c3d680080d240c10350045c1c61840d8203400040802682c5402000d440081c40a40040c41c00e01d4944070000751920b8004210000031034000800c00c1c219662468003070301900d0014070464540f8502041070b0352402000e0440c41d200d40c40c01c032810b180c96005840000c2003201d80c0b002c490700990111 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 934513767 1250 934512517 934512533
    0x1b01060f120f0f061a150a050a1d030a2103020a0801121502211609050d14161508090d030e01150b0702180f012601110418060f03 57
    0x21016280309007840032020000351540103104861207001c00f174a101c590f401081050608208284644e10202042a4030400e40c104060382c1d4511807074206450081c020302c003400c0701000191302141d803500038095078004001101246450704d00045604c511540c0c016001582281301c1c00500c80d0218000e600104682440505c800c14144d1280c010003408594942c01030060381c01c80780200c404c030401c180320b2070030040c9141001c0c3c1e4840b10741212800000000c08000c3c000211740c1c0105400b0707440c501d00150038801d403200001446034051080707034405440c4007000c3c0e0510310103002e0a014440c0d5030101d56111440381406078004d1966802034419410950b400350000d08960b071300100d00e952074100200000c5400000c0c103004041c200d68196691409204202d203144ca81d2000c10a0440c1042c14010004031408116064500b01e049500480591440380994035040303d000282c1c0b0742c28403100d80801071036400030700110340c20303264078040031080e030405002955041d000310b800c07001d5002001c00c0801d00c58 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 934515017 1250 934513767 934513793
    0x903020105310806191802060a051213022e1215030b0a0b06070b061302040504090c1701020408100f1e0917070209071805061b01060f12 60
    0x2c020882840700d44604041c2c20401e60003000c0d0f58009a00300300c4c00036400040840e03020169801085105c0c0041d140407100c0c81c4040000c0d01551001c1803812a540c0a02e0490300d80c0440000c4e040c81c0c6240c60f40348100b0441c8202c1040380644590007860303404100700c2d0b407041b070700651b040211082c0f6110104111942e2a4000040410984501b040e0010088010080c0051806607000750340d44e02e0109004003c1d60821410540148800c0100c0c1c4045007000b0011900030100302c030038186000c1000512006400f86420a03540503180c88200700c01c0054041085040320600380803084519204918a8202c0c040c5100b0400d154014800c845040b031240d0f4400c0410100500340000d80000002d4014880741c51100d001c21820764810582c0c06101028036140401000212410f01c0c00410f540860410f0780c01406800502c400181a41219021100010084c08014041d207850711400d1030b1880340907000900b1100c5c81e500e403030130108a0a03506a141030540c1c030060040f030303085c3e003080d91100890202c1d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 934516267 1250 934515017 934515067
    0x1060b250c0504090303020c0601150215060612010e06090c0414090603031902060718051302030a0e100207151a15190909140609010918060c02010203070f0903020105 73
    0xe42400400c07190f84034407a07a2200c3d40295001a102c24410011914203281070700120071010181001c000b02030760019020300304c082c03c260400ca01d0f8a84a000c10411700801c0400c52450100b017001055400301400100e01c9020f0494130420251500601c0d49028801c5000700451007140503116801401d018030041d400c41700c0a0202d91508050b00d000342035070a024022000140c0000c0140208607500034844003a000310620721241d0766151400040000e5034682c00055060f40100c006a40440c503980580d40c0c1c80c1050b01035070001641c85c0c80078002076001c1d080846070340b030b05020720090581c014420304801c282c403551909045032180301084500302448621500400d000c1018003482c6860540c100c902000f183c4032144000c0c149407001c0d0940d400001c1121905200c0000c201030f03a681d80402d181141c0b40598000303041050300c2c29010304820784d00d401404030350904141d10b20480c0c1c1540154420122a0383e11018090b20321401c0303400003032510000c2c1c000703001400046801000f01010f4004460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 934517517 1250 934516267 934516283
    0x2040f06031a0a0b090d1a040f151b0807050d05090c040e0111120919031808030c100c0c0b01030b04120f141b0d1205181c03020906040e070201060b25 66
    0x80041c01181c47c00d94101c4080701c515840c00c40c04000c210116454174810b80c145401800195002e0310008200a203a041041c10095010085840c0a016a003212a50715240c0e00c02e1003030381b0309440c800d43d4800c19901d00b24003562804070604403400d010300c900440000070801d001e241c80c51340c0c0d6000c0f4003c07078003900f0443c40e40903041a850b446042c2c6280102c03400d1081d180c08110a80c41c42c605020f4007410392009140d5001040041014440810f4a20540c41014400951f400300d5140441d8101c2e060900200111180c0c8000302c103200743c07095140c0c03181303129141d01c5002d40310054040700e44840b510a24404503982e0074100420a0506000d05003410710310001041c41c4010382e451915142c0c100b804840441c40d061494035803402140120f6522a00c4001c40003040702001d141540d0b02e1807244008512180ca83c0b190420a5109070101c5402200088c4060303201d980f507035541098448150f40f4040558600030000440c00b004074140c2d070031282061100c02c03000c441d005c04206010500703101100c82103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 934518767 1250 934517517 934517543
    0x708070f1212110601271a131e0f150308030c0319022a01050106020309090a0e06010f092007061e050a2004030b1902040f06031a0a0b090d 61
    0xc40200481030007000400341b02c58002c5211613071180e4100f01c0024443d00c080c1003030625180d03c4155000307081e0403001900c065440044021002d00281110350b0203400c3c40c10a180c48100c2c615198100b648941c0c1c4080c000c1100300c007060664011280326100007450024148001002c5884040203543d0000c2c0446c1c0516074ad00d06008260120390000580026080e1542900b024038035174140c410150540c640001c110075418420040d40c0d0b0700800d084c45100d1380b9800001014500d503a00501c0e086880c4204468440d40c44014450804070580110881d180c07030210480c05e4019143c13405244503c00352901e91a01d80c4c0e83d16250302400007180c5082c91207101445e030400081151281504c61030f200f81000981c2d802c7c51040f504108440d06a0b40d4203048107120510116500000c10707504040c80d192400c0c16140701d03458000203030007981e02180090680000000b00c06070150040c00702540c181200381d0201d02c07803408004a445050051850245003400320040c1030a060145064250251001c003100c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 934520017 1250 934518767 934518797
    0x6040e03040f0f12030212160501090b190c080117030408010e031b06010e0a0b2409030d02072123030a0801060513060324030602070311060403050d150503030c0708070f1212 76
    0x160b96845820ce44200c0f516081055003100d05581034880400c510040c001c40710100c0008050000600a145810120b10004103104008208980040c61104020700050306030b00c941c02d8503608114914044c000361521090070011011985905880c0c01d444520885c1d00d544001e50000d002d02d140d0b40c1d0700000c4004104240d4854050191a4120388030b4000399650a6001890b0500c0d1690350501c09651145809202d90384a070007054400c6071149900d075041d0450382c1403c02c904d0440c03050006600c80307095501078410a002c0010f000143c015102ca41722a40d03109822262072240c200300c0762003e001c4c5103007030011600c0382e00001941414802800205080600d0b0002c0d44d070171960040303403025800240042010341000c100401000280301400c000d04e05510042c00c14030a180084540365661005d010b2528915001d503005030038050120303620349074080c0741c0e50790311441409000c02e184603142000030202c106011400c20f80303216035642060b4002641c0c40c000ca8400d6071b8440010721025005040c0c6d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 934521267 1250 934520017 934520021
    0x30f011e2103020705040b011b080708071b21030315150c02100302040e04060b030a0b0403080405210f0c070816030c0e13080306040e03040f0f12030212160501 70
    0x3480c201c08414104061551901928003000340c0c2c401c6014604007401003803940c0c0c020b42d0f0681020040494200b4002051404c41c030940b05802000b08101404071b040418081c9102840c406600040030b00d0300d03095100c0d01603c03820140c4030410400551308844160019109401210140c84040d0760f050465480d07142d40c00c400803a0801c400001080441041c0030744c074100140040080c05030034114586410b189034955842c80007080540001d44840358500d26440801c6003ca4050308098600300c00c1c10301c6c0c50b00900701c4c10140c806498902c1040c0030b0400ca80059030419100c0d6802158039440d08146812903605034201d40c5141c2028080c040c00000c0780c9070103002000c00e92417200d8038006000d0841c85c3c1b000f107101c0c0c00d0f000101050141c40402c1458420311a19440c483c1d009250350380c41e03070307650f078001805000500044490350001190015603072100070454001d450702c4403c1c2a14243e103450014602c4d06034a5005401648500554000745129400401c4c24411600880220004035141c0501b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 934522517 1250 934521267 934521299
    0xf01030f14090c0a09060602060c13030609060b1201060501021c030e03120f0a0e1b04090f050d0324090c1e02060a0f1a0402160b0c0915030f011e 64
    0x14603a0071811400d0000e1030048040e0700035000d03c4101b003240c103081200080d5990700007004c10204020004059145c2040d0180480003145e0000040c010401945002c4008e0702e0fa81d1400c9002e081c40c0404100a40301c180150010707038506134000c0144e40301003201420040510f41d11041450b81c0e503041e02c42c508105200519081c2c5c00c5524901041c00c04400c440312000c1c7c02088000d4042c90a0140380c0c01910128183d41740306418038038810340080c5000050001c0c08540350040861281c1c14205003080000310701c0c182103180c0d03900c0801011601c90710742e9100c442d0000550320304c5003403140c0a0080078060b81c0040501040d914020000000300403056a05100580c22140540c0c0b103001009030021082c0500c00418203061800e000c51244802a415003040c510402c510075500440e80040820506401c1e0350302903004180800341d401d0818280031240e019100450180d400700e000441e6400902080300e000750306280900040e0703880c0900d01c0d005030100012000c0d00120f95100040d5083c01ea040c480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 934523767 1250 934522517 934522531
    0xa0f18080106150207080a0b0105090c0c0d03090203100213090f0605030313050a050d050d270e0f1806010608150d0317061e0f03030705030408061f03020f01030f14 72
    0x107a8640803c000703464400f680c1d00a50007035000401c201c0005032001012411a401032350b0500d416280d030030420050707009041c140c15a41c0f1030050718105496242e0800c10009000350150ba025a002000d084141c0c40369000f03880d60b076503080404000e201107607440b51050701010724002416588850000c0e0071350f417203003941c69221008120144114a0b01c0c01540c0020700c1c0c03c81e41c002034050160380315a2507220780c0780c4d02000c0c00304d8080b65002d516038001d550744902880c803c81450042d25000d403c1002c490035111240c0500ca031800088407180c07100d402d00c40100d5418010001a803900078121707980500201242240b0b19200018a40b0f0345442020800d03261013919498401142c1b049681c500207802040b081c03045402a0300303022039540260503005001b1050300c0506c91150b218012030314520560340f00800d00c1c440000d000840c1400030803042c0c01390001c40d90300c2c00c4240c003d21390000c1c40c4046000c080e5005500400d0440c0c9503000c0c1e401b18102c00825080442d240c012000d1401d0008030072203440d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 934525017 1250 934523767 934523789
    0x1407060b0607230303010302100c02030a170c0c100c0f170f03040302060901090206031518070201020406020f01020c06013b0106032708070213060f060e04020a0f18080106 75
    0x1001042c03d0000c0980380c602d03a80002035096600d580c0000740e040341040c035541d0521031240b05600c150346041c050561000d40200040c4501c0145500484242d40050382c8500e50740904403684200d4601900070b5186144c0943c0c0d480304a040c4c9803150b1140c0100c0c44011168000103c25441102c66030001614a58120740ca50b180c403443e05003000390418400400e803d0040e4545001000182d0310601078030740040070b1140346c0c94100c880c400172035081c104108510301c0e54452181003241295054006000b900d070142d00b1395041e5101c05011500382c0c09840d14031011600140014011500140102c0080607200d52480c4a0f40f95401503a100e045074012034098a0342105c170042c010302d90140105000503c0c900804510918806a01603071000540401082400c001405a040d562201141d80d26400100c1c410081141d642c400e80903070700d20521503036000c160451500005450f04e0320a4482013800c81d120f60f5224a0050b0044a8401140c072498035903c107030000119140d0300034481c40000d000c0075040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 934526267 1250 934525017 934525043
    0x2090709150e0a0e0403120e010b12010b0f0d0b040b131406010f0b070215030601210b0a06080705090f0114070309091409100f0f0c05031008010506011407060b0607 72
    0x43c02051260342d002202070410903414040026030200e5188040303a80d080000030701104580301d1501400d100101103a0201c86280321500c44041907000740c402500c1240d01c056500c5c0446d01b07208003008002070203404014003000040200d81181a00c43d80403040700b006c000e07a00390b01e5440143c00d05406c1020030b800da012500602240d00c0010400026010746080c55040108550003d004000000d0300d4204c8003402101048550340550001441c40d11102180101c004171492940300034010300e040180300d411903000004019016150690144800da0707159032420074590b09011030000f2602e0b079181002308400700c0e0021440b1000250012501c41e5480310f40c1c0c1440c20805609844c3c50107808800302c0c000e07405205c01c4080000c2d6080d0325010750040816460062001540103040e02d100c1898201d00703004000000790740c000300440c443c1711542c200300ca041740c40d07604041c00ca5204035600c5002c41c0c3c242d40c15400a00407180540703a030768819100850b0094808020a05642100904403500760121034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 934527517 1250 934526267 934526269
    0xc1b0a0c0e1509060a05010302070501020904110d181a150405010801060603050c0a08011a251a010e012718120804080d021c110c0c0102150402090709150e 68
    0xc0d05440d030070001c07100084542000713800503610100d01e00c56030303041c0f65000401c0c0781086820340684071390610082c820002241203490081240e880030441c50380b003d1400e9009091801900c22504100d50000340508103003543c00380e5090744500c0034142c94244001c0d01a202910b994034020705000e45030311000490f40354036115000e010b49002820711030141c0c0d014040c3c0040a07a200d411a41100d46002d03214000b4150a8240300740b52003040303054200e1424400d10036030000340360b00000761404e00c0780c01020f07120f11400384032a201c1407080c0a9465a0320414004000141604490611560540c0e0303040c10401c888000120450700c1040ea551141c1c4880040c02d406d100311907519114092003410b199046140541c0c506c006480b9419007000e1555011139105c004928110810a14560006040141d4000050300d071650b40c00c184050122446821001a0203502c0481c0003400340d00c1c8171144040b542c03120390070000f404000a040c2e00400c014088006980a11000d48191503681d0380c4030304441003040340c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 934528767 1250 934527517 934527541
    0xf1202011802090c03060111010e0604110402030906150315010e010f080a150903050403080a02100e0c0f0418240f0b061c1e051501080c1b0a0c0e 64
    0x509002100c054144840c001d83c4620166951203000805526a03d0741d945005031000c520b900300d4008598038000400002d031000191060050b070046080510300c19034802003005a20040315002c4031a0001e101080e4100c0310700100380142003000f029140c0038158000fa110100c24240d100341792000c610705c010889162103450340c1001c0c000440c0034213031140d0300c0c1c2c5601445203400801600f5407503440d140041850320070b2301030714080d42d440f0044a940c0c1850120003969444140001ca020a181c081800155240001e050124200183c1000c000d42110300c1000010510b042041105a001c2e400180000b02610186c0030300b101e4205030040a40e65583c0044129012003d407100c3d82494241c40031100d41d10b6200b43c40d18410000380c414804007401400ca000b4040e00b468001e00c400c5411000d681ea01111b4120364030900b003240d00c00441c2d024450044400030b00170b039001e0400b81020480c004514880300b19500c1412001c0c411526040d880303640e20030415410360300461703955001105003c20040c0341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 934530017 1250 934528767 934528781
    0x10090f0b04110a0804110102030f0c03190e010e040504061b05031f0608040b0403031b0e03100516080406060b0403140c0102010b0a2904170f010c09210f120201 70
    0x64030b207090401d4a0100003034000d980241010703060388080c02051032181c0c82042100c110707880c0429000d80307540d00d600303280390380350045d5051140380c0c030750030855151461148090103c40708059440152241198060100031700f8054015070b640340c1c1f0b44001255640108a00707005c1c002103940c441c0c0c2d5901d005525140500d4500b940c3c0207800e0400d040410203940c0c001c081079001600952041f00f1925140b5007130300100924100c10301a00c0164206c3c2c150b0030303002800d0768002130301034080e20304140180c1401012200200e13039414540b09490b8800b21a07910941240e50700900c10350000902ea922280800c1c00c03034009600449007409040078400700300d4000d1060446040c404e000901401c1d0b01d0fa80014041044c40c01034251042c0318100030302c040c0304100c0d00c10310700003142c24945640d1030329112501080700401400070300c148902c5d100c403440b14005100c0c844294000d5038a11000302e00703025548480030058003a40d0708980c1c034072082c42c004c82d01007014a024071f03100c0c00201001d560308040190a41d500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 934531267 1250 934530017 934530041
    0x102040f0f08070e04020904030f020c03100605010f090312030c09080a0f110303070b01030204110d1103040b0f0118020f090616051c0c02060714070b04090b06070201020a02040510090f0b04 83
    0x111300144001038645c0100143c0056042c1003151541102c10000c92034203502490aa07418402d100c22805c0e0b0803015804203003a0b55081e40c0324a02d41c410007a0691f1031000314031009004032040c48810802d00e20907840407104035554545100059500c070b01c0759180c51040081a07c0240d06c4200c000c04010b140b02251a400d10190099401e0030882e131120380002c5814030020340640c0d10b80c08480408489181110040808c801c1c0400000354490010f44c416041100c04650100350030000c14903030381401091a04840902841c0d0304041811210600a500044241b8140010034001140d165031494054501c00d800702409400080b40380c180145410443c2148000c5134035074070203c0048540c4000e180e00d020790182c83d455602c601c075240207e07045d0342c1112408840c0c06030700f1020035203040c1c8100a100719241c2100501c0030394800e5007000b1540c41081c0c1c1c001d0250b40080d000100504003900116030090590080100390340d034a8171400240d9681845039400c0035540c5e00080d5251a281c0303c2d60344041c3c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 934532374 1107 934531267 934531289
    0x70605040312022b090f08010b1e01092102030f1605010f0e10090503100e070f122004020a0302070b18100b030102040f0f0807 56
    0x4109000480c0d600314041d071a0201d061000410709451841062002c4c65002105412401000124422010f10044030000225042905014001400d04030300200d84502c0d504100100b083e203001002c0381c0840701f246904610b036440b005440990302071150b603a81100d441e0f00881904090ba2000030350500c5000c80880002801103041062610004e88110a0540391001174030390038244144c502c009030904200711100d140030440207511440d00d042800040f91100040780c00d00c1c115110034120103441d04001e01c0310740c1003001010001c10303d900c0ba2040c41820b042081d8024001e101000d043c0c400c240001c0203505c94000350544042c040244110b41c3c500b04000040c0c00fa41144005603401c0c00207000007440c000c0b4030a01c0c003242240701d03400b0b0003c8180f0481c440c1c1c0200007401d0080d40542d0309010124614882c0000304e0040c0030003464400d421850310010700d14100e00c54004c0c4112807 = true := by decide +kernel

theorem cover : BRFrame.Cov 934352517 934532374 := by
  have h0 := BRFrame.cov_init 934352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 934352517 ≤ n) (h2 : n < 934532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
