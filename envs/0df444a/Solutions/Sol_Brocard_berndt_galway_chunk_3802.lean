-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3802
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:53.537006+00:00
-- url     : https://prove2.me/submissions/b2239414-f5d5-4df8-b88c-1ff5aa7cbc4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 683633093 ≤ n < 683812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 683634343 1250 683633093 683633123
    0x20d08040b0402120607030504110904020d061e061403070501020a0f06150b070302031902163003090e0619030b0712020d020c160308091e03011415010804 68
    0xc90307200074403c0b640080d40c207100d00f403503400800c003c520a08140d00c0c000381d90709080c109801c003201c00940052150316121304000040c0c448801701200309902c000040b8420b580760a03640b13200100c11007006040da142000000c0c141c07100700d05d1041440000e8060715400c0d0b0725500126140d50600782e010781301d0800d1020440005445a1002004181a108030104070341c58422400490740107500a50059002013811000200030041402e0300c002d15000400100b030000c40214040907079072160501d075003201c0c85585450040040901c64007800c120001d00c800c40f80f858040c1c508006d038041d000707204080d0320001d641800c10803601a21000c03191400348845180d541e5001c2803200c01000032041103081d0303607282e0031404070b40064031080214020158549040840d803622b8903010700b280303000d10403441804202040340181220400e1106a41d19078801d5900d00013040c0e14891080360b81d4042d0318041c24514441100d441003405075602d40070400c40a11082d004440c90f800a075801341c007070418050301d8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 683635593 1250 683634343 683634353
    0x218060a0e04180302060f1b07020a0b03040f1a040308041e050d0504080c010c080f03060a1d0a0c17181f06080f12040e07050415020109060b01020d0804 67
    0x501000003003490200301000d884030100d015102d9000b4143c50f008800402a4201501440a80d034400a01126040a868541c00c051104036078000b00d401ca4450002c0c4d4102035460388000d0001605400320b01c140d40c1e0809280c600c80103c0c07049019200003141681e0b20f506401c04031040c901440d0540c0c0e881d011901c4030740710000d07034402060018900d000c1903540400029001d114034200440c042c0c0b505501d42c1d1070700d880e10742014820b80c1c0c0107040142e0b241242001503000400e40f60368096007546152070380e032002e02040e00c8144681009950950001c0345041295461042034400e401e01c003800e00c80860050005e40e20a502d40d0500400d2801200000d0110301d0044a032940051180044607100d900c015451403003d00303102180c0704019200e44c011b0100344420070101c1c00c1e81ca5400e000f4504021074403104940790045004282800e040040804c081314400e0050b079000d407090300341002040c040e4540107402403004280446409081c1985040d05600208201c110141291145001c50792980d4070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 683636843 1250 683635593 683635597
    0x609121e0b0414010b2205100806090307020a05090408030f04030504170601050906010e0d0b091e01150e010f120203030d0203280603080910030605131a0301021806 72
    0xc1100c651200326a8a004a440020002d0040e8003d0422650082c0c00c07480442c01e548211070034900441c03c02c00403090590004106500f001111030000909440342c100340203001d00d259106656a21a04092106000c000f20040c40803501c21210319a00e42da42c0c1e401d0100565048034041e05520052000406900e100d03038621b40e1007442440c015242c251a1151848601c500041c00b18690748400e0050229013046501c1580041c003d08020118a440700e000404030980308000401d048013140c04505044000c001c000c507280c0b0922000390b1a100c840440a000b448070100603a03035803140540001e01008145d84150690f461080b05060322400c00e4084604102e0929080b030b01031004100c4051140003510141d80208403007112801d2071020741f003080c5c000300c2c0030461030050585001c00410009000390203d0f1070408050307a235503a04182d105c1c400c0c0c0c0203050300d41c026904041c4c0d003081084034040715884820070a84034005180e0b5141484245400c034002c6150840030100050000c40d5945031501c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 683638093 1250 683636843 683636873
    0x12161d010c06020f04030c0503190f110a0303031a0f0a17151006021b0109090b0d050a120207140a0302061c150504050f09120a0504030b0c03060a060912 67
    0x524141e404002e5482104981c05007021000001c0e0115080c000c001c0200f114030000d001c1240181010094014540810480f8400080c01200003000c52401c04c200000084080d40d001405032580f1a03481c1405001b8140018412200f5807600c0100426441c03d00501c00c1c00200103070000070103604105484c201c603010304210070128410030800c01d80c1c090784001518410004101081c03241464801702915207019407800e0b00088040008400b080d90b4444a0981210382c2e04801141891098000c10494994545c02900d40d00030140c900c018801140d00035980c42d0680d90803036840c00d0390342401e000800d00d0880340a81c4013036082000c01c050316045000e00609241a001c1940308800780c0d425508503600e139003803025113400c0340d601080b8501d4035225455004440303048909207490060280e50702c4000c00c24180051a401144a04240c0d1107007094030050750380440175045504003034190100c44d40040b40c00c1403243c950301401168451003241c089048a50b1031585c103507403061503516001607101d03c1d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 683639343 1250 683638093 683638097
    0x506030a21120f02071101080c0f07080f07063e0d18050c01020d0507050a0f1707030c0c0501050a120b0301020f030a02071b0f03030804141212161d01 66
    0x42940384003000d5208a100201e0340010045e92141c0360304d00300d0800e80960103032070f0500c40300d501003042544010080328003c260031000280c1c2c6160520f40200c050107a180f040c90307160030200700402001240c0d401340c50003000200c003c04001c0d0708450f200d803c04218448000c0401038544943c542e10312094007070840c0103009007000c16035051241011641c5042c0303120940719503022403401c04165030180007003130100e1071601e004d614180c00fa884546e6180480e403001003451004060550500c08281c12003507020315000f00103039840c640781c1001400c40200040550314008417220018040d80a202100c2c16100c6a03100c030070031030340f81800780e00c01050409400ca805540170004a100441c0707610082d445020045401620b603640c1d820b28a0121038000804642203000500c18486410001c80005c00c03254145042c9566940300e1601a8030010001c0c5c82803c18496443c00d44035104000c80a8240044041d0704840103568114600c1d9040500b42079400c0400c201103c01801140b181400350040f11042c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 683640593 1250 683639343 683639357
    0x141602032b0c1415100b070807110a09020c0307030806060702030a290a020414030106181a030a210905010c080a02010905060a0c11010209211c020a060506030a21 71
    0x140d49003420001182c6120300d12404139410841d80000625032040948002c50b5800e0800265a8840c43c440c45066005814100300c035085074034a903107402c05c42c0d0160414a0b0b055488210f4129015a2508110300403404281e0030f50000e050343c20000103803200079400030700822a01040ea101e45a000100c0b031407000c03034002104042540301186520b02d5002c2d54000c000107135a10300e0b18180310314000c0303070390000c501c280d041220030840940207540c110058040700b03000240201441020400c8280c1d02620306030180211901c0c10240b0042c40f07a41d40c400d0580900c0d05058103084078040320281080d0040501080d5100e00e01d2021819a002030503100da034500000400c038040d03480d0180340c41d0040310801c0001c0d884c4c80041c610f1a500c20000f00450341444001c0d0304103803510b8005030301014164551100b80c105100303d007180a004209103110010203100d03080c007688000d80020345900c03580b80240da00c1403c2501141e00340c00d00040102d00f40d80c101240703162503034503541c60311000300420400500300408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 683641843 1250 683640593 683640623
    0x604150506011115010504052a030a0f0609020705010506060403050601031e020d05071a0c06060d08040b0c031312080306010e040f110408060a050108030a0f141602032b0c 75
    0x100100342e0310307013050a0b08075402d42c0340004200648500611881d5000c1c0305000c11449442e00e80d032085c2c040c1d61000c004075126a201506617000345203140240071040c4c10900000317540d0710f140d4014094075020f103009100c141d580105100f1140b1407880020001d601c10b00c01000403400b08480c0c510707000c4c0000b006480082c0203800150030545400000e49143c1c029440c200440250b600c04900c98402c7c08070090300340848980301c591200c0d002000719000b111045043d508100c1c40b1400c42d005402e000207195251001c8401e8584d40350030449610754000030540010840e8807401e04c603810a1503001c03055500d165541d200441d007601048282c103400940310b00e0700e140300e441d0368040d240c075590b1038092507a10b40e454500400c2c90201c01a14041c00f19203458014044020003004031074004402d420030450703064481030211402c01068a815009071030214840e440020945c85640c000ca000b18121803100141c20f003812018101402d0300060240c6d41c250003c0d905020342d80d42010180a143c0c01411903034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 683643093 1250 683641843 683641877
    0x90102071a190809030a03050c07081c0c0216031b030c0602030a140406080f04082107020d14090111010b060703051216050706021c11040611060415050601 68
    0x40c0314203001d4080900801c401c200091104a10810000300c0c0c90200c2150401d901c00a803280701348000700d41016255800101c22203110001c86030f4156200001a5407511034506200041c514034080400c10303410200d84103406440000c2c0241c000711a420305105c940d19682d50b241404d0000203142c40810100003000000c94802980d01c401020310ba0050740d6900e41104004140034201c1e40b500308506030601041c80060f601c030001c241e1101c154152101151590706081d0b0b0782d07029501010043e005920091203012180140709030285841c1d030201c44800c240108244e8080030080210700c461181031107020969880380100240c81c80200000048c90200c0c500414095800782c81c0a601058002966464055020468036409400d0400130b410150811000410380e1090001c090001500407850b01e2a0500e480032018002350210410403003010f541c3c00d5404542c02902c2010f001c1411200c995001c0a4086001441203070b2010740c034800003d42044080080002a102d1410000d0b100d0f88030744808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 683644343 1250 683643093 683643119
    0x50901030e120301050f01091202040902030a0f0c2417130f05010209120a05100207060b03150a0609020405060f0a03090c06120f1109010332010306050f130809010207 73
    0x20110b40342259603981070000307210a0f4800f00243c2c604110b4141c50800c442108400304040c0b490341100c2c0402c00501714000079241c40507000003d060780c00412164070810068903a14411103141e04050303208c0c940a10380044412003815035040200c0c1511080540450006040c1e60b84003016010b81c03c80c0c140079448446030b10405007001c0307840d6980068480300624141c210901c000d11414010011040300e43d07900c0361030b00c800e4159208145d4001c12000b0400c001e50304130103101c44020b400c0b10395003411110303120201d05040e540f0601c0d031441c021300421805818001c80d004c0d81c0000d001d051034904030078083c0889900c00152802019a600b81e0f200018078205804001404143ea0390720845460030314074400c450302400241c20852801910b40c40614085c015100c46401c2402d000130301301c1c240640c0101c07203648400300c1e1002c1e0446c00804102081c501070003a050301d00580d8108050707920f640b200b00420000ba02e6504407250f0f000036810014880b100144500700c01803040d03400b895981c2000031014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 683645593 1250 683644343 683644363
    0x307170603120d0e06010b090a090917070b0604111602063007110d0e061803070b07060e1b0d0503090910080606010207050109140a0e0405060f1e0106050901030e 71
    0x561180300c05544c11078200003140c00344c813070726942e546400d03000d0001410004551040e108404c1d2075840280a0041d06244e0803034500300204040d40c1d40141c0d00e04808943c50445a0a104078680004d0400c021003071419907441410302000003003001a15001c001a5401c00d503006000e0300544080c00d00d40c40c00381c2c04101084030740d0220490075824170070000342640410a444400c1035000440c0740c0007041d40442c40c21840721081d80c7c0c041e0750b10b841c410b007002e4a40c40c10b5040c5401d4455440001840216640141020750040c0380c200700703c0080c1020320352940807621800c0707000810130741c4040ca03e240c6042d0554409116034112442c1401e41808220f600d10100c0c1c51500801d0510810040070000380003899002e6024805082c0c164186030000e0301000041c0608000107405c03503508002a210304402a0140140f1021400e46140610b84260749000485001056072031883c04141243d040c1c25244007280400341442c0044da09044084403640c206408890415456150348001d207882070080c07900c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 683646843 1250 683645593 683645617
    0x20906130501080702010504030905010c03050c062e030206091908150402150c0622050102181f0f0e150712021c020703020d0807081308010b0105030717060312 70
    0x48607181c0710001d001c1c24001800c400559042034100130000303501030252401d031442420036150f00b510504003220f103030040b0b914548041c41103105102105c030320b80202070524a000c40541da0200d0041c3c42a00354240140b02c0203402c500d05200e050410702d041040f04420b0301440400013591503492a032545448008101d00500031a03100900c021b5041124002c3d440c1070000c82d2030741c50400301e15855940c44038020581603480b0204045a8407800f180721010301c905030000000c2d51034220040032700511003406040540b082c00200310704080201009296011801e064035400820740d40090250b0300002d1102c400c80e80010340d041c140c2d444048840150003c54021a0041020443c2030b4000e45426908070001030003080c200e05100340940c1c0001e00700c0c29640d058440d03012244552808400394010b4079002044010041241e22501080000d40000c03034031010b0003445000100e0700150b80d80d10040c0d451310006078042c85060f10304000941d41c1e5030001000740c122143d04115102602c1135405c0b0303000c03042c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 683648093 1250 683646843 683646877
    0xa090b0103060b010210090b19020c0706020c04140112060905031303050d081b09011112212202190e0901091406090304061b020612010801050f2404020906 68
    0xf2041d40e040000d80e0030715103101d8040103a00066103a42e0400800100a40c0c4144030107400300e004c039a5141c043d150804444c804407045d03952039400180d1142e00055100303004a203094404840c82c005400c40300c0c1215540c12585068640d580c94540180406240c1a90580701c1000340b4410a01045800740c000c502071405452000b0002400811110024041d203088404460344610460f9003c0101c410040007401d04032440850031020600b40078032180203c10300300c1c0110781040b082c80141130692400c0c0c20460309410582d01e001c45a011000241c2074520843d60341800180181010103480511400707202005416039a14500140418000c8456006903511a0040001c128900b9210b00c588000310011f01114508440310a9580c00b80b44240c4003040588800070301400c00307400c0708442c01a000f41c02240d607401611402040d241c401e100d120b04c0e0f0342c45c21000941d492060512a03014001109548141185d410070102c40820480c08140d40603901b0414141141d0301c3d40c0007000c840750290542a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 683649343 1250 683648093 683648111
    0xd03080403030e010b01090b07020112110406090e07080402100315170709051603020310080f030318010207030e061309092009040809150f18031c170a090b010306 71
    0x5064074645800f0910980c100070010907075a8101c0621002d850201d80d90b0381d01d4840d580012036240f0401000d00e9002c51611000d40d11602803500188155040c5c0e03100d4040040e91035140b4851001d0071030b08400001c0700a000300300146450351101c20580601d24000c2a541c0c0c000b06140d001450f10f602c00080ca00d032000300c0c140c0086090158a0041071032501c1013190b80360502c01f49224140c80380030340003003660000010396240507201e4480040d00504040b20880c0621005d029541c1d4002e07550241150840740c04515410350500803659074a51595075144d0020b4401c060001e0740e08001c2ca188120043d1040115038044103200b05089180241c1075030580345a80081c800350340007049940e50164002c02c0411010500300c0c0115a0502c009442da0750740080102c03240710880c000c440d4909050007000500c030302c030602d490000f50507126044041d580400c0441c82d4940980c1204044180411491200c2c00e8041c0486030266500a0002501140212080c0d441c0031400308240c02c2144c646540307008403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 683650593 1250 683649343 683649347
    0x2203120c110d020304060e0d0203011d0a03180b0702010c0c0b0d1e050402061903090f0302100c020c130b06040801110a08060a0f0b090d050d030b0310111b0c0d03080403 74
    0x840b05540d82c0061440c2078241000282081182d0161501581c9a92080001c5480c2580300f194401040e40d82140b04102d01102991a5441c4003407e4000443d04e0a81030f1101d0690303a400d0040f02c4604140364a8403c6036401502c01040d080420340c1d1015071304400003132004540b03001b805081d0407a200010b848044c0051501040c80722a40c2c408003a162008010060712041c08079000728112008040703601080b4101100a440d202400034000c0200ca14180c0c20150001200b41c4801c02c4031109000b944a210022652030036850503a03030b400940c02120814120a9078052000180098000d40c90141c41e001554203680c2c0352882401040745c0003d16528507544007a03079903001a41100c803484898603084520130340380f94a00038518800c00000d01c043d46995110013070040030f030b4450b050f1003100f61a80f401400400114000c1806809622611002c4800c82c1c411208001203510205081c074000000c11f000c24218110a02c86034410308a200c682c551f41d103018503428610903610240e451919140c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 683651843 1250 683650593 683650603
    0x318011401081e0106140111160306020405030606180705160c0602070e0a0e0c01120f0e060910020c0d1803050a060f06270b06070609060c1103032203120c11 69
    0x51443c281d14090382070022040300c00c2c8240c52a00240f908510002003851111708026140160400007410b510740042000400c0d000b0f441250011030654403290748400034004a00c24400603441c0743c403c9540020927090045002e0007046450220032070551500341c4e038080c04010075402c20300140c0c0c0070304800c0017101c1895142036403080e00d00e50305124040c10808080e546080d000d0348a4180104049110050400340d4010035920180e00402d22104415040080e101d44042d1800d002c01d00504a8441c03080d0818001c45030080700d850028441c00404600c1203841c000980d01d4850b03003110902000010407802c0090003143e50041500096984947d070440c01110310341d5000c0408004e40082e0b080c0c40564002c20b17403034221a8010302042c90200d00380000c41601c5010402031400346080e2036103040c041c0b10f0340003407c8c500c0346485014117000ca0448283c0d80c1d000485407030f405801a40740644a400c115442c80c412179200c1d081004241410314040011741c0e2040a103800043c1030300c48000a42542000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 683653093 1250 683651843 683651893
    0xd050604050601020a050a0209180607120f0b01050403060e0705030615040617100507031b110709090c03060c1202070303050601021e100203040c05040c2012031801140108 75
    0xc0c4081500c9940e400d80740c04547d000a07100f80e85000014070151624144107002d5081d80702500d42c1d43c40c042074041c019403150728010301c0b810f01c0c00700701d050018164030400e0382404058640605242c9155216005010080c0c0c4040d094061141c00048507101003110901460074402d150041000107002e1004440240d488044070308404030030070030036440200e14911004042000842e0b507544808090b40640a007001c00c8030200c04512a01d440164404009a45001c1c450103541100741c1d18a40c0e801601c6055502074002604070384c1c10400280c4503130000020000506200c40c402e0325800401049030400d00c402c0e03000c02d894404111996a05115000d030020300b0200120002c05210344190307542c0c42500018900c103a00101103802c0c044a955008010180208184035106400070300824cd0340742c00c4404452194040d2106034020b6012640ca080040c0c040111f504580d180740003070034500702c68004030f0701a550308d1941161541c66011024041c00c40200104041c604184002131138001c261 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 683654343 1250 683653093 683653097
    0xf12020c10081e0907090f1b050c120f0304020f01020f030d090c03060204081e030703020c0d0f061406031b031908040b04080109021201180311030f0d050604050601 72
    0x39001200381da2442040e880600c11840d065096540c2c0d4610200f00320b42c05408542c051001404101c8480b1300050014242c444208041c0502801c4038080020345e0408803c0d001030100107917582c4c24043c030a0011b0041ea040c07c0d000c440c0015000348a40c500c40e40b0556140300c80c06000801c1209500b82000c909007048420720003400100c40f00031081c6d0300d034060781410000c02070701c400354070080c07201305136a01001d0358011504660750f60380c50312050303914a00d800c41407442440000390b2806400d07011050740c81542c0c047d0060804000c080b010441c0c0322007003190031140b03c00c031301d4080f00c04142c091141c0094001b00b070700795003c00c6c00d00f081014075042c5001e03214454441c845c1d0304130301d0603140071071000800801d03440400c035602054a0900800d01071034210445020703010400103240c040c15080034508600030340790341d020b041516a4032400e07908410303940185048901c0103180000c0c840e904150040a010081d42d0521803100c14145640d88038040e11035075203869030103004007441c1510495402c80024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 683655593 1250 683654343 683654353
    0x30423040513260405040509030c070621050727030b061915030e0f070311090103120806060c030a081b070b04080304020f0a060c030201140723090a030f1202 69
    0x3a81c07809041480000070a003c4114065000200c50089042d5406071000500500851501c0100540d503600540039101440c82060000210180660402d080c08503035030b2207003841c0c031900100301c4e400b86c403001c7c02c1c05081280512450300800c1141d003c6144495048181c2a082032460421500d28a005070010b8810803c00d640c0790703100916007040008480c40d800c0307031490032090b4102c01d078000d040fa121a0031080c041c90700030555021000c46d2a0055034400d12056225021030b00500c0302c402c000f400700421b80e02e80d0703414400d0201d0180420540c0002c0042c085841e00d4600ca00c2e0a0440d08811500c1c00440d041005004180d40209a96009903034012055420020544c44103c1e0300c2d02e014001810903000017000c14195150f001c400c41b003440d0003a1820302c4081d580c410003003607909016000e0f4015440c20700940440f03492130070458043c0c0207903900d643c0000c07201402c02c140c0500010054036900710800c10344070b00d500d9481c00440214011400e400c00b0f06090f0400c80d0303110150100c10811504a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 683656843 1250 683655593 683655631
    0xf06020a0b06040603140a0303050a0c09090b030a020a14090901090f170d020f09030f0a05070506160c0801091b030f0b0a1d010516170106110304230405 67
    0x40099030300c0d00c0035001188000716031102008074000340310581010b400c2612a84182c11409400148140460711a6804100d566106008503048408039411100026201d03c4208900360302c0c1d801c02c400401e002801d9505000e11940082c00c0c0c0021540310301e0a40c1000410b5040c50f10381503403015400440d50000340020700d030a82e40c00d0b4003441c0c1160010081045004440094030f00c0006842050400601c11569070303040c00204031151300030a2055100340305648464010300004030396444160b0340a001002c0103410300b000c120780c170380010340d18001901d01c0c004a01c010a5021b00e00e0402003000000024000501d8205240b180f04551101003009000e05401c100107060000b00017025600b06020507031548501c182c0001500c4904118841502c459105240b18003040d400280160021007030700841200c4003905450300708141e401c600d02204090010401030740110709054a402d81c100c2580e103080d40b100c00110b058a400030822040e01641d100700c25203801c19101d103076040951551031000d4020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 683658093 1250 683656843 683656847
    0xf070212030603061f0906140a1d061309020d120e06070b0c0f160b0f010801200c03070c0e0901151211040608011d010b04020304150510051507030206010f06 69
    0x2030061700011801031460707801080307802c0e07400d02c0f000501301180d0148005a070300c2000b088120514041c8621030074a00c0340c0000c042c07109000400e00304001070b0a000807075540d4010003505c460007100410445464110080040c0d07124541c079007859106030002e0b4001415484010715a040304030441d03000d1601000071501280034880050b034040d4910032929600c5013400944251401400300e44040300035010b00c030900300400020080e2154801b4980001c90741c2c1c0e5540d280d03098401c281004402e41c00c2c40d0032500d03018000344005191580c00c03a0104c03842c1100559500301c07145210703401003403820844418081f00355028010700c122858a03020000009041140d0b0348203481484200410401aa101151072502d0300e0300140c00426a14000b04010b1411601c0030f0051000b0940c0c2c80640e5181c10181d00c101c0ca8584240c902860b0811100740c0200e00018125000786809040400c122405d014000f6144c0d44040b60084c031541c0f05d01e0303400e40703602d064540a45007090680004002e207606540c00d110107a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 683659343 1250 683658093 683658103
    0xb04030b01080d1b0203070f061d030d090b0702040207020607050a170405010f180f080a051006060503060d1113290102030d0218040207060b1003060b040e04020102010b090f070212030603 82
    0x100e00d4001c55400684c900c0000d00d80b5400f688403001081600c1c000140c40c0d50005101d01c010301c2c914103824500551203041584038003203102441c02250f54003c0500c0390b444400003401d8841d01c041d000504e09112034000460790b401080c4101d460b079001c00964030400402c0107403048181c075190706c0141040e003014000f80c500c3d04004008410000c04076481c44500c1d03244858040105128070364800466110003069072a0240307500d00795518440c6105c3d070702803190719105560440302c003642d90f5030075506d54600b0030440240070003040d1136000701540c50031001c3d0f5a202c0344402640e0303900741c00900d0360f0710448008148000c11200076550100b408914607240d8012040320b02d0303052030400050f901d040304884a0089403411006c107412910209400c010821b055001492a034002c4405040889103030701c0840030f032199030007a2000d0036010301040081c0c0454416813a0840d1050002007812124480411900c101c01c9841401c208000c000340545640c040c0a0014480204283c49146103030801c04644c0e03030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 683660593 1250 683659343 683659367
    0xd02100e100c1704062012010902031305160e0c03061e04290901080304080c0d1430042106090b0c030f0f061012060f0b04030b01080d 59
    0x30b07120651074640e60b03c114001030482546404141c401c0c2030a007800740043c65000720300c0e482c1101041d014400c074603103a000c0e06c000300c00c00341c0700c00d1084e0709111100010350400761552548420511042c0300281c418040d0b448034000348403004004c03610b0048108103030000944403001481d010800c0c00034035100c0290000710300c1c60b03041040d410200c0389000724000b045a1740da8041c1c05001c80d2103400125203004210110030030b00f10340e0a030103a40c0340c40a03141c684c0b04900c14602558045105049030b814801c489000302e41c010061010034009040c0c0315030501c0f144c2488820780e00d40240c802800d01040070400c500411505000f20b0815041071000c8a01c00040100010014051240300d4100031850b00f05409090380401000aa8206040144e1264000381d0712050620143d20006100c201103021281c0703e00c200401c06c4e101003d10032000d551a04403940300710003440d102c0401040c08402244100005c242c4211880c0d661403642c241001c0900b41a0820038158000f00c2030300816661000d008004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 683661843 1250 683660593 683660623
    0x1a03100f061b14240705120411041e05040302010e032a030d14071209110d060e03040b04030c1d01180608061914010612110f0c0d02100e 60
    0x44002c0d05040c07242c1207401003c0e9119201301a002641116400b5011650151084441d140c9480f118010f8425005144201c15804000c0000801188507003100c1e10901002174400100c603070901ca1f41d0f0b0b40721700807800050b074495104d10500c010950309209440d508440080a10b0400c03c000e601a9040400224036442560700400281340652080c070454030300740141d050421a031714041c0c02170a407080c41120b1500104900d2541100c030481203008208482e6486290542100c40d92001c015504060501c292941544d80c00510b00101c2c00300300030006004404607490f240c0e4076516200c04a04050b40040c0c0b0504090400103d80140382c0c00840d054440712409485c07a43d10024111008100c1f940c00401e0360b1040c007080c000f840b50791406105d403048102d80184403846184405c000061028452030000508003110390101c10101d6201c1020414007902c01441d00607101c0900b100c541103070805801c150440c0c0d182c0110350340c0401c5000c51030400000309100b02001410b0041e21344d40200a00c0138 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 683663093 1250 683661843 683661887
    0xf0e09070f112401030c08060c09060a05070b011412010b091b130315111903020306030a0b010902030106021e1207030903020d05070f120b01050d0c1a03100f06 70
    0x45000b1090000701c42d1038421400c10a465a80f000352404040400e02c020313034207481e034184081680d40000ca0094070a180920b011441d10030710001b03116081c2d00001e00141000b4043c84600d00141090302407a0017414070351a4010f4040c04141000304620511000c00b01c44da00d09000c2c0113154444100d10740c3d111003140c0083c0c81c070a1455107410410312070101060a40060b09102000300a070305040710040511540b000c0090980c100b500c0708161041c0d94005402012040501c440e01d03219800550384942c0c003406648040181d03030b907260820300c1c0a8100b850000c0c2c011006200c860342c1002400c0e00741c44c030403100c40e5079062001c0015460303c06502081c00e200c40002210401d05000c0e90a141c001c1d03074003414405017040913081081d220910f50250030400ca01f00000000c0c6800c0924060702500c3d04501c113902d15034601000c01c14a1808403404a441e1842040c000403081100303070200362060922540340b0355924045560804082491304603060101c1403242c140007030780c0e100d0820a401106004218 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 683664343 1250 683663093 683663117
    0x2060f0c0a081605192a150b13020403061b0e100c170706140108031c05090a050607080702060708130303020307090f080102090306060f09062e0f0e09070f 68
    0x55041c41801005e40315a80380c284c1c14001c40d41c0c860f51450100d03800c4034a412a405800c200f4401c846401840a4807062030308000621000141d4410201d010004090400c60f03030711000e43c0c40581e00301d41e106441003503031684594460301207070024240054107803034051a030300480c400041607103683c101c4003c20000b400b680d820420004107020001c1c28001078500d6203403c490f00d00708016021441005842214050000410860010540b0107a02c1c0081c50700c0209140b21400100920009200c1605841441c10b514040790f42804520b004a1295451225500d400100a071402c03101520309000c01021000304003401060b00906842030740c0c9440d000d48d49440c0d0b281c045405800342e42108104003912040003a010105500401030242c0035000c0d5545075840c00200550060001000c1d03401011020006006142004107041c00ca80c1c02403c03100381d02050001400011003500e1420046103010b920007404580200050349180c9080395403c0359840e098a00410b59040c1032451380c01d005600c1112 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 683665593 1250 683664343 683664347
    0xe2406090f0c090d320d0c170f03040b0c041202131401080f070501020a1104090309120b0708090a320303041b08070609060c06020903060702060f0c0a0816 68
    0x68810840007442060540710303d080c030240c09100c40b0041450300c5118255001c0c09a006188405d034030010201410107420122400d4824800303141c1e007101d0a4040e0303584aa100300001015200b501c40a901c0c0ca51246454a0309a48261014110000d41c401c00d00c000c000e4842c8000f007410f6030690694240c05500c002d0140e81e8050041e0113009140142520004039015a0010786c001040c6048000c44001c26916030069889540c0580040d00e51100b00c074100c070039410147c1081403054800e140108005036107505007585401d012501303c0306280400d05120f65182d00000040e00001400e0181000001c0d0741c0d40c0c41c40107504111700d12582e000d41c5040030080d08010f0240040704040c10182c0c2c0d600e281a240c00405140814504800b070300081001003514040054410180c0780356403501c4034414106130080d84c0b141c21003e02110341580803c0f0584281d10240440e90182e0041d8005000d141460029608044030042c0351701e2000718140700116140e40d000e0807242d0480c1001080d0b01d0a035a6201c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 683666843 1250 683665593 683665597
    0xd0815011b0b090a02031006061e0509030a1208160806040b031e010603140c0102030f030a0f020f030907050111122809030c0806010308030109020a030608010e2406090f0c 75
    0xd06098a8141000f0030000d000c40c41c0c04a076032084050310070700000d10140b401180c205028038000514442c071244003c010500b9900d00c05a458103115040c11a20b41c0028a02540f08100715100003020814449894120440d2070b080000c03000e0444911141343c20050003010010f000c0c610503034451200d4a02c9840512004000c00601c01c203c0d55000b8401c40854007030205d512085a5000c82c058400080b0306022810741c250303500507409503103400c8114152018a80001d0f140010300ca980710301c541400c0100d840108224800b22030035540328036148000c0c5041040b5a40001d0600041180450714100d010130204241900144e4494551a03503403007609103244c0040c0031106900c40c06c100d00a9131500201110b01303c03442601e40c2185c4030340b00d96426072210301c2840001c010f110244010700c002201b0b600600000c00a610b80050b81320fa90b49804c82c256000c810000140b90000c150b0b0504c070950900300140c0d034400c40b0070405414203004002c04d544070303c000c01c15003084013201d0108101c10402c4d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 683668093 1250 683666843 683666897
    0x20406051c0603020312130504090201021906140403030501061211090409170c0304080d181208120709061209080307180b0403060606110a03020d110106180605030d081501 75
    0x41120300d00402400944095440300c0c0400c140341f803da003c006040e182500564079000d506a001c4d00b4039440a020009140005000c2143c15a48940300445c01222000c40c0c541f089000e550040768179454044054002000300781c45810303950074400340385042c1c0c81c84012560202c2007510b0000c0d010803d414410000c28610154180210000420b0820048000081c106039000c040545e071044046100980c0c914045e03d0350340140c208600420004c0781041407007030400600030b4103903070703d4282c003040e0150702d0042c00c450325000305680e00024081241d002601202c2230b407514800300b01d0900140c480c00c0250000501c09d0b0b040003802e07407012280c64411100c5100034554107020544854030380c07400e00060440ca006580c00101c505501014120001480841e542d425030094180180d2040c0111814881c2e1607440220b0743d00c8130307800600c01000351422591012000c00014900703046c10100f500344100221400d0810500f0401d104400140c0d01d850360200c4001d00f402004800303000c242d42c10030f00c100300f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 683669343 1250 683668093 683668099
    0x10603151a2b0513110402070c09052a0a021c03270506070503010b070210110a060515030111120403020a21120c2001150305031b01020406051c060302 66
    0x406491003031090b00420069000c071110240011303603540c59601007076258410b018054205101c01000b403030610307900130314119001e41c048581254481584005407042920351129004112031000a030607620f540032010710204c0366910386040b144000c02592488002404008c00c0004498404118040c1e4000d400050405000004034010100214000910440300340d90340d0151030005900d142c80381c421030b4165440180e0031401c0507150307000c0c091007840c0b6a608000b031050a200e0159031210401a40104174890301e07010800785000e2007040400401d001e50345010781c1c14460b14020900386102512005c00b041c04140c0c000d82d88030305049150480030100030384034081c0000c1c0050300c8541e0006803038120384141c8902680c1842c404c159021903114800d68000580004461140c00381c44601d800c280c440404000324521003881402c0c40c800000e94812074080e4000a10255248116041c1d07038000480803008509291800310054864899250403000b0183e881e090000108080d81c401e8015540203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 683670593 1250 683669343 683669377
    0x91e03010b0d03051308061603090515131a0c0703081005041a010e011701150504090e0307020102060c030f0f131505010501121803050319091109010603151a 69
    0x2401c0150150380000c0f201c1110a41703549001c01e540f8030010f280e034003c242040040c00010300441c01200200221001210680581c0045801269070300511a004458410cc600000c3c02c0302d2500030b0402081501e4806000c00020402407005003c1d420303280415014141003140d80d407041031030140900c0e10f40003241d1240c0703004030107900c03a08410200c004c008000e0300c3d44041c07014800010740b594690030140300841c0b0600c2006010450315a62200d0740c511080c14005d003013070b440d00d10f1041640c6100c0042182a80040342003803e5681c1003240e1074210041411680c80c5090a81c01014039550042c103091002070040b001c1480741e09d0f08260211a25007100000c1c0282245071680c0024100078401c0c03070300241841400c80a05501c9210314000c1d05603080c46016816460781e401c1d00d0580006180720510800c400b6250747d0f202c44c03801844812846030301ea0721a0100c003682085407520041e0041c404043c40c0003403d080c1c13000d100c0d200030241da000440e000b0007100751404001d0a8441d030780c3d04088007428 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 683671843 1250 683670593 683670619
    0x10c080d0c08060603101703070c0e0a0605090408030402010f05120f060f010207081b0402070b04050703150e06070806061306020c0301050129130306020301180b0402091e03010b 78
    0x110380c80714600303842542d80c080c515140c107002c210b0a40000e840300308003030610310020800402e07120103030704690502c3c2c0c040d07900b004026101c8618050851b03100b0400b0215130000c119884906204070000f0740b40c100ca4000d041c0c209615800c07903900000700b0007410310a40c0003608007800d00940c240c0300d61611800030521140b03440201c688285c2030039211103000705405107100308190700101c0c0140544104200030500c2400242c5580e820015a980c8240c016600300052004203402001d124401ca001e40c1c000d041041c91440c1281e0a00b442c01c0d0000c07540c61904941902082c40070460035081007980c07411094a03114000011101d00c140d11141030400d000000000b46141c001c42c0c1c40f0350100c4100c000308041e80e80e4015003c844e12041e21170040462012380364032203055142c0080e080354143d000e0003a00305a165600c600480e4000c0e00300c1c1c8201c9501400846d543c1c3e80600030040c0c1c284d019101541002504004191813168051810500400ca40074020703064400f5440664281c41c001c10b01c1c800c0d030305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 683673093 1250 683671843 683671867
    0xc060c051e0703090503010c05090d112e0e010504090902011205181002130e07020a1a2d1902390607020709090819120c0e0906040b010c08 61
    0x40608400c801240c2800c0c070001305440c041c8200700c0c0481564032060710b08049541000b0020707403034007001c9680600c100c103801118dc440f03255000c840700782d6450a044211010941012209000f07031081c0c2004002012140e059a000c4150b5045918558010810901070b100598039421700350750300c0ea19a864441001640c40c0f0440c03072206404134601c140d0785680c04440b0004184e1141d0a40101c2d4961405000c11070240089400c5501c0801441071b5903000090b0794505159000c0000114480900030081c8501113030f145854580c59140c148a001200d4a104259031010400a00200d40c4019140100039208013640444194075082040300c5030281741c400903071002078128583e0300190404019245550500000c0e0340c0c0c0150841d400510042d0700d0841c414001e801801e408440400d03003402661a0380c624118103241003100c0c0d441340c102d5017a11080c04421101621829010000c1c1c5640d17021050321150007041e0001c0003a18046000314100005840b40050064010400b035000581d1082041e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 683674343 1250 683673093 683673097
    0x910050301090c0302030114012a1a0c0304051203061206090706030b030d051602130c090603050c130b090a050901060905090709030203250f030b090c03030a0c060c051e 74
    0x2d910798604201c40710514400710200c4c0424000e0132a0140d804182c40019800b036101281c110000c4074042002c8034070250300303507044034460404071102a1031444103140400e0800d40140d10112060140b8110300d031035110980d8404000b00440300e043c8000007c50001d03121042041d9942c444101101c80c181030034500c1a030340382058412034001a00d490000f050354600401d070300c541c40784250746250800c0001c450081c4034008080381241d10900740d030140f0182d51180d000b1800100c3d42601c4081000e4a80a409401e03100000d00788144100e04100565040c0c03462030580050790400301040e51a50000d80200e5082d01d500c2d0451903001e0054030000800542c007a4044054400c240c17418003107900d4004041c3c0301000c00b8000294940c02042041c003441c0900309002040c5a51003030641c14141d540d400095000c05c82e504143c82c01c80001c41001074118080203206002c0d4001c0e0003e502d0420701400050204401da10010310b881e803034007030094280b481041951071b610702a581c441e19045020135100300039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 683675593 1250 683674343 683674349
    0x4051614040b0a0b030a11070b0109090201080901060533040b1e030c070f0507091a0f0901080309060c0c0303030a0e010e12040b130e04030206010608280b060910050301 74
    0x281d401c2000e20025400e02c070110200b201c0f106410141103031281741c460405050302e0107810500500078004413020a4050151074024410140c0004074015a800014070100008207440c11907810044104059240c606040c0c004c804642203d03010247d0020713080100c00050410281030b900007180110310421000e00906007900d45051400305442500a828181e000445200c04034003024482e590110300d100890142c2c0503ca40240c500300c43c1c0b50b40550341250100e200300358011001244d0701c0d1003401c04024034001c00c4411110758201d5850818500d940713200d101e10030382c050007011407000310f8400200329183c2d07444c5c401000d40f5124504004000010020080c0451440d0700341241c0041d03140022a10360030012803c6005407806007021514141135001909080244400000000d40d00c14640c41c0580214440e070b020309030b15454650300a0902001602d03c040c124540d812a039452a145039110a01754aa06000703e078444112000901900500d805180c00c1030107196811050f0754007030700030360503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 683676843 1250 683675593 683675599
    0x607021009062007180f06030c050f030c0901050607031106190609020307120b0325170d081914130c06050f070215070212011b0807120504051614 64
    0x82983c0b00200e9404803030300580400240c0c100c01c005220240e42070b0707107000740c41491080104010028690040840d14241c0c01a03071540308550051155107410100000c0c103030320840003011580c04010008a4014041c07241034400e1000280c204109801141c1c00e40103400c0304d005440c41e41c41d2004103050804204a8002009803800e100442c1003681442178902446a5644508040e0801000c00000702541141d56505204036140c0030310351011080760141c0c40340d4000180c122145440c011075046514031210800c0c45d00719050b80284e20b6484400641c1c41000f22030310200d4a00310155210041010b5800160032226110070480c03801c08094451107070300e1054101090903640e0380d904680500400c81c5401c404a02000744001500d0002a0303a6070170100740880601c0c0581642c00650f40070f280000040c26651594101030b18003655041040350142e0600b8049814900302d840244910420180000b1240da1080800c0501000b000ad01c031640d607904c46030800003515503981020011030140301302e01c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 683678093 1250 683676843 683676857
    0xd021506061813060f180b01090815060f0a0303080906010501111f0e030a0c060501091116031e0207030b1317222709050304060509060702100906 64
    0x100a081120880780c103035991010180840b14840200121008582990300100751903040100d04014a115203000400072082940c0d010714282c0030500540d1101031105051060301501003003801004030f043c07400c0d070348081e88803c07090b40c0f042c3c0010090303640410025000111404040105070300b00c800030740102d01c0d090445100e0b80e40d400044889000804404109410080344240360000041e10325100a5200e000071a0390038140401510b1500b02001801c00103d840c100342090140610482c0d0252916842c1441000507101031010640f242500c600c0b12461a41c106000341842103c19400d60f120480302d1590500190000030f60300d0b00140230503505910290045540b41080545543d10f01e540040041c1d02210340e142c18060503001543e002e0080000701071110f01d09800d190024018003001a212105440310762034201074240c0d0301c044c00609901d00004070700400c00001c241c8040f0f0700c151402e10307514445400803400501420100075044401c41035038200e1960006130036825a45d590f036441c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 683679343 1250 683678093 683678101
    0x180903091c06062c25020a0b0408090109080601240c050a0b10080307051c0908060901202b02040518010611160e10150f0f020708030f09010306080d0215 67
    0x1146a101c117803810001000f001030740c2e200528401c00500e84101560058078246100307600c441c03080c0041150100e4900100142d400c00542c3c1000f4840f02603d50000100565810f00314040e5001d1015920f8085d00120300724410007082c4242540054582d102c0b0598040194924210019040548130111070502420b000b1034004c40020981d40405c0c1c0000082c0b00320301e059854030907a800d455044004100b422400400c1e50340e003c1006074080c40d0000300000e2400f1a80860500c1c1c940c40c8000d035101c2060400032078400304040105050907243c504c8001c4010708003805081c001744101d9100541000704800702003070321480c25107220304072401c0d07499104043d11030510740c40d110040c03603802c1007100840580510008070551101d0360b00080c03030300802c94007070307140c44800030b240c024480d0f4880003540c00c0c0c0c40f0010050f44140c920310030034000e00040c24524200701c0e541e52a40503008200c202c0484c085500079150703219810003401008400c080c1c41000f150b80e0402501c450300e40b010003403070b0342d85a8081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 683680593 1250 683679343 683679419
    0x105011b05071206090c031101081617190c200c0a140f121c0e01020d11030d020a08100e0103020d030804030c0c060e180903091c0606 59
    0x24004060344140905a55828403002c3c40a8000307003034041c0c800565480d1348200103448510035102641c0103040440a10084030001449441c00402038801500c170007021a205a800524000c40001080004c01241ea12042030090000b429007a428400303080164000d0b000c1c0d00704090100c7c98049950344a01010120b250565400040e82c410f078006480c00402c00602c0c0342020a04803003e00144507654914880c0000303170b00da48a0806c0310340300344c000d9005203490b0502d00294108500c0c145c240007040303240000000c0c2d1100900c2c0e40020611071882c07140e0648410510880d440c0c404e548504540b03910750103600070300351081110030200010300184013242c6220800d2205049070303030080c00c90920f051550740845032141c018104a00344511a9081000a004124208060b21090b590500c02d000541c0801c41500300364986120b40545c2501486441c60010003201c180171000e440d400c40d00c0010158503400c910410501814492502c40301041c40f4400c2580c150452214600503003149002c2590 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 683681843 1250 683680593 683680637
    0x5010510170102310518060f0d05060c09180f01060906030b0a0311030c0901031202190c15051603080105040b041406042007050a1703041e0821010501 66
    0x844c4401800846a0000e4070190310394804105400300444410342d03607401060b0101c01003a07082c501c000c041d00030005141000c042a03c0c0c501c40c202ca0601c130080b40c80e11034507225034015001c1000400c0001d0740200c2500c0317440710401b100010004000c004d2401d000283d103000d0342801003400007101d16400044c585c1c400c3c001c071950650010001c0c108903145075100c80d60240c1101c40503801d4003440c2080c0c031242d80c0301c40083e070080d40034075118950182c6809009042c407070829100250ba5000a2503440810107801c1660b0648040441d000c40390003503072000351024040e03290b00100b448031801d007000403d0383c0481414120383c002d44050101080e180100015200414982c048047d00c103c00034169142c1600240e8102c000c10b00e2a1141c00484030828510750f022082c20394890303003d5101d100c200004401f03050000d0b44104d005509500f020b6a40100e030464040d01c11901080c03086007102445802c4089824100d580c05651003100041e103d07000d4420824810b06000c1451480380944151207255 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 683683093 1250 683681843 683681857
    0x7020d0819180f02030c04020403080f031015120b0901060807080703020f0f03311202030f030a0e0705031c120f0509160b122205010510170102 63
    0x225500c296546501e072008911464050a45040d02c0b891440c9140c0141c18039150901d015084010242c4814010306280100720320446025910410041022954900945d0799102040052075500d8070303450303e4540c0e040d10b290041b502040c04048404a01034004a01440c4501500c1080c170105041004114103c4400d05c02c0002081c101c60001f140139115102c40f41c1d0001c041d00340141003503c20305491440350040142111010400030521001503414105459154084000000a92030b030100808980c0d69828004081071588180403c0e003500074016605850485e002a07a00c2e8a07100e444031010709120a800012402a200c0100700703418081140241e055a07000b01ca100784061040850301c08000d2000d07120303030743e60ba000500310201007805050f004039140002400c14044400b0003406603030300c0d9408015481c10800030b0400f18034a0400041d4000e281044100c8551010b90046a00d040401d20042c005c0d4070345010003d0f0001c00a0100c0190386c4e000d26505a00401c0e041c4290803445100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 683684343 1250 683683093 683683097
    0xc0f080a0207050f0d0f0e040216020603040c0e13200a170f0303040602030f09070e07032a020102031f08190312020d020d141311030a0f05030a0807020d 67
    0x28001806410503900240031a0703101d0400c45880c202a110203e040c01c001c1100030380050321101c105014598404801150443e04460031480d02808400c2540d041c0340b0301d00001d0107018044005400e1040d0740f81030380c00038a18107001802a14009003c0a0704558107a021184900d1407500c081c0500111100701180700b4000e0180201c07107007045284030007a00707100744000b1a4400c1850103140d111090001c4d50041d44902c41c096100c0c28048032020901d00000c110300b0303196101d01010010701e22540e2040e034101c80917027400142c0004d0030160b0745810411001c552200c444602500c045554154000d5125a0340c0b44001030180341d10b240030320900002ca101e0b280099012156007040b00103240ca580d19030512a0030a0710482d00c103071250303c051344c001c0d01c85041c1d1183c0c00305580042d191f4a004040c096245c1074084200c9282400500280700d41c1c64401810321070b111925001c16490400042c1e5000d0340001c4103821200c618604140d89902005102000a60b03040108003d2400007a03c14038410070cc0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 683685593 1250 683684343 683684357
    0x30f0906080f01090515030307060606090602030f181215060901120807061a03071203080606190804140304031115030f010303030b03010b090c0306090127020c010b15030405010c0f 79
    0x402688050400585008806c1800a5044d00d041d542040104280d40c4146070124141e072900b2006400b200c1a54080002d5400c02c010400c10842508100c03078130344c5c140100d0040714a0140c000701e80000d0314074000c1c0e9091f200c1d1500e1015102c40b40c505044c80740c07100702c5412809030380716180c09500000c03220300281130702e200340307d19000104a034001d1400fa07103184001c0e14040c1c4440b00081c2c41e000c4184d0000414a00f400300c48801d2584c0503002d1580301c0e90940d911071601ca095411100c00c603e80314400001c0201c10000701d42000502d02c03100030f00e0b007605c0c41200c0e2070b076480782841c00c0c00111503580c0354411503052003100c200b40e004000760707441014a0b511003412a071940e28240c000c2c0c8644001c1543c107550703801d00f24507a5a03519862502511208001c503860f890000e081c08007500e0107820102003560300600404c900c0c000d0016601c0c1c1d02010b0700c005602c50004e0105a4054621180031581c000e0008040040c0300b411a400b07144168005d8000307011055805c1010385000e012111100c0c005081c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 683686843 1250 683685593 683685599
    0x3090e180d11072705190b090606070209041119170d02060727031118091c090b0c0a20060403020f18012d1202040504050316030f0906080f01 62
    0x2030508824011699000b01050480110700950105c0b003040ba210b2040c200c07928115202c40c08240b250f20501c40040c0c07008000b50030301000207035142c06a50340c003d104070b0b042c00004080007100032928125480103880c010303103070119420305104201c1e01d0160758009201d10000800c5114005200c040b8110147c0183c01142ca45100c21984051054002e00040e204c00302c4c3e051015555001d08001103000d17034030000c951040041000840f21003c0383d09060741c0c0c0c1c03660900101101c00305400b0020911904540360048171507205488442413644a0001e444c80401c8400813038001040241079648500000e01c2c039100780704403465240128030102d64003c41d0a00062006042c0707502803048020005000d20f03050142c049010b140c24034241c1000c1e110300e0248552132081c480f50441003040c4504000d4529a0301d0400b05401c0003a156580007920881d21440442c0c20f010062040345d89485021050440e031002600700540054462202c0300001800c1d601c000903251b1095116070300940130030000300b425034a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 683688093 1250 683686843 683686859
    0x51806030c1b120406020106030201080601050705060a0c180e070e0a0e0a090807080309070509101d070519081603060b0912121c110a020a08030403090e180d1107 71
    0x240705a400b0a242c400c040011800c00741400203400101440c2e40049451802d601c0014450040030b1300e07440c14410103008035000284003007a00c5034808550903001404100c103039811180c1d8040444006956001c5160101d40703100382902c5244030b000103031104519014901d090021521062089850130301c0210081540c0e00c450b80c015000c0c150050300902d0a101050715070392455402501c079a00180c0c4440700c02c2200c0e05081118550045111929071240d030719050007030000d0038505003950f407500f032900000b80c0c0302c41c060800d4401d016402c070b440c1410040380000241100006680b0290310504a131200b4030725912034014001920700c603c070441d050031345440900280d00d903400b820300784c140600b5000c1e0b032100111700060843d41c000040000540342403e0a013004540008488084031402001800e110720340019440003401c2e0301c01100c030b659694505044840c828541c0256a03d00802014404224101d50f0305480340c201c0d02e011b454525180c9081a640da8581c1c807548036194000c91000c2190301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 683689343 1250 683688093 683688127
    0x180c050901170c213723010f031103010b1e01140c0705040609050601020c0108040f15050412021c120b030a14060907051c0602070f03051806030c 64
    0x200c503c0c041d04000300c0b9084600040c0ca0201e926001d008031008212000c0d14030325540128941c0d4500100301400003200402c034000c2000300040400e510703101c8840c00085190756103582200068448142c0396103071141e614100e44c042c0710684440d01c4250403255145010b00c51050f400800030180c40125007800b990711441421100c40c40e05202c2145004003591300484000c08000e00307920094060b80f401c0400300000c44016401841d40c2c14681000c03c203203130342c00090032000340364242800030f41507a49103010712070300c00b00b030000034940408040d401000a40541086000d284a140c0c90701c05e00710201c408990742c3e44210604031000074804034118250b8000d0080b40780d11007c40f00046503c61548000c00d00d01110003108845403105000180d590010510440c4d4100c0301e41800f03064181d1a140c0003804012448200b9107000c440240102d007004690303030442d0802035000c3d08840500405040180042d00207001070304514030f4a01001007246030417011a44503000d410549030502800901481e046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 683690593 1250 683689343 683689351
    0x7030b0402030f0106080601080708030c03090f030f010e0c0a1508010509101d04051e100f0207050109140607090803070609050109140102180a050d060902010201020d06180c05090117 80
    0x140c05005810b01c212007085c06603030060481203005207031651400501c549000c06660081c94103410a000301e00071490040115100514120f548100c149950000242400e03030385130300241103610b00365944184140c085100700420404031100c0a11a503030389000501c0809281d920301c005545100103014514000700300729008014010320711030301078880700c2e40850340040c226072941c1c52056400304010040c0400803440300480c8403503c3c8840000f41507442e0b0b640c001c58610141c0c116128800e12401d180550305a40015400000078002c189143c00c0040104088501c44e403007038061140001c070124010840c1c941210f50f1900214500040380d180c20000780200c0740100c135a5500c5a50744800324841400d5120500d40440005941c2c640442c01d080c054218070007400d00418008000f0001c07035035001c1d00402e14941200b00881d80446500c0100d00a21412101c208090328001011540440725040084c0d0321650342020001a03100e401e050f0341e2802402d13222070006019207805540208004452a00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 683691843 1250 683690593 683690599
    0x1d0a060c0e06072006070308010326120a0c1b080f090301110c010507080610050c0c130b03010e0106030f0213090f080304021e0604151808010b10030e07030b0402 71
    0x41d60003460009800c6500c02c070360507564101c150007000c480300c02003080d107804283c080702c84500d4100540d5010b0000c070b405100240074061101048034106000628480c00d07000e01c800c0d40d40c0c0d68070300c8442105561a05960a20300a4500300320785900e00c0c022400031841840d0384619881c030710060794905009074031031800c4140c012401e000000c01524240220000c00805902254481000326102170031100000c08020400c9080400c0c4841c640715081090f0040c20700d454010360b0b84180c41d0a00d4a007020008070780d90807800400d40780001744445d600003a8001000c5000f444000010004c4e41c0c2603801c903000103800c40e02028143c00062900d10001d40160041e0403020a1180d1940c0b2142030a9003400c000713940c1c03524000200300441c40c0c03c0c4a0003803600d408000c1e103c070004180b0301140322070189000f842150781c078441d5650500e034003e406100740030f100c5601407503002e500c81407910701900c005000c0c2c074029148006000101e40c0a0b020b08900e88041c48001c04010f0314680710301046150251059070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 683693093 1250 683691843 683691857
    0xd0912060b031203071403070912020616050f0d021b01051617040330030e01090c1503050609190506011202070c03050c0316090e03040b0c010e011d0a060c 68
    0x30150b10107011450000700340da4070413602e900e04000b001d403544061b00d98980411504004118015810a03060030175a41d80b100d4442c400941440420500e200361059407000170b03450f0a608041020006102c2285008441901d0522048a030243e0fa00c0031800071110201380f0f4680408401c0d403044002d001c0728074188055000301140e50301d03035101054000c503580b103000e5030001d42442804802c107640d04652003448a009501120007244116503010840a50201601c600b9600d204190075004200c025800400100801d80c2c0c4841c01d140a61513032660b100482d08210004650385400a030451142500456801c0c0c00c508200d60080140002001103044c0070b40783c10580c050001910146c604076100e28204040e0074258100180b84c0b001400030544a54400c2a1f04692404a203468104030382154802080314124980d0b000d045002e1a00010400304000c2070a04000005411440e00c103400600208000d02031401a10304241034500c03c0f07582d03540190b100d100090444d90003e0341c2522035140c05c01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 683694343 1250 683693093 683693111
    0xe10021b0d140a1214030a2018030d0305060109030305030406060e041407050303130302060d0e0d091a070201080106360515031b07081204061d0d091206 67
    0x540c42c03101c1031204165911004000041000c18019034042141606220000b00c1c0c140e0201c50103444000d00c030300c11356501ca60041e0801354003140c03a52540314210510710346801d24094100c98a0400b6102140702c1d1160451404403507000f0b02c1641d00407141139480e0061141941c0701541e26034005030088400940c0e400e0700007900b1070817031007a50050b4404d40e046603004003122615807814000743c000d14400c0e0420000503d28600604201d011264103071030b21521040400d04000040c409621601440d0017414000180c0580c40300d2000c064940703045250b40c1001001006d55664026824005c0c00328050000500646000e0303211082000400f0200e0025a0b081c012110344901c807421843c240e11030608010f005500c2c180b5940c018511150540c0c41c21460140d4100c0655500740c8509001e01500107111018003400c0d0084801c40000440c000280b8200ba01c0d00c1801054045074040032007848086043c0c4c50302003c1640e014400d141c1d40ca6040e06801c02d000180c000050100c11103556545401c0c0c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 683695593 1250 683694343 683694353
    0x50a0c1a070c020907171513061202091608040803220818032107030c0f1104050c03072015040606050f030304031a0a09060e0105070e10021b0d 63
    0x25104020980d10000c440d00c151050001c060000741170b01081c030003080310581010420004a60b40311000c0c80d116050100c03101c0124020f9130181003d040150708010b008034980d500c00d41c124402a06c00d47d0000310070781d40c0d8860b4242c7c041c1c0c10b01b0300b040004c0f1034001043c04240d241010316000b01902c100503e2104451030f20700040c18003120704032a0102c010510840c5002024416081044250081c0036000500b0713135001151400d450600c90182070200d04d080c14148a0700460544d150b100b0008890340050342004152105002d610754883c0d4148000202e043e07843d1810b881c0609a9500c5025501c42c0c4510a03102c4083c6040c640b0000b4492104006c988500006946000e42d00030300c400291a0b040c20203000c961103d030b60201c1d00a9100304402c0001810b0921b09500344004a40c801c841a240d9024040240202001c003500d4142803030300300e43c0d070040c040d40114090031260301c815400846c3c01c4144041c8816000b40a00580c020010700d17540c07014546928881d41320010641d00e5952603030365a03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 683696843 1250 683695593 683695643
    0x1050f0903031801030501080c060f0a032d0507031103310f050c0303160b06010c020409060b09010f050d080706020f0a020a05070b031006120f0501090f0b10050a0c 72
    0x107203da050401c24000d424a503018454039000d01001805010300c0d650440c08204a8460001c000404400000c1d01c81d2119100798441251960813003440d1410706903c642d4420028044082c070a000c4d8034280114074030342d000e44682c03103640340e44000184c2141d42d284401200c18000c0c0c0368015007500c455046003a42a40c04009016042c45a016107610343c08a04096140c6210445244d00a40c4108070210540742141569000396038001c405040c2b5603200001256107e4901000a40290a1401d145c0401c2110340040090520548401025a0b139070341c101e614501691084540001c6560110300c00f14403000002c04c03445000e144094900118041840700f60ba103c08900f00042e00108001c1c1c08006050110100800b5000c2c8414118145550040020000b91282d20f05200c0c88460181d541681a0080180000b8403007007000b8540e51020140044c01d07000301e11600307040c64040350803c0b610304400200901680340d52140c0c00c2c005011801d40d0407100040b800c3ea0402c2150f0b02204080070f232020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 683698093 1250 683696843 683696857
    0xd050607030e060f09060c070c030c12061b050f0901030207020a09050717070905101209060f0f0204030503030f0403092304180222140c040503191101050f090303 71
    0x75002a0114503031540c42c0c24034402401c100c600c84420018006040307000100035400c0690f518202d41e981445145c22840e144465000500700c510003040001c4800b4000e0580c429140100c1d401e010f010000010a44000e202a004401051060149905800950015103160790044c10014548025a00043d40c140010740c04071641c240c980c8108142035900c0001c138011038090990041c0142442580030300100c565008250140203140b82d480c110a200d02c4034041914070f0090704010f1b8038a541080406461141c040c42d074040e0401c16000c0015011f0701c00c5400300e9802ca40a14210349900341031b81030940c0c010307100f6010081604004501c20102c00c131000000400540c481c00580541000d0009544070061600044041d210541c1c000d80c07150903d200131010305c111210b40038643c01c0310080003800102918244074080400b00107085024a0040c016688110300b140c12409420b0b0581c4003111810780300400754814000341d40403035400352000d8500700c6003120009061401501c0841d281d03400c012 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 683699343 1250 683698093 683698097
    0xf040905120d291801060c240c0f1e0c1104110a03050613110901030e120a021b0904050d03050603031b011d0606010e060d0b12070314190602090d050607 67
    0x83c141145030325101d0601d40700407514103194406580f50120141c98051600000f812015030104100c4029403080d900e4000800d48103410090701440301801850708811001380302c080345102e08080101d61040360088440d50066a07800d00580708c647d0b810182c0c0801c00c8003950000e48035066604d401c0341c01c00c0503090000341030f40e00190364034140040040800d403400e2803030318981c078000c1d0601130902120110394141c2420300b004112702c0c100c000e41c0351a003410721180403c41c940100d64085016404500c10142a44c0c4480a02c2195144800c000008070180ca0061040c1d1007070307134583d401d58000d4102551007400203003500d041c11490420054240140800961103075995940c01071b81050007425801c40c100341c1c400400b4607251400000e041c40e04c12451030343c4180e001056106840103645c001d080c011102401003546100041c1d80d19a1b03500c41c50000f194807a2950980c90560000010f0280f0304404600d00c00d9041078660711258001e600c604850b6411100040103140403640400110b40034001035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 683700593 1250 683699343 683699411
    0x51c180f0b04170403020f090907050406091a0319020d05030405060a030203090607030603030206061e04111b0f070608060402070c141503060907110f060a09020f040905120d 76
    0x524101d18040c1003c444103960920601003403000d0f0f21000701710041c20030284d5a0382ca00e6229092444c4c40c0008d9684130030740c8a420400302050f61552900003852110703661034039000c0d00244000301341e16184030010600d0b20014410700d0001511b010751207017007002e0061058901e001e4842021a07129400390000d000031035000030074061603030010480b8550041d810f2138100281803e41d60025202c10b4041d0819100741c03603000e0b01c01800505000d244a02c0d00e0024000c02460080c801c40c0707c11500030741e4200320074520900c035482c200e4001188480d042250200680700042c101141940d04280c058074003a0400d40c00d00443d0005609208071070060440000d8036031800046504000803200c15038070050030848244203100b810f0329400d42c00c44e0410918101089010711220002d4981004680350248030b104410511080614903030005040c24020355180c203078041d840061005076161403400900e15402030406141055070710018000b01041d5180100d0701560652015007548070748a80e0404000305 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 683701843 1250 683700593 683700601
    0xf0b0c121e011409270714031603050a060504060e0a03171006090b030615070c09050a02030906150109050a3302070311010e040903030504050706051c180f0b 69
    0xc07408280180401d4043d08a441c0080000c91036080c4c01030701c001550a40d4803e4049150300b41d500c1488820000402c850800c1d60360140030328509001c400c00c50090107807091040c485a000403c560540c1d411000a1083c080541d94001c001c24000b003054445070765491402c074175400107020380c0520501965941d1b81c03841d003525552046420103400c100c12040112010400070ba0890302520440700020710b007988903074030900030441c212009844580740c6100001c125080040d03650b100c4041c0c502c8200c0c1003080e990340000c0401280700580d07000e003440d4403c2c80000c030304c40e400e4468100304542c1894402000303a510b00c00300d4207a50146d08130313000c1086c0c003108010141c004000c030308a100c102c400c10b4210450859001a4030744441d404013800000c00f07030340c041025074068194103c502e600039104001038206030600030010710041d1401c941e80d00070702d100001c1e410321900a460303c0c58040440c0042c10100d40031008002d00042c403d013540c1480b100f07080008604545280400359008000510051074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 683703093 1250 683701843 683701891
    0x7030804080a1515050f0a030606030b1602030a1707170108070e09031206090405030c37080a0c0507050a06020a0c0e0c03010608070e1203040503011401030f0b0c12 72
    0x200c0c090340c010320716284c540594802000c12a2510842c1c0742074802801100031035011034580041604054031880c28044000100140c4914a510814a0b00804021003509010407030300c91040c204c00c000013450032019403440c0a1a51071464100d041030a00d9111b44a403a103860015100984c8900c02c1900407003010080ea8120355540c66125010300051450304520010b005400000944050302800889001070200329080045920340520310044580c0c01018020404200c002031076000d245c0740d100242940d401a03101c1d2440b01c207a0303101c04428140100001c0071100e020085201383c803180306e5020b00080725180e09802c0d40c0504456800340464941c641005590b48080380d01c4401e600740030104000184030b2800a480c15078000c1d21b803101c0240c6800f0001c9942c0c0804030013465118040f400c0e010b80302c010000060044800550080c05064080101d2004012003413001401c0910b8488203400050102030302103500c00c07000801c2c0c84c20082030480d4403640690454110382e00500d07015084d0b103050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 683704343 1250 683703093 683703113
    0xa18240b0904080a1b080408071403060412080a09080c030403020103060b070f0f080c0607090f06030209030618071203051305041b080a0e10090b090607050a0c0507030804080a 77
    0x152520310342402e01d6581ca10580c410603480c8070400c24081c40ea5102e401c1c044951548032074104041c41e071196250b2144a8480c2624400c200c514011582e44603114140030032401c2c814ad1700895000340091020f842541c881c01c00030540e0002aa94010718800a00d02c540076006604e000c800550b100c9003944009006c80e0b407190084070291106103d8900060003050440c41c0c841c2d400380c2c00b408030a0049c5422002070143c2d80d2440800d00454081000c1ca6034170100f00360072115a005400150760361035030150220b1080d20451385c0c064103c0c4001500d04a5080b141c18042451001101c20003a03460030a005011040301d0201c0000d03d000828040502d0044040c50141a04590820104808984c8a41040c0c4017031a40b88c14060203000041550f1001c1d17220141c24101c1c1804c0d15080c1c01090842d0b40240443e8030200c80702000a4041070318408001a500d21416a80c0c172805d28020b04420143d819840c8060120341c0c0384035115000c030008032103a01400041090788020804410a450100c14003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 683705593 1250 683704343 683704361
    0xc0726010e0703060b130c030b012703081c060b0a2a02040f0b09130c1a070213020f0409140a05071d040b09090a050706020c01080a1824 60
    0x940c0c10305181161124000c41c202045035400000020f0003030501000c905240c008412468446103824443c003185501500300e90a221000da030b40c210040b21000040e141e0000d4800c1079948110a12001e200003500d030700c001d215080307400c61180b40c00400045650150b03a015044400040004180a00a250041c0c00003040f034644010b00c0d01c0c2002c48041d0a01128240000648560b458229071482020654800700702008090a40d104038a4241c81810380040802411200354032559000911450605004014406015021351505440d5000c00180310f54604004036056800c02c2202c0040e017041c00100000c1038100f002040d540f80404e21120001c6004000b4500c290401c2c0c108414a40c0c0704c00c00102103400101c0602081c2c44c00c20100c0c00400d0b1021405800c40b0290041c8144000700080c0201d48501c40e80848600e10b444e818100e8a681e20544050302064040f40450b940410079081019483c460404003510114192551740007408040c02d5403220240190002010903000c3c0115014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 683706843 1250 683705593 683705669
    0x30b09101208120a0e07082a0409020a06020c180f04030806011713030801060e030a031805040515030f1902060703031e0f051f03020909070308180a0909050a02040c050c07 75
    0x1061020805015190800c2343c3c91912420104041100d0355071603a0007070b01710f55000340c00d150341c246d160407000c1e540d1341030103d140d4410700300150f403100c803e0324044403544505900c0c001c144080e200c0759400d541304c6001420160511408108040d071443c0e080c1c2c483d41c814420b013001044200501e00b0041c0c00040180c1003041042190442c284460b280040c9080c0a1a81454401080302c855408a00d51541980041d80d2003030400051024403683d18000c5100458203c094904124007050080c1c1d4410400901c3c2c00f14581230300c02c2c0303009032606002a00700b0740d000c0d060108410099225440000c140c4101185c4030664884811140c1c0d07400d0300c103c540c40000d49004a498403003162801b00060341c10300c4001d01c83e4503000b000402e103400a100c504000c0d03600c840030a44550f43e07642ca082c04100b01c62155802030159410006120b1107900820740c507035800002400381400341d07400b4803001d8042d6080070810b001e420001828000303800c000748001044080000310fa071207801210424488010710002ca2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 683708093 1250 683706843 683706853
    0xa08060f01031413020a090c0c1b2738031207020402071b030804140102030f031f0503030d0204060207080703080a181206050106030b09101208120a0e0708 68
    0x4a183c4843c495500541e0701d14400c4d41111a510001d00f014020b5003044840e00d09000401c00003e4026030000d40d02480f55001c66245101d1000c0d42e850282c49103c2d80e03a50800b0f003520404080c01115082c04884081e840103e90b01140090311a1030442000309010005061926012560055042440d04900c02c0b4040c5c50f40085070804200b00c1d004440c03000e48100d6001030050200007200e241d0540c041c8241d4100e04459550381414a015003080c40f40680b50341051081c00b025603c04421200810b60340c0c1c0c07986080d5100da0a82a8201845115811607008030000c085015075040000e010380300d005070f8000d0723170703c9041c10802420f240840c0d0045600703a00440007400010214012b5a909a41603d4074944810041c015911785030440ea1000c0300580c0341d440e2540c1401000d4010a05035502c40e10140302c414004402d10400c1142221849070051f4580024801156080c08a04405009004060034032580300c580c121448820f441d03c10407155144a500b9442809015000c01441820302400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 683709343 1250 683708093 683708111
    0x7120305060a03150e0304090501030308010e090312040f08120109020c101131060504061e091710020c03120606072001200607020120090d11060a08060f0103 69
    0x1a1510542c84c030300300c00d110303240d440d02c9820342d0040050b200100701c80181031100d56981d041c0a02952401c0c0580c80d90f0b03015000001e840307000c00000f02ea40725a000e00e080f600c00d590382e840d060520204081e04031040d5004001e2011180101d0f0251030103050182c00040e5038400038103000c0d10703010b04250313070100c0c084c14030010200380144101990a0500d0940301000c5886e41302000742540815004000008440410040740742d60f031100c00391041ea80c82e03456105050700c80d182c82190201d003880d0b2002c0012a6154248594190300c108440541e4000342210400c0d40f04000e004140d0300449080348d03440d80003252100d0f1020043c0b040b03070f0f00a18103684681c9170840e0307a140c0d01d00b41c1c0c40d803120f81c50422010204034000d81e44038512800f050441c200a0340903d0001c3c440243d00d541007510902e00540c203107072400c0e0464a908012040401203040b000f49002803280c14400c50020312a030176144080c03890804070081d10341d00020500e59056595403515490074100b002640800c0003400da040601d0981c1c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 683710593 1250 683709343 683709353
    0x10c0e06090603090102250606050111060a0c1b050109060c030507090b0306010c020d0305031f050607060b1912060c05040311130b100906080c120f0a0605030307120305060a03 77
    0x120718484082e0380b01556961611200740c003a1150b0b102c0c070300f40084854203500b042c81c2c122a03200c4a40e40305410034410f55903110011210080140305a603a06c2e0012030210710624105e034010302d948a601c0c10107222494141c000c410601c0456501075506945450f1110f0400600c0d01c20301e80301c3c0407182020080d82c1020803005140301418000e070319041400101040050b801001500b041941c018908003c42844e490014101c0e001074940c007413442840744100c1c007040440401c00e016580040d0041742001e0b0542c032032201030f0802200d015000501401d00c0030b0003844034040319000c0d1041404000a510061503d48102d504641081c400c1040030300c010300c00188042414408241c044802440702440c00c41488010300f0142c207501d900c04911013a03201e81d0790b0808820412140ca0342c03100c0340250b03280f54a1000c41e114640c500c1c3c030b205000d02e000529110820b00060f81000ca02480000e8a070303100c902080c55a40301500a541c14420308002d0412035078540513441d03225509403540441c0d2071440d920 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 683711843 1250 683710593 683710597
    0x70b030c09100e04020325020735031303120302031018020d05010e180f0d08070203040f0f0f0510020622051501090506090411090c0f0d0b03010c0e06 66
    0x2900e11610b0801121100107208030035640684100500c11981ca00303001d51449070301403011b500c00d0314250089000090341400403a00c0d0f01182d24241400044501070321840b000c803480c016940c0c0b150283c4200500403524104081d1200041b03039100a000c040c11820f0036200841c65014800415004008205120f00c0100482007156812510303400b04e1403009113a5030180c007442e807074031074614904000020322041c0300c4c07400c90289407030501548803034a924616076101c1400f40d2103078116074020200001301c1403040360480c0c0c1c458410310549050a0300c0d050040c03441c030300c10b50000000b204100390500520007054440b40042134111480210078600102c040d40b241002010407100c121104e9400c090b40605d400030340c1010b0f174854190f0322130164507860404900002e001d10f8070030603e403800241c0ca500301031203482e0090360421180c59020846200708246810f000b0130003d043d94050140c40301c3c1814910213010030700f0010700c0103d182100d06081c07608481d070f0703054500c04209a4484811050701c0e4801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 683713093 1250 683711843 683711857
    0x10504062315010f0905031b01140708072009040c051f08042d0b01080601060306030203070b03070c0605010306090b070305150906120a03170a1b210e0c0102070b030c 73
    0xd0101c4204c0085401369181080c6038002078040c061030603401c00d20200f040c0600d20031b0b6001d80b1401c02821000880398402d000e0340c0c0b001460810204101400326982002c0c041190404460700f941400812011517607e20081c0c0d022a40380108110501062400014281e5454014100c02d140e442103140001c2090b2300190000c1e02c008074110400b03040d01645041d01001542d0034007080440b510529000143c81400d1265181c1c030300400700040340c2503209000700e100f280d0f0010000c001c0c940c10094480800e0f48090183d20034800120030580004072103000b240d00850044d00005242c07600c5007890700c400d0070014061820180f80004000072030998010082d69110242c80b44004c030f030f80e0351001c50240320290700b01c2d4a091290070b08003c105503000c040391000c3c0550545102c01900c03106040000d44002072901d030801100640503411040c49030701c0d400c0c40400c80c04454000c6d0020900e881086507440352101340705070004181405256010802e160041003c0e1048500e180b43c10010240342d802204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 683714343 1250 683713093 683713097
    0x150e060d0902030a14070f08010204140613030618050d0e01020607110f07030c061202130302040c120912020d080405071a0c01050708060f060a0f051b01050406231501 73
    0x120300500b551001c205100500758824440417042d158103022942d101d100b40304080c94460043c0f40407825010600a407000c4a90074040341c6402d0301044d0800c0307199002800740f103210741081880003000c6582800f0b0780034400f4904209c119544c102d800e01c68101000303a10303031070103001594040b02000d0b6070028009030720148528050f040050b0461a2a08200d514040ca60a0b80f00790700020060016451a9000b10b81c002d0b1140166610580f18280c00d81c0211050034041d980c0107007082015003040e0708540c00c42819440c202e21b4800d02010108200e81c2941415980b021007808007648a070340402c45100003102605140c8141e01d819660103a64886500403504126582e400104e8034909410039503043c520001c00034402d524002d14010908d480440c3c8080c810a40c00c40d4031001da06100c01243e10024081c1d540320450f010001003075506038002901c1c08100c240f081c40510280710280314403805648940300c00304041016142d140a000c000c000310904a004038014004a1024080041b02d0101c0038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 683715593 1250 683714343 683714351
    0xb01050313060f0605210105010e010e0103030e0f03030d050f280902010c1a1e07081602030c0304030f0b06150703031802040e1c020303010b0f0702040b1504150e060d 73
    0x50400440603105a07404a5001440c00701946402c00d071b600c03107108220b2114002005641c0c2e981c5603420b402c000c280300c4e403c000300030075005101080c40b608500c0d01034034000c0c1c46a040710744524046451603110500414035150b84009204031000072100068011032002c98202038006003002105110312003888407180b080d600c408032404c590085085640054000450056035101051030601409003210790040755100503240415a400300d4000900800e400d6640050658903082605a203900d500c0c060b80c01d611003800758030380f0400104010030145201e072440802c1c40d10786103000c069001e0040d10300352180801d4020303010499840f0083d10b126641510340810505800c0a400c0c0e0b842e40316040281d001030901d031101001180004041400c12030200ca0440540305031041240c4900080c0030740f00035200100480ca2001036110040c1c181d4500081000510f0070ba081d0001306103883d40845030780d03414004a02008000c1d04400000030002071800c04c2d84041c80d00340001202482011715011140c1c0d60303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 683716843 1250 683715593 683715611
    0x2901051608040f0303080c190c03140c0f01060902280e03011b120501050a06180b0a0207030c1205070603050a020c2b0c260d090c090b0105031306 64
    0x50045480d40150030601c0a541c0ea902d41c404001e469185010640c0815000070100b030340340c000c1034110b60358a01a1240d521100a07420340c201c42030126010b00385d08000c2d4201194040c1d482e28030040048914840c010213180314038914480c20740d01d06501c030012051040c04494a0071b00c100000743c0d1070388132501c5000c0d014145043e00303075010340101c04507540662038403011201d0f18500861404601000341c4411811580300d0a801d001d5540034010190032400d0080b040090501944045400c0f036461a5913148158840c1e00a640b647c1110741c0e0400140c0c0721b02e80400c18043c0e0420120098286945642503086107602c845a446900d03200303180405580d0000030f1844072841c1d0684081c8644030041e0791000446140401440c1c0c40340407035800504440046c80034503405100b00d80c890540c04458a0807183c50300300004401d01b4500d507414801007040007421590170340d0b0701c50010182d12841c544031030981440441c208440d80040c0c03ca05203c0204244042c40c0ca40c0d420307100d40113601c403a01146c00d001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 683718093 1250 683716843 683716867
    0xf1006060237080f040f090b030a29040b0105010e0904080306090408071506060311041a07020f031f05070302160f05072610063f050d03290105 63
    0x102d030b005001000702140da03036640c8904000600807600f03242e0b00703c080c8984640c6010215140411602d905070702020310311001070b40c040102c080c02c910584071240d41c00401e1000720600d100c115400c842035079440300140100c3da000406041a4801905e055205141c16610000306203c060030203845400104d0004040101c000200d40490758014861a02c0045c4411682c0103403d880c051000803a0a28006080940c01030341902c049541c01004d50413240140300d91074445910000090b604440124103500d803a8a00704684110030124000d240800c3c1c492800c40ca089601c040c1c02c0c0010107004008029800c100c070014464160780050610182c0c15140c646903107490740690210964040d00e24030130611601100703181e1040e00461041d600110142d03010502100c40034016440310080078956008858580d202b14250000c28240c0c6003a040340a000c03540481203400c000316140e500241c044a580e07580b50284e42c10485522681076100030407100d10003280e80400c00c0c214100440403070000d400e11 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 683719343 1250 683718093 683718193
    0x70e060d02060f2a1902040605090403050a021005010f03030f09030b13020a0e0717130602180102160b0a0f0302190f0809031c0506040b030f10060602 66
    0xa500030310490f40c4142480d02d4141c3c2d42c01202e506940d00c1c102030014420108100104081052a18003820640122008000f521301c42d683d800e0760000e544900100e02a11851100c500541c013035210691241d419100081c90100c4400c031075640030b81090300401c411003660010509417030741414080100c02c0f040400320f4503c42c0e10352001c5d0054600c038090041303090200d0f01d43c221681c020b0f112022078548500041d40300c0d08003a038010001402070140c4022540041131915004040c007000e00c0d51110950b2503c02c180c5c1c0010406110200e80c42c0d0120b06203607010010000300008070010b120b2524a00540d4500b140504050f44003441440c04049201c0c601c80c0d0704451100d034160380c01869a000d03000c0020400310000e02c43e10081080840030840c08000042035800503148c60383e51515251580380c8000143c10042d01140d08561186080041d980d0305106800f03041364080020512004400e00c0c0c0c2081c2d0310303954040800d42d00545101400041a0240301807628580102199503c686540f155685 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 683720593 1250 683719343 683719369
    0x90d02060a0225170a170c0f010501030501021b06240301020717070209010f0e0601140d0915051003050c091509090607030c1d2808060f1305070e06 65
    0x2001079449000708480030501c000141d13100410301400c01c5684980440e40c42e00c04030b60141c4207120241b920080d01044800601c011a640750985450380c8035001038900755242a0030071283c0d6500418180368030340d40040b8a1103120940c0f0300419440c10008140006201050340741500d6024200207880c454409404603814251320981c4410b25001c4a00302c01c041b0380003100100c1c8a0500d5500014020b000e075a2554140c40b161a03044525441c1c0000640b001038405400c43d420740002e001d0310204c10928803c4030002c1c1e0203011410200c0b02c180380f0b0402141c41c01450a0b08803400c031041440810800505003210b82e1081d549160681c9403c8000f0040a4100d80003a0b80402000100400a1000700c1c440f8081c2e2955141070003816202078043e10b1502d88446240c44201c00c030040c1c41c4a034a04901c3d070002d072018010403c41003e04825441e41540001c0c1c20815265020505100d01c1c2c00045001070f0744101c0c580c209a50800741c0b03690313241c1c4031000d40c46070038860003500001c20722560300c582d004030407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 683721843 1250 683720593 683720623
    0x204060f2312150604050913060f02120a151401080402030f03070f03020c090c030403052a0c1503250e180921030a1a1008010e0c090d02060a02 63
    0x4800c81000c00300c00031481190351003001e0f080d07001681040e04045040e1030a50308020b00070800c03a80d0715481c204103060310100a507030103522803401c10f120342c80510041200b003a0318503400c00b8a00c0c000e030840c020307130341490a502d04038000032104100b040b40300b48813403071060801d1034101e046484034000603103002503460f00d0740360364040007a06a0400007421140d05d0114401c5e02510203402666003080b0700e451044401543e0141c041000800183c8140020180c0481d1480c1c404807400d0307000c20fa50a9800c000600300120f0b03010143c40b40041c41c01a09103241080d5401c0111326505d80411003508040e401030000002004885184242a00401c0e05503c81c1102800c800e41079900d10b42d0a0440360340c191880395060040f581d00d03511400c501d800c14003402e100c10246900e50745807d03108000404582c480ca901d5541d00420454141e03803094900c11465842e542d90800c103504080b00580040e5011f0320490902c2c004000101d01e58560500c0e00c40c01e0b0b601162181d80f1245c80050990600b102d80c007007985 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 683723093 1250 683721843 683721847
    0x30f0a020105062103120c0717030105040f060f091806090c1706161803051515010c110415241409090105120a0b07210204060f23 57
    0x1810560550109100f10000c441d62240d0703040700404511000e10750f40524030641c00411404040c60b0020341925000030044074103601d802c1c100d8442c91403071321541c03142e45144140000100709a00c0c00380900d882440404004000f002d26080e11015024030b02e214040500d500c40f1444800c03081845000000d643e0000c070144005203440c50302c0c03034100d4024003032960f60401007130301d442c03800100240291040702c0358808400b401036424802d0710240c0903c9144c040054580790003000140f0180402d01c1d01c1000841c501c915420a680d9003519640d824081c1c2e41003010742c2c6507020104030100e459541c4004280c41c00074400031081c0c1c041400e25000d801c1901ca46010741c0b00f401184010030149680e4168940d0b40091480110711080064410f03000007990100c08200144100d01d40250030a02401d0604c0840f800c200c455543c1041d10682154403030081012140c050000a2480d0540d1030680c58030070086181a0030820040d019241e0181d01c0000c01c80403080031492240c40d00f000304203121415660607 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 683724343 1250 683723093 683723107
    0x20403050601090c12090f02150903010609090b011401080403230703050a02010b0a050a03150e01090305031506041a030711100207060b06030907030201110114013005100e030f 77
    0x140c0505010702c04540003480344010382d007050b0514891b81c0c1c0301d9688074402c00c00d28000c81c1c081180700c1c001449982000c200801c0340c5030940c3e0302441000010440060081a10940c2d800d000d0031a8805030300401d8081c11020506205a174052400703a48203600d801c0c84080c8000c40030000520f8180e410980410007000aa03440900d40c00c000034080d0003c2c40d07802844100307241410b1100d8900c0700d1043d00d411440f090340c00d00002d12500003000b6031040c0000d0016000307413030000301c60a44440c01c0f03081d0b000c1400007090021340e494540d2103c4141000307032203051400d4941844040e02c1c00582c0b502100400e80400812070341403142030051b4040050004444c1d0b1001010f20400080d841078a0484e015480e00030144c800d42882019241b0817403c03080941007581c078680041d5809418524049071035580c07001404212070300d020846000c0d2110646041e07000401031a09100042900c050280180c3d181208400181c0300081070b25008002e248003040600c64486030600d113001e586c1d1702c6110040082114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 683725593 1250 683724343 683724359
    0x1507050c0d1106091f091a010914010609030503030c07031e0f020c03121615050916090203061f0c0804091407110706050f0702090f0a052d040303020403050601 70
    0x902d001c190000a449094660241c001e980702e070828a4003481059480c0711400a001544c000a4910700072600c00c04503280c0312015603811442600901d804594440032890007040640d0850b01501d042c0c1081003481c1c2c00e41c0c41da00c0c1c0c3e83c000100700d5150824005080010103208190245a50545480a0000b80840e803005014140340580101c0144100040b002c89440c00080e480304040b180e0780003d18000e601c00014030121141101501c9440001c00e12200c010b15034414035120300700001c05411b12110100011005840b2984213104090041c024041146e443d500c62a20000d00007503651003101e04400290350a100b149800340401c0d601050000d01201903802c04140042a050b01c4026661003003000d442c048252001450180d210748414071150b0f001d00014526006c40e9184c490034159164009160840d0440746114070340c05420078006d50711810300806403c03100b40170768100700214128840110002d80425040000402808101858000d90454001e55002829510039685404a03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 683726843 1250 683725593 683725607
    0xf04170c011d012a1e09060813110d03020708030c07030519120302370201060b09060703050d09080703110601050a0308090f0a170a060609020a021507050c0d 69
    0xc0b100e1081020041d41910980600c0750550b44910381000038800201d104083e08820050504142803040c1307504030a003074021000d5040c1c40b640942d40c03149442410008011f020381d002409421075034490f089140006880c00701103000a070402d13500311201c024103040491901007980c5c004400c2c2e00000070103241500b030100c1d516068078000c0013180c0300c90b0400003001c44608078801003d0036526400c180d0701d000c18800d400030100b03043e007051301c041562030344581c1904d417000c00700814012106602851298540a000303450003040e04180381400c004a8a01240c010310034500c0041c20080001441d0b04c00d00e1b80b9500200da442d0b0071091160326449a858043d24022007001c6003076244c454100005031a03d007203440c80c0203490303208036580d040146d09d10920250b07070407a1185c6e903031211001c3e07004a282c040e800c01451008420740000c0031000602e0805030125866500040f41d8907004001c050500c5800007459080440081c0d041ca40030f55403100102d80d0340c003480340c40c54541d010303d224614000380e0242c0d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 683728093 1250 683726843 683726861
    0x3180c09070c1403030c09091005030d0f030509060105100e03010f020d0522020d03030c0c0b0703051008071a0715150501030513030c03141b0a050f150f04170c01 71
    0x2c41030b00c1101040c1102e54900041b41d420b46028400c1259110b18200081342903040074103032008204181e01da03c0003904000c0080724502c00541c0380b1824641c13055050103800c0c1c000308010040c0032117504010200d004408000304840500a000800e00d90300e4400b580800c1c00340c3c00a8504544611026510b10f0240c20700b5070340981c038803520300b01030504214100302c111010799000f01080a25186a0707010b5010340a0320020105000d515581c0d13501190310000d045110300b500c1d40d400612072500c14841103100809410200c4560302040c4140108030000e00301d100010740030100242c0b202c04516001e900f100d060f40031460580c0c1016400405c0c81c044507000401d80b5402d807024001c0e40e640c811802d00700303404018042c2c002283c1d0034103072000ca4040c0e140003200b000c8002c00076141c8440245400c034050300c1128400c4a6038844103100d400d1203010700c415503000d200e400140a29480103c0502c07400321002e05408580e480e254040340801606030071030302c2d101818010040d210340c00304000c207000700b40b08a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 683729343 1250 683728093 683728103
    0xc2a030609030e03060c030a0c0509120a0b0c090d08090406050d0b0123030616030b1c2307061202070212010c0311041503020904020705011b030f050c03180c09070c 72
    0x800211184e01d00441d050344650710300c0c09050704564500403404080c0c04868400390034000b0400c40c01c41a91644150140e83d0100c104c01002030314003030315080c480103a0091000c840d42c0001e0010700d0595840c40303501d02140b81c01580c8151640031401c00900108040d0348007130340c00450080080e04119007031190364103c9481349032600c4d51503041504200c0ca10040008964940c026600140c540406115600070440c05c03486c00080558908020402e20071200840c4000d00d001d41b50b8450030441100c41048491940700307003505140000701e042a0340e51002d030042c5003c1c000d00c000c4000d2079051aa06407884203400820011405190000c19402000205088000241070a4501040048010490b0b0455103c00d2100212849501c4100c009401082019502603020452100172500900551104010b500403551440c031000d900a403c884102000c010b4490606d020403940040b5642540da001c1d000307107004000c40100103000b40c00d103506c5004407940b105006003480801980581071900240c410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 683730593 1250 683729343 683729357
    0x1e030a0b09060f040309030f110a080109050c06090a0303140f030103080c0f1501091e020310080d08100b0307020a050f0601060f05040f29040603050609070e010c2a03060903 76
    0x583c164164540d01110f02602144c422801040055001206110307103e008800c0581080340c0707880041c00444555009207156034440d201e42c01813000c1400580c1c0c01c60003c03580b4034900804900450b01540603440301509200e4914609114500f455044828040840c0da040c0d689684070324245102e504084040c0009101d001c1c0b4000f0740c41c074000340d4a08001c20403861101140c1c0303014014005440d904520031901c001416184440c0c44050000d0340c02040d0f010564031550341405552403405040005843c2040301e81c43c00e11000340040c03800181507603c025680b6a80c5e5841603400da1810580001c010080c0c42061681c00d4400004607090381660646d03640d8600c10640080c0c00c8909000d580070300b4040d4090200308001001442e4010340c0f00d5080c42d0101502d80001c204018110b4006500650110307441d081042200e01c3c01804082d40074240303050610510256000090410029040060003155900c090321800d10030249403401e040414828080036645a140c4a005011080000c90100e904 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 683731843 1250 683730593 683730601
    0x9130509151602060f060d050f100b060f0d050c070b0a1b0c080d0504020f03060901020721020a14010b04060f0503010f0501061d041e0b2d1e030a0b0906 67
    0xb52984080d159140c96000f13007810f4a6045030745120520140c15039502414000750070000480031310014031107100c0000038050b10501d04007144103603007035020005c2c070846d81041078440089440f0141d5a10381400e03807000032550760350300040d00144036146001e84914030280402078a11656003103404000c803619070583c140b0031481030a813840440724800030543d07003041c090801807560541c0f182c2e6110b40001c1c2001e40700f5608501190802d042943c44a40a94002a955090228000701c1c51600c8100a01e1020700245991700203464550789c200c0148000c01030428000b10900035004540841801001040303160358403541803003400301c0c500ca124042d5013403002416052025200e414100d50942c3c441444107100c031304a01c400c020700c40d204182d0190b920500800c2d1600c0b0f04e13010105080794240c002611813540000c001580d0307401c01c5a850302d11180da14040204001c1d07580802412400d49100300800031590314540e5041c1c43c03a1005815204862856082c40507012045000f2011101540c0030343d15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 683733093 1250 683731843 683731861
    0x151302030c221a0d081305031c05071106040605090103140402031e07030c0f0311030d09060309020a030b0901090c0e0705041502030910030e070602010218060913050915 74
    0x1c2010944140382c00580140d040314541d4000e509000354a010078185251004001885144030a5054400c000042096001100751810b0003000c0c0c9002c41c010980540780580320480d20600c100c09408014011544104000f00324010080f107080081903140c0311a00c94500070b105400640d1301c240081d050241c401e002c0f110f02078803940610f4005e405031814164503c000c102c41190303500c4800441c0318480300000818807000040c3d01400c5542241c5035000d1a6040160780e20085860507031081c2c01ca00b03c6400d15a400c806680210781c058240415040c015000140300b454882c0d0001c1d2039511280b041140c440010750280580907c100c1580e170400791a8400740c0d02403002140c208001c03c100b0001403014000650180702e42048601c11280b50041400c08108101640d030300200110303840341034404c0301850a024900160040d032008609005003a0001c0b113601a031009042c0c095a000900404184c455003140403094002d0b140030710031424200d06840d83c450a010080d0035250071134000c501402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 683734343 1250 683733093 683733109
    0x40e030d0c17060402070f0c0807060f03022704091410050c040b071704080d02070e01150e0f0303070c0b04051003290103060f03230c0604030f05151302030c 69
    0x41035510b40802580c1c45006200c000d5201080c160354081518103141c00040c100341c2154050002c010140840a04d40f030300c054610002106410140740c01403001c0c02c18135290460b0250003003200c4600c110104200d038040f5004044061016100c41040c100342c022142c4d0001e00c4a10303a510072441040b566590100000440c002d50289148074070040045401042034081400081c008001d503140c50f01d943c4483c03d038548403500c2d20540250300183c004014030004408960700428450312000020a02500c00421039600c061416210b800710705010405910100103841e0182d9205c60800003107611003a0034441d5030403601c10584500f044035401c080451003402580422011072010030000320600a44444c420801540c0e141090f5a03440d00140ca400c00781d000070300640c0501c008005030204a0000c840015565003c0c9095502074071a443d9241c8502d03044800322134015401c84000240392400300d080191f100040c16148415400380003251059852942e0080d1086048801031840101441050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 683735593 1250 683734343 683734367
    0x40b1507031d03190b070315060c020909061b030c0c071e05030d0e1c120f1b050c010c1b0603020c010e2b210501081216030e0102030702040e030d0c 65
    0x3480c400c4c81020002200203214a41000042c18042810038030307180694410b4100e6401800002c903544502d0066040c42c0d480d0a1300814110042c1039580f800d440440c03c84484020002446080040016400301c1c2143c00c2e0355a0b1014042a42e89259458400c16aa10044010301140c01d50f05500000c08c1d250009203210481041e0f190002e1000c4046c0c1004040030382201c002d1000108a00004002070308900700c030700c412085480d0b80a44526030350f0010843c51661310125280b10307150003102c01280c00028001c41c03801c0300346403003500030404e80303800800404a0504a002100c8018021601e0b1b0b40540213410851001d01c003c0140305150200290740d070310384103c28003e105154818444104c41c5041421884840c1d0409054800015940c144d2450185244514141d556001407003035100500a0046c005400002ca9003000c014440711400c021041e4002402c0c00001888030005034001d0098602d865002031042018200210681d6120360107140085e8240e480c110207800d00780d009800c048a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 683736843 1250 683735593 683735623
    0xa0e0705090403030b22150b040509130c14012c27010e0604050105010801030308150109030822090207030914030102121305060c0306010806040b1507031d03 69
    0x5a5190809006003a20060019010940c5940000f05c554a41b00ca0703103092280c20403203c01107110000800003c079456001c03050b940f40b581c0d013802c004001d800e0342941c00fa00d000b1900380450703031907000c810b01c802907100e040240b1200035150300088060f490038800750585420789841400070f141c8150124900344207480e8038040c0c1c0c00d10390910039604000c1d52010720740104070400129100306041c20b203038000003644045a040100b104100150a060042074010f020a003043c03c055419540d001d081c0e664014041292400e1300401809503a201d40000802141c100303290760380c0c03003170500b03001c54180184103507803c0700f07400314480040c883c0305a10844000940542d1040c60b41800d00301c010031006580317102d89601d9074080c802101d882c100c824a9078083c0207218100340102c002d600c1c02600300b203402407460000a4003841002002d9820040d0302e0303480322003103038005074040860000a00001101ea10445070900105e068420103404ca080d5a13942518860851104051a0304241d981d2081c84140300d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 683738093 1250 683736843 683736853
    0x90d05160614091c23010213050105030702070603051f060e030c0316030605090304050a081c03020a0c020402030604091e1a0702120f160b04020906040501150f12020403030f02060a0e 80
    0x103151003035008060748051007400505e001104150107800707004615108108280d40c001005d043e100d50b441c6203c00280003c0c2002411843c22a90103034490000d440380b0414075403180c1c001039041c40c0c01036584401d0308074444000140c40c0c8804000f0200640b4400c228060f20440d41c80d9810741c50001072030050141040c0007109070318215920f0801030100070340b1140c211711040c4030200da60740d42c4140100160902c1002011401404a171240240c0c0ea0f642201c000c0c50300c10010084016404a43d29111580503540965079403200070100d0300800c1c621002a2485a151000301d40c0104200d0701040010300071817001c0e01c040c120b4042d090031440c013620b07082c0160f03201c0d03465406100402000307000c0c0c2d0740700792054900780b403a03002d0200c8403020710ba80200d8508120754200300451610065594202c2c005840411596041100c005e5620301c150b00e4601c00d01034080900c40c41b05201e01c810480b903d1002e5015511103030b90380341c045e19030440c1d040e20701c004d03024000001d410614248a960000d9000c0c800402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 683739343 1250 683738093 683738119
    0xb0a110115050f0f031c080f090c0f010e0406032001030513030e03071205100c180302040b0301023c070804120c0905090f06010b07030903020402090d0516061409 71
    0x31010f825000040c5401211603014040e9940d004d00c10403070348044440c1e01894612410100403e04003006007158203500340103081c45100c5000283c2602d4a46003a0381420b109803c15005070390190f03030700044641c01428520040204440244400d00d03054000f800034140111010042d415140d044071030301d442c1c0315500c160002182c442c3d8020b1a04800150070384545640b0340761820700c00b4060240540b10307a404010303034040010103032007001101e40107440d01100211220304405440c03001e6201c068031450310394140d00d0a41c5d4081d0704a40385e548001e29800321350562a083d80c00140c20203c00c168031103408225038681812a40110b5020650080d9034510707003801e10944012043c0ca901c0c0c02d03503504590400100e100c00091041c64000e00f054801800242c05290713400740b901ca03050b000550100c1701800448002a0810288401ea0754103c074003580b01c400324400f190004020070800740c0340e03104407100311304013201c4d807400340054504070b40c0c2d030340c5001c0b103000c00340010f500c1610368194001c44c1741182e031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 683740593 1250 683739343 683739349
    0x10051302090306220c140a171504051f14010902070c0b030705270f0f060a03050912071505010b090907111015050a05190b21010b0a11011505 62
    0x4110080d0804e1049883d031242900d407240e00c941c05421402c030001381d9240c00111881d0004042d001082204490301c201703244004007903103644140c01080441130506d00800d04125080c0a10384540c42e00e002c140d0310142c080240c01000d808881080081e1984000022031802c100d4000ca80c0625013111412554900d0641a50140d52008011004200c002e000c0300c41c0c0720103002c0340e01894594031021005000045003c00c4500305201046510070a0301c04246079140d00d075201035a2441c0c105090000300356840d0700c0b5090501c0c1d610b0b981c2c0c503003103480000d002080207504400300c4c4031100e80640c20801c607a00d600c110500344c411f2074544c41e4032000560010740760601c2100a452a00b4000c0d0542d0101c1030703c15000c0043d40e400203228894201074240038030250506010007070050404440f501a560801d5071131000c550f05901998425680c0090b0110301c0b50345220703100f1002c056040b4101020340e540c0b0440480c40d0400d905183c0013801024200c040081d050003074480d2580b143c000215018688020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 683741843 1250 683740593 683740621
    0x140909011203110a030e0306060d031409031c020f07080721020612100501031808070b060612011401030e030901090b25050102032d0411060d0510051302090306 70
    0x8408101101400040a00c018455488918880d80340d41c50b41b418420101402d0103801804207000c0c00052a00390082030340b1251a0708294903441d14141d882c0300140100781031504c4409a08a610350f62822031026540c009030b00a0f02c2008134095850468440e4200c1e51182214410a1584111001f50080031030400d29042e41841c4000d282e00e19094414000145410b8121106294440c2c0700d10208043d580601442e02540120110380040380c0c0b0595804a490007034942c060040450b0340e0005019894102c101d4940040c050b01a0005607500c500b801e5103a80383d00e135101d0010f41400301d40201e0450002c00d403414150140c4602c0440d904055103640c00e80c021080d615501900340e04122001140040d04858140c0120300241c0d403803134800c6620551055034075024911007428031864201022841c0c202d90840e52201400244014020000d0300c00d004d0100c0e40c00710781e40307401c080c0711041201084400441708242c0d04031003c0c2d42208025800c034052140c540b03401d6045400018105204452 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 683743093 1250 683741843 683741879
    0x80f0a050409050a09050601050105040e24060d02031014130b0a12030c05010c090b0406030b0d020a0905040c05030303160804050f2508030310030609020111060709030314090901 78
    0x14156080030740c0d80b8041020f07a00103550041406985031034440503c007043c003585026020a0810070b24041c41c00c0480c480000e0010b004180c10032942e00c0c4011000c5c00f00ca620354041c00005d00301910351070000141f43c0250300603078042c000350035110f00009120f412a40c0c2c1e51031680d0001d140c4e0041a90f1800b912000c4c04582c00008c0e44415044004602130600c4d603a4117120300d0103941d82d4100000e107480c001e801c441441c0804024052051070410200000e07000702c0b01a60030918001ca03089001da4085803e003260030000950045001c500455240c00301d0780711030b02c0740313006075101d22102d40d495080c10740724441904d040044000a41d045280240640900c64205109c1c0c0300300d0307405c108110300b81420640e41c1d050061740803401c804010201051740351010080c01182c0091451400c0c08031401c1e036040c00c54880242701d03e0700c1e0841001568010014080c2d00c00016043e03175030600d41401d00512039552400210041070448188800200413501681d071040d501601350744d01f44e4244500d5030142e002d516 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 683744343 1250 683743093 683743097
    0x507230a150e1801090f140103020a03030f0314010b19115a030405091b210a0e0a02152802030301030303180b04110607140607030b0904080f0a 63
    0x5052100f8200e110310018000c1041800028000004059050544a014503688013601c540c03801400540d65807401b15041344c0d131500341000702480c603003030940c083c0500c8804019202c1c4a4000007556092480003080740d000005051030240a0020050750f401114001d80802c66210388041102d90f01e500c4c10b48c044a944c80c01d1101c0090b00fa12801c0c040c0c0070400605034417084245000300480c0d81515141041145898001d141040c2c2844040b4100350300c014542c0c1e5840714140c54106281007040205c2c1c0a0704000f4100150003c041c4044040802c42611040b80d260320708021004d051001027a0905495802030580480d4460745040801d180c10203102076140e00d800010603120b040f50052044180b41451f00995140e6245040190480d100160280b5031402d000064000080400609079403269111700300003409004400420f5190094610050210031090524613000303800081241c0b24102036a400d2110201a00602040142c2503038020580034040c8009403044030b400c0090610b0401c28 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 683745593 1250 683744343 683744359
    0x52a07150c0e1306090f1b080403020a081b01020703090302010221030a050408090a0603050f0f01080c0d0c0f0308090909120301090902040b0a0b09041d1e03070507230a150e 76
    0x9034444800c8686d0040d02501880d40e40900710040c0d203180c0c00420b01c1421604111035140b505880103511186843c4008120260000f519803444241491a0902c0c00408000b1500c540b030a140240c100c075007601081e03000d0300c14081490256400e8444081241400382c203c00c1c116211b20101002408001c3e0044880300400d211090054031151024001010180d0b00821070341801501850104c0002e40f03803a0484401c18010300c4a642c0001c0c81d911140b40a460802d80190070703090106140001e07030440c01c00401101000810700044201030900400c007141c002c2c1c1d054444030700543c2d6a0818510101d040d0b0380c00e200404c41e4540b65404115554005080030a0708034104001810120494100e200741110200341350403135051038400d42205151034000c446090303000c3c209041d0345a80c208401691011303503000c103070030455042c4203850115601c003040f0342480c0d882e0170441081e10000220003205280c686c20300c5205280521807482115800c3c5030307160794044001c100700c07801c100703160f143c50704800f017 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 683746843 1250 683745593 683745599
    0x607020c01051e070503070c050301020a1e0207090e0d080a0606020c01180521010c17180a0501050a0e0d030c0804200d1212050903030703052a07150c0e1306 69
    0x41c40010804c0318450320195599402c0c602e40044e22402c0d0390412070081e841884100501d9410101e6240f049465a000104000c0d000004a1030641c2980003004001d05040c12005840b000060710f00000c81940c86030344541d0b03200c2d07805d60205e840c60700c01c0c2030059010401e2900554010112951400c403002d03004e40d5070a0b128000300c2c50005002c09106020311000c1301d0508a0315080c42002c00040b40c515000c0401203242c2e03460507a0280252989a0403516041640c0b022a010000c58603030035800002071103c4c1c075010b2030690007800e141c4031101650141c6130f142580c0034480e100341855a111034494070081e8444c0e844501c0180019000c500c0e401c0a40a00022140d4540310b07004800341c820415001840d003001c2004100c07074000c2c0c448040b490705050034009013100c0032041c0c80c1c2c0300e480341c03070f00003990b03510101c0020030450740c403080318005900c5c502c003174070310351204401026540c5c0201c0485202802c00f480d990202d56801e280700c000030358003c4581d20645048400c05104c0d081c42900810301c162 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 683748093 1250 683746843 683746897
    0x60403060c051306030b0a090f0b030f0a050c100909111b010605040e0c0108010302190e041218290c070608060f0d02091321050703030e0607020c0105 66
    0x207071031840900480c0b8049416015400d0034100792000e06000d1400340403080514001c210005541d00400300210740721405842c060030719510039204d00300024211382c0803121114503a0385442c04d100c01036070240203482d40d075116030508040420801c1c04542da0021030529040d01400140300c03018080302d600408111051100f002890103036080d109031800080c07268601000c00040340c003481c032a03000320380191504441c20f81c0c10a640b10304498041c0c0d5000300700001e090b407504260106800c0701c04660601c60500c03040c490707180c004882006403a03e807840c00317100c00000c85140c8042e601c1034140d0141241906440420b07a079070020240c035040c040160a000a031242c490400d480c64000c074000a003410100040e5140c9110204102c1405441195194089401045d9002c10040039200e44010000140003005054456a6840380c048030100304071203034a96004190340d206040540010341090100c0032100c0011460714021403aa030010075829145000565075038008510300303c0210601c03816034500c49 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 683749343 1250 683748093 683748101
    0x1704060905032b0c0f02330106090e0c040e0106120e01060b07021507030806060319020f0d0e070f12050705040603060b100c0201121107060903051819031106040306 72
    0x1400104043d4021030103019490032519030a050700c2c00c20501c2c0d9419aa096004918071410178a4041c0a01a14201c1c00c12400c1d2901c00000903102024050000983e940d0300c201c106060354074030080e51036541c0310400703001164011350146c1c1c0b0500080701c0c01000014001c112078803100c1c040d0729002c1140180b80b0480c074211015a84400304440c80054410f0031450f011580b180020b00e506007550800006480c010301d5604002c2500d4002c803c000007041804c0400482100d4616001b43e041d13642d82d00c0817010b20481d801050000d0364041c10501d2800590201089000a580704181e007020000d24100c51501e02c2080300d081910795001e10140030641d9100d9000d0b5402542c0074a2001c0b030440310032000d202c0c01c5001003842500300901c408034500180e0b8000203150800342c004001042d112940c07103000c4594403504900600262416948404040d0081d000e001c96500410540455141e96400d20001940040041e0740203646203d0a0000030184420400e003880090320312030619403030b955164111 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 683750593 1250 683749343 683749387
    0x712051602121c03021c05040302101514091b0901120e1c0810050409060b13091106120a0507020f0304081f230403141b0c01170406090503 61
    0x60300f05450701e10140d641c0c0f001030014011540741c11482c05400b19403010040c15640b441c585500d40360700118003418400c2042c0454200410b60800446842c0d102c00502440584030f8000c0d419070103004030340c01d0302d001000548100031081100c0010902080e4507040c0d5407160403031505020360001c0c0101484103074402d610000421500030a24804c00000c0e1840c0c15a1341d92040c0200302c2c0390001c1151500452119500b01e0700140c40200b660620741c90f002001d845100b5103150000808401e1582d56000c5030450440d0500400364203800c0303036072101400941d20801141541c5a800c1e8008603801e04610350110364000000e20585101e0065001d040d8250707441740d880602168010815864030816001c180b0502c00e03104081004410600c15075903445404032118540c0350a0050001030506004c0c00200300c2040304030055540c1c034107d00707203100040a8503100d800c2075481b40219280d01035004440048a422401e5000c1e002950b0f00d90310000601020001145c8900007800407142c1500100a25168 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 683751843 1250 683750593 683750629
    0xd0603030201060302090a02070f11060d050c1b010509150406060f030302060a05131106220b0c010612021f02010b0d0b040201020d0f050f0a0e10050c0d050712051602 73
    0xfa14a507004004482d00007906103d0a84e104015007000203068201c04203610f9401181015600140000144280140710550510604000030001d10580c01402424096a0585522082d80b50f0303520345401c0702c6044800c004194858850200b059903036180240d4024400c4001186c0d1548410100034880d000740d0003180035074071040c24004a100d40340110b950068016905680b090b40035155162400c00c003002d058000c15000030902003c000445030f031416049000c0400c0c002c181d40340c011000f50b90001117100155440c0650110ba917401c11314074030011903002413100b1f40b150120262415208031140b42c550039503590320100107441e1502c602c460000707401059011414074080c00061304002c42c41480f030040002c100c40c94a02c498020080e520401d40c510704250b1a83c9401d0010380e200704900140a91044518218103c403d500c080105002001071040d9014142c0c60603056515000d20ba8004044c00208039400c003c207403007500a4455040c102a0111060300380d40c0101c2d007003614004260325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 683753093 1250 683751843 683751851
    0xf070f0b0f0a0504080711041b05091e0307030201030b060c1b041d120c010b030703050d0306050a0308220513151508040b0c13090e06160509010806060d0603030201 72
    0x7503a00100085074404007265050200f442d103555011118400c41d0001132200c21205189034594036103502c22411121030460f980c1100000c4000580306130000d2001900c10400c2a00881d60100e4800100c191490003600400e4810704603030041d8090a00a000c1d180c01400900004900b482c081003500708912107030752403e0500103000140b00c144c9100758424540c54504060600f0b40d9080041c0d048400d10241280f59143d040515410307000d4625805465810320034074002000340440841c1c0340240702c3e0903850400c1401c3da80e90910495030010710008e003c0010611070f002ca6450199544541d03914801c4940c1035458540002402c0840422900c00e2000d0b650124a0103040c1400881002341200184980070081400002851441d0081004100020040110704003035042c000352400019000404606180c603070320000003d00c1d1400811845209010100d943c40c060f00180004070f02059503071a03c1c20408400541d0400000b400d41600600c082040e200841914450b40d0055882a80007007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 683754343 1250 683753093 683753101
    0x1091a03040219060503010f060f080f0a020f04030516080c0904060e071206020733110409020c060403021b09041e14030a08010f0f030f1406010f08060a060602060a020f070f0b 77
    0x18031003910b940c05c0202402b1441402d91001500001c54690008140c10000b00c5661000c1d0b00c180a03003d01e031011010103401003804030420030041000c3c2c0348003680d414510009a0307036680781c0e5512000002c0940d080400d5030045808034215800c048480107005084680042e500c601ca2520a00c0c0520140e84059020603040f0400201070000c85040203104000d109041d001e0101c0c0000e01c1003000c4501c0c10f52b07030f40c801c0c284000c401a03007035030020600700f0002c6454080b006000398598004841c12401401044200d40c00e0341d41d000d40910520030003038030101c2c950b51561745038040090781c03075440460b540140ca4040002000c01c0f41c2143c05248040c041c640306e16807503c2c05840c440d41a000106050681c9505020300706010303a1800c00c03207410540e13040644007103041100d51a482c02545048901448001282101c00040302740101c4ad04501121090786c1c82c443c801040b1152802007800681042c030218a03004003540240050300d60304110b0503d004d94907a652130f0001140101112811443c0c0700b00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 683755593 1250 683754343 683754359
    0x28020a0b040f03030f06050603010918020904060902090903070809060a02011b0f1b054303110612070e060c0105180d0c030203040b0d0b040203070206040b0601091a0304021906050301 80
    0x41152030317540405000ca83d09110020301e550205000301c1601c140da0ba150703aa5600e54440d000880b0580242000d045810642030080240170398000980c0140440740100e10a13400c0042225070840c1c01c0f0440c07908224a04d000c0241c0c81d03101040ba2011036480b49464001d000001a444190b000036860303d000044510703401920030001c80202800320041442c5600c0407072004217140a040180c944604907250404203074a281c00b0711154489107400c900800300381d0800803c594002601e01801081106a1204040000a10400c1e039085020000c2e90040f6140d42c0c010358515645000040c082410310146072a4582100c0044800700014030274601804e02c00d61090022692000c0d0b5460000007500203610042e5691113640700307800c0c003c4000101e000e01180b880e842a2404000240259500d0a118600030b6480300140c1c2e00303036000c0c0c0d484000304d0815030058007864103c40029000802e140c2c0c00c08088070075508000e101703907080135050206009080781d008001c80641803580381c45440354188a41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 683756843 1250 683755593 683755601
    0x190501050102010c05031914010618090c0509040906290907020c030d1103040909031e051603121d07080601050402040b1c09120207140628020a0b040f0303 68
    0x819415645001044c105150740f100840b41d0150003080e510001c02255084400200008810707800d604c80c0c804d0022507541d038000f1f141100c1040070303541d0328906521620420f048441700131003000454820410042d072030405400041e6041d0040100040188000701c03038aa42e000403220519510a10141e03213401031903e0342d4401e030003054500c02400e03160008000310303550300005941718040c44104815603008560400848011700f0784004244400d0b80380707240c05410040d010801040400a0042445280c0c1c03240c2d0607617020a08c0031000300910b20131500c1c1900c010f45100318180446498486030414903000745403009040c1181030007405180d10b000c0c01c0c43c3c1054010b030040f512450041108010421500080d1000c86641c4202910344140100a800003414032400c010007260b855119070002d0348c1c022072450201d607a44559103980340c507035008119180c841c480c0d600c0c580c450401c03110764080b4024500c0860301d4400b40112103158000d6200c20040340300c200c50440340090b902051004059040c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 683758093 1250 683756843 683756849
    0x203010f02030f1906260d0f0f0c06090b0f0601020607020c03030316200303010618030c0b160501020423010f02060106080915090303010503070b0c06040f080d05190501 74
    0x100c118210309101028010a00f0040c1010b010040b84250f04910844a507000b40000c01d114840484400a0703052800c3c81c10030502e510700c0e03090103610120010b41d070160300718800100090380c9000000307071003c07020381e01c181c8811400d840c0d1a0b0345504100c0000e4203c05000d0140d40400102440d42c540070700028038200c001000d00c421500103220001040c0c40000c241c0e5000181180e030a2034507007810404583d1a107000c07500c182c111501c4106000250300100c0214165202641c8036251032200200000d442d1350240310060a4012901080005c1015603024144128820310200c61646a0303489031400e980064000313541e407034901000e5003600149124030652101c800e081a002e51410320f00080c4d100c140511415040c0050000003c003450428080c50010034072071080d100301c07030030903102156903070f0000d02503540244160f000214540070000140c40710b0070402402006155078070342e115007038002d031206e0840d48082d040c005c502070001e10307002d590302c80c04142d0a0004071205020030360741550b0046e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 683759343 1250 683758093 683758121
    0x1b040b011403130218072c010c060b04020f0c06060a2c061315050306010603111902100501081b060301050612131b0603050c091f02120d09020301 64
    0x30000004500000082c2c1c0da0000404103e00c8240c1418004102118135030220786240c0f40401c0100442c0603003100165030081000c0c2d0b024107104003030320b603078402d01c180c11030007240403e851110000000c2d22981004905c4080034001505111070017a4801654010196000b01500000c0c1000740c9030621054143c010711603480441080088562400e01c400b40d414054294280080300250035500d45582c3d218042150070810002e062041340301041010041c0940c80c8039025041c000514684a03001c1c05000c07110100c0360f02e2604e03660310300100c15219400d103038209500899a800c0d44408242c41164020300c038410140c50050440540300d0030583c1c0c0010410300c0307030740f050005100c2501d400c8150b5080d4030242c0c032128403d4a42214070b000314004138800800f942d100400c100c01030a0740c02c1a41e0704131010303601c0034003407074032001c0c0130f4665400b0304019240c010103400001c0d0f01c0301000010700d050300100303401030743c0d0035282c18582c45c122680079440c5000519156816841142401d203c0d0200c030942038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 683760593 1250 683759343 683759357
    0x403210b060d0504050a1b0302010305011d0112050a120807020c0102011407050f07020d0f021002030306030a03200f0102090f0a0f060320070b0f011409061905031b040b01 75
    0x40003618502410251102c800c1e591000a41040420401c00c92200d4000c8026040005c2d40000c0b143d007450700340002c0340000e08101c000680c0241110003281c040c0740400008000f6030901c03c03020440342100909032803038480c036006200412000ba1400002d160184c0e20b1008501d4800406440c05010750803150444e071520022401c0a04041c10359500220b0b1440c0090391510b52200b130004c61b005503d00650721102100600080101004507592a90b2003901d603c2418103032221b003680c80f400104c2d415505900070104110000340301e1a6040780100d0008070f1900c440d40f500803901e00d44001c0441c4803100760b5002907481c3c0c02d841d14014483c1d00a2040300e98400c802d06061281c9400011827003503406054803500410240c01d400c4911040c5d8490040003140c4502139420f0012034030000755030b050060b0b402400046641907603d51a80503809000d0411541c0d40c560302c007800450240460804a10000740b6001308070341d68280104038506103442c0b800300a42849004100490f070582e40c019041c4059 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 683761843 1250 683760593 683760611
    0x18071701120210050a0207030512071b030f0f020103115703070f0b040c0f0e0f0403230d0609050105090c09130501121203020a0203121e040321 63
    0x5103ca00720103505042c0313052901c42c56089400d0b8a049a01e42006125004130162005d440c0d41e6000980202070051103002803054030000ca148208425002c05004215060764400200f00c51240740d862207407061400060300440b244c0340000641041001c5d100c48a41116042100583d100d20b40034001810350041240811208031021040c42c88062010344030184c400c142c00c2d4010030700950300704075080340c0d00e0381c1c244645140407650040111004c40d0750200c208004180000e01c03003c89001e40b0061202045152180350812030880030041046041080e18a8003007010710b1038802c012441540074a100e900c446010081406403409600291021450310004100d41e550780c800c2c1d07a0b044164950365540c1c510055000c62180e4910061001082e41400300028044841c0648911010f02034400d2882400b0100b20850591240940040041c2e2047c843c40d43e580f060210180d80140d0781002032045490021401150060202c0d4107074003050300e607079000c0849849041004650b410b1103000300b0220070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 683763093 1250 683761843 683761849
    0x204050609130b04020307030206071a0703091a100305100e0f010b010c0201081b16150903020309120304150309120c05120f0c0106031103012003011202180717011202 73
    0x1c0b0102a00300315410300410f040d03441c248004030140d500901510343e00c0351a4105180c201c1c50840100c0d100f0380d000e80000d20068030a202c0c504019520122407800c131041c0c4105c00710b049030050320007210030810000c00000070f078042040040407540300c440400c941e10303202141d5080c0140820364400503410942004e006aa014112411041c1d090810910989603403000020758045048140c0324088005812030009280704542151148070350640c1010b07034201d200503c16200490700080c05070744140100407991400070075541007120070380100d070304280e9500d00300040a2030802c49540402e544009036824403600515240b9828602d0900003002c4a0380c0c5c1d40c941d55140d00745152411180d01042c0d001c00c08140c1d2003140d010342c484000900049843e810070a00c544282031999200358a813010540d01c0f140d00c40781d000c500c04d00c010f070900e04580c68400c070f0901c402065181260700804050344104080f91600c40c06003c0c500a568001c007100440d03406081c40f88043e0040079501e0804030340c100060f9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 683764343 1250 683763093 683763121
    0x6060403080a360527040807050d0c0b130b01140103020f030a06030308061c0f1406150109170307020f012304180506030a021002010b030307080d0b010903050d0320040806040204050609 81
    0x400f6451709020207542d14107186401b4095100000c0050240e000d9410b000d83e44030002425042c0a004207500c15203440d010305201044852006105d05044001081091490070590003001410304002d440c1c00c9400e0000c0000707a008441080455a85035410300515510800069015500f0b031983c01c021341d103e5038242000645148020700c1d2003818845002080180c00701c1ea400300b0b140c00101c0380707241000020900018a814a018002141d503040000d12180980c038501d2000c4000000d949001c03155001d101450132045401410f100c00d01d881025545040505c41551405070841c0076111802c25810490034400a44e04600072810301c01886925030380400e9440c511541155080d0a003941c00078164050002d1003851a81400041081e00030f101101000b041145482032042020340041d4005494009a60201034a543d0021001840e00c9010b907009444003200143e5130422040c04c503240250551254001400c5900510705100031810700c0c0c0101a0000e0317040f20b07100f5091071304500110b064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 683765593 1250 683764343 683764399
    0x1d010e1513051f060503090114101e0e0112030e010503061c020a0503030d0c170108060612030903030a120c0f0518060403170a08090606060403080a3605 67
    0x1c60303403074020030985014000040010f11918554440290390341501402c560400c07914202c1e15400e04410381d41c075502c00c40480384101d40580348608440c0c1802d030411080c04903409a494140084d090104440c0d24040300107000300440801c429441d80c0302e24005002802d5450480e0606c0403d10030f201480e03441580702c0600b8034118001401d20302a500008000341d0165200c1c0e9014000018421290350003900400e01100040c2c541e1050b1000049041d48568000d11551229800c11404036441c2c1c54a42c140b0b14040b009281180c4c284800f9000080c00d41d0b010780442c0c0b01044400220403403805139400ba0f0507032000301d41070a40d00c880c4c80405c050031502c00c5d600e0460740d521005401244558400b403c0d100519006601c440e4800030000345944c55901c911895408a180307140001c0030f4490008166200b01070280c0b042e03081c0f82ca156120701407604014141c00074412880c080e00c01c0d90341c1d040c405480c443d0b40c034510018520171043c13070401c01324203236004540201c1c0b80b00204e281c03650024002c4c0e040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 683766843 1250 683765593 683765629
    0x207060c1106090d060c030b0a08070510030c11150f090f061b0c1e010e0d05120a11121603020c07030803071403040b010302030d03050f07030b0a1d010e15 68
    0x19480e05000001c3c565521004c008008515003404125002d500d644030740c191030015502d035001d564940041e582d44200c0b52184540c081c940441012440f44207400c8848040468203085241f01441040303a81007054850b039944d02c00d4002c1040060590b5603041032a0030003249030103452100e620a001940781c0e000240070419503405c50300065841c58a21007100c1100c5844402c0c0c44558070b0940d10300c216043d82c44015080f80d8200050428515000708a151145115880d120314000c081c4003544840c0000800301c400c4113541e09182910001000028004482203003015501071070090a183c484102400300b02040510612644614400004514056035044031000d0b0b1299070301201201c50032211401083d10314004024007041181c049101d0341642c2c400c03411f0300d010f559541000c40032281c040f96202050301100303021602a60095000428041014103007600c0c003921003540511164116451821454080d0f004000c1c1c0d660141103140c2100c8041c115991442c00d801c005462140d096601d002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 683768093 1250 683766843 683766847
    0xf06032114040b130e010e070c08070f030c0c08010501080304180f0207030c12020d05070b0406061518050d170d02040305011103010303120b1c05031b0a030207060c1106 74
    0x14109014100d518041800241c0c0c60303944540340d07800780107550026004a02e40349000907012400c0c05030b059005050b225840504865076071040c40c222103800c5954001d035041503007041040d012400344098007880785e019840d10340c0a11800e107414106001c00740e005045e581d141000501241c2c001000300c800f10f03403181c00781d0703c140310411034410001c0901c2094411070510003da01700c02c02d60071a00c4a00001e0180901c4006030b601c00d6410b907154061314086100140c2c003040040001420420001e0300705015842c00510141c4403803480100303800c0e02001074081202110030540420411040320080d00c01515504000e1041ea640c2d000020b040c0d0501100c00c140c0821828601000762781030f98021a009402407005540c40780c1d03042100d50017800700b980042c4410000211700b07c0c5078010030154407030182910301d10440513403012103d41d001074000c6036a80400c0060507c0d8040070301911107400b4a04000d0a500781e91450301a00c1c0c480300764054010300111440150104070442181100800306440c01c517 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 683769343 1250 683768093 683768153
    0xf0f0106020c06400e0106020d03020a0e13240803070210140406030510051e1014040f05030706020a111504030b1026030306040f0608070312030f0603 66
    0x34604050840102201c80d0200c080402c1c2c8139411454607032038407410704081456502d5004035148000b09014200260380300418156225100e43c2c0184400e80c3d003403070030402000030600018114190141c0f1403103426148c90710145841c00818002210310000038040e0b0ba540d25000b000b503243e00a40d04064812221952a104500d000d989402e0035401c07890300701e90340c85031507000140c0180300036940d490030140000804075003410114407030480030319a0341020700485150410420900180c1e540c1a0410004d82c624a0148014001501c0a006c1c0010005006414002854501800e0b80d0101d000c40d800149440040380c1020101807005405540d50440c208814a400d501e40c403c40d8401080c06000804200241030308420b40025034030070600e5107103a8402c02a16142c040711050005075550000c0021911629095124126210103c40041807040c0d9400f481400c11400c1d0340107a030359910201d01c00c5991f50b03040c4100b0011800c41d0300308000c082e0541e00c0d048155010b0044a88810a00f24061 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 683770593 1250 683769343 683769367
    0x60e010209091e1005011b1104090302030711060a080a0e1e030912241503010e21040b040b0903011b0c0b0109020403170d09050a08030f0f0106020c06 66
    0x7511141c60203404140340c0d0400180c152410002007500c00890980300f808030708945a240540341c00c562059607407404401e18024070310058800c0b013100311445d0440b440101c2c000e4565024100c051401398010b552110300700c6c03d05014501603400142d200310b208204820030103070000c00d1107400080c801c800213030700c84822182a243c0014209a100350307641d6424109a1100d000000b071600d0101580d60500800100f00c00690b2088800c10702c910221082d6003c0c4014403483c0c50035944946003807914029942030308082400c5494500083d451500701c1c200c0d503001400031003d0030b0607001038440b01c03525091400003c00614000c0d8003421040280004028040760b50035007241100040400507950b100c2d10040020300601c0f400301003100e14040079070001074462010b2090324101c070f03009a1102c075100640300e91480141e018510501c400c07940e0b4407a480c0456010000d1182c01341c0f00303240c11617032424204003403001c50100401c2d8011000016005124242d804174001910490039191309840e60b01210071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 683771843 1250 683770593 683770597
    0xc0507300807051b0f041b0c170301060c1202070807050927030a030606030207050c040b0d05010203010f06091715060d24110c190c090c081b07050a060e0102 69
    0x5400384c810381900398800c05040e080141003050440f440310032801140180b0058a05810341070491440403600c1c207000c940282494401a1311642e00d8041c0f1840740c1e600e003280c5404c00e03080640041c1001c00d0103010000703d07500308642c1e09a80d00040c6155071070003081d0341d5110442d0150038040c0c04100081403103e1548074451011107004541c00341103a16030340c421035583c7c100c0100280000e0524400003107950085c4201c603034041d002800303072001c41d0380c80007444094607241c448a0b41140c18601d481001c200284007450282c61040350b0210070380d1412030010020301d038580200703155040402c0040710408000401000010740303002d84054070781e01d640004062044006015010380d0540000340c1e12246103010300300f00d00c10401010403c0b04a14000300b02580600760710403102c0d50102c403064100007514000050ba051085d00d8058150303884820500941e03c0c402c80110100d2a84424041c1e000c00382c4130503c240f0014005128248607650725419030740c0c00b150001030002d075941c440d0814209401c0d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 683773093 1250 683771843 683771857
    0xe180403051b010c0c02130c140703110d120615020d030c180603020c070b071a04150e0c0a0801020a050d15030203010c0c14010605180901060906060c05073008 70
    0xc00014138220360251903402030300340c02ca1098881d4030201c0e0302c0340010311809101441a0351104a83c001c0381d04162003d9201c9101038040c800100e07071080304140300b0400010008090359981011440032440351741680c9260b040038007d03000c86080309810590001e840442c500d014a4003107503503003803400b0035a15503526504443c0c002c900c1c0500810310300d8142c0c00410742c00341c2040849040d030356100c0351a00c1d10b001d0a07800415055956840254200d0103a00c5c454110f8045d6010700707048810302c000c040840d03210111910840d01705000350036079490480003100040a100300290f15003080b8200c000c0462003040d07080c4038080e5445020003558020089040c3c0619409402008145004135001d0f050580303044007100c040314202d0300480c1c91340d0180142011948040c2401100701503481ca14070070f48a000b84003000d07941d0703103d200007103281c0d850046100030070507a1602c00c1342001c01c0c01c015041c21036642001c1008490300c1411484105051034281c4200d83c0d40c40305403500c0c0054548030f1024801d0503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 683774343 1250 683773093 683773147
    0x15010f08070c05120a020c03060105062224021b010905012f2a0a0902032212020f030721180b040612050402030c15090402030c0a0e18040305 62
    0xc04c45082072414480185429041078084a010820041c00c250713403003009001c2d840d00030806014400d02182d03110155001c2c0d081c001542018140c4450389019802d20024003544084103000700c0c2c0c81600d405124204440342644c40042c00080c80da00040c000c9031480c13050703604102c0940a410340340020f0b000c001054120800c1c0c0f00401420390716543d070380c50f26a40c00406220b0b00c0441010311602845403042443c1308040d240c080c00c00c1c07500c0780c250002d410041481007a40201182a0094000c14400c4c0b6231507803282050240c0960200d0000346000700c207013811106a4401c00051012500120380520b0309820907581141407502004200c520003078800c9040c0203c0d05001d170100f0b044a40001400581c1c0d503c1c1c1c1e0b402d884158031502c0f44240c0e201507401035090b400c0f0703404104803401c1070411080c00301c512440080c54440c499010400b240d004441c3c218140e00041350b0510f10b07541c460500a40c0764005c44485061401803c140c0000c1c19000d040101800000107250800e44091403150344460018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 683775593 1250 683774343 683774353
    0xa02030f070609061e03020d110d200c0c060912072409060e0907030b1c2924040e030c0105100b0f0c0307020306071715010f08070c05 59
    0x503803510359400c0d15024001c0894443c80340882d006228a55080d0921748082c1c41104080c4500c030143c009601c04051401420346542c61100100f0665009101c0d00d180c15a001410406500040c0702e6001095804481c800c010440c2014840c0000740c2000d035950121001c0da07460400f10001003103081d00003494502ca00030352500080b001d4101a0394405500140b811000310500503008448030101d0340240004101401c1d4110380ba0b0800241496001c0c00134140010003200c80c5000070107030000c1030a1041c0d41415000c40504020013010410180d003100c1c0071081c0c8000003800506542040184000705100941c001141003060780505034120040141081003900f0790f01192984980c40400c89108941c206008602d1444c0501c0c030000844408028250420900d168a29029031060200017118402440030601594013804124001c40703464454064900c10048101c0c03050070028600c10301d00321810741c101d0103070340c0080e9801c042040c1460101d030550707141304050f50009000c41002d0681e20039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683776843 1250 683775593 683775613
    0x2705040b0403021002130e1801110c0f0c09060907030603060f24030b011202010309121e17040305030901090c14120609070b0714030a20030a0e120a0203 67
    0x3208164502a0740030b03a007540c10b42030461220750264410030042808121300190200010f03005182c13000d4019a07030700d020a000d402c0c214141829101054100d2100c0707840080c0c9c1a00c01001084154014100c020184c91045100300c0002c42c1000003c0c403180c083c0b014840003446d170704e100350b000710003545d4403074410022004980c90113002006c010300104010001042010f01074400d0b61f200000302ca500048500c0c1c968281920310034800c611340030480c103044c0c0b00d0728810b0008651a5049281000384d54480707440380e061203107170489580300308007030b5050040c151b01c0c1080d100d1151801541c0941c050500039902d0b01d80382030107401400c55a1018000854515002c1074114143e40d295520010071036055904803a5000c000d61506810356511031385502c0b03514100030010a10010300038090242c0181c8608060800c3d205045a00c5140d41e43c00064040f5401148107a1034126002e5011220b0000d600b461005d103009031041ea00510900d10446240100401a920030000c160807030358041c00740c1d03c00703502d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 683778093 1250 683776843 683776853
    0x803040609092318150a1a060a120207080c0f06150f0f040903051b0303100b0901080619120305040f05041e1802090408030a1d07270504 60
    0xc1e036400740c240d50504084551100300c5900d1a030210b0101e882400e003401c0e03183c2d003400159900c2040138200030750080e01d0102078000001d2002c00d00c2585000070204007084034040f001c1c00300c0f020381602c1d842070405011006a06501288143c0c00000010006079180c0003400c10f0b441a0107560782910740c038480c1d45000c7c3d41d0f59001060190154022043c14000c1d44003040800c8409440c90a4480d049648070080301903518068102c2880d4601038140700b481d2000540c840845000000c0310480309910000c1400841d0301aa86110010f122041100c1e0510206100007005401d01a140a20422000540711021078080c1c01d144014000b40000029507249450007400c140c000d03209000a0101e0070f10001428181401100c003401c1a42e0804400941030b07900d84401881c0000c1c0c1d501100002803604030060300d0380024240110300405409840386000c150903403e80c1c60205081641c0000009c2c42c000341c10002420b138040e40c074270080120280110300040c0e030085681110080d403460801080c001807003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 683779343 1250 683778093 683778107
    0x503090102010b240d110a0804200108070c0213050a0f0e0703030503011707030203030a0c1209030c15141602011211090402091c0501240503120c030408030406 70
    0x844281c0080c03000c000c2d4241044496410480c1400f118003031013802da005643d07540002c3c4109880b804c40019032001d48901c05000313402000305103006c150440144400d22094180030440d142128690000120f00b2034002401804003600320014804030241c00011550b0f03000200315010074011040010b8900a010f280103003d0b680860f14095250030001480c070384001c2814030507030b41c05440c0e4074607607464000b01c12010150018010994081c50704040010307942840240f40500c0d441e92017010031091820182c0d50041850203000c20b215132071804000103078007247c070300d01100e16400307031048400d1103664143ea20214040314500c0c4c04800180303108407140589182d045160013a82c680558821006005088505079250803210510900c980555840d0075001003445a0024040d40030840c90201c011555a8100c10b007210241d443d611800006038041c802c021714605254a034040340741c07905000c00e03200d02001c6841556140002620030401ca0204121001814140e046036661981c4101c020452 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 683780593 1250 683779343 683779357
    0xc0c0d2109062003040803060904080f181f12020d06080a050f07080d090302041104030204050a05190b0105030f040203010b06041502010c14180f040f140901110d0908040e040503 78
    0x203003d00803452448043d0300a80e449950b220b45241c3c47c6840719030400c441c0e2480144101c441040802079000001c1d00200038044c10003c00c0c04d9800703a60011001c00c895460010101d08a070001d4403030a0303801b9640903d107110b0400315a00e00507038400d041ca0601014003500e030890000c503c19040d1203010048005110440c01030081e055030070351911118569104c0017110410000180311050038805850030f42d110003841840c0207103135881c144c3d61381c1c00b180658604495180d030858ad200101b0002c0a441021080341d50000501007060540160020380f95000251020b05102c0034400000c0441d01c0c2503111851031400181170544881c1d407103219680c090307200c501000065080100d6109034500640401642802c01d0b00c00710308003c00d0300702e900207a200c61108544c0c065a406510030f442d132554440d14124031440c000c0407615003001040c014074a0409008022030f17a1505160751410081071041e2800320700225030210b00c0320107a0404490341e00954101d0041ca650440a100411000000500c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 683781843 1250 683780593 683780621
    0x20a0816091a1f02011b0e121609020304020324090c030d090909170f0706112d09040c0e0102011404020a060f03020d0603050708060c0c0d210906 64
    0x200040168602c2c1121451110441d0061658100502e4060a146540b000c1c02010710001410360301d814100380d940050f03142d80402090f2002c03484a20741c00c0209554810342000c0c002003209480316105101004004d104203900d1301c2e80440800c1c11507405200038000000306000c0020710010a0710540200c41040d6a01d02e02032081406610850030301160f03410001c48103803079502e811868204100302078500c0d14012a4026800007001d04403c030880c0c040c00d480c4000710030f42c584bd0b00c450301d0000c0840302c00d000f1021005c070060106280c1d0780b40c00041900000301000c9030a000d465080d00f8443d050144c8600258402d040403800031440f544011110b1143c80240d0081c040c00150f0007640c0c50700142582d002e50002c1440c1420302180c1e00440c2070a121954604e40180f8006410712030300304840d044d07001140c80350030600040098031004c0020581042850448074588048809410b544200c8400041c061048a03461411850080040390f04582c19051003800000350a16020005004c0d1460b540c0c0c2d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 683783093 1250 683781843 683781851
    0x15130509060f0a05010602100f0f050702100c020f060615040308030f0406060b03150f03190b010608070906091208042c07020a02010c062711010306061e0c020a081609 73
    0x4503540d0f00d0160318100c500640141002c0c10a6500d06409805c030240403251b034949459007192034821622400d403082e200b5070b020b0b00c0c1c003aa10080e8481a034110000540031507101c2c0f003081005520214070740c3d0300b082d012503003030146805503480341d54070340110f510141401001004100d001516100e050740304502c90081004025101c03401c007022400700340e410400d032041c8842c40074131174101000070171644107004040b18581c1e182c08046410700000740c1c1c402c5a064201d2001040a1764002d5030311030300030b0442e041001c003840c140400202401514400c06020707000301d0701c80744148200c04003207d0180800450410072403c0c4c40c0e04260401103240c2e0142c2c8aa409040010368540c40400c10681d17465050756203480500154a40d44090410f030240c074458410300004c5072101040c0c1414440400b4821519460500014800503088400b640e201006200c26648074002203080d06030711400310341d03490030200008a0140040364a120250b00031030050700c500315000c0c0e118480d00106004540c0f1501d000c3c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 683784343 1250 683783093 683783101
    0x100b130602120c03090906031006030809190e04080d02040e0106170c040f0308090a2d120210110a05120904060b0f090d1103060708060306071715130509060f 69
    0x120b8503110307003204000c640d00140300120303241c03802c0000c1c5508a18010100da5800303041400da030045407a590700850784210300003903152090500003100141c0703400c00c070340ea11805460004103240070240240000c000b0940000d901c55111503540c196000b0300600100020703950b0710b44002410b5003240300041e041400ca43c00024044550340003c95081c0e032007030490786c401140f0b1603580343c2c0e050304407190007544031003168004a1008500c0c82d0a841e80298500d56558040316090351140e041e82c0394000307042002400c0070301c20140c0c9408580082072886460034882440003091031600381803182800412601490b0708207168100c1003005062100e0301290200020b80d994651a4141e10443c668a0441e84040c850542545084071360000700a00030103002d034501600da40040c2c00d1034011902040030844041c00d0240900b404c220556010100e401c5c1404030140d01403420200343c0c001050910030190750b2140001c503851745103524400c01c0c0401000e01c40c3d07003441440c550315881d040740c0802c00c03076403940c0c001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 683785593 1250 683784343 683784373
    0x10c0507120b072019050f0102070809120105090d0507030c050d030e070915030305070213020f040e0a18110a0504110a2c0d060e0607080711010606090b03100b130602 73
    0x100e244c1c241448010002c0b40118245c28460321103002e001c4e22076000d00c1c0318040d0700e80303020b0000340803051041101c04d40c0c516224040081001d0500600d044680c0341004010f030740140018860303148441814083d4031084940b908075808045000014203038000c040e120b0000640680048040c400b080c415a0b028981b52014001240e2a0640118070780014440c100003007409900142a41c500141007103102c030540d1200c510a80c1e125040e041c0f4050f00c0050300704981440d07843d0994200d0121607092042c41c0c00301542d510f0040682030046d160440702d90150703076103076125400c003002044007a20921079440d403410b1401c0c0f036800c6440ba0340003103256455450103035600305594480b8100001c84058200c80c0e14001d104114092500480f000781e640d82c00302d4142c0c5010060a48a4030440ea1505c12130b14011301d0092240d54200000300580e810504140308441c2c00c10305c0141038840c010321760b079200d590302000310740f441c00707907610290f0301400000308032001c90380145001051f540c0f00e400301c030400c8020681c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 683786843 1250 683785593 683785637
    0x7080712110f0f031c0e0a03020c0316050f1011010f050103060b0904020117090309120d090605091014120916081501120c08010e100501051509010c0507120b07 70
    0x14140e4250010065449040c0c0c4000c010b891501d8205d0f000143e41c445031803641e14010490006801503070054580042d5460f0420843d1038840c01c00641c03180311450b00c00440c0c2201240c012040c4218040b80c40a4400c2e8844c200d85034201001c1c200034411884852102d000a080038001031351307040d00340401e41c5964100030640c0d90040ba81a540c007401203c14500300072240742d01600007d098003042220429a80d00c5c034408a9646000c00d0240450410014024120762016405502400b070180400100c2d560b0b109500b44082c2208d0801d07132049044c060100d825407003600711380c826815081d03043c0040142d00260101281c81c003000079640c2070781c95034891a944e120641c01e04a0140102c0d006215000b1640b8590819a01c034490100896403140282c0d801e696042d42c44036802d9028080c086050f086d139000b0580104021780e000120307000d10b204018124412000342505201080d015030040000c10409000102a030b0286004003242c0c0f8640b581201c002a41c143c400140388131220300103000d64001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 683788093 1250 683786843 683786863
    0x101128060e030906090d060e1204080c0a030507050d020a1e0602060f04080304020f0d02090703054309030b0705030402091f0e06040905060c0d0c1b030507080712110f 73
    0x42e81c20014a40101310401b05c0406040710302d140c907401c8058030346408122070f04000c1c0c0740ca030f13800f0340781c40c141042d0900d0300c0c0b40049004e100341035804081000c550007103160015038a06a411688459850012405107401640a0300814005800c0210049007582500090700c0095017905d0050316507601c030300c0a2120035940235000300c4040003c41c0c014901911380c1c520580c80a80013104141140e000281008006c03100040442d0b2100d0400c002030060058001c102001c194030041a504803164802203014190001072118040c0144200c8440c007880c0c5200c021a030090300c8120130302e0485c00043c220340042c2d80c12030189c0780d40760110b4140710406806142d140782004010005030315089100300c14407005000c0035000366842c8205c1c40480e0060101500c600e048400d8159211461044102280c8040e1001410818007102c0e200c843c8800340c4500c0720031600361806e01d46030045810a0101c920411000170404119485000911500000040c10894000007a100c107401d010118070303100c0e907083c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 683789343 1250 683788093 683788099
    0x18150f2019050a1b020a050301091b2c090a14030a02010506040608030711041d0c130e1f060504092306070f0c1e1b0b0405101128060e0309 61
    0x40100f4195004d01803036448400d0004200c1103010741d0300d0012070f003101c0d001c0300180d44034000960445100714031417208000400e01e10742141034400c01c41100c91649100003c2501404000d4004195842020000040d0107900303c100014019600b45000395a80c0c000010b0002650821000038181e20300b500c505400c8031442000b440c03a00d8041d945032001582c0c498500c6a1056030b403000b103964162002508914500080000c00b42401180100011030040c41c5909007018100180341c0310781c00011449d00e0b00c00c490140f960480b06408114040580074a420054000346400100390600144061000c20051050f241000500c035100d00151a810202c81403004103091080101d001446502c20301d9450703000e820500c100818100e15003002210141c010b44544244500d00180c1d610003450540c000c22010b014540786c07600c0c0001040761161007010100901a1030030300180890f2051101d45a00c458169071041401001c180520b85411007000948031070703181030381e45040764800000300da505074002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 683790593 1250 683789343 683789357
    0x90f110703030507020a06020408100e010c0203220503010c2f1b0406030c06210b01092105010c020706021902090c030c070c0305060a18150f2019050a 66
    0x141e20300b900906005086007007184190305805000c03030254405003010301410009020748400448401c401c2c5e0340103100e55176259242114a0f07560795000000c803040b0154120b140301d070100d0000304200b41c0c0500769001a805509111507243c50581c001e078940c06e0681c01d1600c0382a00c244090b5003026204400b4000c0b10a54400f1407042000c0440042141c6018002080802d10070b03103a03a614981d88220f5804800810352158030588907140c4402c1c2079102e5211940c04001100d20500002c16084961203a01011030911180010964003024018103985d0810003d001c1c1c2c040b0103100030350358811441204018040d0213113214480180f00c0000c3c08294006243c030b41c43e521001c0d0740031400d900250030205451001c001900004210078860700045000d00050401c602d04188040103036500291064040b603c503024480005400d4a00110300c144000070002d210314650030004010102d0007824040b103251103082c5c2011a00d0000200185900700048035411505400241c80c0f500480701200042081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 683791843 1250 683790593 683790607
    0xd200d14070f0c080904090206070501020c011419051b2d07080306092703070b0a061d15120604060e0d0206070e030a08030103030e090106080c1b070b03010e01090f11 73
    0x4000074204c1a517009000042d80c81d100e50001c1ea46074050001220565000f003080550b1403803c2c8524152402c02d8101c109491500c0031400d000001d680d41c1000b41d85980e240894880c0a40c088665204110340c0380083d5141c031910410741805040042042d4031300017004902c2001941c0c0001c3e9841c0c0f03584402a20708684401c010030001c2ca0b0001c241e0046246414030440360f40e0a01c01035042c10995160155680300c1e00ca0400c00e00c0018001c00d0300e59034500f4141c6c200b00812081c2000c13000d2000444083c041515196601c960070b400c41c4810561101140030a4050b02e0070108038280114030912040020b07901841c012503c607207461601078090381295002418403805100c8070903000c40010709072842a541655112556002a00141c0021708150440946d604125a080e0f007d003000d41804600c0d842c050540070b40b075110b490301406da03e070f00d1744245c100c0a40c0304010754000f270000c0a00613602c039a1150021000c04400344107140741c2c5401d0a0b840c5121600c00c2c81920303a001c5e091001d0900e07004c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 683793093 1250 683791843 683791853
    0x809100203040602120c03060f3f0601230a050607030e0a081c030b0306040b13061103011203030f0506090a11070b011502190206090409240c090801060b0d200d14070f0c 74
    0x21540c0c180d020b10301004085540340d5541070003140d001c1d126585d145841e000c048031001500c2409032030b08600a4480323b07014842c80e500e00099401213070b414584034450104072004140c0c85605070b440080b5070b11a040031441020600440380304200043d50b0108130a0f01f032601016a522000e4501400c842030313043c00700352141e0300c51001c40b00702802140b000c11004804018003481d1780c000d030b000c1c030100d41c0100461810168103005610341000b52600a2002c0d040940010b4600d1001038540508103607a5805080c020500e5030683d50300c20b42012109071b0315a520000241d072002e4502d1400d0041c06482c004e2400101ca00788511005900646203600741605031040c400103140000d400c0d01c1c0d054044c0b1485841141958820440e003044001c081230040f59a50302400508242d040b600e07169041074410302210804100755030000304000d00203e0071101c22110182c510300100c18504814400080a0054100541100e00c08420184640f030103071f910010125119803c0c844004001075003c540352000c40c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 683794343 1250 683793093 683793169
    0x30c06050f07050a0507260c190b071101140a0206061009050301180302010f02040509220f200a0b030609040c0b0a1805010809100203040602120c03060f 67
    0x120001d100c040c50310b14a0b44a036490101840c3e0103c1d415030248a091000c12001072000d810142d812555101c40000e94400c1d50f160343c0f19280450155030600042e001d032000720341d80c0100410b01302c1d14a9030b84003490708003050894111500d03980803404004880701413032150812079440c2c3c06181d01922003a10749c0700070090218409003514081000c1c105000c20b681da828860307000303070540c0060390003448c25417880d010f400c1d0307164031076841d144d94410302040203070f070b20750385481c690040c440d4064044602d00303620220854840604040c000d400000c50480800c0310b4402d82c1d4281c0420a21107002030314050080051943d058000e42c011614140081581c9013031130040150041e2040314000700c2151912840c44058210824000c005413241c141c62000840c80302c0c10344098030003842c000c4032a19000d9141c5544042c4160b0400070350b640080024140682541680c0250700c0c40f15204c8603d00741896484455001610707464418103c401c1030010320f14060b0416090f102206a8181901d4005c07a080f09000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 683795593 1250 683794343 683794357
    0x6141905130e04020f0604050a03081605060c0c071e03060e0a150903030e1b010f0509100c05010f060e060609040207300203040f03060f09050d09060f0801030c0605 72
    0x4400c007070094014480480d500c4078081c00032074072854094035041c0104001c2035903005c1c0c01409120300304401d100710b4603103103202d80603241c00103ca10740d14141407030440c0e161340c1d0303034500070b00940030f10010b100300000b84400404603540003804998001c2d8a402c40000c0f014258050100c030b0a420100802c00500aa042655140c0194098485802481d1a82c8004400e5261207155140e910748031503040541503c2200e500041210003003070b5007c50301c24684140d140241d842810700035403150b950b0307559101d1011982c0700750000c0e00804c80002200c01c090401c00c8062002c403119400e02d040c1c0d2545040521941f01280e464400d03415150300c814007803140741c0d0311501c501341e08640c0800017200403912031405140c0c541051011401515244011805800c4231501e00ca011500100010000712506141d070a05482c0c02c02c600080211a21000d80b0003055103540c0201a0300800c01401100350700596100b0440f8001d03150b83d03c0d0001c82e45412118038400340401000a03907201c80502807a4800c0c00038004d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 683796843 1250 683795593 683795597
    0xf0503150c0d110d090b011d090604030315030c0803120a0b0a1802121e13121812050d0807050a0c060e0a0f05010501150c03050901032a03060906061419 67
    0x144c031100032503075000e99010701d00907a07011030260010088841d2612030f4030a03046030329941c0c10003070800034513581d05c502d0080c2c03001d4105600c0d50020905d0410f0f007032200b0001c503408080940c0c5960b8401c0a1501c1e40c1217401c640c079003070003401c00041d003c880c680104c200c6080000c146091b902d05082019454805500b05450f1f100da0a202c2c030b041c99100c10b21054050642559041c03400d4020b07613034601000c400100200c03070b82c080030031215001400c2c442107c4100364840c02c0c1820008c00c9007007a62910740541d0f0050442c10011b00710903080c800c000c0740b0b9a8110841c0d50f0340e690159900181650b0500c034207041c1c1da0014124212050205060794008140e030074000e030550300c480076507448181010080310016900359544000401081e04186230400c0400064101500d20180a803005042c501400e42c0740b505050f142c0700241c0003010500c00040450b100d03d4440d07200d5440a100c0280100054050345114614114010920034062107045107034598608030b59180494940c1c03035151240d000900001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 683798093 1250 683796843 683796847
    0x4030f02090901021b1f060e0103080315060f03090105010e06030d14120c0a020d03050408030112030e03010c0302090f190b18130b030118050d03020c160f0503150c0d11 74
    0x14030f41003120300043c92000008010040384100c43d8044014009051b0320054580102041122500c0110742e0469801c044001d8a0750b031605e50380551048070821003907102900180c101c2988500d2030155001d11041c200070801caa03200d401032244204155122039140d03100060b200c91031403241d000e4104400d1086030541c181152a110b4507003050040d21280d122042c040744444a141c1d04200011418009280c107200605141e11003200510040c0a08984039151100e410b0605009001442d2013178409002003111a840c1e40004000b50401c0710390500c03943d0808060140d038134003618501d001c2007030030355100c4c0314a1600d940c02c0750310750205141e5129014120032a030950b540c0c60f40410494071a1420105d140030071f0004242c02c43c1c0705030314402e0014245180d0300c000328000047c1d240b5200c0701c501300140d440351003501c603a01c1c081a06c401c10501591445005c20349004ca00184c0c011100103a040700c205840120350041c0f1a203048030f040340780400520101e40f01180c29000540450001e1202c64 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 683799343 1250 683798093 683798107
    0x503130c15050301081002040b0f0a0509031002090406080606030c0616120306060e0402161b0515071703070f0e010e09090d0807030b010206130602120405010501061404030f0209090102 81
    0x7a00142802601021550100041240b036006011880b00300c0c414007003c61074581441e0140a442c01380d18041c20b01114040350014055004904440003007500500715072500f5204400070010f035002880c0c40e8026410802c00080c0c46200050036806010001c0260641190a00c24080c0d903800004003100c420201c3c04900b004281008500c0c212000c8541e004240e00c1d0800101418800b02d01042c1030045204215100390480c90b0401112000d50100c40110307150308908104c0c213072076019045603500020602140c885001980001e004151044049a62046190b20354440c98041187d10202042c40200d041c126070744180c61421580d04141005001150f2003000302e01528001c0319000e01d80c0d4071040141b80419008814607a2000c10b501e070a02441c414400000c4d201c02c0040c1c05248183d2400c04a641001250f40543c4e00c18541c05210f0102494239040c0580645000e114007400302e9041c114102c3c01810001c1104c064070b4004c84c0115000345c0b03a41c280300c3d5242005000c4080d556083c0014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 683800593 1250 683799343 683799359
    0x1120f02090c0306090114010c03030c0e03010e0705041803120c0203120f150604050a09050a0f0c021f090206121905150f06040609060809490503130c 66
    0x46805144010442d649901c0c00340e050080380003041e00a084046900c03034408441c0d81c2d0181c0440540c3d03074585004990645c040c074060300c041c00201d102641c1542400002c40b02740c2c10000300d0b030f0103e40c8103c41c2440700380c0031000700030a40c8081c1980035000a00010703040d00c0581482e00b00b018034070a0762044902c2d00e141c07c0c003030307412000e426960303c1c0d610798902051201d030b01e11850312200071160488905207018a040002482000c01703100b240c145942741c40014074030b04440c0d4800660444401c0e014010090007030309c02901e480e803000d010150701200803400e50440080d442041652a406403221340f030103159072200b4680d214002c28111350b002075440c06d200a0354450003018007625806808070310350348c2160100060021a02c00711401120140010001650700640d500200c81640c2400300083c0c5481c24090301700b201c0c1c503050b0106c3da04503410b042110280440001c9440c044000c4c40d40503250301c2d00c0c03081c0c0c20304610101c2900240f41070010981fa00010315024040380c1c840c404104601c0c4d80d903002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 683801843 1250 683800593 683800609
    0x60f0c05120304141c120c020a080c0a0c09061809050313080f0c0d0b0103020409020607050d05030a0509010c0807051b07030b0702190302120901210f200301120f02 72
    0xc1241d6800c08400260f40c41a0104020705c010301c140300020300c00d41303111400103240c3d800010f07a03100c800e45ca505240300d19500900030710700303c45e4010400c02c0e601c0d40b4080e48103507145c070b00c4001140c206041540c0006c0d9a02944564400d440e0285008a251204400010050010018282d48d140010400032050804003003e40c0014070079a00909207146003d0b000e2030a00c4a05103405005a44021007200014400c0070710344e056940c125030015503400e0030b00125800303000d1058000c255110350350100d02215001000386204400010b0b0074003c59035000360460a85200105410100300340c140450344030307409400034040c07180d00740c0c260080b00041c05000500c0c005250744107980241102c0107003c1e0065040c0032140744c050b9951203a294000384e66400135919a1130076040040302d40f010400721104d038440c0841610702e0410350060031203004000c04c82402442003400341c00c10a403038502c1c1b95506a4503c3c099042003500c2e003104504680c0b07401507005642522610881e8500d00d40300301440141e0f118070b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 683803093 1250 683801843 683801851
    0x9110303130602210d020a0201021c1b052106040f02040f0e070905030714030a0206030906190507140c010b060406080103061103040c0501052a031c0501060f0c051203 73
    0x15418900c03030301e40000a0f042c07468444d510003841800eaa000400c905001c0304681c4891113040006036a10100f02c0224020700038002c0345c034031081407241350418142054000c0030031180040450001041e00120545152082e0461420300c21036103030500c2c112840c01030240740e00c884050b0001c0307050600d5408130400c0b84d12580020380c841a91040a002c0401c42c81c212503440b100078104074034520308040c0080da0700c00c91031082c550600a408160206a10305000a030030a035406448a910713410560101070702d4040c1200e40400c0e10302041200342840c172040c01400d004039016140c0d1100006418004000b550040c1d4501580e5900d03203c510801e51180b0b002040244825500d61419505619010060f60940c6100c219111001c0c420b220115294017291411502c00b4200706503258828102103224400c02c03000312030f002c0c0000703a111403401c00100090000c00b003195082a410210300b068182112402c1c000c00c8000342444848100141c0203500346041c2c00c0c0a101181ca8661001b1000565544121 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 683804343 1250 683803093 683803117
    0x60a02040305100e1509012d0b010e1c0314030115110c030303060103230129120106080403023901052b021204050a1101110a030309110303 61
    0x54100248842402003410700c101c081000c4c014000304c0e5449655413101512104101c8440300c000c201c100d4000d50150841c840040340252642100151450380d0f00500a03102c0704050038180c41000c40d43c030940320300800000040198a10484581c1c1c1e9440610090f44102d0521803884030702d41c01a102500594028917800140a08141412900030841c4d0580342c23040030154002010f1030760355500803050f00d5200fa820700c0c0018050801d2108021400343d4940d41a01c1084003500108104080841c800203189801d900c00c01101c4407002440c6c03181c400c52040d070010b455000c0050240510402540350418000e1040b205c0c4081d15510750500c040d410b040540340805900c08043c0b6002c0742c50f450382c107c94000d0802c00d0802911040000c1e090720700010b030507010b0140180c10b03903141c01168143e03218401000f0000c4d18520706840c08690f00c011041099891000c8400859815840782c00c1d110030903e80c6401403c2d21412654058000d06001c407011501002101200d288580b030030005007004039682 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 683805593 1250 683804343 683804347
    0x509070503150c180d06021209071403060105040513150903080a05041a04260918010302030a0807030306051810140a0311150a170906010e1314060a02 66
    0x10a007010b01d8481892840308404802108000c0340c882c0c101c0944154080201490701c0c0c1143c400b00049510107506001002c903880418544075150141c0b004610079090034045810a5481e990743e00c2200340311114a41d40340d4000001132005042c2908141d030040c440e021102190000d0b61b840c0d1203410307001010049800c1d910f00940051640c41364005401c51007944080110703013090b0b111b50300010002800f052200c04c1090128040065007050360704010030300c004140e6424824040c0040300e90000c480b41c0e10842940511a07048000000307a24120b0fa4020000c00c0c40000d0f0303a88910250700b0160094051668034800020291646c82d841c2d06005404550f000f514506041e040c031403c0200c0c0c2208504282ca4009112584c031045110b000b52a003201c0161941a0442c00081003806c4410099030702c05008160144079541004080c50b017643c4810b02c4581c00d9540c0c00076142c2d104001d10865481910391008254002806403c20003868054034070f030800002d84510162401d01c00b500c0d8828202d40c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 683806843 1250 683805593 683805599
    0x1030b1c0f0506011a030f13080d1d010c05071209030b0a061716140402041a0304121d011119050c040f060b0306040c2703120c1a100801050907 63
    0x80c40f125015001d089060000903840102036a80c6000003803210010300c0c2503801003103200e040c001710115401e501c030207050780e01c812988864004c0d00c00e008181408500302c0602c80d050103410300030002540c2d0300340c1d01d850400c0055242c410030600048280c1c402d11400740c2010010a00c003020f10b510508030180c020400c2854040d40301e042c0c0c043c042d0781c0540c4d41c001a0300d001078200c05250b0720041f05c2d0841884250340702e10100140003480f4a91260707811f915000c02250307a142040b0301540c8100d01611440140c400c29107010303904500074099282c403004045541000300c1d0b00400b41706055003113050441c0d815145081c9111890301503110103580503409034441c401c01e8038041c05040740036004510207021441c0303080d107030548902001c1e120510483d12100303a681118030800703189030300c0d0141030210f020b0070482e001c1c40e4407803080501050326902000c034010b40545019411800b000d0394482d20b040045002e400c0f08000c0c400e00940400c0c41c505060780f0004e401f6600740103c030300031559034001d8560245 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 683808093 1250 683806843 683806853
    0x80708010c080f06090a051f03050705011e0807050706090b040515130510090503090307030b04020a0611061311061b060703050408031f15050a1d0f01030b1c0f 70
    0xb000030300362100c2c40ca20700100030b9241c4480103001d410003a42c00000c210b9858400c41c05101d015800102c04071100c00c440c00005001c0001a48001c5600a890360616010b003c034580708526002d00324580480d07141070204071807900c510018600540503c00c00200b10785665282ca0740e41c03c06840c191899446050302c2005a004a441c80760801124030340b64103100031650314161103405900d0604075060b0380b0032191040c4a018001c8031a600d6008003a07944071612487c00c1c1c08121001d03101640110402c00c00803030b941c4d00842d154003140903140010310705030340d40440da100da0a4003c01d040341d0b90701e445141600c854079120b001d00009a44900e02900c44000e01305500d16142004041c00700301401c04090002260021088940001501640c1840c091920540045440040d4089522429241c040020690340036029202d210744a2380e403461440f40c00c00c141c640d14407200d4912907101a090109103078541c0298030503190f20401500003180012075143d04080c02d00300c05000d860541c074a00e00707541004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 683809343 1250 683808093 683808107
    0x1207030806031612060218030607081b040608010b07020d1b17070501080106140f04030b041a070e010320040305010207051c0e090618090319090e1f080708010c 70
    0x8082900010f0030701c0c68074450241514203004050102940096031400400d100301c02c12951700c1029080311001d0400360401400c0309800c0380d090203040035202d521a00d00d148a42190100c41382550f034034031141d09007400040300d40e02001e4102c1c1c0c40007040d8030610004880382c48000c122010102c5002c40383d46440e84403c03a0b0100b8514010268100c03010074009681c01030004e505540a514180b03410749002e8071080214451420403070740b000d8011030000100f00d031680560b84200d1042c4802003985111180b50308801500703544a50203e60041051011548264403c441c9608094401144841c240341c01d00711650180e04203030381e641d400282840c1440400c00c10850444c148440001c000e9250b6a801011080c115008038400c04011010134202c4e0ba23000c081c60703001e0314100b07810100d500b40482e0080c4d40c1d510088801580700780f11080802414046c404200465014040d6a14a42e5510301e00c5980d46010701401d2001101c50b0f40049100b000400884c0301928810700002960100040c0240c071072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 683810593 1250 683809343 683809363
    0x6030c030f0d0f2d032d1104050a0e010f080d0503010614040308031f0603020418051b1314060301050d0b0415230c0906160203120703080603 62
    0x1aa014981e401e0861030009520041d12106142004040b19008000c8036880c00c0b04000c661440910401006501020b1084481c1c100454404000c1c2e0403005103007180c0d901e0310b2244505000b49180710042c2c0e04015400c0552040f2900b0046032810b41c40b580002c11801c0181c0050302e0305403118005014240700c60b003000340a07203c601c0042c0159654014010080d2205004650410404072250310400300c9040940d0061a4440070342078503860b04028031542245415511003495082100c0051030b54001d108582c1a540c100c004440145000c61450000e03040c0601005400e800000f00e8070054941a40501000b207401200000c4c0c81d8900a441c086480981c81001e01c601d20400041003035654000c4505041d0b81c1c020b031500603541c0c41d070900e00b80d0000d80ca2076400e585070070010018070585181c40403540080e0107280110031070b05c03022400503031030041d52040b5400c0340d01003200d103000b04004900440d55034801000c4842c50f01d41c0f04010710304c0d40c11840080f000719010f0418410107150a020460705 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 683811843 1250 683810593 683810599
    0xe191b0e090c030103050a240c030b1503010605090d021201060b030a0e010605060405040c021c0908120304020f0904111305060f01020a1221020a08100b03010e010608130609060506030c 81
    0x2154115101c81fa12041c45040090001e12030440007490030014134034030381c20014000c1040058546144c0050082d1010031400c1c0c2c03140c200d50014100d07490840b0182c1341642c009a880300d060158103030500c1940441d046040e680b00c85048896011110309000d2a4042c140c110380464490501d0084a0141c0e030550003004440c4e4100207091106480700402c1e07608880040340c000c9202204140309900300301030594810740c8041d1840800c0901508100200b0483c2c11181c1203400d40e0b03040c03581c510007600080c0e0340290301c00e800b09901300311450080e0700c180c3c04c640074a40c1e1035100d4006000003540740031005007440c4100d454004000b07507031800d0b8080d05860035007030010304040c18940d5907001d44503c0940e410002c1c4407541d0005e0312941c80012115211502e8200c003159500b51700310000c0c0551101311090344014404c2c42001c00d2498200d000e503812944c1504031f5481c1a42841002c0d40d42c840010010070820700c00703022070000310340c1c03030700035070154034010000010503041aa05140c2440c214543c0580 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 683812949 1106 683811843 683811847
    0xc01060b0405010207080304180b010210090c0314010b010c08130b03010f0807150c0b07213c09020d050f0f06010f0e191b0e090c 57
    0x142c0d00d00340c088030306559807402c07025520311440c090914200c2c0004500703411b200f00358000301d0612030140151210510303905401801c444006200b80c900081d6034900304107210b4111040401c0b0950400288804480c003800038182260300305004003a410001a4482100c0d20554644050032101814a5a81d40d43c0c5461864a030240c4c007880c1d200d8002c0440000d94804003103401800c5030750f2500c40d40c0c4d078450143c844a501600081c0940140600c5042500316910740c0110407001c0c00080b0340004804054001205055100d404c94075004405898822810384620700803d1805c800b0110103c1e50100f5403000c83c1c0580100c201c010024800c282d01d00240c03d4000c500d0f514062410011108a80c1c1da44005104c910f40b64410712415000480118034003800400030b105481c204900045800c81c160810f0300c805820300b03000140016408041c00c02246441400716030004452003c2c58 = true := by decide +kernel

theorem cover : BRFrame.Cov 683633093 683812949 := by
  have h0 := BRFrame.cov_init 683633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 683633093 ≤ n) (h2 : n < 683812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
