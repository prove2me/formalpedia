-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2467
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:48:05.808803+00:00
-- url     : https://prove2.me/submissions/4bbba48c-2ec3-404e-9be2-fc488ad5f13a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 443525179 ≤ n < 443705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 443526429 1250 443525179 443525183
    0xf28090902181c0605010b070c08060c0d0507090b070b15010c0215090303040b07060f14074113060203040303120906021b01231b0f13080304031202060112 68
    0x2003031004424404806011090481360071000920641d41d6a907a031076400c4d4801c070b00640f0080c001810108015201250b81401481100c02480c140340710300441d035004020203440320003407090004000900764008805024041d0140c9410541c0d864480c10801283e5007001d1528104580415000b00581c1c6080c03151040003403550803a5140c850030400320323180d407090341c0080482c198045240b9042021030740200c40e81c000107000900090100e202840b025500583d2800007241e41000c0650043d16892942e00d202e00b003845a542140300f00b8403074548041512940411600070000c0d4030110034034211951b2005220a20003185010700d9501c1c000e160f10b41c1e0052520314030b6110340100d800d12841d50142da10700e55800030046c110451030b50b0400c2c020510898050103075041404000a901c10030b00169128415001170050103000c450752240c40da610041c640c40c4220800d0018800e1009444180307005400504e0080d6925411418401c09034030440c810b140455101400601255068440350300a0316 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 443527679 1250 443526429 443526439
    0x40b040e120d021e0a0905091308130e0705040504140103051e031903050105040b19060c0203032505070b180114070f150f0b0f060f2809090218 63
    0x7003035002c60407021303100d207408141105125540f92400d100302d15000b001c2801154940f4480e0a584900f80421806c0443e4610000740703080b083d420104480328001c100c0b00d443d641065608645800da41401c030b001c05c0c1d13000c4000030310200e8140a607042174411942c604590820350b00156156580d2542c0e181c2a551007034010740e001d0305504585510070002c4e00c040c02400d000c80c00d4400c00c03140d0001c00801007446010321681c01d005000c1d0b65420900c003101018001c0c030000901e16400d20009656980c010b51080380c162000304402e8003071062800725040c40907401d04481c80a1051070070700520740340807900442004481088080c02c440c2c61001000700c0d650080c2001a5a10720603d1401c03050300a00758040c1c00c1d103400440450410901d82d13824001d400507520208040c00d4013a120a00b120b04507403115400103460325141405103007241c05000d0100c910468503142c0004901c0e9000c401a10003d180f5422460219149038590450040341c0a0298080d0841c100700448064460805514403c03034025 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 443528929 1250 443527679 443527687
    0x60e010e061915081510020a0809030c0901030605040212120a140705030309010c02060702070807140a0b07080405100e0d12031b0509031005010602070303180e040b06040b040e12 78
    0x188003511010018030b192040004042983c520250074000e0440364002c8000c10700384220b28a141403000ca03072a00a541c3d004000d5804c0f155a50001384d849030200b240c1c107110b0310300c0c0030380c140c0e880203002d9001c0c1d1710400d80031465081c42d10500142c003c5100c2c034410359801030008090300e140b01c00c0980794044c0d201c3c0307401d441503017141d02075299074424000050709601002080000031034054000c04001e4120b58211003480d03070740060882c0c0301d8205000d003001d21303008880304100b03000700c2080381403200c1d10050046038a144d464540c114030781c0c8031080c01c07a03440300049030030440b900e803000440d50380e0005402c0c1078481503c0200000d0f101d0300003001c018001c10146814480503882a88030f03401011048411540c020300d0504e010700650805804103219200300e0621403a020803602502d030480d0541d4004001590440c1d806403501c044112690a09074020301c40000c0340c8048000180c00385000d01325141c030340e0134001305210540740340e40341050189040854022001c200040e54014102c440380c401622 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 443530179 1250 443528929 443528959
    0x6080f04020d0b0f15010905130209060d230124110a060f140c07050325050a03050a170115051305040e0c01020f010506030307110d0b0109020d060e010e06 68
    0x2c001c503092000d844858000100071015588900c1540103449525010f0000c51440004450f052140e00406030410b40502ea8000401e0854010b840c2001000b4051401d00c03012080507000c6400182d070014004502c402c5180108400d805500d0240c1251300c0c0180500480444400d00480c042e140784d41007040c0c01101200610042c0030418100b940a00103111b07041103905800050030100e1081e8094860100101311020484000c8a002561010185082119101901c0085003006160851410700b0490210000343e09000c3d01c0b2055109880741500d540701e0344402004099265149a0103880e950010b00c04902840411041c03a03034076103000c507038a07030402d42c00e10190113840e8811a0401c0c10550a901c855001280c52010582c081e400c5441d600301c0411480e0a0f220283c40725900368004002c2103010820070a91400e445402520b0201030b40b245580f40c20701e404090340580142607012481200c0481c281c02100b000b02080d10b0b09225030b5041c441903d01078680034080b90b104080c0c442c02065 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 443531429 1250 443530179 443530189
    0xe012418060807150219060f0e06040b010303080c04031a010f080d0e04020d060f030c06030506030a0b060f041112010f090c0909020304170c0a03030c110606040911031207020f010906080f0402 84
    0x2407484c0300c500d1001021013031131f00c1009465403020384040f80e03040c40914190085d0004405104940200d11100700d6441c681702900d45410180840c15050001c120100c04101602043d0300000100c0d91940c41c035614005861480708034a4018000c81d40111044490300d41d408801d00c902501e0803200142d40345030101c3d04400408040d030264046404010b4004140648600e07800704039074841e2400d12150341e5180c20140c4030340d1008001803c500649010035428181880706aa25080c09807000500744800d540c0032406400c01e4004000400c082e20050142e0031140c00d10300020840100244142a912a0003500340c14890245a03243c550220002d000c0c080c051480c10720301c16484d078060350b8a03101c0c03038001c1da242d1006180075070200c4d080c8104034a0342441030004035084003802010741314940f581d404100141000300d1017900c40407100240c0c28072903603090148001d0450691417166030f13038000c0d10610503590000e1401905005501e23004005543d000f0641591120b01c07440c02050582d00c61000132 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 443532679 1250 443531429 443531443
    0x8090f0d150c0e0414090c01050c0601090207030201090c03050a1208090309190e040f03030b180610020a060c051e030105010905010c050307080a0e180103080d0e0124180608071502 79
    0x80d805420321520344417900f80707040001e000312603890507589111422001951544a0004003142c0c590008004101b601c07840e9001d0000d941c801d20012852501e2074958041505864001303943c03d4000e048100d0030041c01020304804003605044c10455131421020f82c60f100c0c000c5200c0b041c0a00100c00c03240c54403507120b04828014000144021841e414181084096013402e0402100440d00c2c20b895000f6034586682c0920810074801c1c0032400c00d0303aa0f80113114000080c1d81040e000c3d403282c0300c030400009480707000c0c8003609a040d5036103d8903403460090303040c1601c100490915111908100500080e6840309085040d0342c800e080500c1c0e0700959180292031445441000ba01041012410130112a4820f00c5801c25010464401680c0040c0c1c0300d000c00001c03000e00c402403042e903041003100703040340c010340040c2403460b8480300025444003000117004c016090034440964070f001044c0706204aa6030040e2000c204c4042080c10804070b07040c040c1e502d0b03650005001d800c540300640d841420649100700191 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 443533929 1250 443532679 443532707
    0x2030a05010906290a1802160b0720070501110304080304060801050a05091e18071701140106141e07060c0206011e1809080708090f0d150c 61
    0x80040341c80d2030074070800401540813800159400004e540e150303126218204080290b00a0a00b8406442e021440d51000000420b810481c2c5d0248042200c480e04031402942035809017050301701c1e500e050080101a04d200401000346050a00d180000070080016070000f035410138201200783c400c03507800c46403640c000d943c0245064072001501003251a4032405c024101c500c262154980d89440d1810020b0790300c41140c4060807445c036100500701c0d0035111040e107500001c0101404a406010545007820200141c01200070700040305c58110351300304240b10319a410880300c0c03e40301040d410184024010148911010300741c550104001c201c0820340141c422000d000d00d404a66540307081d03c1d01e60301814032456460003500030700000080c80381203008642102d140ea07200750501981072144141c8501000000d21405955901d0081c001860038801407200b90302800ca99615803844004012913443c0c61594140134022606c0003030b0009030000d8401d4000c10400e003001c02c00480d419011100ca010603856 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 443535179 1250 443533929 443533931
    0x60d020d0302010b090f161805060703030623091b0d06031104061406070f080d061d010b190305070c0b13150203010501050405090403021009080c2401050d02030a0501 73
    0x85401c0580560010101c0e0307801340c0741070801d40c0d5845150495800125858640001c92207000c4250b01d00c500d00341c1c495040d590707554800890300c1d800420b009401c690708c214086640e40394284a007880444a02010882c50210b040915018002052640c180601071243c030880c1c07420400b4005401105843c41103c003103908000a540c3c0b41031009050700c00581c2c0c217000303502d0103001103594101100d00c003000030300281000f890f2504c01d0740c92107440d0400000550f4100c00600c15240c3e8103909008440080108080ca1159100c4690901844100c183e0161407214002c002c44241c580380c1d845080c1c9511034900700014a5030f24118280c0e1107014242c4010004d031206d50401012008202c0b182c900300e40254012050303140b54441c514200d00c000e018403800700d00140010002890808191603200384a40b041d0750322001803414003802d807003541d042140d05602c040b8200e2442c1d1000c0020495040346c00801c090081c40f0540300e1044048103005090040c40c00c8040c00c0301f9034030b007000301e8060705a001300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 443536429 1250 443535179 443535199
    0x20a030c0f02150d18050c19030c080601030c170706030f09050129090606030406051806041101080a020304150c02030403170307110a0c09050a0e010213031b0b040e060d02 75
    0xe02000b96500031612111920710700410024117030301503600302c052660b000c0f0082000c49000c40c2005403074569685c481c2d5800b4503641c0c0101c0012813a080381c00040034520010700c00c55055180042622205422650b070340d0180701c40d00d5010400014100d811a0001e0400040030410154450b0280c0141d0401034295170800188100c505007482c0320021001c603050104402030540c2d0100a030051080da0182e170f00a809101090114410341c3c005600700004403c00003e009891103464180801120296103c1d80f55008480855030000c030600e51100f00584110302d185002d903a00c4810000000d0380400c115034030361082030704500070422500a150060180e091052400260201c2b07903004445030030002d00303d5143c0d070941c11030000c3e48680031580a081c0e40c12840c28020300074002c00f4001c101d18081a2204004024074500b0301c0145040311040301a010880e096040c044000704001d01c0010300040c0903441089042d40101c19541170300d01180c0f940c055626084000384894181680181d80314421407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 443537679 1250 443536429 443536459
    0xc02010e191701090803010506031005180f070503160c050124050f03010605030d0f0201060b070b070905031902060c0109020909030c0606041b20030a030b010311070201020a030c0f02 80
    0x4801c4011220100c0ca007000c1d840e9044030b80c40c265141c03c600209000d800f807005000c0391920780003460340403150b4202051041c2d03485001880184a0061120003000804240110408540b8035168400101e0400310300d1818001c040c800075554048131203040002c00c0b4a0307081000300c00e4000662822034451690840e586000310741844402c14440d0521403001140d00d0620760a06015841c21154000d02801d03e00c60a9034040e0b500810064001085560b03c2102003a01d5901501a00b007480c058031480c50503162a0401801d204181e803c40c600c00d5016035015000015142da000640c160b0503074440d522035040360442d5001d4030f181c0c0f00007948582c81e0010058014000005014080542c2d802c03161a5142d00301800119090385200700c445c01c41d2010082c1c445400344111155940071070828850101581000c5810f58104810200c000b07a2140d100903265030b414098000280c04401c100344c0742c83d1880d4000703991030824050060520030710700c10050521021558102510703030082c0c240020b1200b00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 443538929 1250 443537679 443537719
    0x507091a03010f150303051b031c05070e0a062003030a1e020711040b03030c0a0308060406060207151808010212040b010605070f0b0c070213150509160c02010e 70
    0x40314040d03009610340348040340306009074003800c0b100c0619004031000c1d050031901c04807640c0d44000d26112641083c00f449480312074041000740704a45040c180710044a0495000100307030f40019040f50200b02d986005035116985d40300c010021200c05040c03240c43d074520900e281c0c00c04a80c5101c451507501000c4200030050845410030401602881c0c0f00c0382106005561440803405602e402400805405441000a08181d440340c983d0980c01821a402e01074000d150a2070701104090480001d80c568060124504142c0181e1016004c0707400540621b50804a59003d00c400c03080031042004120310410301625490762480014090000003036541380ba5026880d540c95809482c204c42000c2c1d000000181c2910440603540d400740e018003121080031042d1103070042e18038058080c40784413408000d0b42006a56903202d038980c05651002c0800c441e00c0441583e00071a20030350016000380307171010130408251b10304010b42601d4189410200585070a80c00100c95942007081c00c150001c45160001c4c40b0b04803d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 443540179 1250 443538929 443538971
    0x4020a090e090c0a061103031302010306080105040609051c12050417031f05040603030215100b04030b06040605090712091113150b09011b02240c0f0a02011b050709 72
    0x4281c505034000c130341c0d41c03808490031b40501d1403d504580040c0003080400502e50344200c130b210b005240100707070151141e01079821110300361421101c0540d650981390070044140300041032521030343d140c0c2c0b011070342d1060054100030f443ca2800152591790400281004129000705880014011a0707603103a01c1c02d40da0307151160140c81100404202001800621403030140592070a9a605d40d003c7d2103102c180000c0c03081003000143c581032000c1c1c00d58001140710602d880c003800086005407003414403400c0610a1000300d5140c1c1d040140103101e04010400c0c0b0170382048000e000300da2003510015081c0750700d0900c004d00207140da040e00e9000c00058985070040289410281c800c0f15405256400c2c40da82d41c5000c06070340308405259000c140c800002c8030022201283d0046ca41e8005403404080320140e40c2e402d07900c9440b09080f11150304022440c41c0d0455010001e282041701c10400400d00f4080580000e0a5844140c45228412800c203001c401041410311003c001800e000801748a0045030780b43c1482e500302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 443541429 1250 443540179 443540203
    0xa090e0f1c080a061212230901030f0501120f031704060605010e03390a03030c050613020d110613030b07020c03070b090108040f080a17150102070504020a090e09 71
    0x803540428440303c1c103446404201c034000308245944c210305503034200c001c007000c11028080c00440c102e020450110503109020742c070342c3d250080351380f50421000034080307401242007a06824613140c018006400701c00e401c284050340003803c207054018245421100c103036401d100321071076011207400d100420480390408000d4032026201d07408805945028103540c2e100880a0500400300380c14840d001c000d440782c81c144020308e5100b040c2024401400032a280101c9940100c00046104012206020042c0318407a040380c0201c20900303101e0340c20380014074040d840080180044100d1900440701c0e03036401c0e080300c0303110350304150488800e9074034249542c58042c21203600c005070107400a030101510700441c080090b40d480c485074508003403400300110f4036280001c0c400c58082600215500218501c5005040b14000513076441c01c10b501c1c1600b05490001020b0642d6451070303a019005c5409a03004540ca0307050724020f030b50060307c81524038402c0b1035007003842c1d10207485866050b051100101c4c010070751070301450b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 443542679 1250 443541429 443541437
    0xa0f060c0b07020102190809010908070807030f020a240603020909101b08040605061801150909090201081b042606090303100e040302030d050a0507110c0a090e0f1c 72
    0xb0360b80c210241c1c02c3c0e208015188408002c0b801404820078050404281c00c2031168000280340321550341c4078100c1c2d030f00460302030714241f43c01702d100020198840402c520210381ca1001d0045403032203a5039854075190801d41c1841403400c0050010b040307000399024900540c0c004000042034100220590b489409200c0c07036071003140c02c1020703200741c065100907d04204105a0b032816566960f580380c4d0700c02481c0c05091160300110343c603071542030b5180281115002e0030580c50098001c2c0c07110a00a05004006e0388010119414000d103e80541e0300070070380b250f1040c0090888001425456460f0b052440350f600802e01040101080302e03804c0040c41c1130b060076032110000302c60054880c0d01115590740004c4440c0759420421042c180164403d207501c1c0c03a0854402c1c01160704100c198002070080d100125000c0900302c2ea140700704542035901c0302a01c03481e40000c00152102d005044045402488030340a40c0d4581a118104c40c14841000c20161208031210300c15900c044040040041c4c0c00505040124001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 443543929 1250 443542679 443542681
    0x9020f09060a030b090a1403030108010606020c01050301380909010b09152808150a0806130c1a0403140309060304030c05031201083003010909020a0f060c0b 69
    0x40c102600034a0040c000100020112499907684600030000207040100a000b030172050b9000403904041c0e13180046c0301d0740107036859605107030b85103003100c0d00d035800442158043c048840160340c01ca42200c1c1516685003840801034040c003941260444013458544294030b4009000e0702c4441084043c0002e0302d412100004030f40d9940c2e0980c7d100e809000301c40c80c1c1c0015100b86002c143c034200030003440c040f4030070000444071160f016644d6003a1404030407500d001c1681e03201084611809410351600e500e000b00c421031041c60622420b140d40e080002c2010588001905212061003d040b1840004003038840c0515421040074200b0704841e0810300c011500c1282030722005002e140040162984004d0141440b4115522a03c00b2a603203010030509543ca03000070460310324030401e41d00134580a0030004004003231080040b15401c2c0e5851032640f4000800d80d00c2ca101100c280031105c2143c2c11161011804200038855000281c070300301c001e0b80102c0900301c02100014599402008035044d4030b0049a548901e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 443545179 1250 443543929 443543959
    0x60501020a152408160806040f030e240c011503050309010315080d0906080703060503060114030102190201050103030f0509010f1206080f0a11030d08070c06110a030902 74
    0x1541070784540003001c003801c03022290610000303940511801c0400c00e6110000c607070980001c483d4514507420045690b040f44250324060309840702448000d0a1440042c50340b0301d415120307107100c410a0381c00207040140d070260740d0240d030b9501c0140c0142c84005c210a03404e84c01030b02208410661001481d1301403542011400c040701c0766220361006c12070f500100a10320f80615100114000d14074150004507404001101058580081082641d006d030f40e0f4230b660380d401d0306146000d08490070092540c001c00d030502c0c0342480310f0340300441c2031030440b0458803950810000d5040000c5c06401412190700e025003551070214030041d4150461030481b4080d0300c0c0e0546050466000f16403c0c07040c0410240031440f6110004a0b5070b00c91400498640b154487c00500c1d252910b0b010350030903003030b90080403059021441c0b20050050550011004c04411030040c4482298124060011100208030000b40408025020140300246c0c00481c10f0b40c4c00d002040c0d0b91100703d074501070000c101e02032044e4004d511075144080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 443546429 1250 443545179 443545183
    0x5030408120d0c1404380c010b090c1606090b041235040203070f09020703030b040c0807080c07051c08180c04020c030705070b03090d03060302100503041103060108070906050102 78
    0x1070350351320150b03503490a400c011031000c12074070900c0c0b100005510b00482c8081080d6800a42e50501802c555080e5242d29441c9820b0a46400d040140e01c030f011140d090040e01014001210080820408620741e624a01d05209000b406215006820011418200410001400640e40040b54161946075130910141c01041106483c0c0c1e2080241581c40b80602d0000c1c5202d030000780e0320030303c014211034625458440700f0602d41419444502c0c41500402c202c01050703050700810350116400e03030f0104903019003504001c05203180030703004100703100140000c26542da20f000119060f85800104964001424007200f081341518440b41c8000140103402141c1c0c48ee00344003281c1046c1c0300030001000118401801c010007540840c04501d4a48410004400000c00c2481040300600c2d400054a8482c640355444038180403c85082404040c6404828001640c1c0c26410070b40380c80785807030041c1d129034a0b440d000e092000c54440c4698140728000000480303210000320801680c482c4038007403000e5541d8600683e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 443547679 1250 443546429 443546447
    0x3090307060309052d0a201c02150f0a1214060a030b1306050c07170703090b0d1d060405010c020c13091a1003020306010605180d05030408120d0c 64
    0x1001c03030700400080b454900c150002000303140804c66100c1c0411441700000d80c50320b010300d201152411202000d64840d841080400c0100d48001d6501008a50062004003280c2c6102c1c0d100900c1544403e9500c201c900851090b44d0105120a0385543d80d0940080003a0840c203545020a0f40103080250304410b03080500c180074040e407000380800341c0703e0b421030707481d40c2c0301144c0145110206400c404c913440110307025024207800307043d0b8183c14694410141c1840f82c81001d030500e40c032440403010400d400003e0361000410701280d40c0040201d40300e0000030059030285ca40305050b06152640954018a848808074403180140c0c8508020003226900600aa0b1100340d500b0003e0741c481014007a0b03000c52849a00700c11070107841a42141002111142e0591603851b0030380300f2103000d00314a00180b0441c142000750901400c041e0400a051412a80a240c07130003c8a42400b4051510403030703007004001c02013058402034100341050b1b8800c82c4124805c002c554125a6180e08501d05004a407101c2c140110f64034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 443548929 1250 443547679 443547683
    0x611060105060f370c12050a090605090102150411040b0901180207020a09060b040602070b042312010c03090614010e0f090a0206070b070206250f0c1403090307060309 73
    0x142025201408031401a0164452541c2041ca8410801ca040b42c08425081210a2500e4091190141b420f1a50340a030b0205009018424200464a6029001524282122010328003242d85485001c0102e0402500e1004035941c0c0050303505220801201d41000118404150b80402c40d641840c0108a034130482880303052580c0c2c01c0b00548040b044111b40040015900180c840c0180d00daa4034065021101182e2000d01c1e00b04022031f05010b03041e818090b800080c245c40d142203040c982030030360720001200e419544040d140c001c851444041d031942c051810b4554880c1c0020864801c0051000d00503080c02d000844003a4034004440a20500c0c00111714182d54450032028450323923030030000c10200c40c0080c201200300e1160400a400681d6904000c0c6103642c400c0041d9046820030000192800501900003002589204911030a0f00c086030500190201e0516081c0e440030300c1d02e00300752031103082c1141c0030307140314110000305e490b001c00000209114407041d0202d40d11b0564505048040344c401c1040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 443550179 1250 443548929 443548957
    0x7030b15100819020f0c0703020112050114010c02040e07180609020304110d05190303021c090f02010f090b0f1209150a05060a0e0915011403030f0c03070804061106010506 75
    0xc1401415864502c08070083d480c90010302d48000c985403c0c0d555002803c011240342e001c48004d008550340150700d100d0140b00440140700070f505043e000404010002e07116810000d41c040664290758880d04007840070705000c02903403401911108181c0b0400c4071903980c07681240c1055400941d01c444d80c42124459508078200c0e9001501440401c40b95044422007590303144a01d202003c030f00c00300c880b6021501c1d403294a005135120f03440032151209680040b000000540340258180100364500300c17540415509107480044d51100380d00a8603000ea19400c541c50313410700420340d280c9084600e80203024403032011030114242d43e188940700381e44800454120707514600f0f03030300401e01f03d5807207402c080d070030500062004440d6912803842410481d0105ea88170790540c00380ad6a0349806050000c01703405003881c1e800030420310b522040480d03981d11507108140082900002d2000412209209036480329510042250755181d882c400145000c1115540000c2802410000141c40c81c1ca44201c0382081500c1d64 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 443551429 1250 443550179 443550181
    0x30d0f110c0601050108092a01021203010906061e0f141902060a0f05060307030609050c060a0e0406090b0319020d050a030f03050109090c031e081303050c04020a02030313050f07030b151008 83
    0x323003560500a5032071406041d8401c0c074201440011580380918080e1025600001e0050b1524074001c004d404881c0300034002d0090703003a03400d00c6a64880750280c01c07516036041104030050b481501c88102d102c0d00440303485880fa00480c4003040d80e0b000c103c05001d000c00040030702c00c0f907040141402c1100d50a661076607141c1e020080800c00074800350411403a0300d00907800d0307e0f460f8240c4408141c076644804140d43c006924800000d00328074092140700058000f40008100403520321021a0b40c41840c0310511680c100799034200001c550718541d00c0000c4661110030f0341c00702141031070050700c211088030b03c45010900705070001c60740038000c0c45100c182603080821034484a140d0f4a0300806c9084207032000344c0c02c04880c40b0580201d02003000a10408203612040241c480c61820300a0400c908a90407900c00c44c010010895100c0d0700005407900a4010500f80880e02140e2610500d861041c42c1c03030f40c45134005e54200005001d60080494401d1012240c0041c9035140d039010804142c0383c10f4100700108050710 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 443552679 1250 443551429 443551483
    0xb0a021f0c0c0b07050c1b10080123030102040f060c1a0f0609191e2d020a020a141506090403020a1704081b010e060c030d0f110c060105010809 63
    0x88012038101c404d5043c464500070305071201a040810b13944484000600d5000c002c0c600f800d1510108815201c0e51030716007220750400c0c80c4d58061015080200265150001001c40c0c141e03401e60489009062415002e1030065840d030002d009080d04031030a0703c072454486491011144c224081e035100d03e00880713001029540350020400c1031034000d001d8804010544a000d01e6030311040c80f6034549080c1c1113410761481c0c0104044a42501c0584521800403941c0203442e010010300c0b0a050092640b145c0c00c0949c440442c45002c82c904480260080c00081404c1641388400d240451410301c401e00c05c1c0020714587ea204402d21994401c182c070028016405007542a0110301224100301d620303000344c0da01d9850260baa5402500d00105100321001031100d0054400b010740e04441c02030041001503805605162001c1d0f0b400b80c89014412001042d00d0300c44014500d0452290300c42110710313142100d425100c101059600b517039440b090040e01c0c00f00d1201d070702142612500059010307c0c006c16121080e0901180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 443553929 1250 443552679 443552693
    0xc090509010b040e15040903020c030f03090306060f010c02060403060605130e0a03111f02040f0e010302061c021b032a0c010c05031608130b1608130b0a021f0c0c 71
    0x24100441e1780080315403c44165103e01603041a03900076401080b950404000b01400d0148254140c006680304004540060314080340040d031141080315102c20303c1b0040b00060340d40300000040254000c1000401100308810ba5221009030fa00c1502d0166070300c4400b0545c0400c5481c012154815075000084860000e4482c5030140680c0e40e01c01c0036121500c0d2024a1242c0301034414082000c2c1c960041018004650b00e246100f00400001c40e41c81d440d5495038000c1140d42c070900c418410007048281e000e40b0b4a184c103030121451400c00010702d8400348801c0c45440e40ba07411201c2d01d008101c03412182c19403607082141c80c01280d446020302031315012541d00c00549148000e0700301104c1c41c0c0002d100c81c1030440c102c01c000d0f1000c54010509281d4845d40941000800709294000192088041c0a0300707a003a10147e06041d040346e40810201c0d5160080001503e80d000d00d9444480440710003d90f00e03d1443e4041002e212040070101d002a20808013160102a40c1d440f0360160000383e1f0240e80f40303000c2001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 443555179 1250 443553929 443553931
    0x11010c05070b04081e03090c030f1501031b0e0c07020f0405040215070303090b18280303020a1211040f1a031513051f09021e0904020d0e010c090509010b040e 69
    0x1da8045c1d4410b940040480c6885d81007150345ca500354000007100c000c07500301401901e4032038044101074104515140043d200103541170002400900024428180c4a45182c803544060000850200c4040c58483e04200c6207a10448017240554180c1c02d148000d401c00303008003805240e008191029540e0ba0f4152100c8e1070308582c0090f01015101c00700400450000c0701074070700400811402c01e503582103d002061805190000c541000e0840380281500c050304800b00c65041a4189409a5201804082100c2c00d185010840003401d00d08441c00d45920384038030041080f14540e80d07a812000f940c1d00300000980e0328000e40b0041102c000c10015098520704035400a2525000b004c2ca0045007508180e0012641d0480b121920102c0c1e01c0d00340030015002d0b928000061100b203105601d011481c0310802c9106c0d210040498004038042200e1325690784a4051781d0500c00300c001c0401ca40c940b070b4070415001e05813a003070300d0300401c012039030115082c00c003408903605980c51400c83e00c0c501441c04c8484441844 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 443556429 1250 443555179 443555197
    0x7380c0a0b010e15030d120b0a0302060307180b0901090e060103202a0c040914120d0b0f0a030f0309030f0305030609091b010c0510050711010c05070b0408 68
    0x1114a034400055079100c085001e45034902d0200c000b4504034088912000d001046144241e004480c1d00c100658000c8000d01a555480c00c081040501c00d00131606650711500029031140000c030800c8038040e4010701d0400700658060101980c01e9560358410020321410070740324000742460800384081e10a014101d50000c40c18540042c0e50b41640c0c54001070800241554042280c0c0000d514205041912034183e0b0b0003098107031041c0c100c0c44000c3c060390301d101c01d100007406980c076030547c1c00500c51950804005240a08140c0c0c0840540d03080c3c403030440c5e00803201c00361142e20303003e080151420411009001080d0180084014a0464980800421104000728100508240301200103261000c0d0034650900c2516219180d0034204100071805034018201c0499502041030756444e220450000c604105007800c0520790425542801c504100d0408421003507181070109110030194044210130024200d9002004111946941201d82d07209165026080a690070003203404108458005d010440b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 443557679 1250 443556429 443556433
    0xb060406290903060405160b09090f04050703080c0a0303061a0a1407021c03030c0804120509041b02240106091401020c1201021b0a020604260f07380c 66
    0x150b6070314000380c6001c1040700c0882c0c55030080518a190795036010100b801500340e0000b550704041312900803030880706006003000d0341c040b20f00001c14203202043c88140069500042c04554541c4d070140c84075034800c084403084001900e03100c00083d05200388001c080003030840f000030514240200c80f04a4540d07074104d01104141c14100f10b104016030358060520001c3c1c3c003c002c110a070400d2414090100c940303024a02c070601808a041000081d0000c600c0401c41d00e10b030401c15108c804030f83c04540207180b00001d04981411086103840143d800203008004404428450b600303140f2011000a0f1401c0207200300d40c0820300018041c801c1d01142032920740f1007e410f104840b50001c6680c00030300d50024203451008165030005400c859489040c00d801014401c050003008880a80ea0118007644503a20842c4000340715048114100c082c8501e40794900180c0c0000c44500301400401940c6840300740c0f013038442c844100301d0700500f40700d440c115a946400c800500800c2d4100922031840181c0e0103020710b51b0940c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 443558929 1250 443557679 443557687
    0x8070b090d021824030c0109030215040504020f04050307120c0e0c120411120f1b010c0b01080c0301050708070c020d020111030c28021e1504030503070b06040629 71
    0x11502c3d8080c56120308205110580d007000ca06003010034191542043e18029000100f02043e1a48c1003810b1400f00e9a06407000e480050500c03000107181c4c0103d4000503845400001e24242a08403a00a4800c0c1d41046040d101d070103a641e00780c82c2001c2c10700c21740200b02100f070520400610381510445580541e40032070451420302c0b04503591040b0b210031030f01101e4100e0004511407441c01c0000c8071780e0a01c40f10500a0900c4804502c15595442c5550101e00744a581d101080d504c90348035a82600700164070a030449400d503101ca840544078005100428020741c41e002c00510388905c11303a0341600544964540080340f511721f0b000d204030310761407040a0341404986412840d04610420013003d5080c1d6a10242401801c003c004140c0f000c0c203000850360b00101d035803c04000d07a403540803020b6102d00701c8000701544810f00011800310b418151a4240d00d48002c6000018400040000d007845446689c0900c0b1958440040108554460050030b090303c050320a002104c40c0404580b100048090f00340c1414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 443560179 1250 443558929 443558959
    0x61c110417010221071425050601090b010507020a05012628020705150403090b0a05120609150103180605040c062307080f09042408070b090d02 63
    0x1011080141c1e81d10542e600080e07034400300d038150300c0c01c400d4440c40c205560418104180000d00e840910107424130021800100c0003109000c0315201e1981041031a008030303000c901d81c1000e03070f101d40091060b214810300301203075200740758400d0302200e0a041e401809400c0c5c50b410403004440c02031700c004030301c03403003800000300d000f80da07010450314030300c5500200314060500891904500c0d03071021040c280b0203264018015400050030101c3e21000c50103940c581e200180d6601e041c12a4000d150798402c5a03501d4000408041c016031000041c0a4503000028819454035541c081c0403010340115031f01564001001c819441070741c03081c4c1040752806040720103000c2c0054a5295201250000d5900302c81000d10050200042c0d600072501102c5200c4103070070001c502c080b12504054074030540070000c01d008400100d03554071415940584442600180080010034110382e480705083d1403591541c40c00c10004000010740c80800120642a50808050f40e402c1600c40d400740000c0c5003480310200c5c0c0c498411060049 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 443561429 1250 443560179 443560199
    0x403030902220c050c0622080f0301051c120516060203011203030b030a030c23010510050a0801020406021f0615030903181508150d080d050105061c1104 67
    0x310380d0304a040802640c940b40c18000044600401c2600306004041c4403c1c140840c020682c507074018488545283d0303013040010a245280120704004040072030100d1410482210307003010b18142c4006840000c9016620100b0b8901d4600610300144078008550860307030042e2160002d006004c0111b11007002a03c0281d4441c0e051740c00c2600b11964421200305107209040d8540600ea40d048000d07809000104e0b0240c40c01029090550310141081000c491100280d01d5510402152100c0d0390f0020003050a01050720343c090789083c8140c500c100a803a4011580744818401c45003102c0c05030b0014503080e49107020000c9802171250514046560b41c90b400564080043c0d07a05030301519079600020f10041030b2074054a040258032140c1441e062114090180b003c02400322080304c41c00e800c00404507a03c000290743e840089003103141d0480814a44501044500005030078903822400f000d104d181e8a500038031280f406101c6c071083e150450a8103240e84a40700d0ba000d00302500c444050585003a0715888264 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 443562679 1250 443561429 443561449
    0x2103020903012a0311070303111c1a060c030d0504020a090603030804140109120e03010917040503152703090d030504150314220f0501021b0303011d0403030902 70
    0x42400882d02d094280d81058120f288800203442c0d0400f004100340c54800720103d405030301801814146d490010540300d00c0d007030081d13a0540045020120114200350429805440c402c440c0310104903d401501815180100a44403410703c0c00b80118140029680401c0207014054010f0340c000801240201d50310026008050142d03000c0c0e1201d202e01d0404d440c24074540003c4440c2000306925005801c000280c50708002d1048a64914002038500c40d00000a4014500001c0c0204229007040c45510f440307414074098002c5a208a0945588080110b881c04050308101d400e02e22a2040e003203001d03001800500140030f0525035200722424091a64042021402e030b0b58419004940042400c00100d96904a20321080c02c0c1071509000e010f41c86400307100d822034050071080c14031008244000e112600c03070164a140d81c0e00590341d00a21031050904c0790013036000494814818800d02000c0c002040004200c9040300d114040032441008401514140418043c1040742010b07125400000503035036484c901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 443563929 1250 443562679 443562701
    0x9031403030f01120f0b041505011401030f022a0a0c0f1401021501050105090f0402030f180601030f030810050325150c02040b0301020f07060204060219210302090301 73
    0xc41d5a4108071444000509050384038007203c600c0404c0780e40001e05545c82000c1c85903407200c0b071045030f52260310b4071921840051108001551400000080b8107068420340319082c10b0a880400c580035440b1003a50581c41000c034000c014103807c0c9606a50032070301c001d242d03100204007401c0d207011001d0395640b805410003070751091441c14003201c030070702c03425a030140c5603044c0c0c0409000802014100c81c4401001d0201413040f40d041c050007140701c013480c2d11600c1c20010f5401e07008004545e84d2800320140901e030403042e550900755070512820840e01c0680010711a05076500110108200011564100d1b42908001c1003400ba0301d00040d4001000e4a08000c1104080c0c880c0810703a1034081d041e201c000b510340099000c0d610340f0403011090001603820025045034076405480204020707a0010100340a441050b503214030381000010719905000c00b86c0d018100361032082d4240c4079601da280c00c4200d09102000c201410390245c40080c1101191100c2124800c1009400d0141c101b1001600103400c49101d9214 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 443565179 1250 443563929 443563933
    0x70506010e090601060309030f0e0a0902070b0a0e060c070b0709030f031101140601050429030f01090b03030f0a030504030e060409060e0c0c030403030f0905060d0f0e0607050d0903090314 82
    0xb4445600b0083c0005405007135a8642000708407510340303004105603000307040c01c41403184850340c2032860b440e2406ea020140200e480295a1806d851411b44082081111050907042c94815a100e04140224455009104036404203060140030b440f10394142030007406410502c40091000000200c030000e410314000e0007038407401000d0514400d540c1c251410300002d101c002080d54100a1144c0e0028145d8040d0342c6565481d000b0054480050200e113918040c5540400d07002001300117201c840010114180e982122090007500d8401c4181540c1c1c1c020210f101ca0300306420300580d14054480d501465000e4020320f06036020146260104400d0f51050300042e80e180d0b119007062084503001220960420302d104100e62506082041d02074481c00f807030000400300042c400d1070254061007465100c000e8030303008000950703400d2414a03510041031015031059041d818900d40c0c0b0080200400c00380d20132581c50702c0306440e03c07032440e5001004111108044062103060b800120204042c07015548120340310f600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 443566429 1250 443565179 443565181
    0xf060303080a06030209010b09040e010e0d11060403050301062d0e0f1c0204090830070315030b060312070b150a080307030f0504080a050c041802030304031502070506010e 75
    0x30001c00e00d440040c24840560b00f019810001606c62a12650460b06c43d6600c0d075841d5540c0c20700040c060892007041c200e01d0b608100d4808440e402c08101720030849550b0f21080c40015602501c180c44140c120303005000f00d0800d000400c100340c0110007a25012000c05030f04a0700c2001700c03021543c0506200404c00028103880b0055035942484500148a03030301c100c882c44c2d140b411400089940c541c421030b00030301030b6441c0c00d01c0c0300800004078280c40c1880caa80102520b001005030318402c9141094803140f035040c1c81840401c07150b034001d101d010304120b82e2084003403c00b401d6440d86001550040c16803609446800b044840542c1c01402a0a04920801e50000b6506000d0048100c05108007070f9540314029080307003004520000001c071070a03158181400c00b40c1c282500f030b054401e401168014030b0507006051101080040202da1a402c012084404014900c40b08031905030000340100001e4041d48200300620102d8000a010701c4041c1091202525002c03003a500c403420640c080e4400c10103090444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 443567679 1250 443566429 443566433
    0x15060f0c06220b01031101022b0f080f040201030903050d06030c09060e070215070e0a06020d09090b010909020913150f14010e10181d13051c0c05010f0603 68
    0x300500c02c8030007000c59a01c05031500380c680c800069010300c0001e08000c0e07640e05014180c0d00900003405103440000c000c0c890756000b010fa00107154500b549101c00500c5a4030040d0308035001d2040f45014078401004282c0a58490b0f005400411a0075425020301c003050140644840242c0074103400342d8804c401e02400c0f94500039440c4107581580e003004c028148590100100d20b9130004650300b081c000c002c003800362501c0d1b68506442d0001c06e00700503a04a03541c44808200310b5000200404240f070303566682d070940b51b512121001140c25140781140080ca811204024042554001d0004008010a04108910402c04c0c5030100d0300d04886407000d07041d03980d10030804030001800c107038000e06c5071500b007040d03441042c80020304807400341c422144140e1807041251a0b4030320a5a5200031090111000c5003210703101e043c00d45d0484d058001110804501c440042c40c89001220448991030b486401000724a001030004041c840307012107450200b081c1365242c18007080c03090081803a2244540b10004400e4114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 443568929 1250 443567679 443567701
    0x60306140106020c15041206020c0d020732030102040617090601030b0103020907050c010e031b0705090f181203040201120b090a020c01140f0105010f08070815060f0c06 74
    0x100c529490026204801008081d8010912240c40c2004a6205c20550f040b03400c1c8031030500481e0440200030440f0541d18042000340d030b0003042c0010481044036502c1040342c40803a5209a03601aa009000112100c0001340d8a14402080d5540619004249084891000c06d0882c0c210741e010740c1c0081c03a52014010154100840150000d01c12006000303d50b0540e02c4580c0c80d001d041c031000b8000c02981c40060303040b62041d82580c155040210084c041180107104e207581d00d8002200520380161070301c0c030691503c100080d0034011211b0240028a850f1f42d461078904d4400303402450440560840348510f09960001d22008078401e40304071203183c40e0f0916000040003404d000d40010801c40c42c00e8051007182c1e0381e1100b5560310205100001d641d800030910021b0140107188401641d14000c40d0a00202c00c3e8060a000c2c140c178000c0ea00c2c80712a50a04400b114044410b0700d400c0d02050700c40c0c0106451188807202009078040151102d441c2c030b94098000700980e800328100c014550896010310070807000e2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 443570179 1250 443568929 443568941
    0x20c061609080d08040f0204240e0c070f02041a03030c0d0206010b040b1b1609051509161107050d050d0305100812031801060b0301060206100e0c071502030901060306 73
    0xc44001c00d1508510304010f00302d51360141c000740001c60700c1e0651504660b5181c004007507440203941074203406c40040d03c100c041400d60380291031114030040c00103201c81c0789403019140c09507084100005411a142c0074040107101c050304103003440828840e40c205640f010030080c07a42c107110100500109600440090900d40d060300800000c50082004001040a50040e01d940070b03003d03141e05449007071a04006142c80003c0807280040850110300291410141d8400d611031059100c0004035100c51004020100e0740460350b04d510280da24000280b01840f540725800c030f411645088031003030364840e0000b8142d01c0d00b0300821141944181000c42c407859041c000c03542c00c420008000280b190401d11b540341c403040020200003100101200240c01817110302e1a11f40b0148040000b040055120112100720760320900820016106142c003003400960030030103040031190071080d213020640b42e83c0c0144400e0f621568054500c001c2c038040106040740c680c1b0082d03014290324000060428a580f50100690f50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 443571429 1250 443570179 443570189
    0x60e01090507081b090103030f1d04060b12091522050a0b0603010b0307030c0b1815190509090c09011107060306050111030c061f03050106030f02010e030f0c04020a0201020c061609 79
    0x151714401000004c0d00f000004045000d942040b152a40d0194450740000d030008000c030380d0050030f1100c0082d911044000411121943d140c52010300d59586510940d1100c0c1c490595161100c0d1070005086100d8051010109400c01c40d60907031b6a1510f5100c1030300d4405052021345203c10b07100c05111072840c0910641c100c0c44400d80181118501d15101d55480866901c245014450009010b641c3c04c068585400c2d282c4000500202c000c1103104048250342d0401c880b0500412080e08858840302d000e0710642c2c04d240d000609000646e07944942071070f0180c002c112403d0510000151000201c1001e0140c03401a04490790000303070070b61404000402c1b203510803440c0c5100c0c1c0c008104031b110300c09000c41d000c0c0e484070001c2e03000b0940006914111108040030350018007194030780840071041041040308031811034000d903940d19891000804064071120b00140c941582c2c2e00c16001d8840c00e060a4010307042c40d01d01070000604081a190f2003900b06002100c00581e10a0312901e101603407508141c21a020b08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 443572679 1250 443571429 443571439
    0x60c01150510031a010e19121e050a0f0f08120f15010c11030c1005031609080c0915060a090503010c0816080405010f1a01121107060e01090507081b 65
    0x52404130141d10040f100b44030341000045080c2e1443c40d110718519010001c1385042d0700c0580c59940c0b440300140c0d60b016508403039581210007000485c80104095a44242e0801c0c080c1c110300d0015070b00d003404900e426004540381003400000002003907440000c0c00403c112504116460719084180051046001340580900c0000c00e190751020b9a1251448103c3d41d0b000362446d092141c15400240351517400340c3c0c070950100c16145074402d99640080614020312400d030042a0703a070180340c0c00350390a24503400b440b1280c2c0c0c4240d050012a150948009070040840d014051175842c0100100380254400001c01c40402c064120402c0f1a0809200744a40000e0b5460054540d05007034196203a0801d24100100402180001103414044298800000c0828110040004005500c14840340c83c071848410390120716030688140c05040f503402a4034940b55030043e100c0c0360480316a01c1c900104040c2109810640d41e130b000840001d1420004d01015229000040841c2260340e4880405600448019800b030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 443573929 1250 443572679 443572691
    0x402030114012c12030903010c020a03030605010f2a0c080c0a0b03270f030d0504020909010603080a0f200105042001210f2c010612020f060c0115051003 67
    0x8400e1203410144400d07049601c03215031200031511505e1801254829541035184c075101a00082e00010380c1030b802403007520300307000c1240d807500107460960b9108040d1000c80c420482002c0c6000e41320b03500c40e190180030b4900301c5201c44242c4074409c0307407199a0003856003988900852003441c030f0b0400025005100005001e881c5141076905580342031880d041004400c0c450144100d0805c00c01c0c41320442d2400300780f00312903d8403414580321010300400c1c0c1d400d0340a18401ca01050042c0c0b010702400c4103803a080254141350070302e020000c0700c00c040b4004d1442c04010b14500b4580313103000c03102c03543d00300108403500200b52814242850700340380214801650035882103442001840c0d07000600300000422421610b04800c0102c00d40001502c004404006e4107850a03414010701c0c50f03102001000060000403030303c05480d49200300ea0803104d0500a51001c0380e0092903210051803c910080341021001c0c00f01814404507025260a42e9603015200c10480040e10042c81541400300904000c003c0902d014001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 443575179 1250 443573929 443573987
    0x80c0607080706020c030f12040c1211010e030708060a05010e070516021009030f030305070f020106080c09040f0b0c0403050c0a0b0a030f02040f08011d0a0201140a0e040203011401 79
    0x10502c21000000e240301c1d004500b00c080d0751418420b48585144100c01d4942d540f2055590150261044a0440d5001201000410b581c5a803001c4005016440000f031520741c50014011741c0c0003031800310101c0d0700d885081000f0606110520842e409095001c0000c03c5550404041c0703d91500024020020440b060241c038500e0740c00301000030f418613010f448074a40c80314014000c440b41400f982002e00568518003404042503410303400b05128680707559a81c0011150400200d00b6a90076200e400d545600c0615080c109141001e49a50054030541c4030320000483d60340d4901e4489000c0f1480d041d01e0402080c00c000b8024140301501c0da0701c81c1242e610401710300745801c4500364040d40640d80c00301581c43e40400d0007803a50364100c03406050454514004641d035000300a01030b040c01e0480e40e02c1106d401c001c0a0301d18500088180c04180c0c16101c541041a00c180c420400d50001d8110340c041001d410300c444407e031200d03c000c6010f4008800c103e91a952800009042c0c49000c00300c8141c0d064403080f035400d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 443576429 1250 443575179 443575193
    0x80906060102030a14160609080a020610080c0909190c0311060301180f110c100f06030309050105030426311809051002091002010603020f010302071a010e01080c0607 73
    0x103105070480b2000d903210011110458a00d4506e40c00003800e4074503207500c0b402031104030009007800782c02c16402c841555a821003442d800c0f16162040404640c49448116094901051102d611001c040112000800c2d121440d40c40000c09540587d040c1040d450144140000400000038030320041d03401510b954540020204600c0020741007030390b001c5c1e9031002c140790300740160480424604210b007015210016502025101e500030071000340098034002d0420b403140e20901400e1f00f140c0d0507850308200649014019070741980300810440c1c09000c01c12103d08006006076034440150804540103403198603a4905501507500d0100ba04501d00c03a00e0414a0354022503c50f02e030a40b066903124126075905954a200500341c840713002884c40c0108600416100350131380c044c0a8042c41194461000e80500e40b003a0308071640c03800040c0d04110f05984110095010703400a06d0118402c030035040c07035107a03007a041016440083c0c000c4100c0d00041401000241404c102d00d1640742c02c1101c3e0585010580c0e5180a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 443577679 1250 443576429 443576447
    0xf010207110103180b0a02040510031104030201050307170103050d030515090402060a0212030a0f1803080a2703081501090f030215040e090a020316140f0a15080906060102030a 77
    0x1410952134035503007002010b80200100305150f0011030540107003400941e102c041d411234040d00d800341e414400c40c0301d0a5032207402280c2e8034070f0a00008618040c00e503001111240d00080c030b06014064485040ca0a500003101d0b0b450095000700040c098003000840000d00f0b0f00d10181c50503164000348054880959500b01e15160816811035480c0c0d90b0740f1070140168102000040c00712843c804c04401c00407410140d41046c188031408403410001080807060014008034080030140001f26000c0000300f0401c04c560000994a175030150450140074405020f1822060740c4108800284840051080c041c9610300b0f0304181d0030003402d1007449682407108065200050b440007a01c5049400c0b91034510304c480004590142155001010061034003121566840d802044124002e00c29425101822003005c0c0c0c181e000e8601035000c01c2c900003543c6041101082d030380008c00798040884e403400954445210084100e500e00e0743c607080c00d14940202007a04014004002c141590020020340403c280e20150030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 443578929 1250 443577679 443577713
    0x5040b0406360606020a050d03021e0310031403070c150c060207020a080708070f0b190309030207080607180509040b040f0609080403060e0d14040b1e07140f010207 72
    0x1c9803180b84103996009003081129840e00c10329003880803d42c5940400c000340d080740034074100c9258100404084049110b1a01c0d094079a1501c1c0e00c0726000e801d0500d00440c0c001d0380600c00c0c0680701d42c0f00d03103a14041d0b1a8403415201d40d036000007611010001d060701c401c002403079100300d03004200503440b4000d03000301402c90000704890b50000b1040119504e00010070003410500302101d04458a5000480c1d0392943d6008502c1510610000010b07512420411030351281c012400f0221400001c080c01d50142440d05401c42c198040e10a002c42c03580d0701040542c0c45101035548040e0085552401d12070598590b8000502940f030010130000850307000e42c02d85c2d41250344442d448001e540d690411400424458138001c1036904005000402c4c05842c0d04040309100003001a00c0c56880140d5080d074401c05405030201c00250280010000c440d0520301030410f000c050f1052181d48c2550f21041903956205040468201300614060a440a0104145101c1302c100c44000c506c1d01005403140c0e0300c00d8443c1511 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 443580179 1250 443578929 443578979
    0xc0f0c090a0902210607181202130e0d0206011815120c1a0720030a0b10050301330e13111c02120705010503041106130b0405040b0406 59
    0x21900e40040d83c2801d128003000301e1451030003a078138503903d5040c02d540c08800144900201046025594544404c66060602c07140350720041e903003070100340e0828980c0000403a81c1c54044106440c030030b102e081120404c2d603010b40b41c1903060164480d1300086c8880080130303881c82d200002070194101a1202c5c15035403100d11807062407a143c43d00d040c5003070f00c5402c41450403580f1001091400c7c401005821031501c41c8442110161200d140b041824641d10302031640b550100c0605004144080701e4036820031030450013800c8e02c50b21800400d081d45e50914541c0f030304c040b522003050009441d007810101c100307003014030000b0483c0c640341c0911041d10004d80042d16002e10705080e40d04004402d40101e030030802c00392600c01110000342001c3c0e111040d5203405d074010042c00c441607903c407402140300001c0c0e500584a0905545440d11500000442440c004d0b0f0000030801c50188082000340d07022004044542086550b18100703020300050300c0410135441e00550070300344244250800c843d4001c41c6008c001a03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 443581429 1250 443580179 443580191
    0x3007062a0c030309090609020702061902071d0a05090706020a03050c0319080603010b09091209030115030b011a0f0a0e03070306021305032505150c120c0f0c090a 71
    0x15050300800003039100901244054900000301078000700000d080300c40ca42010030646a4404c0700600740e105d0300b00001d500520802480c0036040100b40d2001001c1510320480782120b4442e03030f8040703121030614958a01d85580c00304100045010707000300b5034410005009007518603e001c502a6a54240e500e0040c00d2100101e80040e0090301001503c6000b00c042c0e0034100c05204001002e00303412416070300e8a000c1d5003080704200c018280300c080c0901541c10340d4002c0007140040410a180c94100030107056155482d0403042070018069201e1030003450049003841c846514100e01003800a4003480000a28038007405500d140443c5482900c55034055418020b1055403100c0001e42440100d800041400d880403c3d59100020514a50400e0f00c005030308444c3d100c2c40c4e00042a000b400503012a401049081c0c0080c8668189824540d0028901040f120705104103000c00034100f404102c410021040086540a00c01e0420000b407019090404094024801040042642e5250041000201a403195 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 443582679 1250 443581429 443581487
    0xa090506030712020d0203070216030c0612020c03040806271c18030620070b0a09020604150c0308060d05060106031e0f0204030507050105030903030402010c030e300706 74
    0x55011030b02e10f804508540d0b5045e06140000290025a80c08005209041c42c5c0a86804201d051006480c1c2110407200c3d0309250410490707604100070051490342d5001d101d8800c820804001402c09030140201034000ca1034100784042c00c40c0706419405070944e480319441c40342e41c0004210320100440030803107510000700c10513040e560760448200300100140c03070820003c2804000e6000d45544000344003041c04000201d488400036009040d40a0008000d4070085060748485a2045040c07038801717000c542c14213030b80d800e507005041811704611011130b021440c0c11080550160038254044401c0342c09000721030541d2a034590b9a4014021070091594a01c05490b0550000c03a0514250946038410300c05040c641e07140c071020750401d00c01180c41c0d2003000c4c004219980140e080e68400c0c140b040c01035096035155001118814032044080e0280400ca0170085429190780b501951642210b00061035042e840d0a9440316403100042005102e400c01601403100c0750740b252458000c001c0d59202d221504e5412 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 443583929 1250 443582679 443582687
    0x612030f070818120a03020d0908060c130e010b03060418390618080703030c0305030c0702090f190c050d110d090c06080a09030e13110408011406060a0905060307 71
    0xb0f008240c0d010901c0440c8001003400041c6015056200b51709540300072006010030b5850548602481300181c00440c0040c031a0302c40c0d1005003440101ca141c81440060355140e0f8010408408e0700700160010000017007203a94101400307940072034405102c00c900022500e4640141c58640480d5880381a594000718100061201c10b440441e00c00702414a4070304c41e52580c001e8112810343c05521a501d01441c000036450030042241c804690301910388020b04540e5075001c8540d58030040c419004868140050405a1140c43d40c1070700c01c20048020060504000c0c1c1c0d200c11442d13114200c00e1103181003a5080c4105da0780001a42c0001c810746a0100e00c0c101c86008003400c50041c441c083d29642e250040c681c0c2801005060481168816200c000c059114001400140d55624102a001c50321000581c2c1840c10030300f000802064059100090009501640e0300d110b502076481071410340c1d10707440c0e0740c200708850000342c94200c0800c59146191010210001c3c00400f101d1041030310030701000c00011040c81c02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 443585179 1250 443583929 443583967
    0x20616020a06120501080606060f0c0313060c0302010513080f0a12151d01031a0a1e051e060a05010302070f121d061c050604090c0e0612030f0708 64
    0x3005020400054030307110000c154540500b44641c40130f0a2500000707455001044035806440d01070002d61070100d00240c44203003603000000c9040740d8402001a201a06034401081c009806941d0741d9840390001420020b00b03584004e46402e2003883ca411400c000521010b040340e0300c51103102c1e001b94650110400c03d550b4201b8424611171b4490401004812040c50340f10f0450541c1d201a200c3d00c0003640200700070786501c800340001017402823401d88901103031048103d403030740c4611040c1300401d81480d00760262490f040052081c020b120b882e2400d000811207041c00707080300318103441e1170b4004500d044000100d0343c8002e13100b0380c1d05140c1e000600740c1c103101d900c405944255030880001100e102c0d04080c01080740d41d160803041100000e05c440b560740c40c13a001d011101762080152228540c1804008408020305025042e6030384141d4a642d900300040c0c494450a00401d00c1b00c8403002286004c609000003d000b407010b0702515001002410003047d100302c196070003250080b84054952412903c0c4000c180300c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 443586429 1250 443585179 443585183
    0xf031a010e01030b03030409020c01110a050d0504061b030c0f05360d080405011706010804031d0d051506030a020a140609131d01021306110a1e0314090904020616 71
    0x1b0015004c50142d10a030010700321107030104020080e05136280c11b844003071b00500a03090001740d000c01a1042201481d00107a0704507001d40390000d4241c405107088949031440700d1501010076243d0300700b0075000760403400d00c05039075200e42007241c80d0800d10150300001d4400003005030700030008480c064034151038407001c051114802a0a0060f086180d0500c03400d2504a40b090600140420f441c24002a00301d2810781d02450040c0c54110903900c582d40c0640300103800302844000e686200d001e919a07030303880d00344031014680141d010780001e07802801070350300c080030060855000303500c4a041e420050701c40110900413280b40781c1610b2a014030320780000710544220300500e07034400360556131a6220305142d40700003008044038030365600301034041400500b0b034021098803990303101e600c540400425015958000c030f0421094183c039800d540564441c1042100000040018800245840d0415802c00591003401400c1122a8104070340394000428080000b03000038094600891010340364001d105000710610f03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 443587679 1250 443586429 443586433
    0xb0411070311011803021b030106180b03210c0111120106120204090213090b0a0e0114190e01030201020709050411040b0f10180b03130201081801050411010f031a010e01030b03 77
    0x51485e0030700a6507030441c64100b5103041c2801000c186a85014400c03c0b0480b003291400c00360300d0844843c00f0000b4542801d81070f825002d910030f84182c200c1c0d1606030726038aa541c01180754070303032402d488120700b11480c6144101d1078500c00c00001d04182901c0501c00e0440302d5a15120754000e8041c03030790700064051a4090041180049110415140d03585040419118180030030401440d030a410048462071620441800c664881c0c010b100000d40c1c0704500152003000780260f13181d602409400b02502c141c96020400c00c0e0309100c014400c6680c144031000041607081c7e82400941801c0d2102e04031803030742e924600c1c0b085a861140c00510f440d1140c1d00d14174408001d001d50001c103900000036010b20318541c00c10120b048001d4000c10f0ba14000700a0b40e00030941a2036003400154150300644140101801c100d2403001c07000318807a0b1a0706c09000c1c20f03200300d07c01d40350f07150100c84071800540b4003042007411000b81803d080700c54030311210112403896040000d180403104400ca100058005103000100d064041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 443588929 1250 443587679 443587721
    0x3c06041a0405120a0801061229040b06040b0417032113020d050d08090f100b010e0603011d070801122a06091508071209050c09090a020102010b041107031101 69
    0x45d0000340aa0489280752a040c894100d080956822540c0508113900030181503040d503950003c0e0b03800c0d00d0f00d440a01501c0021200142400a107064010f0f42c4440420403000500f40802003a043c645282d400c41d5200560406c20460307444001c420010340300095540d885e0002402e009555030781c032000150054803401c3c0001c0281062515901200c5e8240c1c082981c0d0000b0034072403200010040c004111010160410100c080395010203001c03107041c85410050000b021498655032500210700038012104440b6075652415003099000302d000700440c0a020740c480040020350303501828001ca441d03006500c2226a2020440001000e0b0b4840da49900b009200c4c10101d03003290040c5c00b042c160794034504211400600c401044481b6107044403000300203000740040245250480e080462418031a60641d90f51001c2e040100d42e056100303c07490707585d5500a44219007956020b01c5002c0400d2410f0f101400b504c00784d6103126009200381107004041003000407611030b414000b03601503608020500585030031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 443590179 1250 443588929 443588947
    0x901090c09150305070f050f04030816020406121101030603020901050418150c09080708070e04080c0d080a050901110f0a02250e0f090c04020c3c06041a040512 70
    0x305005c4402c18007242000c510700842038000c0c0d007038413096550603009a18042c2903030f807803e030b05400c1181c1ca01103140308500701800596440c0548005404032000d20301c1c01c2441e600b0040d5481d00ca00320002d0615148c01d209102588a0f07078100c0b81541d405481c045980550503507840a11443e04c0d401602d004c1191101001010341d40d04041c8043e2010390b5112610390700c8040300b0303499404134851a08540d02c00c10301000440c3ca95110158801d0150a030b0900f480007010015081810031181e0f000000e050301c003040103a080034824580c22602c004003c100c00c1d90b45611110542c81241c0f1200c60070303040400c080d1804c1b80700304131410845003c0228803c1c07100123050440c0561520380507402d0f104008030001403ca000c1c241100d44190309000c0248103a001c50814007000398095004103481e4052100d00130035188400300d081f01001c0c2010302c407813071190180c0c1086120000c882242852074001c1c1082c40003080780c41800040082c407080540070b007a02c0760b107881c918151904000c44075403a0b000c10340c800c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 443591429 1250 443590179 443590181
    0x190f0c12121b17060d0f08070c0603020904060b0703090e060a0306090803010e180705012303150a0812033c1e011203081801020c010b0307050607020901090c091503 72
    0xb00121507243c0007105000000103445011044031440d4100b25200c0d03500d8003144070441010301080c01200007516001143d10f801c00008059082440401c4e000140c41d0180d003003074030500004048144040342440111b503401042411144648454050240081201555006642e0004552040f810001c48903681391000e01a0000d11880000c0402400040e488880445410384a0000c04024220013410000151035a5038102130f504416124051411074401e000d900460007501060307803281d2305000d0001007247c020b80c10341101d8065004200c842c1303102141042602d4101e880e12038034614030b06102d07503989281001286a1110b628400000746c80585129414030f000c0e820107100b890090f001020240040082031040100b80c40d0390314180c00c0030a12840c3d069410015101c648012001c0320401c0909980180c910309a860b50344440758901885c0c10400000100300c02d85086080c542c164000400341201413141200b4291a040e061f903900d849004200090180280f60f8000901c002c00018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 443592679 1250 443591429 443591471
    0xf04080106030c0902030606190e04020c0105090f010e030406140c03031f0b03010b030f0702010e0f1e0d05031909060510330f030e060903190f0c1212 66
    0x581c0e110000c0f100410fa920040c000c0f24405c520150501c1e241041800c903485521140e00c0d01c000c00c101007690b42c1c030307403e80e21030004140d285c02008c008a91402c004011a0420491081c0c2d040c43e40e140502d600203200c0d0100c25a030803140c803410112429840c080b001d00541c442c0582c81c40181c0030010400840e0100203850001189603444030018080c0c0f200e8420747c9034442030203001105041071001480c0384186441140e4800014800400c7c05414400a81d01c4c2c2050283c580406410080103851420240d40780810f0050003000140030304041500050001c0c8005405007601c02c0c0a656844810740e080e07006040b0321540080204001c1c90f101000b800312810500800703004410001020300900e030703a9414500046800360704103445000c90f43d030a440428045400d60249500e5480c0a151410709020403480380790030740c2c05103a580b0020036603100300d5868040200d06201c420307010800d41941c402541c0e403040e83e000802e021030a5541c101030b00d1701e03496180401000c90801078204038542d8414084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 443593929 1250 443592679 443592683
    0xa0b060c060702030408210304060207060b1201020d0c030203011d1f12061b092306070819020f03120a060b031009050a0b060304060f271a091b060f0408010603 70
    0x348088420315580200403c4000d0800c480350a1f06002082c007003006640140600c4e403140c4000103604901c100824035140900034904503d950210754074006c9047c82c080d80c0400626880e0443c40e56050003207131803d80c0101d034450750200e98010b0004c1c846030340b84a06030340a0001c0c0325904010715690001100b4070005150201c0e8903a090010080403103614a04030000411192500100d0604100e000d043e00040002c4040c007410020710342d1107060316224007c10f81240505250f03a40e464010b5142d4408281c1c2c030101c03904641c440700c4a0443c00d000441501c8a2440c4980701440f82d44440c54200040e00381c0341c101604c1030400006100725066402c4200c01100e0310b201d014009669081e00e8402165450540d4a810007000c1000800040043e03000180b00d110b8490001003480c4201016820031000807094003510080480040600910808101c00380c2c0d40d03407030302d1505881d0041c4111385561244072190741400d001d206110040daa008103a442c045109540b0319211a40d9101540c081d11180c402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 443595179 1250 443593929 443593933
    0x28050603120a02060a05041704031a161d04020405040e03070302010e191b030b0c0c01140408180a18020d06050a03020a17030d110315030607080a0b060c060702030408 73
    0x15481c1032900c1c240d55044100d0b801415aa585e00f10b03464018180082c411641010289002c0198041140280000d0741c0030740701fa50440e049540041c1d1706008060043c00115800103540f001403940800346111202c04001036481e004043d00c00308000e40141c0e007009511a0600d80c0c412907620000006e0300301c1070b010b40d0080c0641c0031280845902c802207900014800c10f03440039a40302046640d995451400f18101d0f01400080e580d1f00d0780707416490143e90089052034001400c00b041c0360240a0158440c0200350050130509152751148510320502c004a50320048581410100344d68829942009100042d9042880d0442801010096000074446507900749020808602820511806000d40740c5c06080c1e501d9040c1040584543d40e901e0300e00e0400c0d03d00c0b040010f1104c0200320b009041d92000c0c8400a80d40b03034141a0304e958509120341c0340c658040d600600811465aa11814194209400a1001840411440c007094040c4104181c4051500c01c100a000c481a800002401140c1240d01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 443596429 1250 443595179 443595193
    0x51303030f09110f06070c09061508093f0a0f09050307030201110709090c05040f0c090b0c0a0b16020f03130306020307050c0a0b07030609180b28050603 67
    0x20315401150450302001d0f140035503655211916040680403082002c6006101c18100143c90f5a42860018242c00a000d200c1d2640300030002c0140d076041070081c40e46a41817030991490a2280c4175510200f14100702c010b071100708200880c4403414412030129149540100e00a00d100e46406002d56000c0b903042c00002d21425121505c192081c1c2c028000d5410050142244514680044900c12041c01d02102240540c400001d0b5002040c031800032201c0c0300e9941c818a0615202c00c20084422000300385404904200400688a0707000c10a002a200103040ca40e494407100c640c84d0340f91102c41c050041c00b17010060148000b40c88000e0100c59200c4203503003141c9410001c17600030f80e02d0b4010b200014070850711070706050001560f642c001d1584284245881400c040e29507045a240c090401407d540d101351000c24003540542c0741c01020083c00d0007100034040d089401c4046507400022a001500310f500c0c0d0400b040d0745610318050b200e0442032207047e020942c0e50844000c802000c0035280f86201b84110b0b2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 443597679 1250 443596429 443596451
    0x7030306030b1006021504020102160807050a090c2c060417010507090e0412021507081819060b040f050c0a110105040b160c0503310b07022205130303 66
    0x5103c501500d00a901914400c60003124030351490348050f1049065016841581d4108900340403180d00504e9054001e0600c00d20f05418000780640b140c10810b0510b06001401007a6608980c103a0920481c69400c88842c2c0003110b0111342800c80446035075404200024000346c121161a804140850080d008004075120010309560f0b4845910400461044910000d40483c664480d809903040050066400c0b04c800d894203144842001c40b8081c01041406085c001e076041c10780042c2c80b04442440080c80c2843c0040307802d1545224080d0f0040405407a4016034600c4d44468010b003003107020040e02440389003000f400c0c4031099001401d004000401c00051a050356005000d82c038001c0340c01144151454403640116900c0441e102c03400e0050120001c51311000540c2013004002443d5000780411001020030b090039a505565440b10400782c01c070010502020040d54111102d040c1d0445019800024000401070308048118501e207c05203458100310103980d0740c07000031309414130070340d004c01049502d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 443598929 1250 443597679 443597701
    0x60602010f050709050d060204080613050f0a0c1215020c010204050315070507140c1207050312280903210f051204060e0109060504060b010206090a030503060402090d0807030306030b 80
    0x301c40d100c0c0021308a010401c0a8108050b2030710580b80a203030090310b401d0302e484800f8a040401c0d11480c01034954408101c0c10700c4024800c80c280034020070041e2070001c005450341c80410045000c1ca81054084c04200e07410460b0b08800201c80c0d44042d5015900c0350040040d442c001e412a100e05802405140541141e0103070020150b4400c11180c3c40759401e02c41140c50748031240f0f6104071010a14850142018002e9481c2400320450580510050900c0d034144020301d4106100c0c0c0981d240f456800344915645888000346007480006425840843c001c5e03540c2040341c40010542c4041c0803e248403c665440c4039542920305450324207521108052402003504403520711981c03440c50070134100d110110380040c100b40c00c8001b417401854000b150480306070710745004441c0242d808503400f43c0d480400801c0e558050004a5120218078081c00e284942c50324040e1052200414951003154002900009070751170385550407041d80c01017440d40d1644035502c0c006c0e005103141d001c00d0302c03c2c0a100001078045440d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 443600179 1250 443598929 443598931
    0x3160608010614031b070f06050114120a02100c080309010603230d0e13020f09030d2a080d0609020a12061208090414070f0e0409020d0b040201020a05060a060602010f05 74
    0x150000891942c0e85c0c100002c07540c950740b24246031100f0410020740d400f15216140034003145006080008007940f42c81007800c0d21f541c03001109801003031080b0b4441c00c00000420041150340d019200f50780a080c0d2040c0032600501d086070000d01e03035400402032010441c01540454240c91082190049640d28079051801015003400403000b01d0380000300044506118205081e081e4070003514005000c41c000c0450010798003d8141031080810114034449145420004541049158180078603581c003620904d10740008580d0a072030415542c504000d0400c4010022a1844041c4c15000c00c01140c881400001030350042c010725000030500034224a804119100780012100391444600e05911195141280c41d0003407118135a01642e999542c1c983d03011301c504a03501c9038040c0d96540481d0540b1401c00740c03e0400034400030f401213250485440040c0c481654071241300b9080a5408915912840102d18005050700000d0590144030180007a051041d0401d406030382c4260001c3c4041044206001c0480700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 443601429 1250 443600179 443600207
    0x30d050604090c05040c110303070c0b31080c01020f030405060f09030d0b04090c080c011b050703110f130510050301050405120306013b030a15020c030405031606080106 74
    0xc3c500d80b040040b403819a0050742ca0588070300300b81d0500b28a10420303d013103801c200c5541d008544445104002c114040c05203a80c08244000120304d140c188668200200d251500480c0e07840400244540900c2070710400ea034560245003000755903502c03003820a44069081a80e007242c1910654000c5511030a000040d030b841040340000031418010220361050140c403106196580090340c03054520041107040701d861024015020040102121600c0014090050a4514403032481080c0c1c24000194010407080c0490303405c40b903440114410075000500c07107886004031070780c059220301300051018040e402a5110382c502d4070030310f180c055030741d000e260a845045400400ca9041014104c50651103080a15040101854005902d0032403020a0000c400c2000c074200202c00c02816015800006000480480105801a0140c214140d4a0701072040380c03008640c0829401082b1008101d034100309450081c1401070846d1030340c0042c0c17490b1074580382090188500042d4031000104545000710003240101d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 443602679 1250 443601429 443601443
    0x4050a0902010e10090b0f0c0f060106090b0901050906071203231b160b0609060f06070605070e13020715020301080a14031c0b031606020307062c030d05060409 70
    0x43e40004102407040480009800e01211100c045090780109003e09039081801074856669160007c0480c034100044034130304043d42c05100140007065104501100301e5506200c015180c04c1d0720700068996000d42d400040c1c000c0c402046035000d01032940d4003551a0b205a8034100900d40c0e5110148030410040061001c09810304008980000c911400002c08a100000c07200c0c00c1c04580488071003095001007041d90180b000d80140000b41c604400429000003080f602c41c09600d4990b00400c5031401070000c06468140e81d8000168060b014002035145004010103080d012041400054025000584140c8000d040c0000d442542075207442200d050319000c800500b4074050540c1c0300c07844810580340d800401d00080c041e041004d48a040050300c103540f444c00105e00700c40d44e40f003071501d888035004550180d0850703404104000340c0c0100032919400d80000c0e02040e4144820400c5440340c0d4070341c0d903009030441400383d00c2c220b4040c084003401ba42c8865640900050301c4100410003a990910130203440a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 443603929 1250 443602679 443602697
    0x7020307140313050d0606090e03030109050112031e030e0f03120604020301050a0b07080d0c03060e10030b0601030c11120301031505010b1614060403050d20070f05070f060e04050a090201 82
    0x40c41c1407107040885d035100700008a2010740b501001810380e24a40246140342c0d10200c010b001d4944203000e09409000303800c030804450540780c0c40040c28489401d42c0c1c4092090303c821804e02203840b13900020009941c444c21070b001401d242130a0f9540e80e014241e60135100084501007900b03441c02d8001c0741d04980700140400c800c1c504046248045611611040b00c0100c010000d25294186a01402c8460482c41d01c0000380640b420001010402c401403400303804a540300428070004000740c8006402100078039001a60900d40c0c10180c03940300100c000c0e20280c0c0b1448141100b200c03041d03001581680e12840501040440e11100c040030340e4401e0242840406081c00704411102c1030701440030001e406201e1404012210104550078007005076001d03400a074000640ca80d10011a0185143d1945107403703240003540315080106d41801810341c002c0c4902e000344d8000007842000c00100010700304501079694015501d15000d0044500c040b07040d0b001f6410b000c00551002d0740343c8280840150180c4408400f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 443605179 1250 443603929 443603939
    0x2d0f030c01031e0501090b0111190605091509010e160f0509040627050d050703020a110a0b0c1f021204030c0c15050310050909070b0a030f0507020307140313 69
    0x1074024540406503110a042110083c0b6145000e494001c3c0112607001400d00c10060005100c1007401e01151038650000e000c3c0c034500307000e0140c040c00c519000f00700040d01d501c5a008030780c140704145621603540d051660a00085c0f08040d80180304912900e1304860384082407a19100041e0401e2040b5003104000402c10055030400c030b03080d00c0c3e1103440340100245042220880c0400c8200d802103251100c5418501041045001c00040340e145209041490800402da0341c000c1d42d03600e00c0c040052801c0400e00c400c11030350712001a0303480940080b01080d40c90f40e1031002ca0a5807511007240c584801011040025070795a6144200c6061f06c41c03c04000c01e265485445c02e031140750303204008849a034002040059a11810039661509116a41e50190349041207101c0e1030005d4890f8110511441446c001d0041600001485608136840000ca00e62941c0200000354014044c480c203000c0101c0c201803c0003c421fa01000800505100b0701e4090801d01650a00a941f402100c001c17001074442541c0600c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 443606429 1250 443605179 443605181
    0x1b090e04110a0308041202132f0c0703031805011d010c0201110105090c012607080a090615030b0f0c18041808071406090a0201030c0e2d0f030c0103 65
    0x90301c0280041105079560341c2e980304154020f81c171000084011741894821858002c03001404001842024010180070306001e1031401101c01510b0003052000311000c8900c1c042c0c40613200b802c980c0c00140c0d190301e541c074240603040b2010070710740d10440d00c130300d030004a41980031380f0381917025003000709121b0340c40c40340013005652084038034605038180001c4000e41c0314803c2017405814840e045242c060244402038400141c0206541c03000060003801c102842141c0414030641107034010000e01d0708084548802e40640300600040340050040ba0800340d100c40040c40c1c500e40001200e1190100300e80c1f42d51091441c150000c2e0943c0e551929080400000680d80303170038016006001070007000010308d03000d22102c0c400070000b060421510300c00701140c01801d0001d5803141d0100503d081e00602000d1078401c40054031a02440c40c0207050643e1680002841d84c41900d11950010001d0301c2d00c1d106007403c691241040a1003241c03c00c090303580d4060381c450703410300c41c00c0c1885445001e8024401614a480154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 443607679 1250 443606429 443606453
    0x507080909180d1d0604080c151e09120a050a170c06130c1508010306200c0f01051003031b140d09050109120803060f060f07061b090e04 60
    0x7924003a10302958040d1500c148403d500e440b095032101c0254020414980030581c000d001041c5c41079405000410400e0004190725180c074804445810244000c02140c1005024042601e800c148002468050f8902507030010705500100719030014074101840c04050380c5503141c002c01080c6804c03e411550000b100c0d02c0380310400383c01c1e092507142481d48030040f0b985015000c80f0a80309102180d24442d052000c9803842c0e40151103c02c00d8000203050b4040050203940041c0300060040790b58a80b985031141292003030303030701d0060b2507004c0e640d80f00309040013180e80d1241640001c00c10f51800001c2280203c900f000d0604483e03043d22120f08244103012207041c11440c1d403105803100c40010407140b030a040140203441005400e82c50300d8034400d040500040580045400041c880b20f2011080400714043d42c0c15294004400c0701c0320070490070030a012a600d4040c0001c10841040f01103554400c10025406c06240b10800100141d80140242d40403200500a4441c80850782828004100843c64080120b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443608929 1250 443607679 443607691
    0x90f07260a0b0d1511160b010e06090423100906021317070618080708060118050105092215061a07021804050a0c09020a20030a0c030201090605040f0c060507080909 72
    0x19820002c001c01d1b40d65210450510481d0882c03840e00042c4500c0803408039050b0003036400d5440000d02d2601d555009480700c0d044512400d440614080354820b4441007090f0030f040d040522051003e4085494183c001c0d402810310100003031120500840c001b44031070103a08038050017000815445203454016951130580016401c10a13488440101e6004000c0089000414201d0000c1c045c0703626217042003100d040710318214000c9600700401082a9a900d0540710780100b54650310a0b00f031000c40748002211f0300310180043c9208034136480050340c102650300440403245501e0f81e1401c00020100e001c00a4072404800951000711500c8807254183c00440040d4018811000c49100c4a5903840c0d40e107140205900c8642d5542e0000707428135483d5170001d403800c22021040100f007240f178043d8048580380d00403d40c21100300410311026500349032003500050b00c10703038103c1420405400c06040050700615190016150b030002c803080040d0b610322600490341016080400b250030001503c0402102c0c0c4070107814 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 443610179 1250 443608929 443608961
    0x408160e25032a0507030206090c01090b0313051b1311030403051c1802040609150504051b030406020406030605010503012709050f010b040614090f07260a0b0d15 71
    0x3580e003103c0e04070500b6501c00002c2d00e50130388810552078006e1900100606100f4540c0190300c01583ca41d811440c034000341c03100041030540703035540c4044c034040d03c49921030081c0ca944a100b00708041d4040d400c0001501c1c00c016180c2d10105414180c124080d60741000d40801000401c100103000b180c0700d5001b41c015403004860045998000a0300f140c2614801040034803140d4a03c540c501c21454144151070040001801c240401e0721200e9500051035564858980120b0321000081d942c191007030586040c000e22a443c60341c0300e0a140c00c2040081d0480e01520011a16042c000704482d0b0191058134120740600e0310300d00c036244120144080081348401e01c0c103055912001035800195007400841d041c0c503400400040c0b074020b440c0401080d01d115501030b40403203800c0c40170115071b0344400d142d0f50392000c280c2100102039240c1d550200c500551b034154800d5a480062040d4100307a00303074403005005045040302403040f074008100300990224400d00042010300300710307884801055150003400a055801d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 443611429 1250 443610179 443610221
    0x1060302030a0809011206080c09060a08070e01030212070e070c030203310b09060d0e070b07080406030609050c0d2412050f060c120c0408160e2503 65
    0x1000c42c1c0341c0681114121115000860800925688501c404178043c03a402800e0049501e0b002401d030300c0d01240000240a005501c002402c10303150380344c084000380020b40407912207558804071044c000d9000e0200700d00c101840300c6010514040001c621045e42c0d00c02604499603125494180d07102403040608800307500051082c540c64080c070100b1003644415100000d030250684d0001404030038140d0300070f990451010b00c1070180300d45400d02a00c81d090101c50000035848003260810b032030419554410311040e04000f4000042041c17420140c0100c80d100d49040c001c5940b540c0c1075805a8208451590032510144014255504103403c16407800da110602c4610485502000c0703081100e080c1c0008080070041c2d2840c0041000800c03030940b00c401002d020304254100314015015074842e203411080d070b028101c00442c803442d0f400c074100c0b00141f5005040300c00c1d032040b00c00480711003a603030310802e56508103490001e00100b61608c1d041d0307480c40c41c80080102d01c0344001c000b580207107030b14114240290340340c2c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 443612679 1250 443611429 443611433
    0xe0d0807050d061d04140d0906030b2b020117010302060906030a2004150e1302091201050708040309051002070918080c03030402090c0c0309040504060f1b02060702070303140c010603 80
    0x104c080041c41d02590b214a01d001e04040d01c0960703e62901d080183d00001200c522180e00100f45c0c0d0075501c19207404602ea0100c0d05c0042c9040007084030214550406a848007140b00d54040c8142107640f0031303243c00c01d2115000442182043c0d00b440040e400102c1005021111300d000d0005582c041030076840061007003c0c803001800c0010405800c00081200094280511240c004000800301818034014803080c070300d03101245114230b120b00050811034000c2522251036480d042c44144c1002841c000300507034601110014520741080d00d0983c0800c035100000310702410300044129004003960000c08080d840e1004d200014654144581481c4400100080028510a00900d4103411510003161a07003411b0041164045001d4416583c01004000c1d070070640740084140c2d200e80e40304486c0000c4c1596941040c1010700281d401690351203240074a5090b40e5056200b558038007002513801c60342a980d41507001e0340d45400500000d03000c140041c40800701241610b004201c46410040040b690b90340d26 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 443613929 1250 443612679 443612699
    0x30c160606091b1101020f07230a260a02032703032205030d020a080d060f0b0a03140c090d14010e06072c0105070303090b0106030905010e0d0807050d06 67
    0x50854540c040440b03c10003455101c11400e018065500c000c618042c80b001217000f00e485510070090540103140082408a074245032047d1924101d481500d105144078508400100c100d81c441d410300ea21080154403000c803c801c01c0d40c0b1499411740003075103482c00e8100c8000c41c0d02200244180c0c81c10f0303820402000f41d00c050024118604072002590340c5104070342114400c0d56550b803c0745000c2da00185414080d142d00050403564650041d46155035a0110f0b40e041c2d000d080c44c0d400482c8a04400e6a0000d1464807141c003c10b03030105642e404005c3c60038105c40864810905480341070010a0a2081c1051441c1000f44103040d00e220b032048000060603003010501796840040301010f1500b100301008041d50300302c2d1440190b04810b500d02c111441030144181541d19014010b00d04118000c82c1500400d80203900054546800014003c8150f81d1100002d0240c40501000c803650b5003803408600706040c0c0081e40302c410129584808801d50b5410f8822150f030307004401002c200c60788841c400101080a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 443615179 1250 443613929 443613941
    0x1a0a0306050a0b1e0111012a022d06100609090b0a0e04060509070611030a080c1b0f1005040515090a0b040f1217220c0e0a11030c16060609 61
    0x3d03a0a03010311321503003030000f6144140d00d510112841c0d0402c6650365002c0c140c40e100000904c0d43c20602001a00042c03c12481d00384489801c41c0300c200f0305444403501d030040300e0005014681e4030040320b001c0d42e40c10540c1815104076200d00c070003249000c24184000d55080e00122840c1c0f030080c20030b4050f540e0f10400c5020814041d42d0581ea156610028022084c400f2702c05940604524201106040000301416a49120b4180c0c20803c00c0161004070382e485071541c0c01c0703c4d4601985084c10160440702c0e81c149880b502c1c6c0120a166901c602c45001401c800e80c0e005030b41c46a504017014080001003c0750440055100800c6601c4900030540000300096404507503c0c040c1d4001c0d898030a10040b43d2500100002d407481d07014050040340c080d07903103580c114030540342d41c0500d03c02032104903c0c00341c0c03280c100c0c0050480c600410894000401065103080d50904138868905560f003888800300030b00b06d0003a14031040e550036105010401c080420341c0e00c1c0c2012500d0b0716104010020b01c2d00e40c0d421440d411640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 443616429 1250 443615179 443615209
    0x2070b180d0c1409150405060d052b020703150908070b01271a010c02031c11100b0102031e0d020403050c010f090609031401020408010e060a1a0a0306050a0b 69
    0x18251400d000402d40d08161143c940c8069035030744414204a0718056082c500c001c00719201e02d4840c4000f54032070301c9203100c103c1b602c1e0344032040310b40d0910f29003205000c0710f260495640c0104141070740c00c0055031000554004a0f03407c852040025013040f4000c01c06000b07403400c2655640d01c00c01c401800101e43c5182c181c002c0001c60485810041c0c0d8200c000c4010790035a100c1e500d060f081c80c814a00402e11300408010203502400c007080040c055101280c02c00515020f05003541590202210401c4e40009039450340410f02400d980110780071150020840d03803128540c90060f0300600a2400800303080321444441403200a0032800c181940c2c00800607680903401c2103502d46c00c01e061b0034459580144643c4001e100074140400ba241c100400145a8a400d100181c040c0070f40c4a11000c54000a5040350b0141c010700000313000010240c400b00342d4800050710307450040c0e490030640b441440081c80a85054000040000c42410701d541c4480014050180034030180c1f03591003125001940d0740030040f1301601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 443617679 1250 443616429 443616443
    0x907050d0e06100e06030a05060a0b040b090408031b040810020d05060109080d12090b130507090507080a1109041e060e01031208070207090519050705090102070b180d 73
    0x44124104007550916198641203510000c10310a429144a00d0502a10780749481038840c1d648031400245400d240d22000303003260203003138188140d107062900428005e44081e00e05020790030240061050f100380485011b0316441c0e050000c2003445c0e003182030001b01c05801750501d80c20143ca9222060800c035100200350b0344a0742c0001c500000d500302d8010740b54004401d0a040503003510340040030303032151141c0e4646c0c2c0403c000c9070105101000c080d03118510300c94000c03d4800703040c5040340ca248a0000744990030341e5544180e000005000040d4003815110300800d0b601c0040740d03191852024003a002d64104244100b4042c40320344556152132041c4115140920004140c0490726003541c000c03100140c2000400307080000040c000704081c070002c0c40100d10645010070180c0c3d0303018405c03401d04801c1d4100c81480c0d0b003460240185000681c0e5803450603000c40408101680741e02c01e013a6440d1090864682c056004a8002c0100d00d09400107401d002c20342c1d1b0110101101d103840010340010540408641e04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 443618929 1250 443617679 443617687
    0x7021f090605010509060d02101b0b071b050d0c1e11010305151c0204140f01080d03020c1906200706060909170304060b040216030f080114130209090705 67
    0x11000d140241401091300356500d03070003400c0c000040740500d41000c0029016003800324008900511812842400002c21060565001050300c3d04002c4004241c0b55200014500b00e80c1d000390001c03201585002507849801010b06e0340440d034040d07c10002813002a19868082c1c1c0d03400020a0000100c80381c9a03102e0210003158044100c0050700b02c51000d4002d440c540d901a07001034070798991401c10880c0d0001c1e42042c400c02c50031032001034007803ca450148030203200c0030800d10199040d00c15419043c2c401038002e450007001070000441c02c138029200181d109600c1f500070010487d000014a900c400c0c007a110200c2c0d2002c6c040180901c0d4842c41c411103444450002d05132050011510070134000d00882081404418000d4507100c000441003c201c0300c0c1054004089801c010a59001d8407280101600540d200c4030740b0341d8079508480b110041a00442c003001000e103001403040c10414141e0785040854902c0305800402c0c81040c80c03046840042c020703402c02c0040580d0781c0d01d82030944a00796a41e03480790b071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 443620179 1250 443618929 443618933
    0x4050d020d050a140906070c060c17161103010e190c0b0406050906130e01060509011d090c16060e0303010f0f12080a0203120703051602061e07021f09 66
    0x240c160511a480304109041c0080c42e91984d01c8141c621004001e09941a21460340c603001819600c161100100110f010300d2002034203e402040052a0718090010864100d400442c41c132410302c071740c011480315210081c2900b000100070020383c61400c1d00c003800020b100c0c1581d021881c50f01d201c92541404200c04c8411503c20488400b064001401c00000c00350f003000d10313086020b8828050b02e101d40d44241e5020071130000d00e81107400018002d00c0380824180b480d5a642002610587c8481d801c80d0018a164199407800c548010407602000b0003d4080440364ae1014100710003600481495103515500311b541001080c000d0059003600780720b01c0040d513503952411205086107030943d44110b01d1a85894010041c1c1e008505034009150381200300540e036004035030000ca085104510f0f40030501018082404281036150703001704d100f2100d0b0101c2d6038000f00c1d40082641e4918003100d0300030a100d01c4401e3b01e1100c150103089280c10003c0c2d0b004035258440070a56007040b5030b040b1346070354940d0f6030b5075428401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 443621429 1250 443620179 443620183
    0x605090d050c09040804150c0b0402040c0c0b011508150907080a09021503010801290d0f060f0f060f080304120203031317190f0b1f0603060503010f0605130e10020304050d02 76
    0x87c0c0003580c2c18060f4440d052559500320034080140040c5c4995a078cc21504007041c0a07071070f081c14056000c00c04807040e6841c1c0100c081d11406400e444030014030703460000786a80440c0310520150032070041050b01d07140d4403440101c507880402000c2000041d15141c10000580f00c1070300610a0700c002208454403581041d03102402c441e4802800c0201c00d4081c3d0704a00c85c2400c1030030941820109032079840c0c071204181042c0c03d8000380304900515841c9000c1200c80100c015a0000b609594800c806100c1c1c6a40c820010f81d40d09070b42d00504030181c2003000100b0281d1210780d00041058030107820380e8200302c144158000c07003003034a03032014624034000c0041c0c8103641c0c010300401800b0919140140c0c2a55283d880d598460614114000c0031090b104002c0380000385e800c4105400159040102d0044c5238407031400401130a410701c111800707582030800c2c60100034603a005000036650003905c00f0501d1030200340710502511000004007854000c0c1e11404044100d01c1c0000c502c201d0040703006003480e1040840080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 443622679 1250 443621429 443621459
    0x190303090515040b0f0703150806040b18030a0503060301090c08071a07170307030617030913020a050708070305040302090f0114030a02060306120c0d1415010605090d050c09040804 79
    0x141c480c042008001c0000c0c8034050140c0c02484217103907a00c0c1c40d540c00e10709400a040e090007201074042001c2001690313550010740c40d4451445184d040442d500e0310b90a541e44c0c038080b1441c1e210113802c140902c81c54180b28001450744604003c0001c1018941b45c0c0b1007055018082d04501d240360002d06040c00400c00a200d20b0f119542030300d41d0603180c000c5d55151281806400325241c142d00100201003543d00c0e100c0d030000e4001d8500c407440c4812100c2000a8199607500440c0c4043c02055441a0081800c0d1284203540410070641c403414906020707956031052942c00500118184203080c0400300141c1c6503c1c0e0320070b1186441a41d0313440340303504001c0f40800340b03480203908920951111203281c1c0180c4420b004d0741d0704240282c400200c0750002d10401424024134204590f007103841e200300b5100b03102494150200d500101020746860308008408115404002d00841d8081802081191458107002c04154400341c00b9806a811301c842e11341c005286008140c40540d280300e0089000e100c400e80d1801d1712 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 443623929 1250 443622679 443622703
    0x906020d0e010e01030504021305090d03140f010b0309030d020301061d060307170c0c12091017040209040c051e01080610170606070803040804030b16050d0e1903030905 74
    0x181218140300e40008101e120650140c904240d11b40010800f103440c3e065121b0045d40750f03148248600d2401002c00c559a10800142000290421801546070b13401c42500902400700194100201e80c24041803003540c0d40701400000e16480100f01d6032075010342c3da20141d80078110b560f403070b2403d260182c07410f0103408141c0024548903480c10810311080c00d0300209910410b203001441d0300044c1e40c1e03d6454104a0143c20030403000350141d0000b1103000b03110f60000340300d0a1400c413020850040101c004441e40c14280b0564449001c622005c50094079003009811b84c418400c0340c01c007207459103900100c0c0e045103c1014060803140f61401e515415030f004828550702400c00c1da5568000f00310020010a2540074000040c400c55140c400300d405034544108070307424590450002960b0b410503182298259105202c199030f00d20303150f000f00d640780c091113000c0d100c8a0055903c46041c0400482c0d614010310303030880c0110755481840c070007036440d807440c4401c941e046009450000f000001e40c2000c43c207060700b030452 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 443625179 1250 443623929 443623937
    0x14130e130b01030b041101031a01080a1e0204051806100c0f2111010213120212010c05030a0b011d0f19120510050603030a0c0609020607142a0d0515070906020d 70
    0x2100001d065427109041c0b907480c003480c2c40442c42c0c4440409000400801c8494420f4024a2030495911a1560001e00407100e0a441140c1203040070b0020710703a01001560947c3e4041841c00c48941136600c40c03110000c1d400c3c083c2c03102c040d1039041943c6140700d0100d50065000c0141c0c1d10a24117180b5500802d8074042da000301c000a510f00a922031288001c0402170088600510046645805640301c0076003d0399201c900500800c03503603c1081025016070400c654814417642443c2c03c02c0c01551040190b210300c01c00d6800e0a1a03110102d0040011001070505016040950103083c600c0304803126401100418004080300e040080d103013880c1e03041c01c8040001404c400d05001c01c0c032180391070000c12070303030036405070b14160a901202e442c104010300150300340650301200105490701844104046107416024120880746010002c0c910703005540b003000060107080d0300c41c48420800c0c0c1808082a4030180c818810386500b200400c1000813013010603070307000b800500441710600846d40c0411107007403508400d040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 443626429 1250 443625179 443625191
    0x507080d0c03060e090a0c271401030c080d080f040503190e030c0a0e2703030c0a110c15090d08031311030f06011a071a04020114130e130b01030b04110103 68
    0x503403810241180c8161035051400c41c8030300d800303450b01c0b04c234043c85441115002c0c0600400c40c3c8107001c4039102800306840509200500180980c070002e0500d00c07058803610781904540d60a42c1401101c48010000d17181800100010345586800001950506803142c40d000d500c44050000e05160100100740c2e03078028107201c4400e1000c1244240419071210000c1d031200340480011080100d800300f40d80f00340c54148000701c01c0c0f080683d41d100c050554444995120041c244940c8880765941c0389404600d80c028600c0618040e00b0940e40e80200099070000d41000782000c032030b0780d030040143e004940008041c07000c2061801000f845030056220080c00701d0040c110b1a81340c000603500c50700188600c816085e021100c0d04900e4054009854000d5001004c030b035415510800010722850341105c00700d00042c1d00c0d483d448158282c4d00180c8281c40030342c24126903614140744010900210241401407481209a1510005607841d41c00b10b029500c1400d200b006418240340c103d00304000c0f8980b030340c14107042c07a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 443627679 1250 443626429 443626433
    0x51e03130303060506250302070f14100e0f0f150703080901050117060a0203060301140109050a05090718020f090d05030c0106210f0309080601060f08160509010507080d0c03060e090a 80
    0x35490b0101c101030034046101b0802070f00e070031f906d411016449910000f400d003600203002810601415510b660a4800c064524003007a01100c1078440395959030761203415000075041c14103207022141c907803138406080401c3d039000c0415112a42e0700401e00031400034020404110a2181c2070246a0042681c0001010040c140e20441b0761606401400d00e926141d000c00020040e41d000d4016294014003042c060310300c0c2d61648903d00c00780c4030854407180114182030100c1c0402e10006102822203104003032072a42030f4842010140a5406600032800316107084c03040128607642d0310081c8070800c0c441d40c011659841031211450940700c4540c4032a10180b04084500046400009600070040d4041c0c0b0408090026144c203640000d1b064200b0002480b4840010601035000040c8003240d02664607908030558904540b84156605105c8210004800b48600303101c550103600500100c030701c01e25456040000c0c0d82c010070101c8203036440d5180060b45a15081240c48030348186603821610f0360001d010880b4071a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 443628929 1250 443627679 443627707
    0xe100b1603090e0601020c280314010516050a05070302071a091503040c092c071406160303180f063602090a0207050601081c09080607051e03130303060506 68
    0x600e1186009420301040c21102504102e074003d103c8c07203880c1c80300c00c80e50380701d04160000c00181219022b4940c81c003404582c2840503030445d80c1204900c1d50342c2c81c0c90000c40d00030840b025000340408500f503101360100451020400401c50351075803010085a5224038042c01005150007500030500344c900e108205000c08145008112000d80740300c110046010450751502d1141f442c02e84041c01040d141241300e0700c111040c040303080c8003118289140110852501000c00484d4031490201001c00c251140e80600002d009400c460403500c0223108104905000f81c450b00070b984c501132411211039980e100401c4594101d900c0d12045680c83c0180d940c9840b09514208980f8000b02502038450f900c80000540c001d00c20390112420b440c0d0200565201b940d4410f9450b686400c42c0e0300107015455420640180c251140c2444c0381200c0c060030050006841c0c051040d100c82e40814800d80c0090305030480180c00f01c0081c40154040e000030840308218003003909005003203a02c10f404c000c2c0708107010003054404c0010307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 443630179 1250 443628929 443628943
    0x150f0a1b0909110403240b3a0f0302030309061803180301150b0705011407050a080403051902060f0a02090303040513060510021c0201090b010e100b1603090e060102 72
    0x30b2140c0000c00c00500c4018030803030700503940010b24001100034090440f00c504002848428601c040500000c4045030422111030203962020030007804103604000002c42da100c0520320341200c0380c01400501b0560715410f600d0040d1041c2540542e1000052040c0d40708100306055000f203104400c5ca0b00b140f440c2c400d140c0c9a2140202d01e030950800d030090050705603000c0d03106012110b030358440b620580c0e5480480000f0fa402400091b01c15510304040d01e035174140c80341d41080c401c41850340d940d803601c0d038462800d4401c4800608160704100c824803421511100c1c08903601540388040e001400c080c5040500c80042080050485181900500941001f40c5000003601c0c1a00c0040710390865078001b10b1102d400501385039000325807018404008405a64012510000344040201031100714001c07100107078261039901d00028040d1403090010410380c500340404030781090804448020242e0760340c8003504683c0107020b19200b403a9401520a04043c6c02050010040104110fa5800c41c0303420750010f03441d604 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 443631429 1250 443630179 443630189
    0x4032003060c19031e0e010e2404110301020f031510050a0e060c0d03020307091202030c010e03150115090e0f0106031e0905030706060815010303050903150f0a1b09 72
    0x2d03d00e110f07101003400398005600d00345c406001d103400181d180070700b40083e14501e290b4006552030301c84e40c03000112001c03507030006031034900c980e07208031589012200008680040069075034071500c1c40f6000b400e40e400e000030039203000541480c0c0d1312803c04025441010114545a42c4908101084505e49540000540b1010250350411150005100c004902148034685e1705207041c1c05007100d5548d82d0b58140e8051070044c1083e030756400b009901e400e00d49400c404440c01c0a945980004840f46079036119106d600403054001d4192801d503207608403002c0741b02d182078000350b040803a00c0a10b4899154096152002041c142c048004141440c00354411000e00600800c0100b42c0c8484904184031442c2c060b46c1c5509120032070410246ea09400c00c0c1e41c480e080104210303030981c10803000240c56200090301d8501d104200303000580503403842c1d4060b103a50303000504440d0107004600144000c85213403c0701c00d2082e0815800c200072498101c04020441750131040b414000303003a000305000540e0303010340c201040d10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 443632679 1250 443631429 443631457
    0xb041e1a0709030b04050109120804050c091504050f060f1804020d0222050f060612070c0c0801020a03020705010e070f03120215130521160606080304032003060c 71
    0xa01d56060454204185030409882c80c42a1028841041015800769911501034102c21001c0c07a1545000c1f81e4168003942d014242d44d00001a84820b0b1402205e1542c01201300c0417480310001860004c107003940c0d404c48980300d0741c1204108000c41c6003010840445220402c54880507004c1c1f00284c0021005006800030340102000e076804811500c85140c3e15400130b174210b809040407400712030107030003402048901d00208035003c408241c0a050041c203440281c5408040b43d5001d694009007114003889040341990452121000000c64113020b00c028206507125541c096a514003604048c1d082d18040110380d42c10303034031a40d001c04c287d0050384a03400950b40e0080803a80100c85229003240b50500901d08201c406d0803050a0001041e50074150b0302e501407003034060721084006c00030304c110780c040070005c42844850300b00729980e880410b5a1162210a20a545c00128682c9945c9407138034540040d002100c045104d460510100207558100301d1003d48120000d284520704003100e46040d000350b1001310341c50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 443633929 1250 443632679 443632681
    0x103110f2505030403030f090315150306180c1403060115170f0708060a060f050d090b07031509090c1a09100207050a08010b03030f09010c0803040b041e1a 68
    0x1062040c0403000701070004011445804181442502c3c0e0f07019100c11808112aaa40000c00718002d0104100301e90700148540841606040b40c400681910070340003500740c01c120004000141c070b07032041003c0030082c6210f10a001b205442c040c800820103410043c040040e1051002c2955000180c4506481c103481c40c082100e50044402d41e038010790101c50002d24070711902004004103641c0e18062180300d450340c60000d20340715041032113140075030390050078000b60740504c1009040e0301480051510031000c490005110489854070010702c81c06448003c0007989031030310a8a100ca1603020741e005094061010003004095a4400881e04210f21a01b0802010ba116a040001c001e00c00d179407650101a101c410565052203009440d20340740e02803940b080f0000e84000c65181e205105071006400050011482c0c040043c0e04c0c0ea50941044031642d04200e5030504100008942001440c0224130401c030140e810705084c6844110340c0c0c449140b035042c03007408418081c0071a6071f4004054030b00300405801041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 443635179 1250 443633929 443633947
    0x100902033706090902040507030e1b0117010e060123030a110d09060b010f0f090b030619152d0c05030f040308092823040e010e0c0103110f 61
    0x800802080d003001c086140c15400603841d1019045141120b200325001c00056a84000c01e80031103104501c50f94899004142c03815030800810b090110607403050409074655649550b140076140f800742c0215040c60543c0d0144102542c00040c50320f41103030301c000030b041549000a0030691a020040c400141035443c0c04075008a00d6801044070100c99140302c0900901c6030034200031028008d01d0a038503002682e800284100b091042480300b015100b65902c603d9400d03c0e005081ca0682c2020b8030250b03225200d402c100351104e0703120b01ea400052000c05010030000c451100c018212900b900d0702c103212048071080003c510b9944503c03c1401021034202083c90580906080c1d01d94080d00914291001c07002902000748200c803009480c040750f0441e80035070303000940580020104005803040f07071400800c5800303208880700168003031006480c0c0c6100c45103540c4010001f8086d00c00c1c0c69450605a5540d401d0303010f407800140101d500d008000e0030103000404007141c016203103105501c20551080404900a11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 443636429 1250 443635179 443635261
    0xe0c01141e070f051605031b0f06120106021203040816060e1f151511100510060f0e030622062c06010305030313020d021810090203 58
    0xd801aa058189a02d840c007070328205141820348202034680d88204202507102140d100308a00907036101501400003004d2044200c8016004c801240c0c0e8410b80e4142c41c889a511500090b014000d140b15040c05194500351000c0d08025808040c0580c46030100200404108443c04465810030048140c0815142d641042802050703c12030060590103002c0b40c1c01040354250f100c2030000c00c2d0414040151f641034900c041d4810072144543d00030b004502c40d0010449014030038128a890031002500d00c1c1c40802203003c000c56000300c68000300c5803416401032103502d600ca401204903503050f003400911440207000080e80c444004110700c51600c41d80000f8200d01001c0140101d0040e40302d0428003001d416000c404142d21a01c03035106003a42000c4003a132141c0c3c00c00240060403240c00c0030281d80340d521140d040000f1048034407000d070781007030040c40310f503005840b019880e051048010565048034144500340096035189540902e01403401401030250b01d10300f24101c20800c00c2507100720702c03000040c0f000e844 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 443637679 1250 443636429 443636467
    0x1090801020a0512090f10020406030c170402010c08070b04081e0a0e13061d07020c18010306150312031406040b0102061906050603040c0503190308060d0501020409021305040e0c0114 80
    0x10006004600812260700210f03000f41065902b1502d003440182440c00c0c0848000354020f00c007030301c580905e4010030050350258840050181c01504098940b600c117880322200e003c400d41c1d0491340d402000800c0700b501014903240d1028013490207480c0e8600b8940c4000207041000c2c1e01c4020b48030b030340c0603151a4054011039100b40020080c400ca001c00703d480c1070040450a10003260303540d026016520325400d092400042d20010b078501041803c0c926400d45c0c071075400400359905c1449040c00e000c3e0011020600480740c1d103103804090b07580401c46010031244111104005088103001f1070400c01202d01c642c2c0c01042e0654040401032030400100d1a1148034809450036900464101000200b84801d1041e850304070010356a0075000c44a415117007080c80382c86250310b440041d00040302000403401c1403508400c10480b5601440c0090b040a031280c20041c101d030700030400b1000448202d2020051420325005546240051501038001544444c002a2074074001c80c0c121660400d0028001810400c215460 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 443638929 1250 443637679 443637703
    0xd02030624100c050c0607081b030f0304111509060703030906020909070804170f0403080a030b210601050d11060a0306080d030207060e0604020109060320030c070201090801020a051209 81
    0x8004802402c00020f00501482d910a40d85400307802c000c030840342030101c1107401032540b02140e00d04d805e0701c0103242401803441d10341d01120707804101b0a0407442c0d16034030080c6019034046c100300300c40e01c4102d904010301c035200840107040030702c8240240100760ba112400d0302c020541509000c12031021030324220000b4844e01c4030f415401900c0d03000b4040c04940c05151203205500c40d00068074113003503c00c1207403c103016407c04a801800100300038000100701e1400b92040c41c946083c04101d03d210f000020325154041d41c03142400e00d0725050111a020000c12005e4014042500c101484607420740780c0c6400f860100842c140199400502c10580390701c030b81d01050052084006030b03000ca001c86100200690310100b030035180706040111003044010003044150145605840d140003072441c0c408260b000d440c854901030381c408840d0b07041540a06100b401544100602002c590791002c961001601d102c46940090b03015178414000790030540d0f00001103d203021000c2e0a802d0203951800c091910742511a5a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 443640179 1250 443638929 443638939
    0x180b0f07120305011d0105090c0702030a060f0b01020c091308090d1e02130e1f0e01050112140d140d0e012c15150a0b0a0f020106050d02030624 63
    0x108881c0c5503450b520450685200103c0700f5000f20341400c80d140001000c1c02915480307150840400c103001815070003084124805015600a04000d407604000c54040d041c03a002c5441e103540348210700751703030500050242401c11140c5c400da90801d0703400043c48201b203841c0100a60790000d400c02c02e40c1e84071145040015800084000041b683c0c800340700c001035401000328021003040055508500d2540500791120300c0960081280003509025102c1c032028402d46101140d0b83c88010701c540c08800c0c080c0e10301a01c000041820341c80e040c0d1501e012441e0f04401c1c3d4071341a030420120344401035800040c41410007a141d10040d2110f1110300c946001304503617410b0380c46030b61a1201c1c6808910a2a5950320030950829405d440704d92400000c3e500c5030700711440d40c062101141c0014068a88040d0041c1540708080c01c0268100e07159000384c4215444880b081000ca040304403540f440540c24041d440203004191600210200b5550210740c1d1000d010389000c01c601840129802d0170010841036005040000300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 443641429 1250 443640179 443640203
    0x80c0d020d0203030c0304060905060702301203010315020309030406030b010e1e0906040c1b0c050a0303090f060903080403152702031e03041e0302030601180b01180b0f07 75
    0x80b503036540ea21511491700800c0344007030009a507140807400e440c0481e8028280004010b4a207140c0b00e141d00e5604c2c10300c0f07202011340b41021980402000082c00301c3f040c48083e6a980d50450078105092003044a00c000d0082c0100204180b0035400b100740e90485040b801c01082406845005840b2584501c07002c076000107024008000400c1d81942c0c668869109480c010640c1c0c0b120414081558030144010022902854600800b8003066440481150061030742214490b203c40001d689000d141e40154001404000c00b4070000740c0c0c0f100d4400003001c0380cac20904580d91655851415600980c480a84004591318a0480031a030070b0300188824018248103034a20f100d40040b41141070300c8920164044d09c9001080d40f044000d8241c80c00c41c4400b400020740c1014607010000c1c0d2a41d4040900d4000c80f507410744000010f80702080040d0180103482c00c0306030303403c0540c0d546508481406001904002c40507998030a80940000701c40e05135100d580000b07540310445000c50340307140300d0481c0052850380d5580c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 443642679 1250 443641429 443641447
    0x1002030c120711010c0206180d060203090105060901210b19110a0201060906050603130203280605090c100302030a0e1501031704081b2d030c0604080c0d020d020303 72
    0x700034000144a110300f600c9500c5000b0045904280602000750080b90402c02d0025008030340d0704502550400420506404201c1d83c2c601040e600280c0b40c1344072580d122814031506142ca18003460150074107401040c0768400400804440e000d5400e405003401c50103d02081041506550113031421149000c1448103403410088458076034405201c0c41e005501c2e010010a00d030020f80079000c01c44000a04690954841c6c41860411850040040340d1600c5501102c4160128a4601110142d40341885684ca40034608003a0281c580040140c00303250070074200d52819a80382c001083d14015036180045c0c8030f41e501404071004004006000800b48034903044080d400b014240614140e80c03007281c40941d400304080203a4224001c9010b07070507050700842e1139815403140401406100740030003010440600c0702c010724902c00341d07048800d080c3d04906a070710034010f40c02c5c04c0080c40740030310042c0c6081d0300d440d2511103a0350700c1f118840710b154840c40404400d0019540eaa00c540f40200b5001001e59541d01c10807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 443643929 1250 443642679 443642713
    0x4210209151005040e0105060a030603121205010e070c03080405192001030b0312161709040c080717040f0b07050301150221090d061112090106050f1002030c 69
    0x886440e126401e01c11400042c0342c40303403041d10100e030194901454203074240b500b04981c68020140d80360801d0f96480d000404640800d500c92040c1d02030791142004064560014019102c3c141c0001200b19002018480d0303e940c8034240b410b000e500b61074071111580702c2d8900503080c100281c03800b0406040010510050098070010324601520795041c04400100c0324005405031000150510380c550484404036000f01c068100030312041ca1603030205854401c0313507aa170320601202d41104200b5180086402002c40c10030f8032074186091814108055580b40a881c01002002c1c0001404c414103514008a030170401c0608881441940c041284503007841d05100003000d80c5c2003449419003801117010400445800407070100e004000d05928800303411030751419900207603c61494643c0245242104402041d0301344103021610380d0011441d41c1e240080c82000e07503036583c080c1c8055506c1e450a61308004617a20010403500000c802d403050042158404003e07811802400b1501c9007500440014102e20101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 443645179 1250 443643929 443643961
    0x41e1112030a0306080708060c0a0e0405100e13170705010b1002010c090f0e0103080a021006030503030610050412030e06070602160b0702010207050705060d063203060c04210209 78
    0x403543c0c1049040e40d51090560b41e601c40c0d10034100c150b001800071030700d860383c07003001041c4800b85400e11070009010840420102e607011221003452141c415014400d11009086154100508030740669607804152100418041640071030300240c940015000304001083d0005200000000c00c000c41a40d032400c0061701030300c0b0b14001400010505040421000b4072030304900151111640200880d80c01d560310510103a00000340f10056204400d1400c0c00c407160b9025600246100d03902440c1c4904080c0280111041000c401d40140041400240015801c41d80f2000c0281c4e014a800050078040c1d03008516140709885d17001c3c0409000080314012200e5070307101040d82d1803040b048150f1035500c0b07100072401c0b0f000e1b2160060540d0040c0ea000c100f01e2401d0009412000141c80f0f000815590700d1068020501d640c01c588421401e40300030701010b4050b1074008810001c4141c000c3c203590300d00800800c14038400d43c01a084012105400b51052425a110890764980c3c0504040341c00e04040e00e0070281420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 443646429 1250 443645179 443645197
    0xe0601090510080d020c010e0a030b180607110c040b0d021f0206130f110a0510170705040e01030303111201030302100b10020a0f0501020c120a0f08041e111203 70
    0xb0254000241c0d035100041903021402c082e405801c004070060011580811070101f040d501402580011011442d404401e500030702d40c00354007040498107140c44500308680101114140406814103007890f4601180c05217040000316000580d510313050300001e60070354041001a400c00c088444880c06440c409074140007268881c1c00321551651008206200858400001000c4e004c860b00224005440307003019068400c070082411031542e8454022810350216544540c00090800e0305d083c00811008036a107405c00311501d016890a410325007a90340d01203040c0300050070150744480c080b400660000607503a030429544011002542d407414000c0d9964151502402c5d1240f42003030b02440f501e4940e001210003000343c0c01420150b030054440b85440403d00e10140c4046d5000c0100450508060040103c5000005d24454a079890032034014011555520000300b8811228248400b203105840e00501c941c400d0401d004003d0018130384181850f50400240385c00c402c070500341041c0e00c02d002c406001481 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 443647679 1250 443646429 443646451
    0x309010609111c0c0504140a08030f21040f08030a18060507031508070501050703030b1003050f010909050615010c060c03020d0e010603232503020a060e0f040b040e06010905 76
    0x43e2101d4440072107011041c4071010070800c1001708801307111407014021003c0010305d2145880d40d155400e44c11940040110104a4000038064080400c00d410083d011a54000c14a4141c80c295944000d0099540d078058582d44010000801102054100c503141c2d2800c0d20295007014514500390014000c01d0390440046403e10140d80c141040c038060080032101c418008250407031408005480caa4000c00d0180c04140d107170744080d18503071119024601d80081d00d90b000100343c03a00d001d03801502041238001490f0a0b00f48103025000c95000140d480d0840310380304480c1d2007062040010384103102b005100034440b50601c0c551940c0b841d05940a040d03d200f0580080c0000c001c0448a1403c0f2096400000c1078072000140d80c80394154000300181c91001142c0c200ca003105c070801d0600c4084420411032100b21a01d0038014002c604081c1d103031800800c9542042541840800005810200f0080009001d595102c4507200315a640303400401d003443e80351301550007a5841c0c0c0440350103840d00300c600603080c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 443648929 1250 443647679 443647717
    0x14120310171c091205030306010f0f1e050c06070306170703020117072d02010b060c0c0f0a180504051608030315040204050909160812090105030901060911 68
    0x107480703984070700880542540c00b8180749241041a00000c0c00c210040c80c00300051034402280040a2144460311503000e00015078807440e14000041444040e6038680c41080303070440203050034981140350460500220080f00d009212820f0040b2814010101482080d1003030209100d1441d4055010700c0039039034040c0344040c10076080c1d03902e241e962819210090004011410007400c05140f0100b280e0032181c1e51401c100340010b220035407240300140c642008100d00b05072014840d002c1d0244680d18002c1d00640d5458203000c1d05848003030300e4a0680320801d0060850512031a180d5480e400c0e00000307800040071410510202d200700c54000c000c00c4038101c809102d00344000c290b03020384100800840715803400951071035440c1c102040c19050314040480d0400d07001c3c40049420b41d101a90781b0300c0740109900901f11032039100d080c41d03d0703035190781d1001ca04d41e0040b034140d502c244200e10413191800c100382441c56580e00c03811642030040030190300c40a2487e1030212402c0d03c404810300140700d4845151014000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 443650179 1250 443648929 443648939
    0x30411040e120f030603070302151818040807030c0c0603061409010b04060c050307060216021305010f1203050919060f090806071d0306010609090f020708070f14120310 74
    0x1903a50140d01100b04401c0a010f00c0410511a50003180d00c42c0024050314a066660b0f80412820341c003992120403104008110503500c0003180510f001c1008040307a04ca4140a1900040c1a0014019002600c14440010841c05041c02006110142036101801d003080c0b5549080040c0106000d014a40c0fa0110305c180c81c80080c40d00016007816140e214510501d032618104081d540e9504918080352940001d00c00e86000c108030b0720151410310303a09042c4010100e29441002501c110300d01c42c0c1005107261000510001d503282416500790780c009400d03c1d08001083c1030a54003802006a501e41c0842c005890100c20750400f00d45004460550b182d01101c00103044003520342d00c200340102545035200710001000c080c03292403101c40c0580c00088078050b10321031002082c24220b0907080b140100c0d41c060020013141040f8440e411209078900d4046013072007440d030f81c0e4050328452060301802c3e12950503034003420702100c0120010000b41c0c150031a034400c3c60a40107c065900221152211603190749400a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 443651429 1250 443650179 443650183
    0x60627010e06180f0d0807050106050a1203020a0b1806040c140a150c391d0c0c010b0d05010c1704150f020d020a1e0309080319020708030411040e 64
    0x72040500031150300c585003c100b8809a5540071001c540d1103183c0410343c40101d80c04000030b1640c02d000b0000401c0e00ba0030300041c00b03507944a66200c801900860900030022030740c040b480007260796001d114000c583e16614000100c100001042c20018002d44061008002810249004591f02070207202c078920802e00030044809100e108801103034040e0048014520b2040104208261041c0510101c42d0313080a03a50401c03680c4159102441c5045c2120441024281c030850002402c007840418841200d02d100b9000802003e8281400c1074404100e00407028002c3d000030407030708000381081607000c1e00c500701b0a01070720000801c140410381d100d101844400710502d00070300c0381c0e0300701044580f510241126240204491030b610a040c6500f403225202c01c0d1150300040911003982c2c1c2e1807208003c3c091200c0c0d40c4800450040d001810300e07010302d0b01c00250041050f29409040d0f0850b001516003410086030103403240d8500102601d2001040200f00202401d41f2072002c4e00aa43c108019441c03140710795 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 443652679 1250 443651429 443651437
    0x40c0503090a0b0a0f0c030e060109051006050309070e1e090d09060f02150108240105010c1401020903010c200607020316020a080604030f170c070b060627010e06 71
    0x400c0c0b40c210546401c007040c411240940c1003591410009401820b00e8004c3c01200c03460040000000d032210302c1d844d424041001703504d0140c000003000b00100c0c00d00b84800311080489204038028403101000041c40e641051000000422030707038034502d20382c0c501821110800e0180b40b081d10000003074100458403a00e00020310714030541103926291085402d140080d1a000d5000b140002144142d901e0001803407ca59252402030040d10000c0040c0085004410f031111405021051241c0d54880104000ea0303021030440e001ca07070800c035440e9500e03100e003810601910a4405441e013540c20202e0302c0208030f6100303d81400c1e0340000f800d052002c4a410b20442d03107803001a142c0e440103a105000004600c05c0c403c99018400b0f10041ca10400c20346c0c0e482805051260403581600800d881180121007035403c141381501c7d850203207050043d00e01e40501649240e0080c100c0162a5009480024120352101c204a4040c0001c070584501e0314548140002c16402e094071078140007aa81c0f050044850821500741e03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 443653929 1250 443652679 443652691
    0x3060109120b1311030a110310091e0503120c2107091a07020a0803130e010305070e1803030a0b040c02070f031709150d050106110d030f06050a0e06040c0503 69
    0x341c0200d480c0c881c9080044080e0f0740056031000c010440a00455504000b9160300c2849502c0c0391000710704001c201402d049c2c0150a07a0805420b207222507000424005d42d11071059031031040c9030100f00d950b05010340f43d80503040058107186000ca0900010b94034550140c02000030303a000d900510000465851450841a1003400128101c1f03042440b801c210310561045040030129644d0030314000b600019a4400349510040107600006101e0000c2c20400010902904100c04c503c00154516568a591746039644503142d40c40f50440d001c6000d81d180361111500d0010f000c1c0c21262030f8142040d001005211907081c0c2032149141011200540780007099020031070f424225409a450700c2c60720340c15001101d1035142d0800030410840003d11399101c0000690298010425603281c101c24400b4030308447c0103130070000c10700c0b0309180600d03206000020360b6000a0301514000c1a1581c02c1c1206001410064020640c0074020a80100741046281800d5100c2c0c002110103000c10414a0300c180c4540c407040d541 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 443655179 1250 443653929 443653943
    0x2d1106060d150c110f0718090b0f06030c06120a0501050d030503070f170f090601080d050405060f0f07030909141506070f050616140a02030901110721061b02030306330306010912 78
    0x140240503e072b04095000002038107070740c420350f0082d00181d00c40d4011681001c01c0d040d0503040c040c50415921616024010640d084080030410740c0380a406c90200521400c00c0184402c42d186105100751a880c0c07101c50f2808034042d090520081e0728a0141045a110740d50b446003100001741102c1c000b03840c0c00d8550300c9071500f0340b4050518082c40307030300d621030841140000410085210f09010900c0142115400795450882003820071071407074140c072003451004606a01c03420030300c0101e41d20301240d08402c210448003da80e507041032801900303c1210b201d0280c1a4003130350003000300705903904220070481c01044c2d44440030403044c40700c0b00310350b80030300c08181b030040c4c0c818044031a45500901e440c00d03a01070004102d0b2189551000e400c00e100010200000004030f44200f40300c01c001e0180140b200940c0c020490022000802e10003d640c0c0c0401081c2903c030b840500000e09140c0b5003052007000c0e50911a03050242484a1050310519030700a40d085030004501110008000301d42c40c4040407143e030f01c034007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 443656429 1250 443655179 443655181
    0x6160b1f061b0503040e01150507080a030e0f0601180e07080a06051e09030712050306010e040b04090b0906010602060f162d1106060d150c110f0718090b 67
    0x200301c54480a0100840740e20500d402d4a101140081014000800c800c1c072001010b903040901680085000d07200c003c05011050003000300140c290401c0c0c404050340e074540012000d0583c1041c2d490000009046500c81c0501030010400c40040c1200c900c0c00d10442c841803004803680c50402c2d99038580c0388103032903007500880042c0f400a40c642e0807403a0800800c004030703800f00f0341100031111000001d844103040703640001503d03000c03c002c801641000030110309069007180b82c0040061f08100d15012001c0c4150380e0382c007284010f903403541e120450300d0b5000040e00540b86850181e036030303944070280544405880303480002507441200c80070281c841e10f0810103504500c2c2201000780d5113080709921800b4603241314240c038860742c42000c1c40000741c400160794041c91420300360034090620720090000740c0100c41c2c41a00c40082100020401059480303281c0004200c0440c150448083e42000010200d602a80010031107002c0001441820b0f5003912003060092140400c05000300c0d40e14450061144000030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 443657679 1250 443656429 443656439
    0x1611030403080d0504061419150b0a031d010c08190507050a111e010c090f12031809050115020c09060904021e0909030a081f0302090a090206160b1f 65
    0x504115040340c0b243d4004074081f1062160741d50b022204540307c0c1503807009808003a4000050380a01c40c42e03500c0302d00b00d5414984c10440c40c0d80170351180200400a260300c039401501c028640e44007118110407060000c01070541110b100801d07501c400c0c0c03010018501c3e080e2103402e1194a610032207004921540b102443c1603010941615108800741c41a14280920000039980340c94009407002e48501d640000145074011481c054840d890a4202544104111406116003410841007100320303605400d1103c04219442c401401301200390308001206800d180000402d601c42003040f40081105400351002042e02109100b05000700711403c0e540f1500703ca0104001d42440322600c807404903240555125250144082a211001502c5100407984005229180c5591043c602600101400501600c4031821188000b0f00f41c964000170b403041e0b441c4000f10b50b080d1555400000301e00c0d0b0242c84079071160f12004640d01030204030701058400101600018040110310040040441800d000c4144c03510300785 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 443658929 1250 443657679 443657681
    0x3091401020f0301060c050a0501050106030504210f11190302070f1a0702100c1202062403030a0e0d150209040501090b15030702030705060103111c0c050607020f091611030403080d 79
    0x80c646c00e8941e80981808000403d00a000e6a4060403140d140800c0c0d42c01d143c0fa0440110206241403059604500100c02005902203207259402c00e6038a04941c0300702c920b403130040c1031041086440000c4620305128008050b000301e10041200c180c4040c0302011075940c200944481c11030890a6000441009407000504d848501c0f10348090036864807841c4400701c0d5860b1403003802c10419841c0964800020000340510305440345100080303459003040715641d40b41c04039503640a08900c10092041610480d40ea07911303188500c0500541000f090320080c200d0180c1c0c44001d52004104901450500713001154400d114001c1404600d0050000804260800949052500080d0122045000421803c00070403020800e581c017035030081907528500341204040103140380c00440c11184604c0540028404520102e2003002140e1f010340d0916540d00701880011051441a03810313642c40721104003071180c480340341c00500003200c4068540c0f65580011010082d07407030040d0b12000344100d1041000314948081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 443660179 1250 443658929 443658947
    0x90607110706120e160f0f0506030a02030901091209151d040e0111070606140d030504120318150305014407060f02011505010c080a11010c03091401020f030106 70
    0xd005400910340030030300c0c800c40c05c0100c010304582c886929101c080c864403441320032010041c0f00e0310010b0f61a06203040c000c0740190000510301540d09078040000ba0a060007074020406203507100700740d60301e44a2500c01c0074082100900171102002000301080724010300034540030400f080c10b0f04000040b5030700c150070400541200c1e04070103c15520f43c80000b05541c190005000114802c5002141031030400034102d02007040401c00511030b40707045585c0c02c00301e07400400325029120850b038800303110100350030b05407800200007035030900d10304031500c0008803285001000c4410003515601400399903a149001288260064840c00241e0703040840d41c208209074000e01c080701c0f003100c000d050080400d41603490420140e80d11034004900c10a00d0100001c2c0d080c0b0403030ac100401d46003800e00507402c10f07000808240512400030410780000030150809400b400e50640a05240b0300203100c000700501001b40a45940002203841442182c000d0014200600070b07a180c550040c1e10480c2145e10300601210742d005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 443661429 1250 443660179 443660207
    0x40f03110712030e030601030206030f04060b03100c0e0a052107030611090102070603050f06120a0c1e0b0301080616110d0503250905011d18090607110706 68
    0x3000654000d409024440348000b000101036610750000103050181c044035000d01000c0c881d4001c04014001696240c051b41d82100500f070f0002140d03512850100010950499442e91501c940b406034402d404c2c3c580c12007030705005160380301b4006c0d6989405110120640d4001d0304c2c0d1280100e4000810203441c00040d4494146c6030044811266a81e01c03034004442580e0b016418145c0d0005101c21903580410005006003680d00e800c11480c5000700002d480c8030300c09800c8601c2600404548903654004121a25800740c011050440f043e6a628440300c090010018011010300c0072000003e40b03c890b9805c3c0c9040351640f001520680c1e0741c10202410780d1b01c1d160080014092101c14a0b06800d004200d0340f4599142d070740318190749040184c0e02c0107840005000510050b21500e961045d559031102c3e040040318800c0c00c1000841e400b03020b250700000140100250030000031101d103d50080c0c0910100d0080d400c00c2d00341c464076200c0d6031301220300d5580442941c3c000c0e44149070421025104102a2052075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 443662679 1250 443661429 443661437
    0x130c081b060a18030b09010e0313090b0f120c030f16170a0c0308030f01050411191b0809130b09011403030712020a12030513020402070206040504060602030a1b0308040f03 75
    0x840d030340d41c4200d02c83d03c0e0400d07900313406200c0c10090140360900c41d10034001e41d03003401141004d442964040f4042072500440e1142038495213406155100e2505c02882940010540448659400501d0f0f90b21a0781c580c42a00c20710940392800c506c0328001c00c8a81046030b280820700300490920202c142040c1a00340001814400c941181020581032800c50303001d036103d000001d980341888015203030a003006811082c411450941da0b01004583c02080382ca040c401100c0e09801c1da56028002c0d5058040048012200044040e11804010903c4001d02d0410000c54956118920751b52407042214010f2500301d4004000c44010700c600004081c0d11035003000024112443c0c0038841c0c1d00c000307000011001810160b070000780c06908019240341880c4020185280400103843c0008400341c261400d400c0280c05140d0024017a019500c583c011503001c0d00010708140025980e944000b983c940c41002d4850000701d051031b01d00f070b40c600340c80c02a90006406546401c060345654403401010b1800c10740c124188 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 443663929 1250 443662679 443662697
    0x10f050d0c120f17040e041b0503010e0c0306010b031605160f0f02180403020c10020c040204030b01051806012001020904060b0c010e0f0613050312130c081b060a 71
    0x2d40301015010b08454415211516680e0561800402018032404000c4107010213010900480913515600b55200f40c0101e440c01031401c407891541c840d10166080150103500300b030555140c6400004a101000d441a0704880c410703a81c40601705800c0c003055503041060f441d5802c0d8110004e01c00d80242250a402140d00d400942840c1d480814001c9a2142101c030f00038030210300015454048441c0d443c100445078403100501c0d0a0398025110007147c0d6506200d07284151200c81c2d0180700b04403802c3e4000000d0800c560300d5441b820118012102482424440c038204180050b4410807005c07018018801078580d0f240c2c46080c105001492014642c22a40035076081c800444a55201c1c02410010000c0e0070b142591020200c0007a801d40312120700d2034680f03a0245114030700407600003a0742c07a80204a1001401040f002e89800340c1144a10030380010700c40720a07820f00000e070920001c0081003e10a081d942a0207070317039080c096100c0c12450b0b00803410b92891418100c01c0c1c00c0000040c21010f40c0d500c0e0003121 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 443665179 1250 443663929 443663939
    0x11d1b0a1404030515070305060306071b02040609020310080a1e060b041802040c034a100b0406080a11130e01091a0603060c131503090606050603010f050d0c 69
    0xc1d6041580181da09078008011400741e0716944040d42c0d08154580780c00e01aa26088022036a0341e00041d207008104540383c07200945400c40740003010b4007641d008006122847e070301c0c0d580324065007055940c89403000303800d1000942d912001801c3c0324001c1d07010703007040e401c02101d624488050003810340641383c198a6440000b900c2c0e03218031800c010700c7d0040800740070f038852a005110480300f100ca00c507424545070901004100b9040c501407009641e40d2440c10704c0308a00c0607920700605410031007244140c4032681c8441c0307501002168161401030701c140101700022400b000c01c82034500c05e2080540f207170007050051012540d021040000601c015201e003036106035200b070440886031440303656481a59038850381e40c100480c0c2a03d42c201c030030b144050100c02d820100002910384102900c1d100b081c0c00c0004140382d015986188100007800308201c80380000c50440d202501904001804541581c544180071807645004000d49058600d0a050010810300b0103052046080c40c3c450701b0313200c1100391580010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 443666429 1250 443665179 443665217
    0x30c0d0e010509122d070204090c03050d14030a02070201020c1c1a0403050a1b06110307120606090b090a09060f2c0406052d011d1b0a 59
    0x91503059200001072107240c0161001e09108501c881d00e0542d08080040f2181c0161603002c13911602c03105101c0d1a020081a10210f1091040c543e000790840d08200c2104144460a040d050469000304142c0c0e2201680680c21510f401e802002d085402105101003020200710b0703406031441c00e00c180120344001c591140014a0000c02c11254848014000501d00810a6880f103484120f14039940522583c103090f940603009010750040720042000380a041020f40c1c2c403940007003001c2070b004032040000b8494400405105e5200312084404200051081c002e00c4440780310302c0c02254402d03030f9803810050070701a80181e50342c0861110340c0c0c41a28540003203940f0006110714001841804200440d40386407066030b102906a0342d0440c0d40d0300c0000c0c13036004241030803400030030f500541c032a0000440303607030f403040c03c04441d0314520142900781400802e01c00c040c03140003400c1c2c0c1a121402c04407044440400e2241c0025002165004400d220003592400708140c88401781003005598102a007904402c465014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 443667679 1250 443666429 443666441
    0x1d130b01201c091202010c02010c0f2009040507180e0318030f060106090902071e0b04050705031f0c14031302090c0a0c0f0501020415080a0501050123030c0d 69
    0x841e00d42110000c01d10110000c40c1d59580d4000c14104981c0c002d1814014044803040c80902074144821110201c0031a07115200c115200c0303602000340c9038245103a080c0780ba080f803082a2000458203105a20035983e2030082c401912682e4040010042503040250041241d2119030b0214045030321203450408603034081c00501408602c0c00700d0b000680c54400209841e00003040200d401903000741005020150b40560641c05030780e0311504c00341c3e4640c40b0f8a402c1c464110b0401c8038450400e85051a44200300c10882054081e0340144e049480442d1150105074a80ca500400403012441c503e8a900900b403c40d0840f1580c0600340c140b490380b40704d400701c8150142e441213074050208a4010b51003421490603507209a0083c0001d4181803e0009102c4050401521501d0103411203070b07a501a070081200940480d0301a01c540400c0c14658048403e000d04a0764041d5110090982040000326244d44500e194014a000b28171341c0b203c29040742e28180d4903561000c0c00603250110200082030007590342d40204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 443668929 1250 443667679 443667737
    0x2318060916030213060e1915080417030703020d2a0c140708160902033d0f080f01020901140a02250e0603070602030d020a0201150305010603031d130b01 67
    0x106c140004032801c021100c04010902122001301d818240400351a4002043c007210990800502a0b1540c3c03c01c002082d1404100e0760f81c880002042142180e4140c01030800004111014480ca1030041c06555103a1304404a240e1407e040b01d04215003188900304202c0b01500910043c1c5510142100c0542040510f41007000258041003000e01e00c2e000504002c001000c3e201011801d5013845040304003884d04064882c044001c20049844003821a009103c150020100f080c1d1141c5940d90b80d100c814006910030746610b4081ea0070380711000241070080f582070b21070580d41c080303984002c03e009a1444d0803500805086110f521250b0a840441c40c0f81501c07890655414010140c1c0b81a1102c041d03410020802e0380280c000140400001c0e4000040d500d0314420207002689030090044200d0051007003555407034241d60114800018084198040b80980740207585841203207111103021003801882d01300c61604034100031000e20a01400780c1c804c50f20f03c20149400110880240e104101d01d000030049 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 443670179 1250 443668929 443668937
    0x31d070b04170703120c14010c08060a0506040506040b0304080c03040306150909030c02060c0f0a0c1403031201030204091a0411010801140a1a04231806091603021306 73
    0x14088150350110502c03405034864024160542142e441e5910110700390b2040003446440480c030001c11a03142c0c2070005615801008200318414074034005d20183c025256140240603a010220300c6040150444040e940094012450103182811181c000e0f800200280c0e00001c2c140001002d20702d003400200002d501070070001c1015101c0403800c0405a85a5002503d0303503150107101c00c0061340052183d86000d404440e12920b41204180c0e42c1c0c10141c0840700020113006840c0700c0010450700d0051035054070000110000c40401017401e056880c825841000c0d2001895401000140ba05400105e0080d1043d09034044149142c02d06c0e82c5030200a42d0111200c03283d12000302d01c15640714140a00504c01000b00d40304201c0800045401c0c52194001e10014a00e41d860f145c00012035070044900810001c0d19450f20a404d00c80504480800b110500b0720441000440174140881c040c20303140a808002d01c0d450242d103444914500a500c0c07000c0007801d0580078042500c02d9171000300300c01c0042c052621 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 443671429 1250 443670179 443670187
    0x5040f0f0f09050f040f0501060510170702060105011209020d170306090f06060a05130f030c0305060105041b0507050106051906030501050603040f021c050a110102010e07031101031d070b 82
    0x3401d00d000325065041651854940002c1200d4211000040c1c1c0c0c215400a00103c110030640c20194007500d020341001360417824a407204100c0e04d0744a41109514100526201c8035a01d64240481e00e90400380308290011340010000034600207035900410440d84014082e901c0b030302c800e681d1880310488640c00c2d072149200100c1082884c2c1030110a86511601400c4d0364007581c50303d500024002c0c06048500800c01c60041307008007002c528000d000019010540c4407268456581c90500040801d5000803107460040704000122420300d030041c513504061034400d18400c0f1590440498040e0000740d400e44103503403100c6001581c5e4940780c4001d24110b00011012084a042183c05000e450041c1d00131402000208200300114042190118060b0384c1200c101c0c40306104c580040007151980d0b00003038454080e08850350200105401304110340341007038000384444880102099102c0780f50703200103800001c4040000c2c101d50720a500c10904040b8440030207020500741c10380d80c1e00e482e8140c0c01019074450005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 443672679 1250 443671429 443671439
    0x41506331103041206020c150412080601090e0a02190e0301110708120601140d020d11030402090406050a0905010e01063209131a0103030f0c03051204020105040f0f 72
    0x845020500c029424030002110154000303907580d100340d00c107458401c0400c2031070038100280c80d01280c1007140000c0882d03100302d201505000c980c0600b80d9040b2801c0703001e0016161618003801c0f803036119540584803801ca5510700100091005001800310440d81e03800c03c009815088120700c0061034486940d246a006210f02c0306260846864a0780c41c030511909002e4400001c1051048913031070030b1a00e220040e0740c0c0f12100103031005100800c0c040038568000c180440c0c13503801680600030500d103800c01440150010036540d0070350300c010742e0003a401043e200b000401052041d0000b07600480d00300303400105c84040361181400c40d0383e41140ba102d02e075141c4e0410004600c803010031081c10340c0d201d14003403050710710b4403108051140d032049079a00404909000494007100401345907003013a0000c130718a802004507a010816454240001c4002c00c000188130641a845035100f011a00da06842d203030b280481001d98002c111030b00500880c1041806c200101302e1400350328400e4001e0004a0b44d003a0610b00348 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 443673929 1250 443672679 443672759
    0x50705011a030105090c0d0204020a02071a0918070806042007200f0d1e06060e061216060804050c0a180b1504050f0d0605090d030b18041506 62
    0x5e44030180640c0540c148001ba41d40340c0c807843c1e801c55811100141e40d2806c2c24026400c00300d45030f0210084010119003e40d600c440032004284543c0100c0c1c550382d000f4018016100e0b181c10584801d00050f01607000a012420158440010003c100320750840200c0400002074655111340ea00321002d0216000e141500080002d00c012554402c403200c9444030f01d0503002c1103940080f043c1c060b04c0141013620101c003501010344d80140540e0010018411240c40300e40400781894161003003030003031802c2060300144042c0450440450740d201200302c4c804502c2d244040700c0b0728501400a075031601682941201c549c2c1d410b130152004005c1c0180e26041000c100401c0300131621210f2806004014440d40d00012080801c119800da540c01c549010404122502245000a81070f100801d02d0b442d040900400080c0055605503072525903500340000088a000c0c0022030040d69080e2440c04044000315001501104c81140c40d050050000240c02d5a10581c4542801440080c0034008001000500100c614 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 443675179 1250 443673929 443673931
    0x13050c04020c16080a020f0907030e010501030c051309020105040b0c0c270c090307090f0e0a08091e100309020d06060326031b0307030e0a12111209040b01050705011a030105 76
    0x2044050804e0501d01e1b000b0903000e001e043e03880c0303106010304800912010700a82c000c980040881c802000f0b10360b1070b03290030550001e840c003440d0301c65400c0520328170a201207401003881296040e92000d040610706030341041503401c802418150f0f0f00170f04161468a49902d80c22888680044860160341300c5542d40e007040401d00904004106242000b44030100e8400040b030104481c107000e00005c03c04d4500da90305d4003c140369071903180d50f400703085140800d1202c1080a010850412542d4108060702c060121052000c2c008405802c5240c10000d0301c200d600030ba101100503030002e4044003c07010b0030360b221402c5030311503042141d660705203921110f01036940c0500d1600b103106562119103141003040340006044401c2c00c0c5030b01c01d10b0000000070b035410710070b4100806111441d4200e40514000749003032018190035050040004a01300d00c0d8544000c030020f02600000603c07002c652804504100707100c064015043c020741131060412190001820900c202841c1110641c03103500141010300805081d128 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 443676429 1250 443675179 443675189
    0x140c090a050a0b090105090103060e10031202010b0d0f031b061a12030d09170d020309010e153705041a0601210603080307080a15060813050c04020c16 66
    0x2c41d9101072145000050848480c0907090a1242d210051580101c0182c4409c0e009101d1008140043c0a001400c29510f24181ea03c140c44600307180020348400ca00300e4561007406a440300b03004c0c440401013040038200e01a00e82c0245060020301c00411b80700d941011130040210307011039035002c40d640049000700108107514070850f54465580d846014441c0d0340e001b510b0300074a19654840c50b820410640e9840300000390781c40c3c450540c0354100c00d5011402034000302c40081d10741d402d005100c0c40b601004203420581d40c0c0c00c200140340c2034a80d100035118044074120058280e004250405241c00c80c40302402c0304907204c4400100d030364502454420617556807644007c05a4100d4401e002c0300b40e803c0b00014001032685041c42510341d01900f01400640b041d44d201420560000041c054050b60000340c580c4031760307140d4905000c1c0e512001450000d41d0304510031600060008004070301042c0e81113094480b0b11b8080c2044840155900f07001a040b40e000e40034040690380803c85207901c4217400c007002c4000300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 443677679 1250 443676429 443676439
    0x130305060a11040302040b040626010605060a020a03110102160609030e12060c160b0f06030f03070b0c07032102090a05090910020306240d1407140904140c090a05 71
    0x2021a40c02c024940200e000c000d100e940ca94408000c9601c03164400402405403500b100000d2030b2001c290301c40c060541007c1c40181d42000004a40350804030200e0f601d03520146c1c02428013642a4034100c640f45281503170f41c001950200105003000c0820244041440d002d0b0f400010709520900e800ba000c0031701c3d5008180141807404008484400109481d81d11944205a41c0d94030034081007030600d00e24100320f00409040c03003482031000b2402d5180d94607200380710580480701914000b401c266503d0150710001801c1c182204005403121007420f02800c140e03846420402180c400203400f84040002d44103555207840d601054503100c510b04000b00d40002c28064600f43e40d50704203007002c0c0d501c0d600450f48030109207070008082655911059001609140100c03681201e22a40322240c4071558003900f20304600030308103c49070394949021a8494060302c400e84640b02d842c441d59001ca040b0f038200b0b03c000c5070b101e944e40507100014488202c00c18402c14003030711001d559110f01410461500c0142e003085001d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 443678929 1250 443677679 443677691
    0x18090c0e10020d080714030c09010e1c0f03170a0f050604020f0706021b070801021c140622020c0c031603150525020a020109060f1407060b06130305060a 67
    0x182c0c021504001c441034510344103a07070b0317952a2003d541c0f4607800300d4040701d43c0d075002040042d080d40c07a001802015800b42d90300ea0680503200c0030040388081032084c58242c0c401401c41400064010031403100d5a92103410180501d1180c028400490354048a041c50815280c0f00c1c40a8000b1046c400e0581c400d000300c4e001c5040030300792141c00c01c45000e09880242840d90014803101c041802c6440d500383d03020310314111610242c4805100e03001c0e4000c0c800f1009980100f1742c00d80c000415500404001410034020301b4050355800c801c11204d4003c2007486020343c40c1d60303009008070b100341e80010310501030480c00410103540d009060600e410110b10318000809800344d414000a0480c031151401101e00c01c02c080381540340d804401c820201c603449014681c0980712161802507400bc00c600403128000d884400145035582d00581d06e09009805020001c2c41007280441481850b0307025000890040c1030000b802c1150f0800b1840c0e60344a10088074035140c000304108108001008500d5102d9003900061000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 443680179 1250 443678929 443678959
    0x80106020a0303150b04030f051b1008060d060f1508010e0304050d110d0303050f150306070507050712240e030912010e011e0606050909040602070318090c0e 69
    0x150201c07041c00a0801d070b2200380042c0c00740c060110001c0901108030f120344d91550b980c03605190318012030b081107a050083d0101e20307102d41d01c1c42045c01c1c1c035200c0161141c040190b40340c10485070500c0040919038017010070210f240114455200d21805088200d000064013002ea07200c44015103c540d02c821056814042144d1503000c000c0306403411102e056a203412aa015841c0403854044801905600701070f00c82c440c04180b6a00d41c0065006459a0050403216110100d0b400444003420681d160950320120204058910980040918500510544000540300c61000c1741e031000580301236801801c408181d1069148041c03100710a00c0f007030b14080005225070b07030f941903d0b40035000c003003403180c608485100403c0c14290044400a494030000300401c20380e5160100104000c01d48000041d440e000d03001c0b4400740160101c40315404001c0c0070105580d5143e0301c840295001c2d0313000724104040d03208a494031440079400c246c017a10000401003002c2170328940c0280b500c0c413213600f0940f04203190690006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 443681429 1250 443680179 443680183
    0x5100b0f0a15021c030605091e010e0c071704030219031e0614190b010c1104020304080906070f2916051c02090312070c0e090a060f0c030c08010602 65
    0x82115801100b0301078504840005a0070b110012241d04500440030203081c11040d8182e0004050356412100203140740c946155044419160300403100869000c80014406401d20780400ca0b4400d840c1c0b1405441c00c903a40c1c0e02c00034187d110038050a101c690100d400d20031450088140480b808803460350541c102d01d580c9900114140a803040685c44030461651004c2c04815089200907803086842030015060008403c210f1520a0380076400051800c94426010340c410342204c44001e4003c209030361001c3d42001000021b40c00640100c1e0b1030902041040015203440d80644442c81c00b454079103c17002e09500b4040700c04103902080d3310038541d0f5089100000380c50b108006030071100102030100d414404010690f200e2140e600c21450030b403042050010745129a4008180401041d400d44401c2085d010805010740550000200810072042080c0902441192041d601c84880303411500051955101c2d4022a40d00300000400c443d268503400f880b007038050007982c100015521304904c2c070350701d8003000075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 443682679 1250 443681429 443681449
    0x12010504090203100f020d090321021c0f0e070303020304030b0c0708031909140a02041508031c2c1c0503160e03030c0102130e060303072d05100b0f 65
    0x24450740d0303021405e140e40a150306a80314a042e17084100135007030700ca050107090020020000583c4540c0c0a0034001810a14004d64140040b101c158010010f808130815001c1c04609503102e1800f5500d45e00d5800078441000024011070094018550300da0442c203100030744400080010f18008020090308001071488400c0740e61025501c0711242002820028aa007e8101c405015114040030114200c5242d004101d451a06108450420a60140f00c1b11310a4040c0d480c8103540c07150b007080c000895105542d41c0580704e919202a4000f40d0f540ca000c07aa00b0100e03c0c612242c40c095001401c1d034584100080150354070740c103030314259444005070780300c0001c029200081c0125a0001e82c4044c66091a0040009403040440102982d8462501da51481d00075002482c1d02d030444c011070200060188c900b5100c0c00e00604014015500e0035407541c5500d40650b0384031101a10f84190711010260000d03251400f880750500c100c001e000b00a0484000e002034940d401c842c0380c8142c10f0100703101d80c45e40d0707070700044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 443683929 1250 443682679 443682703
    0x4030c1707060813030e090109050601020d021506091b0d1a060c28210206010f08060112150e070e0c0423030106080a030503060a0b0703020d181a12010504090203 71
    0x4040071580c5c901210310285990714290032103030390400031a01c03a003a41c0080744201e0080c4e0850b000804000030480c0d0b1046150826510044000c01003405401d05041951340080488405104140350300c0f266207643d4002c2c0c90071000070350780e101080003070380e0700200860b140305048411600304407103600b905850b0b07100c001c0c8409040b05680110318410364a94050801c0326000050300a1560701c4d070000c1c2d80584810184500140500d0b400404c210015198100642c0c8650000340003076800c1221512824140d01d80581300c1c045484600c00344003005d4001c41e214185584003500c00c80d482c201c0d11074016032000c0d00050751200c00303000c28480e64028112400890504c03800b0600c1070b101400c08603006081541112480d4040c00612005054003d00110701400b0103807040e400040e6950072481540c01000d40080058020000b516580ca00c600395030fa16003124100481230701581c03400c200b01701008041c403070101801d01040d00c1c00b02c140b01c514410300600017910140500304c580d40c0041d07190450f003100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 443685179 1250 443683929 443683951
    0x906010c0b06130b100903060e061003140106030b011508010621090206091804120f050703050904150915080309011403071b060603050c03010b010801140d060204030c17070608 77
    0x201c2801c484450b00604d0306554060a502d41d02d00140034001d0003080340340019a030007801e00e408190250400502c092250808101e090140d03415544c1d500030551961805a00940d210100800481c2250b0f200b1802445944200fa000c203480e0380d405054220142e100c5011b0164000e440c2546001c40c1f0b44561004038144000039444520b0320002e03040340254070308942c02400c2c05241c00701690400000602450141600e070140d004407032400c0303414421034080b00340003e1051004900182c05400a42a2218000d001048068014240002080050b407008205076140c01c0080240d4001003980f4005c2c0004030301843c03130440d00200207010241c084808580310f00c80040051840c0e0f10940191851442d0080744010004a5090100280030f040c00150f40c1401541c0480361645014420158900810317116400f03075070719000c285802c40b008290200c1d00458034003000c1e0b00044861004001952044408001a508140c0e40901d000c20150316924a58440b003801d000094000b1b412550001c2c5000c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 443686429 1250 443685179 443685199
    0x9031b06060b0c0a020a270518010e010203160905180405072c01291303050a0605071103040602122802010903020d1418010203090303180906010c0b06 66
    0xd401030041c8841d5204008004010540d4820002d011803828140340c000c541101d00c81c1d442c0d60801800c1040c49903000f00e80084000c0c00c901d444c41c3c68000650000c141d180741e40c001184609210b00307448420020410380d950000422904c9007600c00e0b03000d0729000c03034a0300c500150b080101080e10150340c8580c01400510002c0042c081180410401001d042c40c00a522540800c900c1c5030040810410f01041440042300d002140b44440c003040c2d040c0103001014a0b00c880a400d86443c1015846a04841d9107a50785010200228504111150300d4034400e40c4000344a1074258001045003d031216070318100c0d0002c00007080011b07070004d020003610481e1510303030356650b045181500035041205254014442c1681409825980650091080030300075000d81c2d00740400400708070340c147c2c2d10f1451a210707201d050055524801e00820480242c04040c01240e00d02481c0303400107440c541140382813401000d944400124142840800301da0042001c1c08c0c04c455690040c2da41e1440c6807002081e881c00b402c1705d11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 443687679 1250 443686429 443686433
    0x20603040c030f110a170a121e080103050c030c030303192a02010b0f1305060402071a090c010216030308040507030602030108030c0c190b071b15030c0309031b 70
    0x501c004000d503485030100c82007055601e003400300b40340703016003040c480d040c0d076840000e640440c450009064a0b00302c0c050305241e241d0395150702d03505a1b00d4240c07404020a200c030345d10041259034101d0b5500348190700d0700c00543d171640c54403e181c4000c9402c414084e800803141e605980c1c41c0007003906d4019041603408103030b110220750490002e01c810180c080459404410041e40420807640850104000e5802402080c03003403c180203514098034242900078480c02e50003d03040c038095101c15000701c4014005481c1c0084d503100c1910b80f103220928400b500c08000140103429004016000b007140083c00030b480582148200c0802c80303e454403000d0203028040c800102000414050712002d1507000604640303958680780c030700d5a20782001b05404050300c201403000c8001d2608000c41d000480c0040f64801045082c1030080343c6d190414581110421070000542c0901501509124042c0c05004085030003808004401020b403058840850f050600d0725101e000840e0307000740750f0070100c01c0610000031218428 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 443688929 1250 443687679 443687693
    0x140a02062106040605221103010b0c1c1e0c0b0702060a0b15041505040308040303030c0e09040f1127010e01060203031006030f02211b0a0c02060304 65
    0x1400025802400000c40314400c0000d0031640740c02444a0700d9180899550805120071903055008555001505103c803c107080a0000100070103000213070041002c11079851a140329401c2a04500341c2914042442c03031260320200306e030b45101c1c1d0500c180e145d03000402d14800303010f95501145040400341441510540c05001e0b032204800550f1010340452300b45070000000f501c5000035074038005911304100c898a154605142c0501e10001d14515451070640740c10880c0d81c103c02d480e9a802e0071300c00b060000102003010301001d08001c5000343c0700826103050302c0070014001c040705858540709210050501011960b444d00082510b6844071030443c2b00200200010412880403d14656403c00c0741c413144000c40320141154100c4105103106400d507600c420088c1c1c0c59000c111281c085507d5801c400f00f0405102c1e4100280140903000e0052a00d010410801e109803407610b5103034000084c41062190301700c00c4206020040c841c00903880c0c2050b0231044024040074104034082c1c41003001001041c280045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 443690179 1250 443688929 443688943
    0x3031a03060a0605152503020a05060f040b10061205100b0f07110306071715060c0c01120b0d031211070b040308070801030f1203090b0a06030507050d08030414 70
    0x1000c540e014540142d40d0b4016040ea80100c90003a48210b50340c02d40102c000c01902d520303545030442c04282100552500c100118100801c1c0c0451090309000400b113403003448294003d901e071190f0320b10503103440d051110642401401d07132001c546d0088000c03c070f459800185074840100c3c48030f0120320b07501d030481000e228490701c1d001115000e800040d0060b080c10b00000500400744a401a900608000c1c0d0800d52a26401c507007000c0814280e492400d00c80264030100d503400312941c0030385011450210b0100d0041d401035076502e541d6501c4080c03c080550f030407001208100c483d51006200180c41703180442d01417101080f0040074045100c030780c0381078524150010401c01c1e01c1e5031481e648540040c203000502e20400c0da81a80803401da6800703e5081403007000d8280c141d070341000c0002d140310708a68410b100b1041c102880c9003019514000c0304c0002c2c0c6503080717050203000403c4001c21820308505042d810b2481d40d901c0548210301004103100094203220550342c0c043e400c8071b2075800a41c9000e2510303052000e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 443691429 1250 443690179 443690231
    0x11707120c050a020105090102070201050304081c14060316030c0b0901020c0d03050a0f05161106160b2d0601030c050408070e07080108191218080f060c0a050301030303 74
    0x108050052507295405000340c51004003980c001c0c46180c640316a641e00b00e2080c03901c081c2c0010030404c00100440c840400a1003d012110070810700c44491b0803008044505400300510000c0e00320041c06001e10741040000c141c1c00c102c43c10360341903600e0f559452442c04403502c01d181100e80080366050543c0e00a1010190f00040030b000f035082d000542c039009000b540200c42d204089038100a403540100e04c00e078142c60407120101e203004078002a90303d07606014a51074090b181c0c000010400f02d9110720341c00c1e104001283c07094a80400a0614000e80511110245004421101000d144541c0b031003142012581101c028240000c0b400c0504804450501c199001b01c4044c2c4203011002545112400c0032603c0303403080d640d07603103881e0b40c840c031907291105150842d00e000381c0303240140a000b040201100c08013407142d41c107200300800145070300c010340d10207954000348041c4c0080607200d92070681409038035804080311810034a81350340402c019140d80018007028040658030a00c180307075081888a5415500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 443692679 1250 443691429 443691431
    0x231804030e151902060903070519080f1204060506010e030c12030909150114040b390708010e0c030d140f0d0203160206010807060804060b090c130608040201170712 72
    0x3803812401d2840f041c0011581c8001417081c500024030003807010054403001c55024014000c444a00100490140000003007550805c3c030402031981d802c482c40d0002c240d880c6e2010b64100451810f401c0ca9001c0340d42c000c3c105414000c10344010f144558002c680b0803000c1204071490999580c0e5601c0152950080b40085074202c0110018048441c01d034184441501400740d07034a000f01c00300552080c2142c0a548540000391b032003400b0102d04514080f1a42001810400300080b02203454445605051203941440701145c00024040c46042c50030b0107211309241400e00204a0490b044001c02d54464502c3d0070141045058548000000701c008100c2e20700840303102c44980c0702c8500070f00c528000d43c0141c4208110301900707103054200c1400800c04604075044e0101810885192180949040d840140b0840c1d501d80d85031440c004039038859200500a0304103000d1143c682c4208140c0402c0c1030f24580041080c01914420400180e83c8144102c1c0c3c0e80d100c1d503800c000180c88100040e0380d516004c1390801081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 443693929 1250 443692679 443692687
    0xb0f1903050a0b040c050636040629030f0c0c010b06190210060b1903020c0609031309060515180d030f0f1b0201050c070801020301231804030e15 64
    0x4440030f075004034060390180d8600445030390350b00e0400100340300c3e0205143e01d040302d900300c9007101c408040d11000683e00c80c8403e903500090b5203000404aa1072600058035a983c00380301e410050070200007208071400000e03259445e508204404803c50b035002001411000700000d0750441c800400c7d000303403d0b00320019080c03545400b90b00c14007800f41515003510700c00501c58111020b8420070680240400c40e0b5100060070300e0301c09820714280e110710490303a041041c036800b042049250b400c2040b80c544a0200100555201c00040c0640c0801000d40e81c070400400341003031400c1c880d070742c1c501e0003001e0000d1410304415034814901d40e101d0140e00c0d59505580d888011a0f801405054000ca80451500401d03a0b400c0380706c2100c0c1c007058a401c028190800f40c01a15149104019409080101f009a5201c41191942a030354111503003a64400d07000030a02c0030660828182c8444191851881148100d5045060f50100c2000284010300200060308010202c00f206015031203511210005025080540ba51 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 443695179 1250 443693929 443693933
    0xa0902090135090d0915170f090601150504060f110f0c09060a0f050d02180c09011407050d08060402040504090b060a140604090e03120114130b0f1903050a 68
    0x71111a000700c0c0e0307210007051000901c040001040c0080041c2d1307540c58855840b030600e5100c00f0021061580d8005000e90114003010a900b1584160f1041024150b03039202850f1500070241080c006034401c10102e0074511251400315000000d48042d205145001106440c91500441c0c20b02c400e880390b001640901c2e0018000e445010075114411541a1440da8594590009000107144035100740c0d1444218880d091040d4541200b413047c1050000f400d103183d000c1411045c4042d1902038945c0704c1c50300000a010000740d42c0043e94078208080024400c1e0410110ba19681c1d2111810300c4943c04021102d0300160843e611581610080d0402900c00c00c520802458420103e54081d01c00e10f03c41c41c85d4000004564088a4480001039005081b00342040d01d010b49000241ca0006040da80600091110b80ca41c40f90805003a4000c28810003e800c0000d1007070140180c0008001c0010302d10b50411602c002107403078500b01201d18040030750f010602c041c01e50360000580c0b074660b04001d082e0700903c211070301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 443696429 1250 443695179 443695247
    0x1140d0f1508100b040f1404030806060a1704060609020c0d1701050604150203040503010507090306150506030c0c01060323060a0902030d05030604090c0303081503030301050a09020901 81
    0x544030000c890410440000c03090411480c45940b1400c0d4090703000403490b03203490511380c1102d03144190251020903030075100841d00d01640c0105000d04450355480c0c003000241f6510003800c5401c400d098440d2854402c640344000c14041151025601046a810214003040076230b43c01000245000c0c8021500d8240034145a0744a000c80c0c100d810000701034a0080c502c3c24032002240d4100c070030081841c0e00e00742c6085100c40c2c00640c40210304080d0302007440300095544007809024861413255a07400d04041c2180317011011580300245401d02c18540e05020f011039114007084a402c292008520b507211000400301c02d01500568100602c0c11b90328002e4840d6426101c1c40c2d2504490354482520320300e03512120701c1c004480f50140c1c00f0758940c0c0005002103c06010b40011504000041e00126a21200e070b10382002d090b40560084001500d82020440b84441080c0c101c5102802213014615551601c000211110114080c000c0080e900140801c03503603006460440e00e1003070f10210100b51f140c0b003010841c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 443697679 1250 443696429 443696441
    0xb09010213060e0f0405040804030c080127030234080105010603060b03090a1b0b160c14030c060307090509090304060e01030507120c1b0b0a060b072001140d 69
    0x210a01118200407604502603e00d0104040b0040c0003072100b20341a40400004e000f0140007503071555020030010001c91003440500000e0f1003005c0020074840071340d840c0380451503003280c01c02c0000118a0302000000e44d010a107441c0840c01610501c6005a40d10441d25002140f00640742128408100000302c900e0190859030480310552001c200f0240d8440c1c00341d409100807900c1e20750a8101913410b40001760940c0c441c03071424418807050b6100c00d1b112141c400c00c030740c0504d451981e9040560309070f90400c400344400c8405000e685800c021442c45000101e80c4c0c070032420302c6043c40780d1808400100c400d03100325400002004000c048200b28140b507440c103a10381e40316000f0400020140000b040e41d40d4000e00900d130080b542581d842018440f007801110062502c100801e0400015a440f0000c5602105020031498003070302c038030409401c10354608400c95180b0740c069030300050180314031400310300900e51040e902d00900c40c05160f4181804012a03c0c003551001016403031b100805e40f401100c031075038440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 443698929 1250 443697679 443697697
    0xb0a030f14010e03040e04050c04050406090221120903010e01140f091209010c060605030d030e01140103030f0c0c0503060a0617280c0e130213020702010c0215070b090102 75
    0x150303000c0611100c41d142690414180d0728a59401040704000085954151aa010f80202c0c21707a140c101007480041c09849066805495441e2150282025850b200c110001160000d42c2104003503109003401a894445049004010400104000da92030700c081d00001c06807140b0200801c2803020884a002d000c16080d140c081d80e403403a00e40090f101940001b85c0c400b01802c1403440604042a940046800200038002184c4c0c245c0c0754030b40054980c400304136800124903030740c401045030007401038158215001541001e8050392448010804650001045502c1c1007c0c0d14200044808500340305001c0d08560f4051500340c41a01c08001c0e00d2001076004034103641700341901e007400803061642c26548201b04140c460341d1820500c1108920a240c00c022004548102921900d0554401603102c004100b200c5030361840141c09e00080031458411103c1146c400700110071420169142c0008080b04000c58000b80030319070300928004281900400e48007841d51140304891646440d42146004c4d40100c144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 443700179 1250 443698929 443698943
    0x140705061b04050306151210020a030b0102070e0403050f040815071d01020705012a0503040f0e15101719200d020d0603020a1403100e0606090a0b0a030f 67
    0xa80001c03031241e004032411582c008000b004140c4810195100b9200b613484043e134483e1038016a5510700c882070203c4030000c03a048500589500d81ca0a016041da1030070015181150020a81400700000c0360024980064061a0060320b8521710700b6410721600c200c0d00005654840c0c000e03007030380030800920540d01c02e03807440e9074480c28030641010724400d00110713000030343c00742e00a0a402d2215511641521030080c00c4220b81c002064245030840e004128503082c10360320798000203001d10030469003c08010040a1400380c2a40501d0a80c6800403443c5842d00b07502e02c82c500ca112101c0c286407042c440d030800d01002141103007841c144003001e5100c0300e6540b40424141800c2403c046101121748100602007400017140b03518152020380a10003d511546403900031940d580743c0030002da11004146400340081c1d008091188402408041c0303440078400103a242581403400000511a011500a4000b2020355980e10545c42d10031014016221412455070002401440001442201111070900601a400c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 443701429 1250 443700179 443700211
    0x3131e1101030b0f09190f0e07030c0f121202010b1017012114011b0504081b06120411090c2d030619090207141903120c14070506 57
    0x203108041103000d2130035902212a4001034115201808040501101d80c3c90020f0490601622002110384645010445034809030042c800c2060105901c0301500d0202c0c00345401500d00411916445245540101044015a40c102500f03001350002c01481d00c0003007002c440c43d8503040c4014040c0a0204031103800410301c0300002441144001d54211031108080c0300e84060100d42ca54102d0350264040c1c5500d55961110000c000c01e007080061540241d441d950650741e14605500704e0310300707403841c0340454054130041c42c042e81c144c0d0342c2d100b1180400103845003281d01c0d503140d04010500030650314046800654810811035928400b00c000d102c244110801e1686042007411421900003111a00156010080000c181c05252810044540303080b620318601d44c8503103c2c207032101645c04c1500d044440942c1d6144a01440c0020b0095062000c0c0400c0103510540050710010040c2c030413101d04904242d6115070030300d1402d01c58202d4143d114900d8064540c0c07644140380041c1d82e01821501a609802c41c20 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 443702679 1250 443701429 443701451
    0x1401020c100f03020f0405030607050a02061609060f03150303030608070815010314210403210906030b03010f181e081e070f0506040b090d020303131e110103 69
    0x180e200040741080c0e51042d1800c0c0b00600103800a52081030b444c502d184050100080c2da50701044910f1054806545260701e5184940d0081d26060001e0540d07070403c000d040341000c0c2d0a500066010856031180341c8803018035110003041d0000c005080d60034002a40e1002d02006040e0150019012103c000341111445651000301d20b8031105146451072055660f4401040880d0105072044042d20310703c0c054401a2240c40040c0c901540741c41050740c0900000b0404000f400a05079050004400e1014038800206400400070000d40442c0162400c2c17540d01d000010781a2002d600c015164204d03003008000c508511070684001e004400c4046442c545c4198214800113103000c1d494111f580d2208035a0f04124030010400318582036040100a111b509011102c041603461442444450240d0094001400d01d805c1003001c851004000d9000d591110240d803074a00e074000304486d44590880802d20b0349514600e06500345040c0510000b4852207080009024001c002c100006030341c0d000d07241000030340140303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 443703929 1250 443702679 443702689
    0x206010f0b040602120c070b03070804060f1109010f11031c06051c14011119020c040b0112152706140f060702010c1211060606090916181401020c 64
    0x10f0103070b1001604041210310042c650000a40910040441510036240d03c031840080f094001311441c0c3c001594000620003400075510a41c4070b100c2c4107600074094000c0842200503940300703072650241000100f00d20418100c0c81607040303188034094034041d070b55218200ba04a80440d03e128000c02507091a0110002e11440d010304d89000e40d4041200c2c0b400d05089070348440c5c41440b0036140d148129522104c0c00600c1c00c2c0840000c044002c3d8203607209002c1d9100c1c0d6002450081d00d034003054040e41c5030007107504981c3e1b002038800000b400301c44c00200d6041004040080107074338551118016105504980c440c015244c1c041d034008007465201040201d54030303041c00c3c0740c42100007801d075000b401c0c0741c01c903031990305000d0014900f540c01810601c1c162441a0354131382510400c101d01c0380c00101000700e04006d2860030300a41c0c2e0031001c1100c1c000e00380282c0d040040d100071b60107003899050740c191343c11000f02c00340140c0010716800b0102d42603003104c0d80e07075030b040c0d0365001d0400324610f00501034820592410324003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 443705035 1106 443703929 443703937
    0x30901061a0406300b01090e070512071b12020a1709040b040e060730140a09170901020f06090d0806030604030203090603040303090b070206010f0b 65
    0x9406401489801366001c0007594180038240701c0070751042c5480c400c0b41c241184000140e40441600103842880040e0321118424118001b000b5082c0d1704000a000f80341a00308841300250381d0181d04030303003c00ca8814000d003410321144018010aa8507100201c0d40300e16401107494011031910f443c545160308005100f60380c10b00085e20300c11420b10303000e0481c2100d0306880078084d200341c885109880e244002e00d01020000d529443e200c101651040b0000340b80f0841001c0a03039003400b60310346009070241031424110041c038400030031001c0030a4814900c519800c20481d0150a4100302c2d1006940d01034403e05045200390ba06070010f5450a009160281d42c0d020010540146002c0001c1c209600c010142231098004408100100342c0200407561003e40c116001580c130350310b03842e042c0c0080031944800350032080303150100031001e074000035494180e80c0301c0030080b0b000950b0b940400c510346c49 = true := by decide +kernel

theorem cover : BRFrame.Cov 443525179 443705035 := by
  have h0 := BRFrame.cov_init 443525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 443525179 ≤ n) (h2 : n < 443705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
