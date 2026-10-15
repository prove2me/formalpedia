-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:41.076463+00:00
-- url     : https://prove2.me/submissions/6338d909-462a-475c-9a45-16f7ba4f9c28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 728057553 ≤ n < 728237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 728058803 1250 728057553 728057563
    0x9010b2107060305090f1506032a2407030206010f08160506130e0f0a06080a0812041a0f06010908030421052509060b030910240905040b0106050408 65
    0x103000700f019161130114810f90303002d000080e02c00d221002100e4400b0300030741c1440d1022004440300d0f8407034003901240000200307090b48111403148055104600c02c9001d68204a0709241c2081c0a64421801c6001c0600c0040c0301c40c000c000c201c0c045d40082603d50f1401c85082d80900183d00641e420343c10044130300300e83c11404c03502e103402c2c0c1e0002c54200751584180c01500c9252400c40d48100303045081c60041c40460110b10070501d00850000106000c5c40e41c403640700c50341d40d00f4000001400701e0710800c4013810200350002615001840b900d403101900142c0701e020040c000013a5504680300c22414280216581c00942e0036004100c80d070040d509061402c0180060740810b2100c0410f80e0320000c0020701048010701803070403040c01c10169a28883e8094022101151a41c014200ea8034500f0b0000b040c0c01130b6140a0f2441641410000d0804090f900310481c0a8000e04141d40301d000700002509001680080704100905003409001540b480c0074104142003c0045c1e02c100d080c0502008280030305100441c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 728060053 1250 728058803 728058809
    0xf1103180d0309081b192001052805070b0f06130614060c0f030a0c171305120a060e030c0610030b0f040c0e07030912090609090b0a0801020309010b2107 67
    0x101c41c41855a200c21803904014200e10410711035a810043c41040060413400041180105150086086041c40055030f044c8a603403080ae0f1b210001c070300090f22440340d1700000c4044d914545415030810b040c81d5038654052005503401050744100c0d108028250030000040800c801c1c4802051051030f14018141e54004100540796010b407000195000106908100002401001c0411070343d540481c4c84000f45480c1c0c0c40b01c400c807180d40c0c507241c0130041740d0349990996035050f01014814868514000420007003650700351a0784e07410301403002d152001c43e10f18410143c044071050051a965010a2452401d10b070000b0802854481e2030482030012071070300100d07950310000750940d40c04140c959040414038a41660f1160307e0020081c010010025130680012000fa40b150381d496100050306001522044428000c400014007014410061308600c0d810240724031001400d00d0380d415450b09401b50982c0e0084814a859a4540015414a0900c010107030420711400c0c0703030708035805441900a600c5109600c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 728061303 1250 728060053 728060077
    0x602010b0d17071103101b08101725170a050606010e0607060c0e0111030909191e020415140f07061d0d031a0a090f1103180d030908 58
    0x4210f003001c02048110800b800000107044031007040d81200c1d01d81c090601001c40031204001a0210701195005207844c5020350400080204075078105840024400d0203441c129003240715000e02c0c0400c50000301d141d00000c100207290050550700b030030b0342ea00311007005100c1507145611007107002001ca0f8000c00c4c010307044002440c00d4514104444006459401f0307043c40075007145d203443e080c4e4007030907004001c0761140f110030707280c468500d20040700300b6813a402402c08807900840c0344000208040d000d42030021004950b85000900c3c00090a450102c00701c00b501c0301540507500107001e2224918a445444200080c0d1801040d0080c04d801030300001d0041031001e44d0341e01c0000ca020390401069801040c4c2100441040e215400850640d05940310a414010340100e45000c802840180309810303030701a04500034204081442c0b41081c00c10042094421108030640e842190540703040600d002140181004000301200400c0383c0400390910b540e40c000c50b010700d8036010444001503040c0b001e07a00404046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 728062553 1250 728061303 728061307
    0x5090103081605161503060302031e01060810051e0606040306050c040308070317011a040302061b070b1201080c0a0312030906021b160e010b03070903060212010602010b0d17 76
    0x140900e4003428500b00020018040c03400c1002801100c4460303041114800c4410717002c00039a500d010390131980720b400042d41540203800c000b10b500c8240d1002c554500a9100005951655a40e132507040c03004c0385000090075511381c002d005c024541c00100d4500b000650300c09030202d00b04140010010301c11440010001d540f40c0c0d000410700c0e1401000e40300115081115a0750722000703841d00410f110001000007a020700c0104c000300c0d05440b84103100d11101c980741c49651429003980c0030800d2942155020920301c03ea480300b03d0754004002d102c024000e100300d10005817502e00840c0b106900b040d058206070200d80c003121070903e1954501e4031900469030800071448140301c02d1013089001e40000fa03800390945000040360b918001d08003d11001d1b10141c2020344120021504442451640e1846840107110740c19005212a8403010019a00260b2500f8860f0003c3e5581c0c0d980b0050341c1040c8603030b940780c02e043c00c010041c40d40c083c0154400f504d0b0407110070002010582d244817000000d514980d085483c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 728063803 1250 728062553 728062567
    0x171204050d03050909070c06240612020910112e110d0c050301090e07051003020a0c0f0c090605101205070215150337080f0c0f06100509010308 63
    0x1441c1210802d10001d014040311b8078180c1c41c06003414802400c00c0741e40320325080740540c03a501d505840304900d0601884e0000e0041c07601d1811100c485c11040b210b035480703500308518403450b03460000d5082d1066407501e540b08848540301e040c0b420a103809100060010b00340c059074000340c0540090b8900f00410350701c0010090315482e410510b41c000e8410040c520707458400c2000c01c0c1ea41081c06541200c40b0403006000248850a00790b07120941482180d0b008078034044800a014029000303411903034118a000c842c0f07203200c1e0325152008054103000b9504030b541d100042c050280c460059402508040c1c8520600080659000741040000120301d41411395a001007907005200b40681940310f10b8411090100b81040ca9890001105100d03103103220b8841d0300c000704010007a41460a0600784c0e00f40440039010340c85056028800f10f061011124903600300005021089031501402d4003811480050080000e1a80c0c624a00b02d4050448071040d15100c0c8200290746d40e401d18a030540ba808180562101d82c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 728065053 1250 728063803 728063807
    0x1081b0a0c060c0e0307080c030a02060d0908030c1c0902030a12030e010204061e030c21020906070305070b090705030709020c0102040504060b130e0c1204050c06040f171204050d03 79
    0x5440d040003072901e4140f00303008000d5a8009809011540c04405841690342d881078010ba4400d003d550300d94042d004001d00c04058901076000e001c102c42d8050000c200c2e013600d65200c090340d60044400c10500303800454070030005103149604440c071100910080242d60035580000b43c0d500c0a40790014008440f0004006225119402c544040c43c8103000942d1910740b2600050400140c2091000c1c4001540404c414403a20a0082c2402c448140d11036800702c05602c0007450808e840540d00306c0c501034080020200c00c0d12600010700d0518026641c01340c550716186404c0d01d00d95005028408907901c1004103002568000c1030801c200c0c0c0c841400107a80301401e440301030180c040e56001651043c42e258000850f014440c0c000c14007107920303907409080c40380c40710340b681c4141e202034841003842c840074000380c02c01b1710304221340a0f0003070f0296045903404d0200400003030b12039001750050148a06403881c00c008a6a09a1115801502c00c00142c450142e0306560704166024034450540b00709407000300c58040c58 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728066303 1250 728065053 728065067
    0x80402060c1c0c06051f06050a1704080315030f06070c06060f27020703020304140f0a080f01270f02221b0e031b01121d0c01081b0a 58
    0x81002c01c2c03000080020a502030000b044044043e600d03542000c3c00a00204440022050704032002c9034003070a040e04145d000c0b2825040000500d09100c5101e401a40c44034220034468070940c1710709403055803481c12609401811080d254118000d50011465400944010910a0b4008ad03c1c2c54501d024000b5410014007034645d503480180203012503900440c20048003108981c1440c0e0f086810384c0c4184044071114200d204001020b00140c10138002400401c42090b105107192034003c0a21b50078201820002d645000d0b140d000700c1e80c5038081d00074170b84003110038018892164030450201142c1d2407036038500c03241e916192400404540071100030034119514192801c032036441e01a492900b03075040e41c0b841402001543d6134004100061003840d0412132050141c44407081003d0040c094120044039080f01d5984040c1140b410300000c14501407100103180b00380000ca10b58000a05511404809900c0c02d10420090b41810000d2550400c09609100c1d601d8070800e4041014a0303940b0b610b8084219110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 728067553 1250 728066303 728066323
    0xc131703180118030b1f080c0906011103030601030903050d05072a030e040902030708060405010f1515121d012003040209040809010516030f080f091b120f03180907080402060c 77
    0x140c1c0002c41c086030100001800248c011000c0d82c05070001c0c1c441c0f100640381100c0b2800c100495500810001c3c2e0294880c0d001312070807912a0507c45e0034050182507030b40c00d40d0821030b03003580020b1105070b030407280000c412004405880035000078103e840300340c0c0300141134080b505c80443c02140c5841521085440030803005000300902800e0715458140f1340340c942c0c042c15844d10b4111600c1c0c10250349000001c000999032080720300b000000c0510701c4161209035024500d0740c0034482655522880b031a001c101110010841c00c60303a600000c0c0000350410910800c2c1d1220322042c2c1c0c07007142402000010b846115001d60840d40080d40b242c0c507402c014004840c14800d0120405101c0740c0036501908050300442c0d0400e5140083e10341c0445561005880407102c80704841206281e4004800c2d0801280f07214400b000702840a050402e079200360421891403c2942c1c1a542000d900c006581c0f08003040701c1007585041203044440c4038172401c084d00000c1032144003400c043d10503400002c003210448002c1043c4000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 728068803 1250 728067553 728067601
    0x52502060c01050c220b0901080717010b0d05252a080d0b01110c01030b03070801020f0a08011d061e130e0d0203070b0c131703180118030b 61
    0x15070311303142c0414a0a03402892a07150b200042505810700101201088030542d00406072903400c010724003004407040304000d44800140050703c2c5c90642500303802845103020313180e02e4030100d07a1513a075920010101c03400241801160320440c1c1c078450070540c0e030401190b40c42e19180340c2122550000c0e82002c1c02094043d10300700b58500c02201070300410100c1c00180c0b46144a0140c108440540c04d8019903071800d84008403603140d000841804c90035802640042051a406012100c41381d40761042c0740c0c2240e004034109102034001050b040c203002d5003e10964054607040c0800009980c0500010810410150150388904850b010b680c038550442d81e0160340801c0c0080c507910548841444c0040200342c41d0261501034010400e0301d8000900000803940d1380ca45c841c0006415a03140300840c14180c03c00b0135103012003000e0440015403000c17450300c00d00d461010714000d5542d500c14200000c1110780f031f82e4030f11414440c4610700701d804c150402282d44101d83e004907c0710407135515003003001c001c80c42582c10584 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 728070053 1250 728068803 728068811
    0x10e0a0e2505041a0d15060b07050304080706020f070b0313060911010f03060e13050a1527031d060d0608011d010209061605011b0c020907052502060c01 67
    0x108039940c540300111001540c041200303858080e0408806441d01071310360781000d100c0c0c0112001a01c2003e002c034828050341c000281c856100c00054003964048a130a0f0b0b41399001260a00c8800002e008281c004d0800e400107103685016400483e07140c0b0b909100d07401034000040f00040d41d402d102c64482c0c01c001e41c010b80c2001001c06601d001d0000160010140340007461040781085014020300c00c01c1d042e0b41d007960035104581c1e2a0101c840043c10906411207150003552083c00000d190040c03040504518a400230941c04d03184c0040001e20642d4261016a20700030300c0c0201c01090b003161307600800c0444000450b4145556030040341d4180f140c034031110100c2d403411700001881e0a0651144c04440c185102c016035203900010030500742d009415000d54014020804109908100c2840c450b025200b10000328124150f03c494802481840c0c07080e02c082035401c070503042140f6050711f129030b100f1100d0511605000d03458140d64000f8410584510008000d070701c04900759601e01c001c1c1c13420b4540707210082c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 728071303 1250 728070053 728070103
    0x903020901060c0b070f1706151b151302091515040501030f090c0b030703110a09060206090706090b07390803071203020304060e0706110c0405010e0a0e 67
    0x6142c90200700f000c0e502c005144002c2100c45110300c0c00c1d049103400940d80c403078822052080003c1041c03400b5000c203a200c4c05008004074201c1134000503025140510645008280c00c050182e0b041020000d0700300d101d00007050400c9041c0b0000070400c20303a903405071524103080c2c0d21003c19a501010703012910368001c0c13206284000c009040b80c018819100282e13014001d210030700d204503090302c1c4101401840b08034505020301c500c2080310040e40d40452549808241c1800b000c0d20381c3d400e031740090200310000d01c68140074400c0c140c040200310381040342c0300700030000c442c9459001011103283d0b01900d1002c0500240d90000d003d07a034410800a031252400d0095154a2802a0314984051900c2000002c00c080d000045d46040801541c0da8943c0000340600340b0303400d43c4e400718020340c07000f4801c881c85036440c148006818000c2041c00007501107511610f804001f44800a407811004c900106d100703e040030014410b0810300c214840e00650344100c007141c05030401d80b005003441c030b28803400400071030001c03d40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 728072553 1250 728071303 728071307
    0xb0708040e2205011d030301030b2e06030501050f061306210510080606150d050a271106180d020111191b060203190210020706060503060c0903060f07090302090106 72
    0x5c445410010748414101d51100c01c810350300c03400244405002414050001400c1a102e90800d08440044041b055001d03032035102500c40c0c3c84070a800c0380703000030342d2040144080c2c02c00300201c24034288102c855605010541240800b10007007401660200f24181c5402098603003801c40050184680c2d1106008628002c405502452641c0c45018000e00c02d201c082a03441c10034100814000c00c600036824904804940030340003800d400703071010400e565604005603054100003581d05140d4003030848802041283d0401800308920003040381d00c110030410004859100044205017110000d442100003400b076400117031401d6580020306c3c04680101c0050440707400000c450001440d11500c103a6001924030321070b81c00c80c032480b4068040564000c1203440305662100310003043da44c0b8107104a8641e004a482c0d0032003680c01204044800a0701c1d650107105d07a01e4240100342d80090500011420f20b0100c0c0b00182d41ca03071018000d5005101d0380c00104801310320510951003d150050a24001541d41f1f000c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 728073803 1250 728072553 728072561
    0x1110d05091009050a0303050712050c090301052508190509030c060a06030b010e130606060509010e041104060c0c090504080721090b0d1d0102130b0708040e220501 72
    0xa0321501d4000c4403212510036106100e4900c0e4180c009004154002017590107078002c1c00041c0665080c4604800518405405400b48030f22402144881039280ca031544141400e5410103440000c003111844102051140304211704005180c0038503010790305813034070f600c1603070404205070400f6011410082007001c04100000200100c944400032184e5a6641091500803a403d034000200040103040041117038108802c9042d400210081c410b01020140e99034900840d03c841d4408000f00e90045016001ea60700a0300c02d08001e00306407424002c44482c015618400e2040f03000d900180500e4a161b075041c4000949080f01410304144204110300302410625540c5d00310520846003a4170f0049140046e00c4042c01400246074a070300c0300e180c4e49090035110318054002d260541400380e42c480010720a002c0795107401d2064207441000690b15101c09044041d502c800d80c02113001c0d481d0400a0000055449081350b080b100d0054402025445017400002f0071301000921510780e2001000d200c06214040d40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 728075053 1250 728073803 728073811
    0x11070b0105010f0504050609041d0105090705010909020319020f040806090c040f090b06060c010b03150703050c03071b2109170c0112090201110a0605010602070e0112120201110d05 79
    0x1c03060b002140f0b18034111224800c03030086039000441840301480e80d08103038000079201c0040c25000039001c169180b813a030846004450b20000c55008003401c010a5030441d12a0000c1c00244100b035107186890001c107410390340c10f02180c4034040d81c005150b481600490b800e43c0c025001070015643d00303050000c00e8590b1981c294005034410351a081c030411441c1e84a2040187e981da01c4420017995079528020070095410602020300c295480301a0b0807102c0c1e4003800003440d411541c0380041458204a00b00400b12a0000c151105d07500e0100240000140c03c4444103803042007003020000c4003000303441d02c0074003080071090f440344440250803c4056560085140010b032180030f40b403d01002c1e036005245999880455480c1c0c04140b2040200d0107860007030300041c440e140103040081054818106007071501c00d81e80c109643c003a079581c00620103558140580d1005000c2a10b12444550501c0749001c0e0344400c0f080b008001ca041c4041603402c85000307401101001050032541901c400d194205400900000c031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 728076303 1250 728075053 728075057
    0xc0705060109150603090b1609050307272a0903150504030e092a0405030304060c110103060b0a0f09051903031b11060c030f030a02070302150f15010311070b010501 72
    0xc40428111300c0303842014003540d08001d4011007a211004104442408d0030300480400801c0a008100c81d141003040c5401003180003c5c000c0761000c52500441e46030103d81500b100103040c2411021180c2c0d00c0780c0749050019200c00342035680440c60707005681440b000e600c010301141c0b1241e91729401c8006640010311941c042c0c0c5504410242003800c101214100321541070201188500b25100e4010103210411002d401c5800341c0c0ca800d4443c400681307540c00c19400b044c0002c4120300da1760100700b02010056500d45080c01e00b0700400b810710305c0503a964003800e02c0c40400c0241e9510741c03c4286105508a00040c20050000b4030080c038421100030401506c0d000030380105400d4141e606141d4400c240300021503400440030660084480c0c01c000c025803100d0100c40c1c851009000030b101e92041140154004e405041c00182d4880d1a0700d8060300780b011401c4503075060260300d4100b02d01c081078442d42d030b039100210122040200c450117006900501910880350310048001c11220300300704070420594181c803026 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 728077553 1250 728076303 728076341
    0x50604030e180118200706150909030905061c0509031908010b0702040905070b0d1406010e030a11190906030506060901030f060b010e0d05012f04030b0c0705060109 72
    0xa45500310074071801c4c41800f1070074085070030407140600140e0100b0301c4511180701d0300c600b41008072001030094000340003d03070b111651034208a240d01c3c1c264200b13500410240c003003400003060a4902a00c04a4103202e583d01401000810b280e4200d00880d0060801d221410304011600301903005c5581c940008c0c04c840706854030900c0d80644079009a000305e040f41c0741c00001c2c42c600311640d82840013903c000c4408071094412014081200c40c20320000e40008500e40350300003050100001e0090000201a02c3d16050081161141e56940c4011038035024268000024044440d03902e0081210f030030401c089800c000b84080c3c404070740790700981c100d6070072640903000b154100d032a0082000042c26082c40002d004088001c1c0040002e10b083d0040081d0a505041c41d038054074003030303011407015078454004850596607980c03028000c44c032088141d51b450044100004c0786502c2c0c62050300d00e038802e6020290010034441d0000e44082145000c42d0400c0b54040166a00ca50751219860060920708001424a082c0c2d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 728078803 1250 728077553 728077579
    0xa0206010627030f03140a050306040c030501140405040516030311060612070e0403020114041103010501091112040c0306090b01030606080d27091a010201180f02090c07050604030e 79
    0x8460056000d285842c8090010705140da607401e801950080402c03018444d43c202d880030542d20301c4018060902c46030300d40303998910f03080c4e0410084a90f9409480c0c103140c5840014840070001c4800e986a07084281d4000030139860701e0901c5442c100340380740702c103180409100c40482050b0303010f616152546105000c40d880c039212041040540c0d0070180212400e540001c034100000710700c056000c3d030000e01a000001c0d5800d8121510030b1179440071503056030500403a15001d001c078102445100d004004000f02084000d0040401c04114459000c1c00f2502e104a50701147c00c0c8646451203400440c3d02403000c000440356440e1036022200c0904c802c0c3c40c494a490710004082a005c94005081002951070040401000c0a0119007440001e09500f40701d0002c9030100b9068450310514002c444400b80c518a0792001c0c0000a00f517840d4141c5450580003002000c000140f0030514082c03806034121008000d45e42c8502e828809409180806015403248605000070700d80c104494281e004410381c1c112130700b02c003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 728080053 1250 728078803 728078837
    0x2030105131a220303090c260714100e040f05040b0a05070525051614030109020a0b0f1e0a110609060406200708090a0f0806011e030204020a02060106 66
    0x4129540340c0305034403074034120701c41041e03980b0f400f00c280d44a800d00140c46002a26400c2d020152034100754800340d840490b80c01e00b010707500c2c1e0486070300c84103400804282d4181480202c82c0c45001c54100c0c061100300b5907010240703000350840050344201500411881001c482003102a00081e541982d183c44140d000c250071480c13034020075114a5264591074035010810701c0e1720040c0c10048080e04c0c000008000070400098050012124032026400000c0f42c1c0781c2000c80d121440040003a01c5d41c46685091210070050706c1c0d02d48441c0c22518131040094561039114132840750b5100d40303d50002c100c3c903c201c0140827200303500050100b907000769032803a10104202607020f9172a0302c20340c0d610485511100000700000e009410048443c098000340c070f2a03200140350000240c1e0407642040f5505000822154254144148141e009000000140e41c0c15440c00c481c06807100010b01803d040601c0892040c04070080d41c45111000b9940030b80b04541d0741e518400029181e0b0028055803000030300308046089110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 728081303 1250 728080053 728080103
    0xc040c0207081f0f1a040501050d0c0e0c0405060d09030e011b0605091e0a0501050907030c030b0c090a080a020a1703040635042f06090406030203010513 67
    0x1a030344000800c0050580f81684031255140c00c3c2e00a1035640301c00c0b0f070764803030419130040b294000d80c0240911078502141d001c0100b912016000140184074001207400441c0da54a68601111140380418030b09072100680b100d0b00d44603d400c03d03030300841c0c00185a4410f810301d6002e8012304d0b000742d0314005e111a180004442c0005e1488150004080707a082c4600864120b92090342c021010700201c40c004914240356400d02d0a4080100b440c9802c02c900030350500800703000351030f0300c0f050480190152500315503c0040e0300d0140c0c00094103580c01000041d050070a000100d0b58220b00040c441480196503a130550354801208408034007580c89640001044800c0781610802400c03180c0103035080c50f060190484001d61110103200014504204104010f4640c40804014a803e40108013961500d4100701c0e1301c0c058500580c40c50064210b500404e03620a0748103540741600700715012542d0b001e0202c0002d000d040c058202039815403a01c4203101260800d2500c6103086481140b91042404905024003a24 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 728082553 1250 728081303 728081309
    0x810050108011109310f0e0c090f04051513030e010309081b19050c01090e061c030509121b18070c0201110105010f1a09030703030f02010e06090c040c0207 68
    0xc1401400310b480d4500d0b025001724200d1000d010481c031480b02922079610b48040d0b5070103000303050b03607070f032030300030524030050041c00e0f000b0070a640240011b59107280810310311030008000003801da040c8004201000424001c0c04504c140601d03c1501c281000b01c8440e042e0410004101d001c030b10b03514207000c125402405614022a003002c012f07406c0280c0901307019a8200c04909809080c010501c0c5071000301005030002c66810b018000811224046000241c420005070300703d103409101c0d0804100b00365581041e041c1d100400c3c40d9036a40c185800f4039003a00c650042400f4154011108517084d8201240020500f6550a14007503803581030f0041014480368a42c04414080d000c8402c0e800601603a004411030105548180761000c2a01d41e81c031745603800c43d81d081c0c0080303040400d0410100500b10200b140c440c0c403244410342807480c1018290000369100160300c0010240220504554800c070b0003980060b0b81034054000341c40941c80c180c50010b403583d0140c50740d02c1c821351a14192640140c400106c0c1e40c29 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 728083803 1250 728082553 728082581
    0x90617061e03070b0c01180804090b010c02090f0f100501021506010219030210050105010905030307020d060b0604030b2505041701091202031c0c05070209041a01081005010801 77
    0x50384540040c410846146040740000c022010510707041c0b520100710f078000404180c039007161554401501282501d551a42c101c2968010b40300b04000b04003003038215011120900740006071540c0e400d0040e940301c0075054029500042110421843e4060b41c9412403185820b00b4000c010380e6201d180040f048080e80c028280141d120b148203071480480000e8458001405004444100ca00421041842c2240c01c900b10300507003000188015442580c01402e014100908084480c5404c0001203a07a0740110100a0700c142a4107140c81c090100701d50001051590180c60f550b81c84e40c503400c0c401d007400419210300c0c125000030380b408a13403481c00d0f09000d4502c000c17503641c20345018070380041e804030002108110b0849540c0e0f411220700141d40102003502d03101c02da80255448980c0f4041c120b1000b40c070398402c581514280600718079445d900408a0b40d101c2d0381101d6440003901c40e81054102110031107101030300709203010001701c0c3d0540c000483c082c0d280004a01400b640c0c0e2203508043c02c1e140b11000b40c1c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 728085053 1250 728083803 728083847
    0x406060c060905070e04051501080309220f0203090109030210020a090e071b151803080718051203120903130528060503060109050f03030a1b06020414010906 69
    0x1c20680160400900840c1110009621480d0901680e4000e4404031641c3d44001388407200c43c00e10344112030040040c030015500700301004020031103034031103421000c007a030403011101b401841c140d5104802d10340084408544900e4170310b0f0317894000c10803502e00350090710400720046800c48060084a401800c0d5a503860760310303450110300030800200541204140000c200b41c05030400c81524841e6100c40c00340ca4890344016101c500d5801b200e10107180610507500f4080d0800c0841d4002c0200364000701c4502e030212102844240900301446142c009035403010400e0410a03001e02c000003c1d0051110300c0350013090306c0c2c42c1c114502d0361b28402c1d9500303501c0d0207503640d80c01c011500d880010300d00f540c043c1010010401115000f2900990300a410040201d02e0101c180442960f2207203d50000c0c25007581c819002c5811040043e61342e0140711140400c00041c1d521250740380170074018800b04a50300540540d19a0b46541500a485141680d07440c00205e100400080440c03107401982000729060616070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 728086303 1250 728085053 728085077
    0x723040501050d0f051516110a05070312091a0705070b0304151a090a06080d030213120201050f040603091a01061d060c0703050c100e0105030c130f03060e0606040606 73
    0x4a00404c640300300b070340d280c000c244080b6484640310010034031a1a049503420034501007070303001170125101c1305c02001d9a580003066a600040002030400c09403504480c00840c1c0301e80c0c441c4215000d03200d40d00124010004401c03070350344400340314010745540c5208000350f6841948460345c94186000468014011104030780d101c0300c2c42c9800c3c0d80181803100054044004110100e0041407440b0f90690f26008a10350f102000c1146a005021440314040d00345000d529100701024503d16440720b50180c0b4129a82441543e000c40e80510202c1d40303210020b9075003980703031a5140c0000d00206001201640d41501c140079a20484402d40c013154140c0d6950786901c860700b0791418031081780e0081d80ca07103d80c000004002c0801c10180c20010301340103600c2180180402000b200900c0a00c1c140180800705100460a1a0310382e81e8100060f0380d41b000c8052441031300ca100c00d403030828003064640d00902c14040701900c08414840107400c20086484810f0403686907845010502044405a1050b0030000346075822817 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 728087553 1250 728086303 728086313
    0x7030507060209040204030b130b0603011b11190308010807050a030f120905060c03310b03070c080d0b0315010b031504110c0a1202010b010e210723040501050d 70
    0x20b06080e0f02e014100504140c5c8a9403240104803060301e40d030056000321054401000182e20074154850401e070000e10000c1e449030190075403a0702c4c41200f0014401c6981480a2106040001a10309055401c421494050605000c1c25052080c01204c1c00c6000d0b4010200c0c1c2410004042402c407540310480903001251502e515410b8841c1c8941081040340081000a40741e59041c00307032054072900c2000d15540c031811440a0b07841010100f01d020400828040704240004c0f50414001b00d80c42a613141740d4968482d413007190482150440100304071004074421118441603802484141010b130308031031a800ca81100d90303480c200d09105008022000308001412508030ba0000e13200c1c06000781000c40c0c441c40700c20008180b50410790f11120785600049861050106458000044003107900003017001002200c0000c020060701604580504d1410081c401b40f030301d80078000c5001c0780e001015203148940303039000310004c031484030700ca00c1407103845820349052450b051081604072800201040d69209150b42c43c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 728088803 1250 728087553 728087557
    0x9170709021b071401090f120303200c01050f07022b0c051203040b1b03071404150807090f06020604110d120918111602031207030507110303070305070602 68
    0x2440d2803210000250754100c5002c020000c003421136014150403102d11078000602e8030500303902c0341403014080c0204020042c91444584001c0e41c040ca0003048c00358060070070034600c0104030030340c0003a0440001c0003000d601c01076229038001c2154235040d01e040d46940c1000c17651813215000442c0d08088200191240c0c50809070140000403541c2001e404115072900e40c2400c1c55035042d4450314641c0700108010030070020040e034a6000c03a24807610745015038480c0d4045810b020084c185403e0002050f0f403c061400ba25044e9401420010700c50000b030354601c1c5005020040684a00c008509840740104120000c40c5406040d651260b00a155a0b55951038068844e88522995500102c6540c802004560040300342d40440e051910707259181803601c00504110300a581c5295000b6203000044003420100318225070051101c0c05071614100a01c3c00000e0030b1820800c03556a00d104001480c004054025000d042c29602400313034411002e0010090503180e12502c100140000d41c10000e8000181250380 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 728090053 1250 728088803 728088817
    0x12050415020a0203121803190e090a09020906010206161b06020a0c1a04031b020a081b0108151f05040f03061e0b060f0d09050a0c060917070902 63
    0x510050403004603080340089034480340c0842d00681002400800e0401e042c05110b070420003240342054459050417030980c980c040c100b07810042d4201458500740c424441c05554101c1c12000f4030440711270034181c40d142c1c024003400000700d0140e42144001552503001280491041e55041c1d214252030f5005501200c000000400c41d183c41d4400e04220008201d40d88080c1c680c0f4902504d0b4100600c90b0fa051810f40d1114a04a84000c0c943d54410400065404000801d500800024074020b031f00b000c0c800104400a50b800050301e604c02c100700401c444801c4100c0c051072746030330f1701d030307a40585c07100e02c2040c00040620104e1600011034601000414186954945011100b45081400c180d2101544101e01e1005d501c00c0d11070136150401400300304100042100c401c114500f041107142140804140310f4050161000d401c036101294501f80c031901034111a54481c0d2040a0b83c0c1e44a14918046441c5661405503500140f00300602080440d00407074541d045a45000007401920b19004031103020b544205 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 728091303 1250 728090053 728090063
    0x3b15060706020f0c2107050d1b0b1f080114060d140d0c060c080f0424050f0901050108070303210923060702030711060d02040b070b0a06090507120504 66
    0x2c070507183c1003084040c04504c040c4001401c07070803a084101e210880c1c000d41c1c460011000400c8000c1c00141c000400f9000300145040c03520400ca49644400070640b04403a01030403581088042203810b45200030520301c201c0300d0010b003511158a41c0030349403c030b03002001c4000d641010b4070040f0320705240140f044012030740301e26100300035100c000e1200b03400e29000680032030208504840030010040c0702e001d41041c110300b5151280d11403904185101c1c10300d10141c0f02508100f040780c40090905c03402ca40c54840380900b5807044c00a0700740400c5032500b8440444541c00e8a520300f40012900e4070010420604a075090342e50203072540c4440e0507003184000301445950080c4d0341c0e40146000600c1100c041400c44122200141001503d007659a042000c020446411500200703c030b10002000c0c0942c000c1a03000c04d952180e100c589030740c80d0382d000b40300c0c81e040040d04c003a0105000007044401010f041c0315032061001809100e075110310b280c040e5030042e0b03105408504800c50401c241d4038a0307400141d00502070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 728092553 1250 728091303 728091307
    0xa06090503062215060603290d3e0904020307030b060a05040c080402040e061605030c121306060504180807050a080d060e0f09030703080c043b1506070602 68
    0x999a90381c4c0130440c0503000f160194481c8002c000c2503415114000131070310280f2505904007000c2140103004030013001142c2c4510040643c0d002030141160302044207030200d00e02440c1d20090f22115507220742c0640c0b00c0f030001d581044270001c600c3c00c014034540e01840d80600107141060456580ea440c100000b0065030704a4003e45000855941d50f01403d0305001142d15038072081e05280c018002a01d1000030f09481a034410000e0040d02ea040c0d9100e00c420300042d107085512a2644075090007180f047c025220700d501c0300c580038001d43c107241d105051b01041c40b4140802801e9034510a01c815217003599141540c4186d11075904010680c00c03801010343c50701c00c8060710305503402aa0382c903056803c0106040015959034505200b5203801842e480e8101c6a07010301d094003860310608965a900c18800010100204140070809120303485007920064000d101d034061652100b01040d40440d000d01740340c02140e106011544c5541812190500c6c040c0b07490303101805880b02d0903018003046030b200307103401c880003139007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 728093803 1250 728092553 728092621
    0x1b08070b0708090a0b0703032a03230106020f150601020c040f1401090f1d0318010207031a040308150127030b0a0902030f030c06011406040e04110a0609050306 70
    0x2415108405805d9010000fa1100c03021f080050480d4049040384000740c803240c295083c505c0d00046d011074000d820745004130f079400c509004400721009200d20010b144240500110340580c012410520302c90000049074941c0d01510826044950309485160246e0003c80030911503051541182800f503c2c0580f011521107031070078500b000300809a0105214a542e44140c1d08000168080d0341a820200c40e94203181012441c02c881e01d9106002000c48120700507020341e040e690092159500864004011404114910784d09404d480400c07039088000402410003d2a5100340e042600807802060751000c440d40c20290011800500306d1a40c040c2c80212030038004001070402d4100780c1319031720008001c1251401e40c41031514140c00c1000d03416158100703000c500701040c03000a5040c11101e81c11440c2542c4443e40001c0703034052103980c01c0210030503413941c1004140000c0100c03180c0c5512054922600d201c0d0360740c2d0121040842c1d4051250315422540216544d0002d05180c1c0d2051070240c1000442261 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 728095053 1250 728093803 728093809
    0x7020325080c0f060103110a0e0121120c0308010f0803071407150914030606130f02091008091c020d030b03191406010905130807031701121b08070b070809 68
    0x11142c102d00c44552084d401171040004201e007035603200e8403c1d00d4900701c40b8103046a01a2000c2c05000c4c1c01d50000380c1c0c12103504001000c2c0c1d108a41150425103400c103d14010358018500d4003400d10a402068410f13000080c90505030042c0c000315040d1502560600c842a0354948408000000345400307403040c0c58020030000400640503c542c4201d8594031126071034010b45403004040312601500c40d8211504000aa858100d120680b00d108000006114405401c0d504000c1c098010380c2504041000007031010142c00290050240800008032242d11140022038103070381d200c45003c00016000300b0a0a449207004e50040c0441280c0142980d41c0200c010307a1360301a8001100041d240e41c2040d002c0c500300c0c0030301406881e02401141a0620507494400c2007140b0b458980740740100b03202c2001954505251244014007004c0340105401c045a594806001034114001da4050320302800007403500082c001040c054034112501d843c09001854900010051503400500060307480100402c0344e00c00980d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 728096303 1250 728095053 728095063
    0x50a020a1403100b030304150309081c0b10020c010309050a08070803010e0a06030305160302030d0f0f06060216170a240b060909011a0d0207050d0807020325080c 71
    0x301840c50801c00250440041524108864000f808030914044120301d941c2c130701008480030f6551b2402c1c900b0b980c000300c80e0300b140249680d0038040d14035100418810740245003d41145a0208000424421904c00104000300340c000e0310400005a40910900601540a0f80000b020240240c1c00d4036905220b54a031f0b0030b0503038000101212507420010052089050402c03a0350b80140f40700310304000460a50343c0107070042c420a451521800160b18241d81054400c01c121891101070071421310070004c010f124100a0328486407202403040c20078002184091001900c02c4400031504401d1503003614129580c6160841c1e41c208040c0d0340140c406190126a40500780c00059921038090110050301c0307c6588203c0711b8aa0341f0910601d0100716080c0d01e5910248158151041444408020a18103042e061144144142e0030f031458004103660040c090082010803401480e5202c034665a0b40f802e5080340c0704c1c8280306646d180708072010001c12000300c0034080061440e1299801500d003603038081a481c070384 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 728097553 1250 728096303 728096309
    0xa0914030a2901031a1602060a090c08030c0c010905220c020a0227281e29010801030f080d0b0901150f180e0c0f0f0a09080705060301090207050a020a 66
    0x40c0103803032100d44500500c00354070f079030003101d1400002d00401c1b105802500e400000d80032607061522008071109000342e0014050017000034a040f20740c0c48244201e10b680b07450f0400199404200d03200c0c00041c0d0382c103008800c64088ad0218030340000464500c0703440402490000821011031060f00b400c03030300607110240c078821031400000000398000900c510071315805200500c1c800000c5524001040e55110102c11008007250100c00841e05080903081c1c112424000780d0301d01101805c010342c80d149804880c00e80c0910007000345501d060600140b0064554050038480204282e40c1500d4442c041078108003c0c06100b107050f007010925118090005415503802c2e00014103100402440030b10154224000501a02d0b003800c112041d485030b800701c450100d40a100e6036603580044000941d4441090703007110301a402030748050b61105c200c5282c030f402540140d10000d002c6010020003045120001510038100e6a00800262641e0b00b0b041030760010390031006040341c0c3d502c51002d040006070b590346162405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 728098803 1250 728097553 728097563
    0xa051b10030e1c0c1101090e07200d0909050c030106140c0a060f0b010201050718050f06070b0a020405090a0e030307050f13141507050a021210020a0201020a0914030a290103 76
    0x4c000102d08282944803650360003e41804060f0004100702101c0d89480756115809050664600e1709405054408a14402c0c4c0094a4062944031041554008031745d802a900045010440f41c2d459810b046080c0c8020300400001c9254180380c017070401c1c0c8a4000b80303030300c54001c426210544890781e6114182c3d42041c0d1510200e0741c80e20207031441541d09200d030640c083c405207001c41e01e42004184441d001c0b911405031074080c40c0d221005079402d440b0482254606a802400c0161900d00611040300075081406814820700c410340200d61042c4050041070440c04000e00a140355484042050766258800300070160b800300107100042d008610280900000c0c83c85000030131100d1111010080703c00e102903501d00030100c052001c2c101291780015800c0d406503055400e810524104080c891800d8941d038042c24000c1d00000c1c209850341d5042d000b0b001500d4035078640d01ca1181d154852460070200340f1031840e405d94010a40c02000c603203c10654520a003207000340c4540c82040d090642c080c0c44098205a40c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 728100053 1250 728098803 728098817
    0x503061e2e0504180b0f0c041802211e0a0618090c170c10020c0613030b0f150904030e04090b011e05090f060f0405090a051b10030e1c 59
    0x4420304260107403d000075040315070300080300c40030340c1d945e014600301a00641288039820005807103612041c1c1201c01500204034069001e01041c10500301942c809104c40391100c4529403241074058488400ca4050781d000d0102c0b0800d114109403009243c4c40040c0411030044d280c1d00001a5200400c0103100c07a80c6022901185015490a011040400d20351100052000c107a01051a80f200403a41ca001c00d9401ca60308001c3d400501c1e03040f880d1016850f1401c0e486440090f001d0300c01d80002c0d82038412640b0403c402c070401c1d41c075500c0c84154007400301d41002c04045107516806440c41c3c1100e416074001d2003424116941603500d8007207011118290405c50b6100e11640050120300700307003a94006107080e030b1a903040c85a41005c000c1405030b0405048000420595070100d80281c0d9401103020803034201a1007040070340f9110f8074481c2e942c2c44001e0251b819000315041c1c1b00c41400001000c5e1702101010313104e03180304819440228000d01c07641c022138100380924174100e200890103440010100d0301c0c81d0740c0c1003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 728101303 1250 728100053 728100059
    0x1080d1d060319050c270d0c0b0a021b060405191a04050a090204060f0c060207020303160201030e0a020906010e01140c010605120105060a090f2a090503061e2e 70
    0x80c121000501985c1d40c00405004900001107101001d280050204100c024480c3c11080490040c64103000d0060081c81c465001040030740104018106a02c2580d08039090748080c0c0b50500d01e03c1084401c06608000304010a100030304124420f416540f84190700342001560b14000d00b20407032001c48441c0c100400c0001c1c2040780b4941700f01a000680041d90085190a140c80c00142c5401d4a40740c0180600c0481c1d05100180021076060714040c0d60040e003030325070b1030b0382c2980409194030200700100e01083c0b402001c540e021381c001130000c400590240210381e03240c84220043d00c0e845100e0303000da0b04000310300780c041c041d4548030800360090b0210680003041040c1010200464071f28004500000c0b685018200070040d0768824242d01140c04a0000290007551408494082c01806403001411070308140e6600c62078202c90012180703585140d6600c00800d841d94209500c9810a032242c005d40a2000003041c0c1140030768940d640c105142500c3c00481645501054000f008034003203640c80281154420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 728102553 1250 728101303 728101351
    0xf0905120a060915200409050c040b0a030f0c170c0318010f2c0303010b070c120b060f0a0e0c0f12040f0b070e13112104061401080d1d0603 61
    0x44003240e41d480c0b041c02017002c04e151541d0380e40242d00c80c04485644076408502c030501c442c01154081c02c0c80058442c2d0356200300e040036002e805201100305119107448141c4920b58852100e41025080c2d807a040d5a0300d4071076070030021440c0c1000d8468800e03401800c0600c85c10920920901c085640d180c0300c00b06010281c409400c1c1d0307140e0204d10305440b040308801030110012001c021241541d104000c402e80b61003c500b445807802540381c01148040880003009014409604405442200111401003903140700a06001c040811842071043d8030303e10034049640b071884040034000301d4200c100f00500700340360301c007403903006101c00e80c0d054132703204400442c013018007400d10b9299074040c125080c0810044076000100e009001c4962040c06034070f6070bc0260b0f4920812410840c0c0c500d2400103180c0003000c280c00c0719024004000d5504032603080c64110b600015029140095040382c40070030142034141d000f0b04040e6200d102c4480b0040450440600844590340c601000e98001c1c110304074000e070b00086032107203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 728103803 1250 728102553 728102561
    0xe130e070f050d051e07030b180709020c030a0302030a02090303040f0602010e16060e122d1501030b0903070b24040b060d1e0c0e030d0f0905120a060915 67
    0x1c500443c45080301e01c000c1440040c003012090201c204c03080729120704d4040c060a00210b50001041d196102d42402010783c1010403401e104a992415190840c1ea45c000c4034040b449299401442600140300c62406240282e000d5a400120340070003502e0810240c0c0082c1c110b610540102c00441c0344494107000050f8240300340c600501000b001441e14582c40c5500316220704681c4505020058000204d05070b0351a080010020300208a0440d00301035400e401c2500720941900345000c400c2c03080d2100c003440301c01c00103404c255400b04d1070500b000c07a4203540301c41d042d020009054030031a105c10082c80001071990000948120103100800700000428000c400781703c5164441144901e040104010250b56000700300c800a5131039501c002021400300c040d00300c034108004291000c0e240350061141c0c9081d0040d00c03101c4440011415542b5441c0d2010003070310b801c40c0a003203c0c000110302c00303000e1100307080c5540c2022558032860308417200f0614a0762400c00b03075100c2c80750480d0702542c0507002c6410b504050203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 728105053 1250 728103803 728103809
    0xf020c01110c0d051201050d080d06081f11040509040519080d0516120506041416140c0d180b0a090f060507080f0307091a040e060f030309010e130e070f 67
    0x4c0c04034989080c0c507140803c42d14044c0941441920181c01180820945104445900d11826401d0188a6031000d8640d10340c112064514007102400e03502441e205014407505110419000c44942054180814060040c1c1e004004440c5441122408041c0e002c41e601c56804c0d280c8a00d81944d905c0c1101703d240010345001800012544002090f03066407260020803005030f01700c0481f000603455a0f5100000c0c0900700203071800070407400c0380c000c1c00b640f9110708840d0300c842d0150f43c0740d42c40c0e10fa40b4181c080020344940b14825484d5009203000401d814890045101201f203000c64607200c941c0c5418042c1c519034810070305a0007181848208014103455412004000c004505090707003050b40c10b441d480c02c90312035003040e0080104000f0014507450301480c83c40024000307100003a5142c00200c2d43e0000b181d4071500851100a420034001070300d616010b171080d140404040c010b58141400c0c6c0005407509400f45440d1b07584180d80200703071006034180303100e101242031400009004903890100c0c684450380d0590 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 728106303 1250 728105053 728105057
    0x921050c1f06061b02040906150e01081606080f0405030f0a02160b0310090b180903030f0f070e3001020d1b051b0a1a01150f120f020c01110c0d 63
    0x4903407000300c0c030b43c40002c00b0b81c00d40540707000c142512545082c0004027280700c00004103011082012981e80d02d11841c560594109608030342043d91820710004a0020318031a04001407c004002030005104c0d0b90391542103481082280d080030f20048900c003050f00010340a1005a2004150341c4801900311050001050315554051850600300303401450f8070302e00d010b08440180c441058070340a07103c4d1141b560030403d0b100102e017810f042514a0076102d50003501d0306108036000001041c580c0408613101405412181c44104000103c44240116103040c031030541228440f000c143c1c242180e50840700b103004401b0100040c0d94088508d10001100e0001c4440174000d40c2c40d003c100d03c4a90454101c035444261310200225550740d0544181c076046105130b0040c81261088400d00302e805043d0400c506850381d44500b00e070741c0d40c104801215042c2206060000007034440c400308c40c0050440d48203000c80f00d070080000d0b1411003444030311400d6981074011714419100004440b4065203085c006550003014034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 728107553 1250 728106303 728106317
    0x24061c061a091602034314030316120e010504150e070f06180312031a010203160b0a0b0d0b010801140408040504050c0d1407120921050c1f0606 63
    0x100f2009549028210160620540b0140340d4441c01007080a0b00300b00f1001c90a0103820391000d49404540100c01d10b908030744801204c040100c1054001c0103607845148100c035405000016410200c2c0e26140c6440f59500c00c3d69a110059003054080c000c10307104038012840218503a8125055100300c9002e12400e09894201500038800110b8140c0403404480280c500740c40e07400ea8440e00d5141e5a803190344000c0c4040c0301500e0700c0132034030703010b400c200c603080d81000c138891601c81010016a03c81c410300310010001c0302c0d0107100b40c0c00145014401d5070440c40c0071000284544988000c01e040780020170342070740d0078005d040c0100300e640000d000b80301140300f080c0846400ca040c42e5031079401a0085002c0d0922964a0f800041c031513402600c1903070000350020100b88860400031010300c0c10300b03000359070f05c000003001228104109102d03802080c81c400d60041d80032141c0e0280e0120000b000c40c0741c400100801108001000b10803004020303c0c1003048080c1d24400002d4070032800c17203085a0301035000000b80081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 728108803 1250 728107553 728107591
    0x609140f0a11240a0914240f1201080c0a0f082d071d07020109020a0b070317070c0501060f050a090f0608013206090f07020a0c1724061c061a09 63
    0x4601d804000c0307500b54582e180d8490b021108001100d01425142c104507464a60001840307032340000e03300703801001c151000b01447c0c0d255242c0040c003003440e02402a035544506c401c1c402e04040d88207a43c5800c08000c005041e1707940300001c20b40c1030400540c0841c59000d03c1c800115083c007040300340d1702d41144850000b0804441070358082500381c215441840101140070501006260269000140101e01059542000d00d450900904000c80071182a10603601c0e00101040070b0804421031400d07200c0052103840080c2c5081003040103004503407031603103400d03030cd80340300044a41003401801041440c03840802140c15440c1c01402c004140c01d4100720b030b4000a86d00740400c0b030301c0780c00366250004861106c18842e40d0b0b4503081a8a04010004002c0c000f24405500180d502070060400b0310031416201a12050843c1144148900d83d5012003100c0190188021070060302e031208042043d0f02030041d00210703195030758031500c00312810000c046106440c40d42034050246840d1410a1740000940c04440110341 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 728110053 1250 728108803 728108839
    0xa090606080d0f0f180b040602061026030d06030b06090c0a081302040e0a05100f0207150507200706030b030109050d0315030609140f0a11240a0914 65
    0x155034a5184207101046918070026071103016184d1071005d04540340503400b940e400818009500c207100f2134005004100c00b0411800070030044000303c81c2d80d403800200303203454403000c401104c0c00c0b40803030002c078401008424021220f501401004501070504080c142c0f82040c24002405c200904411007660100090500b668011003070070303008044004081c021542e0762012400401203800ca49101d44918090001001400984c82100c1500c0d44400d015880c081c01c0520280e0180310002890041c5190742401031103856072140e0b52101c0d407840c1035000030710405800101001641d401120640003501c1c240800740d0140034400f210741d0b064008004450403600c406e03444812103032510040548980f000032440e0400c8400318091900040100100070107480e204451403040d40c480c01c0c0c0c500908030003080380b91307012424811080c0c10402c403800d603003203a000300324a1105510345009a0044d0341045112121503201400d1245c2e40394884007115801c000945003c01e00010f18907208141b00e00200394051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 728111303 1250 728110053 728110067
    0x9050609060403230f030406090503070624050a050402130e0106030e0d050a0c020d020a1701090b07090305120a0201060909050c030c0909071223061b0a080f06040609050a090606080d 80
    0xa0710881d464483d140e07423420f0409404400806845440040390000900005900511403002070012445901020000701c0d0510105441182ea22844024080110381070039002400d00809012800c0184e54480c401200c48190a800c07400c0001d640e200d152000b89010032481000c80103c0c2005820606e01c020001c0440b50a914001c0c041e020f2800c103a000c48d162284000f01400002e08210342180350402d1041c000c1c01c50709000c0d103000c040d60010654060003206c812081ea900403002d002ea900c1c0d41800c514482d804010703c50210341d131720300c1e002590040510402c40168418406040c000320940d013090b14040c0303a007041070310410251040c800405000110101160b442031141c10040c0c0140c14018607504d081441810031b0001c1d0b021180c0c81c88004030741c0501c43c0815103401124064000000c1001307004990000c00401d00700004034856181101d03070660b020000420108040b03071668413403c1585c405880005140b619110340d03a08021550241e0800b0f8001c803801040d410f40d01c500010007003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 728112553 1250 728111303 728111317
    0x906150c151f081506100c15021c0c0c0201051305060a17060f100c0f0c0902031006020c06180d020d050105060411120408070311010908030a110309070e0a0905060906040323 76
    0x110040c4540102050241c02c803861711f00d401101840448101c2040140a5480420784414044482040c0b00e03030344019224246110040b41d07101014801c0d20703401501c10390701400c10302130006540310300020581e885200800380e27043c00e681c80c42da201066445c540d84040020b00302d0361090f40d14858040c02511514200c074110852482c20a01c40002420203010603040d00708050b09a130b02400f404642c04403540c004600a076220010b0083c4161340b070404a840e900401821a80041c0030400039250744c0c0089028a017815004100306240c0740b465000885010180004580603515001041541d14140c0301d803001c2c11a4a1000c94038101c01082421540300b8002c0c0b0050401e075020948909061080c64601b41031903000303008106a44490070103401c15041103d1130484641843c002d0111410140c054a024036840401405442c2c100300c4c01c2030003960f0003000f8443f40e9aa41c8e0400000c41c0c0c0802602e4010303410701020f000c49081504000300100341095007020a40000102a143c4001c0e14048400c1c07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 728113803 1250 728112553 728112559
    0x23150901090e0c15040e0a0b10050f040b0f0405040c09090c0504050109030602030c2119110d050c250212010507090605090a12050d0e0906150c151f081506 68
    0xc80701814903031310214000c54224000300c204039010852028401e03030281c2c00c441000c07204074030101750550b0304442520500130409200b00d000e100c100200c402250117803c0390f1128006d05420300b0b40b154040750440e10602d1084c8001a41c1c4035080218400c0340c0314041c6608160b161452030b00381803400280200d00b480c40700601081d4000300140960f01e40805841452006801048660001d50480c01090f60709403041100d11448900030a00c101c2d0910865240061070301c903042c1001c10152408004180c010020008a4410884a04103000d2042c0c0b0348401100300d4032003020901030f070060015a6044130a0305000740c0c58a420b1100103034111303407107000301c0f10b0f14940a996410f03120045540b21440d58821026030418030b10500c1088408518590051100c2e507500d0400007030142001000c4c1c509a805603045064441c40301c05503104980101401300c603580440c0c0c0404c0a8841c50200c00a0841d601180d214011900140f01540c548140d401004840e008200d0310016580b0000701c2d013409816184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 728115053 1250 728113803 728113819
    0x6072009090c0d05010b10020f0f03030115080402030106090e07030b1b031303020a050601060504060e03120316050c03072402040f180e06070509040b01080f0a23150901090e0c 77
    0x1040142c00d40246d034258002804002403030740002070181d80c418840e4a41c03a0540640511000c04540c0041668101c514804005441c6600014213690f80030340680240e030076540360b800c0420280c401d8020000303820305013801000d040745941444521160054446808000050901110007002100f500e80006d11110b481020000500d802c0e843c001200e1001006802040000111150000083d00489840d84c60382180007108101b05611199191203c0102c00800e00108801b03191324542d034040079820f8200213162100940c45039182d6005500100c4101e680001101d00d1032000b20581080c0c800d40100940c10f041c213040d54905900464000c0100c81d1715942d4480c0c034041026001541c0d4920241b0030b66809080c5514000e00c568000c0d00c3c1e007070056041c04c0084855502c2003840d144143c1c0d0032000000c1580b2200b400a0262541451950701403041d560400c13a50800d03070107242e0182e407000e502c030091202018140025140164012143c81c1d1030440d0088040101145810303c80034215083c007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 728116303 1250 728115053 728115079
    0x30e1c02031803191707170703090803070c03080901030e1207020a121106030a0f14060306011e050907030b0a06051e0301030f1b1706060928090602040506072009090c 73
    0x41c0442c0207603440a05a180c1c41c240000f6001404001080c22328000d948181c055510360070119501e1180080052680810410401c003092283e400350400110515020a00d1004140120300e4024064181c036050708000680904514040102500514000500c4c0e02211890b40391520140404c83c3c00c103008017400000241e1082c503a60101101102c5003000304900b071591400c0c003040c9a411584c00c0d0003441248004a40105000c0703080d00d00d01403024000d035040c2d082c01c0a104007401c002c5c04200030306440b2141c01a07a641d50314850005818159191500d0308054800c4004488500305170b864000c1c070810062003c503c203440f81200c0c0c16080072034002d0030000c49545070003200e01548001c5405070401c160102ca0100460500d016400459199a8603103d0703040c0c18803101c0c0d42c21034104102108000800401e106030308078002d1140910001401c1c2995900410901d900500088444200c103809058008210005080d1074110650f123825807849c000e0f10907036880551141c0175201d0200c8503150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 728117553 1250 728116303 728116343
    0x20d1409090a0b01020f010203060d02120a06020403080c070f0302280806091b03150f131a040201020f070302010806040b0a0b0f0a090806070f030e1c0203180319 71
    0x11150190040d040441a103009409003005203070f0340342d065006010f8041c1000048205000f501c2c05588010034a502440c11542000a21650345111254900032007041e40003045451018000550085001c15035904084000e01d0910003c0c0d0000325085e00d03122014030150715101c1c5421254040d030700030070300c0b120103a83e0b0000c014141a0b2000c0030310302c58601040313510040031840c03919810390a01c0340070091305c0031010140c6a02654505c520b403072000f000054000074050b0905600081d54070044440c06c1a1600c0c0c03019a8501e54002c001425000c0c424003023156810071441c401022003101510109041d42d00007891103001500c8180305a45030100f450b0195211207040303000300442959143d0368032a25510b600c0d560400c3c2a00b101240c0341c5007000881000100f5054415441542d410503511490703a030a8004202d54040108540305a005030320341041c40c401e1152400005400841c1c0b14441500300700441e282581219020350040800b121414070040b2504000315401110a42da615044d054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 728118803 1250 728117553 728117557
    0x210c280609060606020d0503090c0105070f06090b01050f040509060c09030304050402071104060e094605010c03060605041a07020303030f0129071104240806060f01020d14 75
    0x80c104524044005003001074903440101269920f409407030408201e680b0540b602d000448103000113401007444036003d907120f00c00800c0c480f4400d1115280e0f403070260301c1c1d000131140c140c175088500764681c40040c0214a002e205801d10301c0c50841d028411440c00f5402d8589030000900b10f4940c40a01090180d90395805105480c041c1c40b014008545444150601440b03019805160303a018030b14010380441d48003c06002203214050100040c500003003030050003400c1e18464080d1070401c0d02461881140c090040e1440d00c20324409045090495a031410702c0c90840b01581021000c2c94500b00c010002a43c010317003903900b142ca150072a18940141031103050082e00c1040c000a6040c04000104049420209003a5040e83c4001d00a51000d80e40c04c2e407a452400c0740100c0c03030544604280a00c500007802c1c0c0c403d100e0b52080241000c41d2420b0000c05240036100e45400f0070380c2c0482010018000d4030001c000c040d81c00081101c1104900b60400c00103500c41510071042400c00c00091300c01c00c000d9035800300f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 728120053 1250 728118803 728118883
    0x108040311010c051801020106083c010902030c04150b0f0706020313050d03060b070605090708030a02100b0a0b030c1b0703031e080606180d0f05210c 66
    0x802403015a841010040083d40701d4445009100217070031411040d9441481003200303031203041c0c00400b80032003203007055401b8001c0c490004a4000c881c00c1c4001c0292040318200321511161b10000c2240d40481c4101401c048a40d85064052403600d8100c5805400c0c402c80041210000800b50740e5500107001044a03510880f030020784602d0000060000c7c1d014940f82100c10b150251041d12070340807a041d402c800b0f50750944500c1007801428041480400c01d90f60103a50402e641c01e003241c954540d1004118110741010408102582024040c0201112240110007442c0c4040b526070010a04014040700715010240100342c06041c0800c0910406040c4001c4400b60041d90b002c9983c01a500d14004010f5100da1059041c0208a68014050305015010f02030203010f009211130f05051200800e50f201c41d1f044410580c3c04020103540c20302180c0600c600c5851180642c02a2072120400c85030091141c944d40501c0c0000070b010406100854001300c3c800b6844100645611910800300304030300003003a1808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 728121303 1250 728120053 728120087
    0x120e07150c020d05071a040f060e1906120e060c0301060e03151f060806030a061109150408011506020a031b140115050604030809060a090308040b030702100e030901080403 75
    0x104200044c02000a080c408076183c028038010750b10f11005e803020040c002c9100f400412600070754107001180c0504a9010b05000142000744500e00505110800218603400180030400c680700c8200d82d08450302400309502600e100030a1a8142a0441d4510384414071a0b842081440f00000304251340a0260354081e881c4000c1d0b40b001c50074100350040007801e080c00c4560311500140d01c00038619005040c9a031242d10028050f0041050342e4036607401908880c4030203411036004100722000b130741e03913940d42c54905e01845150a486908120540b03084074145ca05c84191b40240000c1008450390010705508582d40c5071612500c4400b00108591101070801001007072005c686c030400725070800550080c400580038240000b007450740d03038041c0100b40c400c901000c0e1101600700941c0b921810414020200c0010600d0100f802e21f5698035039200e10303005030304072509883c400000d00014903030400081020380c2c44150704008558500088a60700e00c0398012080c1404560070021f802d02d0b00503503002e20342c0c2c9004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 728122553 1250 728121303 728121319
    0x70b150a0f0617070807170613020c07080f01060f0b0705010902060f07110a060215100503061608010b0f09100e1f091502070320100f120e07150c02 65
    0xd620043c0100c00c1507008520b402464000180840f8824450b4500641290302c4441d007a074140c03a48010b84140040c8032a8200c20394a0a84c07000345442d10080c84240018001740c950309040008444c11b12001e0401784900e6030501e80c0602c040310a0a80c00d604464401500307607138a010b140b80190140116100183d400080400d890076071000000045c46000e214441480b844242c1c43c08105155089001d00d100580c008140383c0740c8031600d050f58a03041095428018074031991180024038190b0111501c0817551402c00c0d071214601d030030070085c501400034204440d05041016610366103900802a030f01c0c2c030518910b500c1d802d0017402071000c101070010141c90084800c03990102c100c9461004160380e00000d001800001c2e10144802201001102c03681c060209545580c40c1e900038450845103a10103c403400c0300071080d81c1d90b150f10300e4101c43c65a480f44010f0b6200d04a02404132231016402c10b0181d814110304481c005004550b03002a500303035125020789402c0307a50317040791300c0b05030a50025082000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 728123803 1250 728122553 728122559
    0x9110f0307030906062705090613031206030c1502030f0d02210124050403050a140f0303070c030906020a02031507050d020409062c0103030806010e06030403090e0c070b150a0f 77
    0x22124040e134030300700050b901101c010b2002c2c6d0071038101e410444e40c1100c540c10140220b103081d8a01203403680c0e114024549000c540310204400f008481042c0e000311030481540720104603401140b01455003001c030350b001075070030107110142c44c01c102e101d00ca6000c140c0e00e80c00140f8064220034505107418422007a40c48040c25a1104100809001085040070584032941091052244110204d600703a80c0d01c000039024152103503030f035440e0420076044c00808a005007103c5103910003081002d14450181565500400c00003402c01800319400b60b08003c0440d0041e4000e00050788001454403244155511181c00075074903030000711424041c85a40c03002e9035000183c005450741c07081d04418107640ca4400840c150b1408611301c900e0078480649400c40c803101e80001000800c0c052520990700c4041030401a03001001c11002850315030040340c0407404034a2b0900c080c445541419910355011000c1d0300440d2a040080c2c0b140301312020001d2041c621a4003060f880d40c05600c8200d00003004122002c488180652 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 728125053 1250 728123803 728123819
    0x1e030e011209211b15020f040e0a0c12180f23010603110405040b01030b0a09080a080f06090106020307080c0f030403031d01091d07140408010b03060109110f030703090606 75
    0x29503149a400003c41c111000745034485900144400f04d80d000b0801c0d41c1d4401c600c8050000381d0000c100071140c814052000090003181000c440744115030303a55002550040e1b00401410604002e103d00e40e60741d240006002003d1444406c0500c50340d082072200030103111f40c1c94481602d03003040d07051750121550280d10071071000054110b1002d0701e208640c88076101a00005002c00c44004032030280c0310100d51001080480c42c00c10b11550081601072000c540e007003aa88900500307903c04540c01001841c41020483c038509001c0b4800e4000b20101d80841d00c039450003400035500d0050803400340140500041802da54241000417418940d103070401e9986899507828054004400610001d414000354028808150303c1008540150313445e06801c20980a050320062004900003041c0409000452088001001450028100800000001007003d044050505003444411b13445a40e03158100781020740b210b07001d0070984054001607008251a680c1d10103044003d000700250103410383e0b2a105010030015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 728126303 1250 728125053 728125103
    0x60510091e0509150720060c030a0c210b01210e100c020d110c0405180d020105130318030c09050105041a010e190b0f04031e030e011209 60
    0x110700034a08000d075550329107a00e500c640c0110f043c081940303188400904800e00904074014103264288810042218184003145008400c3e100c425030240c010040007843c0003d801950002e000d1840d001004942000307000d43e000c00c1543c101e44040c1d03200d401400007a4400c00464000c081030140350300210501c014103d004010402c00c0b00c5032070051004020714010203011740424003a02e9401030221401000e0100c5032001003445445160144100078195a541c41c010700c1c1c01400c0c04d008207000c0c0c10040315005c0c5002c1c4030190820640e4101801c01183d10711403060007202c00d8150404000304411030250b11180324041c2c2000304a46480c1c4008600004554803060580d42d003600c0c00c004400b000c004900400420a9080340040c00d01819103806050450324500e4681e40045090940b0b41c840c02e07615016004401d10408441000c21f00700306110f02590408240c19008031110b452446944001b0503d441d03900b404d0381031045080c0b2070300c010081d95000400d034039040800c4071400e140009848102c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 728127553 1250 728126303 728126351
    0x203120a094208190e1b030601081606031e020c0d030e011109040207020d0213050403200a150204150c02031e060403050a1b05061e010f060c020411030106051c0606050706051009 78
    0x30302c18230002140c05c1500094054985100002c00000b6070b1610f0021400f8008141a40b844200c200240254243d80c44c0090204d004102c0007a003100e010740741c0700a00321802104d50004a07810907012104100314041103503801041a1409030b654071245c0046000d44d02440310003904003016001002c0741061551005010b24420f0b92000886c1c003120b0b120f6040209075541c1e00000da00003c445200180c81440d140400c540900303c054182035441100701060201c400d02d140c0480c00000001c800c510741402040700c12040d108071001e0b00c1400d00700e003076907401c00280024248400060360340002c038040c50300a031054044070366000a00c6840e140041d101c03007003600c14480510610b03130024003003049441c1b41e80c1a141b402401148040c5019000c550007004183c0c10b81e00169100c1800351400d13841401107020300348540300e043c0e41c0c10b20344c032046103a212100800a1741c5441e240c03090119552140880d90b00c40e42042020485444402c40501d020003282e0105064a1400d50b042c0003111301030442c0320700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 728128803 1250 728127553 728127559
    0x60c2315150306150904050106150201020403110303181e2d12210c0318100e060f030c09100306150305040203120a094208190e1b 57
    0x1500e18110241603880b0410340e200d549400141d908000c039805d00304e5075554498080d80001c50090355500712200454517601803078006035000034050041c00f206148801003a001500118501110504c402100c10501c046052180c000d15100311311b0b2000410f5000da80580042400707040300c0140c0c503400c00080100300d50f1004201000136880c100e01d89584414051034200016110020241d004c4d0010120305003501181c42c0e81c10300c0b0301d00c06000200064104407461040c1406008940c17410410f48203c10b011030300030007c07600414034480d01c90009807410f011007144450740366220340789118641c2c094081c1303142d00018458030a40019502d40c01c84403c486060124015000d180e05c812416520101c60294042d030200d4a0041100034120041c0b1031004145890315105480d01c210003146480d880140d250701441422030a030007580d8a254800400300089034240c1c0d1000c40384041d1030000000c4c0481c03482071240024040d049002d80022001c03038101025101d0006c80c1a000280141301c071590980 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 728130053 1250 728128803 728128831
    0x51e010b040302090f0601080a150b030c0903070f0f0621090b060913020a050906061b0105011a07050c1e0d0503030103062d020a0201180b070305070207060c2315 71
    0x400601d03c5c0c0072490051606030b4405441d0354418070200043c100044007001c10b624015800951069a8400707036000f0030301d03100c1c910359030040d501c205480e10345581c000c1c03001c0e40901c070000c0003a10120040801250803500300208007080960785003032000071007030120b420282820240c00c10070031070380c1106200d810b0031540301d41c96803030f454030034020b0890030000250132191040080c4800e01e000040c00341e200d00c000380414581a0103403003030045550b240a203444182c0d107402c0148442858087e102d4529050b030380900d8100000c0d911a540e5a80050b05c0180c0101a01c0008032140d640c45000c00c988508007406950402d0344c40d04c0c04680d40d6100f440255180d0340340c030400c80c00300c00d07021408190740c0e08258000c1004001d501d405038001d500c606c6298040d0742d070b503a070030b03075a1000c0741c5e24100040c90081e25142d08501e8400406004c1d20001080e00d011500b0416090003900d802c040c40ca4440e9401015031120002a018030100007056008410310602c546820b02c0c02c0b104115480700e02c034001e0b40314151 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 728131303 1250 728130053 728130061
    0x60b0414160f05190e13090507080f15010e1503070b1810050306060a110109060c030c082a070b0c0403050712081b0a0c0e07020c01021f051e010b04030209 68
    0x241c03d03001c0e540300c0000c0ca812501084454501c44c4403540c11a6100512800740c2c0d515083c001001c54a0000c400c84007504081400c020b10f10050221503040800d0704050100206000003c0440000501807400d815903d1b801043d21b0300301d05d8504400780a40503003210201d07030f200d480342542c0f9040561048415603940c0141c500c9820549100c02036154641c0344c1b2401c5444e02c1d41042060f4021a042500b00a4580f20283d2200024048d4810386409040b000450744a46c5030028242c0c2c1501052005009500b000d1100d80f0022007400c468226400082c1200004085a842c0c15480380240207080b041460781408085a5070070028030807240b0583c21110320960301d6844030111040e03c4800b03889140d091180c1210701c140260018041d6601f903003940d803114803554031445e5128030341c3c0190002951000c03c0101040c0c0400a81e06481b80c00d00007011b032100d10105000c0e030383d070b40c4001c1d8150958a68010036040f00403201c80f1840400d00c0584010150317110703080440142c109110036441100e101e0041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 728132553 1250 728131303 728131307
    0x13020904050c0406060c0c03060e03130f060905040203090a020108090f033c1206060f0309070509011d04061505091305120a1b0201110102040f03060501051c060b0414160f 75
    0x12440700c075400491005a41d123140c03644402484d0110320304c551400208051400070902c90503e07405006c00000048021303060403402001110a50882800b49204005000c00c1140c001030351025154246428001035841005140c00e20346034100ba80c42910000c40d80354071400c1c042803002854040c074020600c0115025050a0910724250382100d40c0c104d0800043c0310850000380201e901900c0900000c2c98040c044915000d5944215009690303904908018891f92400030062401080c0e401040680364046910039008140302900061034155a10b400304444110304025000520005144004515192070300c0c090a40c464107040300c490061000402c3d845002c2d500b503415100765a034800502e40c040c22809034001b91202c07005da0521003c1228003040c904240010700150079000010380c0000d03d10320b0030009a4070117030052840754036100c65070207142e40d000600d0b0344426080a0007042150103080810028080101c19580b00a60802080108000701d48640f85c020303c1c594400b5156884c20f1b0007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 728133803 1250 728132553 728132567
    0x308182b150510090902030316060509010c0e011b0f0209190f06031a0a0f06080c130c14070804181a01090f151205130b070905060702060313020904050c040606 70
    0x1c505804480c030f0a09214041840d800858054809411031307182c84811841500d10458000080b55425100c40030001103203001e0050707009840d550b04116001c035012000181c40001c80c140540c4104107910807440a100c1100410208903030081c0466415060480c4803041204190405a6a203400e0210001011f180b610840c1b0481c0e800400c40740d880c81c0302155100a26501610315007030305484444154141005115950081c038801c2e0081000d4404c0300240304000e8460f01886104030f240030b50002020380c0100181080c0144a04e0a50b640c0000b49002d003800d01654109031281e410f43c2000e80302889944c2d020305a10000a50303521071904c001c03001103030103021500036a1048589101e00304445860034a0b00c5071000081d00340003140441d468944030407110f04407100c5c0d600780f4100080d1400d0006020005d1741080d2146040c2c0015410080030440b0b500ca0482c00034016040000020f0a142e91390340411002ca600400c80d80c981d06181c01d0190355100c081214520480c0b0344000012105c2c0682c0c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 728135053 1250 728133803 728133811
    0x9030f0c0515040203010b030d030605010207230105030912070b010914190507051b070f0e0108060115050c010f061a04030203060c0c0106030f03090f0b040308182b1505 74
    0xc002d01003a1000b118401c0282c40182007280c040d92118004452540d0a00848031040c141340c2d00010f103036141900080c40e10f07503243d02000d1001944c01d204080e2070318070038109000c50003c3c20310320341d80d403915100180b80803c6496484106000411000c0811240a180c2ca040720750485060113044030044079051a48400e550814a00c0100c9245914140740780d00044c2c0d004100c0c0c1040f500344070380700a0444580740751002c0004107811451080c005400c01d422202e000e4640180580c1f4258102000700360380b06418003e68070000c400c1c50035004800d00c82c3d02110040b841200c000e0000300710701c0312040b0280c50580074101086c9440c5046888801403d8146c900b12500140100019103866172400e9003039018500005213135491f07880220100b580c4810a5900c14465600c1701009813030444846100761898101020046040100300086480c22041c0ca442c21411140b1001e50344030740e00010b10700e800781d8880034440c1614006080c4104840605250260f01800c07108841e0380500545c04101d981c121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 728136303 1250 728135053 728135063
    0x702031314011e0306120503030f07020703050a0f06020d020408010213060f02030d150e070c0b0106020a0b2409100e01080606011e03020f180f030a150c0c1509030f0c 73
    0x340b100d050700c000300f0f218010740c04500300020b40644890307003210400d1444009483c0e503031001082c403072110011145594880d44a2001c0d0182034296512981c03902c58181024100301c40101e59101171016990403038400c030112001c01c540d2075035a860228043e40000c101101c240594013000140d5a0041002c102c4410f001d5020310301e0305000c400c0e80c1c002044180c0c0303088500c80140001155006110084a000f01140c0d1115583c00005140c080101c00c01600944d08542256401c0c60006d07449054090300300903003202c0c503142241c010810a03160f011182c3c00c550310454050a11480b04003070903c0d40192010b1101a02d6240c0c0c0314600b841d0b880d901921a1800610a050a0030752410380e10300a555100da00d14000d86801e03194003041c081c0f60001c02000c0e030401f603108080d020030b10307000070038032200b55003035010348143d4a90b51150801a60311400d14000390f502c480002035181c0c0301e0584180070603072010340806440303105810100200300709001100411480188008031030302400000e41d0710303a440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 728137553 1250 728136303 728136317
    0xe0708070f05030106050f0403080a0c021e010516110312040f06030209030705040e030408010504060b0a0905040f0210090302030604141204030c0302191214010b012111090603070203131401 83
    0x10040306c2c940d2140c001c02c0390941e8248804000101c3c800018006250705c1c0c2c2d2010b4044005004102d1900f5000125000e01e81902c0c04103841030f6040740a8806000c1005101503400c000e0341004460000e0401c581d580c140620f842c544000c0707d08401030010390310340307008101d009522050164224070074000810380c10b40c0304080070042440c2507000300401d6030b0f006050780d09150340c0385035a07800d41e01d003030360300311080d0b61603141c101041d06200c00403030010402658244024201380e02c40714004440004003030300a07034a9484216107a809003000c2e400866001d0101c81c000e00d024105144080d103404e0306080c0601840340450032f07941c648026903041da90000001d802c0700b0320396401c00007001e1980c4055100720b820000001007a19044400c1d50482d40038021802603050407886c06802c44c0d03140103c442c14040752640718128000f640102d07024060741040006101594078103001058010249061b03440f00e40001000a071650110241800d2180b12130080d0f0b1058032040c2e80b0440d203401d2800d0900203104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 728138803 1250 728137553 728137559
    0x30d02120307020106080d0509040c210f0e0d0c060b190b071b03030302090108060301061404200a0903060516080732070b1003050c010c0614010e0708070f050301 71
    0x28000081d6040b542500000070680ea030751010900380400c141c03503035010400c08540c189107803c15002c0c0340c5119807540341039646040c030005c40b203801100002d4009611a590030001700c1010290307000c1d40d0b201051800b1034401c240010f07801000c1d40309117001110403a017014008041402d10000d003d00c40303181c080d5140030f90340c286080c08640d90400744080e54002e01c1b1400c50300c030a48024104102850007640c01594800500c0c002515504000d007070341780242e01d0324508000d50150340b0000d000090003250081207802200d44d14121111084002c4000e4040002c1d51114503900501e828040343e1080c2018005599a0140751000014045581020a0702c40c40041c1f5101e116803003da1a01090240b10981181500030b0b01e00c8201d040d417403803880240000358100901c842c80800d00c1d8051000c5803004c004904595901d81c82d490304210b824103100c4034136496030030000541c0000808031051380781c040c4030703607521560840c6415080e0381c44001f003421340f80030820b014403882c0c0100c5030301c00a40f1054a0b41c0d107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 728140053 1250 728138803 728138833
    0x1a0726040317090f10030b0405070c0203060f010b030a09020d0204061409090d020c2709030c07090204050d0303050912030426031302010f121b0801050a0806010315021b060411030d02 80
    0x48085d00d580400d03076140b0007d00c065a480c4110390081000e581c940c810b11070301e44145440e1000182921402209201c0104289070044003101c1d0300659001010400c1e1546101180d11491003910096000781401000300d104860306000081c0c1d25412074103090942c55600a00341c40381c1c0a04ca043c4016004004104040e0800a100c04800c0201350040c0281583c80d21480c9035011080e25100c0d05508005030b11030045204000c107201900d280841185007900e000c0024141c000c040f00000c1c203154032600002da051000b801a0b40301d030b059a20001c0e5880c82c207842c083c4000011400c0c460b1008802da20f400403401031900c1582c0c410940101c410b03c40d28a250010340c2c0c4c1c6406c103003000c810810404000803130394981e40114200c600d42d8a060010080249401034842a0305070010750140c040c0b03000c02c10181788c0006815044940000110488140301d4240601030b00c40c06056003803110303080640d2a01c4420000d0071522890280c1c005044603065074041645138044142c11302c00680c04501d020380303455 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 728141303 1250 728140053 728140069
    0x9030b0c0405040e060702061005010503061908060a09020306012c270a0210050a0503150409020a0b0a08070810050f1225050103061a0726040317090f 66
    0x80414401030038503550381d0014050304c6451201440d20b4000700240250150100081500f204064201e600315908040c002400303400001c001520070442c500603078031049128441d0502904156094808600d004610b5401a2900c0c000403400b03446640e0000400b417100a004c0c1a030400a02810210a039088a03061010034001d09010550230740810340c54502c40b00c1c00d03400780700714001d1006001c0c092102e004000303640c3d19145140040c40b0007080015011503100381220740c0600080c1c505c050909003034020078002d00301e092000b50450320005000c500311503a03402901080384c15590b81c070441c4d90f600000f21046c0d24240c6d81090302210002c000d10940c43d041540b0b110984010f00980c0a000b44001094030b05458815000922088281e51200740301c803604401c4046c000a00381030103407e28000501e40301039110300125024400100d0710408000b541080c0e8003000120344c030080400168007400194070303801440700300c238078800000791080702d00940b900391105008000d10b07152072800b16038180040c0c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 728142553 1250 728141303 728141311
    0x306020a030e0d11070b0717030a0b19080115051509011404150801080a0201020703030e0f04290301060506070f0c09060b030714030f0105220e010507030c090609030b 73
    0x105441d41c040e040e81c95410041c2180f05802d41e9140100380118281d21428115035402c40b20442c4820080d80001c0344c0202d03807510014510101e140d5032942c802d08440c0090042107001d0f5400070b01401010a0034000040300b1080e200303000000c00425a01c5050108403840500c0b415404c0903884508025412020f0050080e001c4c060401010f5002a00e042640329400340e08010030303030000c0900302020603602c03210180c090181c880c0140040001e81e00041d5503910184001000c1010400d50403025441314a192864801c02038014001404842e0b554910300c4d006a0810b000d010008100101502c2d05002d0102115400b4000520307040554540801c42c5590341e00980700000d1815000503409520f11800b0010000282000e40b03a0402c414014500504500c0d242c2220b48140203019001d400e98030024116001183d03480754000000e4505030740d8004240e4051f081e00e00d0042000b52803e03040d080f444c42111165800c0000d0041c003081941c11340814082e460011701a81000c0c800100340661180e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 728143803 1250 728142553 728142557
    0x2090f04030e152817040b0115050405030f15150607080c0a020303040e0a18150c12140417070804060e0414070c020f0a120f02041803050a14130306020a 67
    0x1404403400342001366140320b001ca040c4480e138a001c8004003541d0201c508000200a00d140c042c150820f034889041100e07040c00740300204e4648400e00001503000d001200d00400d03001d0251062608046403460315200185000d803160340c2010005141d03054000881602e4400c014030b10360500e0305a4030307006840c0d000302d400e6441a110788500000036a50400140c80101489040f80c030b00f5145c000b00000a8404002001d050201c031004001c0020b010071052040f113018100d800554040341d004200c0b2080e043e10b040814142c6418150400c3c03804105070f4902c078500403214803160062504130501c40e4420302802402c0810700b8042445128480c20003607400f09402000420320380000103411310303500400c1c0d07140c10105113100b008004600700046000ca8070300d0200d480706e0b02c05180610220f0300740d108280040207003418480140840d911313a4400e41000300000450000c1900a160143c100d9204001c0a0b000c1690b04242400161a02c8100c1d0a00c0d50102442c00f840780c51a5603150180d0800c2c0c42c4601 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 728145053 1250 728143803 728143807
    0x507030218070e0a0f0b07020a261e071e09060b0405090709030c06140f070321090c030210020f06150117010e06010e0a03080d0902090f04030e15 64
    0x50798407800840c00d100203800d8070341c50341e080c01a00640030000f140702c014094540c0c3c8000300451000e00c0460000c4410441d0030603a00c0c54644006600c1207074a80040c3e0562a01c1d0801320b0fa1880d034038070440c40100c0c124003103c4a2072420100301d0280c0d80c1e0441c000b505030b4441c44040c000c40108102e0b09022045200a50680f03640304d0710070344240da02035048210a40340c0424208410303c1c00c0c03c0195004000c60801040d21030440c2c541c0404900345000b19400c0c03102403060500881c04074001c03101c03c856092240c60311900180b0b002403086102a00803a01d41c0880c40302c20700020701c0c0d841600d040b81e51103540301c250a40b4641c00c0c0f141400d1002aa90250302801c4481544c0d900300f030040034403e1022070010103051503400f00160a4031194070700c44821490840060181e5042403e80940003542402d0014038440c45000103175240240c0e800c002e010420100d8056030305105074000e0881c50341b0803205c0202e1980c480ca042010b00b030085401900086064a00310981d040c601a0208104202c202c124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 728146303 1250 728145053 728145059
    0xf09090302031e0d1103070f08062809110c1005070c02090406060602121c0b06040510090f050906010e100509030d08100e270a1a090d1e05070507 64
    0x140401600c901c0c3c0801c1c4440042c0b00042050381d0301c510300e00e043c0da25141504500341500300610a2a41c204000d01303208070800852110340d1020745030910070326180c1590100c0020050080201d200074429501d4043c10120400282c03030317451058640f034102520040161a40900c1d010b005440003500c81428441c6110400016031540c003a0789100740d01030300d0085445464032200030320f09a0082e1407500344410a1140d00c040d002d031100c5a01c008007030b4850214020003070600184240c85143e20243d48081c83c51148409560032284010841e0442d001004545503500103015009104403100c83c002004001031040c50301c0c059004401c0c24405142c110706103200030010038a044190b01c0b082d400716048400300400701c01d640c81103030050704a40f00068480e040c0740b0b5906104005803000d00a0016290a0701000003a0801131050309a400c600c5040441c1200c2ca0002400b02054801c41201e0040c0c9159071012400b801c0010700910320018000d80b00f00c00c2150444181e04141411511401800000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 728147553 1250 728146303 728146327
    0x623031b0304081e1c0506060d1409010b0f060a030207030905060406020a05060903040305061303021f024906080616080708010b07030f030212040510060806010f0909030203 76
    0xa54070a03881000c040381d4858415018059216903090320201404c420090b01038a003d0b400b2400300d00c0340c03103140082a2910380c130380011802e00440202000c400d01e86841c4030310011801c035025010713191020081000b88410300902c04200c034a803240c1d40c1c00520401011150520030750082c8186406031030400c40c40c0d925500040c80c0c65120307900a0f401a0301c14003025081c41014045079070081c00500055140c249103680701ca840d0070000303040c52021081c400c1014140f5009000e411480e0f42e40071050203035a00c0801c207440c02500075402c80d20421048504079241d114801d00201002c0940f803841d052240540750840c004400ca03801021201507c0d50070025820004100d80ca004102c8170441320000550840c00800280300100810104178500b401080510078203821912850780500e403102340c0000e08041030303020344640803c000a0712242c41c100002c0c4078002c034034816068106e404c14003c080d0f80b02e981c00d030741d68402c1c0034040c9005c008910400c047c00183d0300c40806030748240162800c10540d9440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 728148803 1250 728147553 728147557
    0x80c0c0a06110706090f05090402060c0708071508151e0406080106030605091c05030c19020c0909010608070923070e0f09010b1b0c12070e010623031b 66
    0x80071000c01c100b021081c0c510300090264002804003482c280b5205c2c6c0c601012081258410710503a4050080c14003c41c0540d2960000c88a49040c04011608a103030b03500081340d81e9440030721408552011402a90038407900c00d02c2142e02902003815040791807221407003000364211064040d02d1242c0c40340510248981c4803401004010641940001381451844c2443d40c10b030341000b8030307070710a0341c2040006007100e60700e400281d20000780e0ba00e040c5840350b4404660764035a00c0740a02154001004880e24001180d0028002c42d2589060720304440c20388411900500340c848602038001320390007042c414050b44180e640100300348a480840110f40000c400c882e0101c9038010f690050c0019040522003042d030400b090400307021241030311840d84035850541902014010355000d0b03000400513814514007980c0c104550a40c0450051000c001034113420b00701c0381d5480c1f480c410380c0c520340103d50000030428024810001d1980e599001c00301200c020004056103940001e1110f82c4903120702040800001ca80d01c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 728150053 1250 728148803 728148809
    0x80a03030e060615040b16020a03050a0203010b09130305280c0611070209060409060b03070b0705070909030504152f0105090a210c0f05030304020111070f03080c0c0a 73
    0x40010781042007810060600a00a1250340140003111480032090004411601122030302c0414a49030b0500150340e04070f000d10000e0295005040c014048280580420070301800341c42240208068004042071010000d401c4a105100311805d01c0c4003000310340a5030040ca141c8010f00c041c10346215582e503550000b410101081c0e0b0001703055840b00e004002c0948500803050060180c1903041100d1a40003580b0030500411450049484104450400c5400e42010b1042040282540d00560700e911000100d904911405d5071180b04100c4001038800091085181441c0c0503600d01e8513090520000c82c125490060300002000420f540c0758800f11025482010080b440341c03040c1004480c00040e0340e081d544003500314400740e00b1280c00c020000b031800d019519000e103403241d40520344c000d81c6001d0303c0c0c1446541c1c1c0134040820a0141c01c00b0020084002c6104a200b6259181a000040e2081c1d9131911b090180ad00166595041030000c038a0180240141c03028070800c42d151058a44040340403540994 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 728151303 1250 728150053 728150057
    0xc01050c12030406060e090601030b01060c03120f05150909071401050d09030810080f07051012050f0109050709060512131e170702030c0d03020a080c03030a052203080709080a03 78
    0x68040c0821b007418050705070054031904c000c10a55046484084440c141071180105001812400d03004250140c40e1031081d00f0070030301c400c000b0075419401171000b80100f124912441c9080c030302d9014552516403840d0703002e00c4107070004001d140c0c03c2c07d804080d01d501e00c40c0014180071080c030000c1c01402c524081e100805100b61b94921190500d20f512194481041c0c015040a4000e44980344c0185000600c500c200c490440e040c58086404800948a45065180c0128054242010000e620311078a100c0e0341296943d0781d08114960b258442250311038014000c0000291040000390720f0000c2c21441075401c016041e1110025a0300b82c5c1c1d8450343c140f101e8540c1100300c64046858028851544d0365030901068503001c091900e40340f680000c0c0ca9824010405100d910b611500c003041c1031003000141c0e407243c1d209081e295500d9074103002c02e40e2600101c400f014010305000024080469004040c40032408031180100903010310f41d82070725000c90080070380081240800c03000503072050070004900310500035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 728152553 1250 728151303 728151311
    0xb0702150a050903010f090f1205191d010318080f041d0618090a0b1e091605030714060c10020d02090a05030715054509090c01050c12030406 62
    0x280301414299008a000740b418203140001f6080407a482c03040c40711100d44d2002c460120006118410348150290f94a4504a011090444c1040c160481108000584081d1440710b010818034011800c0d40d0f1304140041207a40e5045440c0e0015a0f0880a0300d00c402400310194180394880540c80c400b01841004403c08441c001d00380a024203250007410143e030a0082e03c06600c0c90240c40c01c565911390040020404000c160000340700d0300c03017040314080484104402038160b0900540181c6d44190070040034032000a12000003034a454005030f8074045410346031040d80b5a5211004121840d01308085141d010300a00407030300c8955100e84010809441d42d170300010b0302e40c0c15000a1141e59000c82d00710741e0180c3d0100780305006100d1542001d083d070040e503103001556140d0840c42e01020300c00d6a5040900d82d418100303540d00c06c141c1e100b4a281c10751451380554041500c90020821211070581d0b01640e150021800e04040f17501c04d000038000401010200d510102c40b26221058030341c0101ca09948103a66 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 728153803 1250 728152553 728152567
    0x503301c02120907030c1401090801050c04030c0e060f0f040f0606110f032a0703080d0614030a1205090303040e040b0901060e0c12040c05031e0708070e010b0702150a05 74
    0x50040c2c0f5085040f45006018281c150f0ba941403a40303403140602c040300f145948815803c0e038803540e401000781c80e429000b40000c0c20300c620440d84035002030204030343c2038003000d4003c54250082000140704440c0189001c035681901014003500711140180700d50042c2e15211202c0d011500e5000b050300030841541c80d80680300c106a20942064161020202c994108004450316040d010712502e94510750401c02c0d94181082d181d24500e0059aa84002d00c0c01c0c0c1d010480121003441580301d00e00b00c4041142c1c0341d60b018501000c15440d0f4038209402480c2002406c0400ca0701031107000540302a260240072203242c180c441b0440c1e00450401c5070b04854203001c072410031040100130702031080105042d1010541d036041089102c5103d000309201a082001c402d8002024060142c03d004002e29001e02501c1c0c05550352081686461080b17424100544500d0200040280c0c1c0014402e00320b0b10451940f03d003e900340348014007941d00041040c0d0b4044407100c41400d407003034a000141880c1c6503076150f90b036a42807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 728155053 1250 728153803 728153827
    0x60f07050f100c110c0906030a021e041505061911010e0f0c040204061d041d0607020d05031b0c010603050111120f010e040f02010c051b09010503301c02 67
    0x807180780c181013000401c01d0b400002c0c00c00001d071605e012800b00c0c3d8032092a5a4000400d1800c10410f001941c0300e42800240183e908107044c0c02c010341803055500303000c0b0303801c01d00c0b55444d41140c1c4d1156a80000d010041e00340080015a26480c0b1401d27139160000700540c610381a942521280e0609054a8106907140718440e03004000c0c2100c940b806807029030400c2d03e44035010707062003458a000c103403014800b410250150b440d540101c1e9054051420320300980000d4000c15661101260315070058400c494154a81c18000c0e4160307441138038080300e00380610f80d448a1900d200e80140c10440354540d211180031002810a0040d922924022410962102e541d0302000041c12000f42802c0d0388556031000600401400c4040c1580c0240c20000d040c0c000b00103032004a921a0a01300d003d0410300070380e42c820104a04c1c00c0b850f203030200b80440d0301c4101640c03a03004150700c800b8103001302c1681321504400d8083d038401404034203caa034054100282403282101c0c107001243e605845100005500003901c60400d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 728156303 1250 728155053 728155061
    0x31009050601021e160f0f030f051609020714060610030207060908121009090302030706091a101401110304051507060609050609070201230a090f0b0f1e06060f07050f10 74
    0x1258100b00c401549404c40c00d001ca01a80c0c00042c01e009206501d2200382b180810000c64410b040e180d5402c80d559071101100025000f0381811502074071100d0a00c001c03890001403c03802010700501c1110174040700c1400340c0c025440a4021904c250f1148881c85c041500c60011300600702d0030402034106454800b54444c1c404500750001451580341058030340100394000203490301300f50b0000d000110706001c2d0501041ca48c0784010304d011281050410054803400a00c0284222040305008202c0c903000c0300010342e40d028010009840c0360307206100400603842c00740d03251480d51521040182c9400000d40700e0b14141d901030740094030100d17111024080107081481659034000d442e0304c02044403034059015100180303502c0d1440c1030201203420210324000065444408643c0c0e010840500341502458449451901140d48a459420050000c3c181002c0c1e08080701103240504240b0380d2079035802d002c120742500901c03203668045000384080f0340041d0081120961200d507040060120340b0401048000303032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 728157553 1250 728156303 728156309
    0x301080a1e0c030f060f0e010c09210609080418050108120f1812013305180a0b0d031106090f10020319051006080c031009050601021e16 60
    0x4101e0056000200d0044200302c1c00340e81c0e000c00e0704542001541001000f03484000c102c9010181351607200906c0046c15441031070054250b03254107e4a1b42e0700d03000250074101444c01c140d911005094100006089940244101881002d4560929480d040e0852031a04004600e600c48c9680b03400503c1384090401541c1c41440d40010100c4c5032031000840340000307000c2c0038460b1944209050424640d0744c1c561001100080382d1400801419070065100d41c1180794070b19400040301e5107246001e004107000000c0c4000d544001d020100460600588503c40031801800c40080d6a134942e01440039540b0b00004640d0640256140740c2d0350310b2064425410010050300c1c2c0c03481d650103c02c0c081c4080a010030500380d5140076820050b2079075214410b003000c43d08400c4803000d5080c9040e0810118441c01c00b021720940c4d00d2582c8030710f6281c0d07440c500002c1910050300c3c0d03c44180c10042c81040724000507001035a000d10107105940300c114080014000d490030300c040800341ca420182540a0462101d070030070b401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 728158803 1250 728157553 728157593
    0x509060607021212030901091e0c0605030903130b0301061e0206150a090f0e07090c02060115030b09010e061306261203130201121b03200301080a 64
    0x42810260005000307031040640090040501a00800002c84140820f03415400b90909141c1c2c0d0f03192183e01c03030f802419070b070038100e03130100c01c0c0c0d400c0e000c0d54041e2611650750340f07030301400d030445080c02c2c1142034902c0d4000605030b8290784010441d088803515201100b40c0240010741c01e003a12541400303005003140e212408003035130070150704d00012015a4001401500180703e001407110f44903451003c07a00905c0241c0095440500b41201d55490242d6580b20940900400702904d040e07648806a00701034600c5444245c0040c1d0000b0014042c3d403415031540d104407040c0e0b00f40087c40c600c038031012881c16803099000030074120000c020800182000a502007514100c4003082045c503007004d0601c003240c0c1100c130302d80c02c0d980500b0040c10301540d010010640d1060300d10800765105c2c0b824100040105030049401c9000404800414040710b485010f09007086a100506400d0490418411001880505407990b0340725481840e441131003461100440c06010f0080240c0f10b11141c0341402c12840d89181a1198 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 728160053 1250 728158803 728158819
    0x1090b070c090f021e03040308180a080a03180606030201030b150f3103050c06040803090f010e04140402041506080103060504050106030c0e04260a030209040f020a1805 74
    0x40c204200034030035100c010600242c0007252180e044000c0c00b8500388200d01209a940c1c205c43c04c10220051880340d440b9683e454904c0e0b0380c4601d560121041018441515486080741500080d0b4000151a0039540ca00c0e0000d1156885801000480401542035130a01d0303440e8410b10a65a0500580000c058140d03001e6604a030080c9402c115403199004001190b075001c105d080b41204100000e5600e035450366414440f0034000c01c0020300c400d090348401c440a100c0c4402c881d443d402d000040d00e0484070071601841c2043d1140c0f0910805181800c152410045411107415859071544120f4146010305c103114507280c90244180030488103d01d002d0480640c40c548200300180d0b212408a045da6440280420300386c0303d83c6022030241405801c0144121001074000c950389810010161240e07024520001c69000311319180d10600150001194200000300005891030307009170024847d440c4040c000042446084101104a810a149250014040008480c4c0d00d0306622841805014119074a027 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 728161303 1250 728160053 728160067
    0x30f04061112041a0606070f0c050604030b0708060415050d03020a050631021c03030207050604060507170402150f1902010204060f0306080d11010209030d030b012c01230d02070201090b 81
    0xc1481c0103000300103081aa023501c0002c108a0b1000c5c10b200280740182c1540d45864880c907240c000d010080b106000014029000030b20a85400c1c01411400c1890f0600039a4050419061000d0354242c1c40e02030f01036200d81c5c800c0c400001c00400c00940320300b440b16902d0001090420b820302490080003110140619440100c1001da81c072001800c2040d0198100310412aa540c9009c0e40603014424000c1e00c2402601d08110601c295500410322039200d139592113403442c2409800388098541902c2c0a504000c13095030201040c8100310041201c055101c5201d03003071440844524130741541503401e280c0180d402050811425400a80701d006400950406128090502d0721b9503541e401c2e1200030707108000d100703152000c505a080d8100d55034400b000d0306a83c03022440e404090007a02c11944001e000600d52182940c800360a151290100212004202641d40c1307090b00458000aa031110814840125603489440c425014014442103030400360240c0c4540c45030002422a2400340d2041c0409541003143c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 728162553 1250 728161303 728161309
    0x2a12030204081608070b091906020307150e0a110d02031b090606040612020304080c0a2f010816020c030d1206090c080a0f060f09020d0e0a08030f04061112041a06 71
    0xc0c1e05580c0d00030071b031a86a10010000407219280700c170f80e020b03032070304071400106507584d0207c001d14802d409070184080e4010300f00c1480e8111880801c0c9502075070070030b140c0b1600050b0b80f03103000c17080b080e001402c0359000211074001a04007600021481500d01040d0701c90516810a003c20766407004081321031034101480d12202801410f00b031000c03691125400800101082448800d9a8000e07082d442200c03503900030b5142044a140c0c0460400c2c0070b94001511000d440b403a00317090740705800d4040c2d642290544030070700c0d0b004e041d4128000d24010350095900030221500d00700504500390341c40e07940d03114002c40744246020450305950083c0c96082d04085805080580158402e44c01c615941d10018018102c0300015000f071039a0f0704070f484a0307502e02c840010b0035000740c4c01500349080451400c114220b80510300e10360340c0307000503401030030310f40144005045d00340a15161580705004600100314226030b00030091680e440410860360002001b4240400d10180f11080301e481d010890038810300b400c00b5000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 728163803 1250 728162553 728162563
    0x402030a030c0206040b070311010608030c03271207211208070c120306061b0f030c0f081c0b031f02220311180105012a12030204081608 60
    0x10782480124491501151110021030b002016191a41034903141e4901d00280001e02c0845104055801c00501048492000c0202d9140d152803400951402543c144601800006801c42040ca0024a400c41d900c5c0c1c1c8131102c1205002c1c2444002e8000700b0b00b01007510741c0c41e0210100c0210301c2e54403005004006034002554103109101810040c41076510003804540c00b40d200c03d00209800c8914a03c100c00e03a030560003080654820340c860715041d02c1200c90501c41301c081000050120414008000302290040750080d403840e000759003001e0300e80300903212908164402140f5400c8000c8004102024002c9072160403540c0c402200548564051213400102c18120750510390700c11075000070fa4612040303070240d1841000c015408a03d40140d62424401c00d4403c2c0d2802540c014241144000c4030b03506005611410b80340c7c161180c1d844918a4201d481400b0084c0310b884525a089080280200c0c00f205010b0810055560340969201d0400400d2400e20740c03111400b6003481ea028034140030003040070036 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 728165053 1250 728163803 728163823
    0xe060703020d09140610050102061b070f06060f1802090a06030b03010f0e0a050105090d120f0b040f050103021e030303160c1b06080105010e220b1e030d020105040203 73
    0x30380580c5550b01c0e481010020507a1000c002c0010b00b404040c010309240c041001e610545004056a900e582d80e0740041e43c96090444041c00c5408020402c0d054580c40b20026000179401800c04100d502425603420040b10581d0b00100b084003001c1e0000c00c050401c1d00c03e08144000c0405083d410104902e012448403881c900500d401e040e102e69440c160380c2c809504c042e03820700d080b040070f10031005c2c4400d40780d85071b42e80c000045d031b407a508080000303032000f20000728035038400080c1d1746800686440c2c000000007000e443d04145d81d101d4a81c02500255529270040790f800881616000805524501c100042d02c046207141c00d01401e1003002150701030350017105696000307010043c8041035190414003220a916411002007a188040000141e0000106038050654996455000311640c0f60707001599400340b0050580d50184ca24a00c1844005507400aa80310209440c004070b4241328010010b00c40b940296030004a111410036682c00138542004050100d14032800200241d060035004039444d940050707 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 728166303 1250 728165053 728165057
    0x60909040b0604020f13171504110a092c010606170408090a060809060609160507051c0f1220031302030a11041a0105190e0406090506130e0607 63
    0x40002d041512a90121044104158880d546e90030302c800ca4080c95080b1405182c441240030300540420b890000f4681c3c140c1c1c1c2401092003400e40e510f99a0340802c0c90090203603500303e035911100150114980c002c0c0c01c100000601100320701624440e2120f2100707000e80030a01135038103064041105070f40025496042820120f92b0801d02d0b515070410400c103204001d01c0b42d40050f080d00f00010700950200100c0d01500c4490180c1d180780e10b44500700000359030280c2e41141800d044110102c0e1160050000b840502e01c1281910f1588480a00702646055640200e034003088810305480c0e40203030b001e000017283c0e00e0702d0f82c810403800e03000c500125030524100e111314014110010105a000d031840c41c2e9203c1d4107034000c084492000151420b1000c80c041c0f4140380e4065400c3c105c041c00d1090340742e00390203104131040e5902d43c100b41500c000c28090b40740d1003035030009000400c480e80d109a10b0314084d5401904510b072010449040180c28406803071050715105d2001e510f00407003c413910101050040e0002894 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 728167553 1250 728166303 728166323
    0x3050705041e0f0303080f090309010e10020f06040c05040e07080d030903180b13210605070e030a0c061e050405010e0f1e01030605011403130507031a09060606090904 73
    0x105820b941641a560070400f1180c66050b000001c06071300640700343c4542c2103c0c413903400a40b5454003c550f24010709070080d01040b07502c040b0200358104072003042045480340c811210342c482a410300c241051001d0307130b00b610a2107100d4800d0007103041038011026030002007801820244e03d001d40c403e4642d5000052881059111a80070003854403994030219102e503045100d45405d41d0300c403480c003480d601000c0e12040502c06841c000420500c6d007030200c01004140010380c407141d00300e507480600030a1300400c11401c2c413440c0b0a03011481c3d2002c00542800e43e2141c84205105800c0c00c43c00380c0001a2000700c070b610600031800e0550b01592204c00d46080310401e08000903000b07112000118543c1c8503e441035000031401c6200c4610300800094001c0c80002a28200541074980700119005104aa40395920107000c10101c0e60500344a6419405103005009891000c0c1d2a82d650b040d007042141d80b054007500e2814140f054180c410301985410007c04c4031014a4410220041409130270024006020a50f071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 728168803 1250 728167553 728167589
    0x120305060607201f03060602070905090309151b1b040506010203070312020d0504080a1d012001020708030708070806031606030f0902060c0d031d21130906150305070504 74
    0xa2600313101c2504e805490002080c000d4600000e008200500c1117200500c01d036600007502c2240c07441100d00940d89040a507250201d82c0d000e001050304c0020741007806110400ca8030041120032490b41750a1003651000d407003a10704081c0004459600380c41424407840ca40001e0040320380c1c0000889070308940c98200b0598550004490400a01402e13100880040c1040c7c104020007514200808812000792070701e50400341d9400d0200b0f0054031b1516100c1c0440c1c00803130000341c0041d440c2e015803010601c0704000342ca00030b1384c0c0d59118096001500e660020484840a0080007604484c21951100d02034000b0503c031038035506011010700151150303009065941d40146112034090300000a60360300a0f01d00d07940c0b107044841c42d540c1d4070b010000d5074000030702e4039840c9420b051850101ca00c42d94140c0e0014200103140000d40301020214001a200c080c0f0100641c20101440c1980d030b400401007202c0004406140c410700c1030100049041d00c10400d840d190400001d80d400005660664034910b005100d2400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 728170053 1250 728168803 728168809
    0x24081825081c03140f0705090a03020409110913122a03050414030609070306050c1c020d05010603090b01090c180801020d0606020d0e0108060d0f12030506060720 71
    0x100c58108034480d02802100ca18a150150304910346030b1032580c3c1c2040f82038125810600359000555600c104414500d0100795285c3c880d101a01e1100b0700209200c400d659280d00240807100e5003a421111364120b07903003403c1c5920382040d159910a1414140c201d600d245640d0322070000c1542c2c0d500c081801302c004140100c4080350001d8034000d90200080719030212039410080d003d50440d225500c980700c142c44680c0c0c4070b8240427440301c0c0110a00c6c4018407050341182d54490107401d0040c8486800b00d001e11400100e00034072900b9500140b1010700043e9246201c1c100740e001e03508143c0009080c5030034030f040c4800041c0700c2d41c025811a486824009080042c110044079892400018105480c40c1400007041d0408194020b1504d064143c2e010004a03641c2c040c244d0310740c402a48084041544a120300d80c0b95401501030039030040c0c008012821031001a0b0f101d074404c3d00c10620a40b20343d03072201c050405554052040b02d03085003084601324101b200301d98038102039021100b0840e207600c014041d5402562 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 728171303 1250 728170053 728170123
    0xa060218060a020f1c0c0f1403040609060206010e0c0304110f0d080c07050901051003020a0e10050a08060604050a0302040902060c030705060f010504060303090b0a0207240818 77
    0x1000c000c060594a9502d090000e5507203040c6000c003982030141017028140c3c449000080750000085407149a03d11116444e100c032008a030480c29102085030800800704500280000c00250005482d072095140c10705030700070300e003007016004001812082420301941070703c2441600d900c241d1014a600078500054003103089001c01078041608082074012160401600ca4003507c0e210140100f2640d01541e18400c000895100388074164010401c0c54040d0b0300c1c0b51084d0002d040603e0b55041c20301d6049200350100e581c0c94180701403000003540c04900c03180c2da982d100c4002600410200c48260500e0300306400100302d0021341c0700c000c3c856581d52001d50215290442a00c440705400340035a0746466650038115110b110498000109800341c10010803185030910030102520b803da80c403c40924280070315203003a41d1048403c01d05510441800140c1c804c0171154200c0c000380741c26181243d198003a040680140c5000c1c02050f00d203e00321341c0c28242c45d40300084d40c01024403001c410303020501c10144a02c6201c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 728172553 1250 728171303 728171347
    0x1e0b22030b130203010e010504020603060d11090103030f0f030506210a08040806060306010602030721120f1a0d080901031e021611040c020a12120213030203010b120a0602 75
    0x5015040200001d604121030b88260b6180290000d0002602240c000d900700c07401110020340c084821b2000c10120b003412140c8000b860b2140d2051000c1c2e091805c0010300d0702a09900480c0060840007a082c0185d0744400950810007041c24140b101c0c1c03c10f10b0000f8400d41c2c103143c419203510306000b00c500008904010101c0d0145d000b50000d581c49031202e000640315242191000d00911844d000080c0043c03000088580303650300162000c80e808007078644030b008140b010120b001081000d45c0c02c41280701592003400c080c400c0b41d8a00240c21081c45030020300400c8503e10321845803404400100104890f2000c6502c100400d00e800582485c41d00410b00380c2c00400f00d420681c40740301007214a102e8071480303003400344c181c000e0f112244000500b0003048240c902d442030080042c0c000e0380ca000001244000c50075480035031400c1c021903070005510328200b01d8000c64403810490710b00078420420360500b8480c122500005035054105442400c02d1160b48058448000b45955400102d0501401001030b080b001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 728173803 1250 728172553 728172563
    0x8040b090c060c1e0303150d021807090503010c1b060b04110c0106030501060b09100f1215050a0909031b030e090f040b010f050f090c04050301151e0b2203 68
    0x1151101c0c008540da9008045180040130381e4203112515066001050f40e03c500618004912a0007003102030102a40c5000750890b0000c0c09442c0c16880409100705032071246d1350750355400b2074051034a001c150a44034004458020b0140d881e005d80305203180802d041d07812982001011030184840400301c0d00810b5038445035001e40a02040b040c5a403e01034001004490040009228107078442c070380350040e44155180b207540505203514010580c0e01468012074041c9850a1a801d100310140031101502c00c0452010001d030102c07242030096140000407400641281301041000c64000d607030186c5001c0c6113440310031900c4074032603003001094856984081021300141400b42142803812041e40e0284094034129191768204d4000326050684001403000c83d203008181519049445c0c05210411a004d440d100010408110104890314240102c001084a076441e420380181740c112007802c0d940c2010b020b04164098480b0400c9408000f00c2500c00300741a0324004141c5e0301c40b000c0480301c000c20175400149 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 728175053 1250 728173803 728173807
    0xf0b0303070b04170f0a0906020304230f040f09021503090304170a0f123b120a0c06080702010b030c150d0f0b01270306180b01033008040b090c06 64
    0xc0340c400305001504c00646c081e12809807458541d1b0083e81ca034040c07400b991000400f00f134035054103c50100703001c408070b510250095044043d11070105090f1145441100c40b116102e2943e83d003141000c941103c039003451480c040781113040c80001251244624850301c650b81e030410b5208018000d0600c4442040341c0c0c0500d500105060503c0c0c1054070880e080d95010200d40715030070802c1124481d8101c41100d0070080480c42011152284001f003c2c651555980c0d000b521a403103034403801c4d000b00300c01040c850140c05000302480c03428000520459004103000e04690404001e07000c107031000107841450980444580c0682c4140e180c1e40b441c80c0c06001124130045042c0018201005180c1d40b114071005000e83e42d801074040c0b480306883ca4807402e540005408210f0050400109110741d02c40c0341c034091550700340503a0300110b88422340b002c0801c0e041900c041c0a503800601c11309000a5861041e040300c441c580703074000c040d40005072400600510161a41c0402000a060f044003845010514103000300034903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 728176303 1250 728175053 728175067
    0x91e03100203040b0a0c0e0904080a0918020711010c0b0c0711040c08010302030f07060e06130e0106020709060f030b070f03060f12020406080627031218010f0b0303070b0417 76
    0x5603029400d46065128900d40502c10380c4c220710507c21955402406070125810352902e03178031f0050962051400c107080290303802000c01c00164101080d08001c440c400090707161461410021002a211510076041c4000c010324180020000c1c1c85a0764080c190b40c0e6015114025400c14140d980d055140060b8440d16084030b0404180d04140c442d41a01c1c02034003250701c1d86003151281795070382c202409510086060802200020301e031040090008420794100203500e940e45100202122001f078000c8000b50b0000300c0c0c103000d541c0c030b02d210700c00040000003006404146903840311840390402030001c80800c84d000800c040e0550090300302d0f0005000200c610360400d50745000802d900e0a04030f404034030450038010001070070700c000a0344a004007414079014141c12400e00c900030b03120504080f00c2915000c02e10100780c4901140c007140d44200c00031015504810307514181d150841c0d140d0310760981500d240803080702c915140041591002d590101d8046010740755810080307a211040caa5450282034000303182 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 728177553 1250 728176303 728176313
    0x30c04090506040624050d0807320d1d12070b0903010b04020c0606130f1e0e010c0806060f0c01050109020c060a061503110c0105012702091e0310020304 67
    0x388510702965007081003003103010302054458000c91510310b28880c5d1840074403040c600380c60002d5010b849160040d1500382c055a603c031903070409020380c5560544844004880000c000e003440000108500a004052195031380a05800a00c05a0310942000c2d4100f40d8030a4403110701c10124052000c048407603081d51441c51401643c08042c0f40b40c000e5080a80854441c01c041c020340300b81e00c0b040c0e0050704442d030b0b031107052248000742c106070102c1c0c168690007000032040c2d29200c0c0305079032100264203c02c000422010130094443c200304c11001030380b41005140f01103510603c0160061000c8584c40c3e580c0c2c10208d0004050300441000d07554551901000144c2486264000c1080810101c29200e07070348c5c0d40b0641c090486e0b20900c07074801d05483c60307000100a90301c0b80c2e10481c81984070140150400c0c418000d85402c4030f41c240c2282030b40d4202c112000011051640801c104041c20060039403030040540d0106001204d044648094107070550f1175041c0c243c0c0e085c041d0302c2c4212035400c4115101e04d414109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 728178803 1250 728177553 728177563
    0x503190207170307180e0f040201021e0a03090b032802040e0c120c0406050409020304020a03050a0b250e061315030204050a060e011704050c030717060c0c1b030c040905 74
    0x207080210384066402c1c10500e2039248480121201c0c0ca200e201b0603543d1801804100c00020300c00ca045014020040c020300e4001001e8850104200b0010950040d0918000d00505525001082100010710030811404203c00d982201c80300c0562100d10f03109030640d203c0029000315006001d13009144010046000c0c1004050000350b9808064002103482c1c0b2225050181f0841c05040e002072810001480359020135001140c020348060501096140d0b41c1c1c5456080090000c001c0741c10b00d241000340582054000704003d404040030302c08103100140c10700098041001e50251602481c4003261805011101d010700000811000d00021410506402d00400035849809007038801e81c041da0340461158411948040950410f0f100c41401c0d500c50140140242d000400031121031003092030340c0503c1c1d00c05000c50001030543d11784107402d27480004181418044000c01c1c241c0440d406116104d03a484d000500c2070003a00d01046150030038401c02010908106440c0d2441c0d4002e400d08440d00d0030000c000074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 728180053 1250 728178803 728178811
    0x30406020115050415090b061903020909180d0c020a24020d080c04210204020d020c010f2c010e010204060f03380402040302030105100e13020105031902071703 70
    0x560005056200c80c100000c07501040d9250600c480d100400f4041c6c10080da10002c40c2c0d1200502080c14800300c0d840b00b030f0344450400030500020380c020548541c03e040a11440f5088900c078035001a84840401e0380941d5807415444031000c00ca800345407081951a07483c3e01c2d8025080451219074582c3c8480002d110031401c1589030b070018401e0203d1080c00610500865004125070145c2c5031410345400c100c00f40b1080c0c070340300c0754815003106420030300140c0d682d100400030004850409611802076000d4142100c0300304541da41c8243c100a810404100384281112000029901d141d200c1040e41104a0043c009000d03120034562000a011440d217402250140ca1840540d80c14000745981002103082c1c2c0c261490800038800071146204d00e0f48181e000901c1501d04003600041c18a69250000703820b494050764031144000b5441d006120403071101144075885240e001c1501118806640020a64400102a000cac03070030140d601049816040e1301255059500070010441c220000040c4007015030040da = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 728181303 1250 728180053 728180081
    0x6090201020d02150117010e0a0c18021e0c07121b06180302040b12011503120f080402010c0c05060304051b0307120b13151407031407030c09080304060201 68
    0x380340d0800c02d501c0007950003000c018100612101ea46070250104072100d00100b0b0601e59500c0700440040c1c1c00041041e102064007984000040d03d180120840495480c00402100c040c010401c0c070802d014040c5084130000d410904083e6500e6094a01c5400d0200503040000c0e4580c040d0150b40c10320803c07840c54501d109071061200d01c12541d9060903511451031001c5244000003540f401c00140c6420f510444c003468002d00408011072605240c58210b540300494600c4ca51007140c1c050003030020101260104001608201c0280d40ca100009418514001d000a040041d00941e078800c10a1f003c0303c14004280151086840341098502207860f21617694025840f5600e40300501171629000071030b8421282d51a821288031800d0761600d41002c040140302e192002001c0000348000f0301c0c0441d0ba00d6001182510001c0c11600c3c51203001c40306007014040d14101820501d031400c007040d00721062500701102c0e082c005544903a000058466044540c00381e10707035000101e4009142501900200040c1e9501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 728182553 1250 728181303 728181313
    0x9030510090312141803040b0408060a0e06091005091218040b0307150309110316080c0402030106081f0e10090509030304050a080a02010f0204060908011d0d050a0315030609020102 79
    0x80f0840803500701d007500509454504020400b00d0004064120108440700180ca282c1030301c604541805500c0355204002a510200030030101e4a05803203045901ca030f00502501c41410200041e5981d55403117298114156039440105d150810104580a804401c9440341d41e01c2c0c440080c107516044a0380900340340240e0400d80c031003415150108942040e00c0d80c2c03e41601205201903011070080028003070032039590b11480105000380c1e50410126148030348403420901e20900340b0080a0420071841b00707850050b401407005101003504540000e50051440c010700c00320400c980d100000044040d4005a844160b010a20a040060784c081e14180c6000389402c1c411501c1c1e805102d40d0720300c400c032070107010741d08036622030000620725034010a840c043c54400401d8003100c8040c804102d07801035020341c1c003003401401c0400c1081800c0c003034548841052a154040b070003403080919120300001510b5410005c000454050b000c1c0030350f00c1025000410401c00e04041e03100e19102c002000200700c10780c00751240c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 728183803 1250 728182553 728182577
    0x13060f090f260f0303150a030f050f120a05180619030b120f151021060c0828021201090c09050d1e0c05041a0f0a1a0a090305100903 58
    0xc0081c0030780c083c00d07543e0015413842c1d841015001c0c5008404841e5503000c520240000003043c48001c0302c0d2611030040c0c0c0a065401e07440700100349031140038829008100010301449440542000030388042540c042082c030310400348140040c44a12910300034214020201001121490349076100c0003a25406450198103500c000048580c0d482c50202d2109080d482080500201d5125084058000b00e0500005a096481f5034442e009038990504220340381d030704507a883d4140401d60040d0f5804c0642402d0015150a20b4420ba400317108010768141183d66991000c0d0744c0b00d1070701d82c0c100c8115003c01c5560030342c0c950b152100000641251060600020040407001c1031615260112000c1c0b035a00174404c00ca400c440c00551a464a848042921001c002c140c1c009070949590003641c0385500b0466011500c403142d001001224207138400c50b02d01a40a2013400c0c001c04041135040280c0614103c0020340740c180114084850681f9071f0402441030144802d1001400c5a41e003000901c3d5101c7d0b00d0303014400035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 728185053 1250 728183803 728183879
    0x303120603051606020c0f21150c070b0f01050d020d1b0303020304080f0606091801020f0708070201022e0506030307020411040e0c031501050c01111809010b13060f090f 74
    0x3402d40303820307130300c4109000684585e0310092244c10210300004207541d003049c1c0b04100707951034110468542d001b0031000600c0404201c3c060341440d41c4210f0903800300c2902e504040101e42005860701d00240200d183c46034503810311012101001031034541c8418103040c90385134139000f501c98015101e03a61042c800c003100050640c001107902d61051801400c1035040f031380c0304c0c1803100341002c00c2004400c440d5800c0003400000f9001c000103200c1da50003590641d6513520203100091608150101d03a0b07100e1883c5540804005081000080621780c5441c008600c0c1d40704c0400203400c40c0310760750009501c43e20b405071009100f5180c60140045030001e8440c0c4000740d503000386404462104030303500002c660a030f060f140903960062000c1c081240a141c0005054002c20711b02020541c041d0320345c80d918030001c9180104034508140c0d0309016158140c0b03040e0030170407039100108100309a8080c0380284003020054019280c0b10386600700003850407980030709445542d038001d180740708030111580c10144000903040300094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 728186303 1250 728185053 728185069
    0x910050409050a0606060e120f0a080706020c030403060209091e0a02071a0106031d0a080d0504030c0b0a051515030106200703080406031d0a030503130b0412021903090303120603051606020c 83
    0x20300c12788068884017810340e550b990703998403100c1c0484240d5030a20821064a5081014101542c4201c000580e11009042006034144000300307440c682070241e40710302c2d02ca4032401c907865811107003201d400758945810f40343c00e2410820101c0440b8112840000004516038103030003022040030b02c40c10f202c522280310b0382640d803a0124244050800d480c10030500790008180c0e40071540c454004d1070090480103c1d90b9034600d0102040c2c65143c42c4a403194140807120f0600c00313840051881c00c5980280d42c030740340700f840301c11400140f0032203017800158255282c3c03809000002d0240c450486d400d0729903440d00c915080100e41c00600903800064139025982d001030700584d0202d01100307074071001420b0030b084590b0100c03490341c0010802a031901c00fa48a00300000d1083c0500741c000c44c03140450031303855150110024540080405207810440b4110f150750003080c0c0000840c41941c0d010301e451200f1094601e5100080d00342540010a07074442e1400904000401040071025105c441d400d4071240d14000b02000088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 728187553 1250 728186303 728186323
    0x1050d05071a0f0c15060301060513020c031606060311010804050a110109050402310b03160c081603092c150303030c07110910050409050a0606060e12 66
    0x1940c071120080c48402c90414050310490101d00d801c0c1e00d804094403c00d0300b503401407460120164402d00c4800b0f03c220940d4030140d4040804d5001700038862130140003039044c140000d030380e0341e626600040c90341c0300c131a092040343c0c0c1c2c8080b002d2901071030b0010392901c1d10003030202c0d101c00c8ea40070b0031108400e261588904582c1d030080e034129006004069107512461020400c2ca1000d46c144590f103c000500c948403070014043e00881c882c85d80c00c1a00d001303234103c4010550300c1d4010141c0c0c20b6250061291045245c1669006400c4802d0411307000c1c0d0040040d203130a07110f00030103031817144007003140b41280310b207810683c8185210350b5604d1065079445c5104500301c01400310f107460303654444d2542d607000303881d841c0150383c0810f654194004420489001c80e0441d40203a41070070640310005502d0041c4803800070110340b501400e6034101c2c0c107407a0964005041a03100c0c010548110786074000c84041c40f00800c900d400c01c0b40c008100b0840155103110180c0b070094110341a5000b104040403046090700d02155400131 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 728188803 1250 728187553 728187563
    0xa05070c0b070320180a270f0204150e010f0806010f051c05070914241b0c03010f0e0c1009030b010b071e02241b01020306040501050d 59
    0xc002180c0d551184040c41c0144180d0401d5a206101d004045091003802a0141c5240c040c0383e0340c0d462080e04e5500034920035607050103842c03810b10400500c3d20120704003d071901d00c2c0c0b24800c02c201403480c01c0805081e0a40c140700d1302600101c0d000c0341145c01c1050496600a40c0d0315043c0c7e0b0b404400005644103005450383d10081090040080e144d0b50080c0c0c0035410110b043d142440c81c2c01002202a030241c80c40303104000300107580c0c6d010403003c242c00452460142c0034180b1840700c1060602d000550300d4240040611001c04005482d0b000c1c900c00e002521401316041035000080c401a20b460f40d0759402c00c00e0705d540701c0c2d828072a4107440d003096403042c2060150700380041e02c40403856405100040301e5440c421410040000000008a4015203880f40604031b8448942d40c0d44031507040041c140302c904038001c10385a090b0303010040142c0c0c88110386820240c0d004a00300c401520710301a040d0758025440e0f1003c0b181c20f07034044c010b0a0713001980191301c02c200842d001c1205903220810301580c2d01c2d240100520b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 728190053 1250 728188803 728188817
    0x40c0504020c010f110a080601080412181d061c050303060607080f0a230f0a08060a05030d050d060909021804050c0d080a03050912160230060a0507 65
    0x1203003000d03002000000990070000c281d07540e10203501c1044840e4003464944e142004140845490750003d61a0b4001d042441d1511181c1000d03112003030801c41c03644050040c02195280910103408845a150080c1010b840100117022811900000e03180100c4a01c1d101340100d0054000c1124000c054825031500f2000640c195a00c94091081c01c0d408004e055404075401d10600a4002040e0001c2014600030b9540d0b18150080c4010900c20314909001b10b12070002c107001031250f502208003916152041464252900d031500c1e000b041303000100360440d82d00350141c800076035a459041002411903da103000d0812003a9135500c4054225419080e009511250f046002035144007450780e0f55410a01681c1079031148205400001c3c0031080d801e408403201500820050041501840342030b45c40a03012021303260504036500c0d04000e500c58000d129a07842c2c00b540b07242d000d640f5020141d008203c2c69501260701081d6620061210703110322820388400d440f503200012400040c6018440c09204d260316021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 728191303 1250 728190053 728190059
    0x301b030503100b0301080a0308281d06013002030a03050f0c03120109141005010c0c0b0a020105011a0909130203150414150408040e250905010f08040c 66
    0x120154000340c028182e401000e880854102c10110045009005030710007054021024034015001000043c1440c485002e154081035036014040c0740070010b94140d04c40082c0314420b640084048410340c05100034684100340010071001c3e00a21034442e60100c4034074220b00c1207141580089182c0348075500035055080911070034000380c021806810766000340b00c0918101200b0112203880d50300b022068103500d444a800402600703106106459445424410b45102890640917030210000b091080c28104010615624140329101000402404141165994610001744024080d003c207014503e08020001580400081020112100740c1c1014003001d4955803948440c8240760410007040c0e0f010b00030342d85081400c40f4000403040c440c41c4070321214044281004141d07490a039450388120070340c00d46803041c0408112280141d504881950305003a0b841d41d502040d0b00358681d48a081c4101203080320030100034241d000122101551801c2e6546a144883c2c0c01d0200c90100702550040c28175840703140c0c18 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 728192553 1250 728191303 728191307
    0x4051e030f0d0b0a181a010e0906010e0301020f0d06030201080906040309050118080a0506011a07021f020309030f03070203010f050f042010030f1d060f1003301b03 72
    0x180c0d40400c001000076400d00e584600b800c4480205c100e003107250741c0e62105c0700d1440f00c104503820300c008002841c1101d504000200402c1203190050402c5040c40001e14079564283d07801d404980c401c0301e80e43c0c1001d4031115547d10040c05030075580012804101c0c5030001509481c4005603e51186405a881032001c0b450300c0019900a1f2014805144101070700c840801d00c520100540e0115511603402410550b1401410090b4500046010312510208003c8100940c1e5518804a540302081e55010f080680580c01a8034600c80d420f1901d405005409400b0f10000b00840507245a40c000d80c003d03c816410410a00c007214800c0310100501e116900100c1c0c0070428480c0701d2100c84111021840b08642d18000041814982e821242d0020b83c9402c2c5180c1c40c84a18080c2041c0e079001800c0c1c000e040c4a00001194550307070010201d1115034130110000f0101101e5000c3c0000454100c0304480c00042c59021079240690040c905070941642c004030028001c0c89842a540c00b012215100f41d41d4191984d01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 728193803 1250 728192553 728192561
    0x90607170912210f1c0f09140d0c1208040317010f061803080f1324030c0e0121140a09050d0212030105060c011404051e030f0d 56
    0x2089203010000e10801c03071aa1160a0114910003020006084560300794001c034071a0410340204a01c014018041280c1000c8960b00756100c4d84043c54031010b800140ca01e417100148003e10380c0c80c142c9401c0c010f024040c407140141a1079074524010039079803403500b80a800e98036083c11500050403101059100309100e8031a10a0603001440b174500070003105081c1401d80841c01c0285c02c0060300034804001080242c1e00104107843c0f00204080000d0b090749103455902040c02500303000c01c40c0c50000250802203034520320711f1001505030700342c1e410488443c0b006145580c0140a40314801b00307181c480000881c90080d02d0000201038141d6840c9074800d03242184008600840041f82d02090715040d1200c1400c0b03410400c0d5108018540001650119506019203844120288181950004696815100e000f0b1081b00d065580640356685c2e201198985c080c01810b074442d292002c0e44134041408100300300420640308240c520f600449007180807010480d00da22803402c044507040400c0040513203541e00e41e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 728195053 1250 728193803 728193833
    0x50a05070501060f0816140103051b030109021317070b091206040b1f0b0919030b0709150e010c140f0a0c0e0a0515090402040b0604170f0102090607 65
    0x64014202015075031490300f0745a858201c02e050103403084040c80b0703600e01003100381c10000403000014001441e100344a4010030500c0c03407031410142c0740c07170002e521484880542036140c0341e01e4208a5881d0b0351440030b04002e404c0042e0341548513258080004600e0301807018166429003240180551900d0002d204889034808000f25400c00031700400611031150030b20040c0c1c480c41c0200e50001c2c440c6421107440910f0ba0303c92044224081c07031600240607400c00b404c00c1d112801070581e110705081040d85240040541113a000411050b42c207810068030586c0b20318810308550301c0189103000300d0002c02056644c1943c0210581c000341106d005280400c0c0402e805612100c0c00300107440307142035004c8525040003040e80c01550b44640c3d1000801c191020242c409a1095041004200a0420304c804900d88506401a41c4c81001f800300483e003550360f540c0c03040070300c3c40700108030a80d02e030390b40e000b1a9070600400d504008140140010543c2d00b08040c021280200300013001c0510300701e225540c0d0300c801080c400e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 728196303 1250 728195053 728195057
    0x100309030e0409050309040506031c052a010c030b0402030c16020d0606060503042001050f0a0311042309040c0512030c12030f1015110a0807030c0210091203050a 71
    0xda40c5655160343c03040148060150024541e2120040280010b5a0780544054002e5000c100300c864036102140c0c4940b61103e03240b9055070b03922000c0ca000a401c01c1e180c4101c0582980312040022416015444902e8485507910240600e6a00c03100300422400120f820154200d000c02130384030500d0343d010080749214402030000e44c0c1031031141c6a10040310025085070340800c90000502040c0010000c0541c03188940d0200c04036020b00e002c000809174041c1900080101c4004500681c0030360003504180d41801048050b140c4503962034501520a00e282e510314040307121003821007410350410a80c3e0910590300711038441c00691524050110302410030f00d5030046400180003004200c2c00a0180180701c00074210036583780d08200300c000d000307510044c0010044941d10341080010340419400500101550b040103c54103506c60b4195080180440740101b07c418002501c0701050f40000902180600a40c6c4020000038040402d44a241b20307401080003420101e0001c0b40020b03c910014900701030360f4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 728197553 1250 728196303 728196317
    0xc0d05070801051501120c020309040921050423030303061c050304030f02040e01020702031b010c0b0c18060a1b3008060415030609080405030a060b010801060e10030903 74
    0x8500242c2103910584000b103025103a46608000c543c0d1100c18540400c070400401c0003908400b20000e50b483c851145154040c2d501c03070501d9028820580740341400428401d560950350111400002e145510a001e90038000b1601852400851240c1e60443c40005e00a001107203191504c41c100940c1d00602203404101c204401c1c44000050424005800114071036040340404030407510400042d5941c1a19450140c0c0c030500c51a00580e030300242c2d621101182c1d8100301c00480d610b000488076140c0e4140301810d05602c4a00340442040058020200c40780b0404a208059420004104262103500c1107200041d90311200400034000300070407900c0541c85040c001961070742008038040b03420b004404103c82c406482d50030405140d04a40020741c840000c803002c03c400c00042401c0c0660843c0c5000203000c55640701081c80422908800f101c002c2e01d4001c00b15071030191140340c40c0004e2318041010a000424000001030064040c1c104c0c0600300c0c00c014000d081c02000c8000880041c142e0b590160204030344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 728198803 1250 728197553 728197559
    0x180f03120d0203010302030c010503070e040b0f18041118010303140412051501050f130b0303041a03180c010801060305070207050613030501271e05010c0f110a03020c0d0507 76
    0x20042100d2441c099025850b5851401010b0a082c9000342c802d041c44401c104020f41107502c419800e12105013290002910181000800c1e02c400c01440100e80008400c07108600307408000c10351510403882030340950030151660090103140700f0101008103a400d5404018400070740582c0c0414805402440e02e1030030700e541c84152a2003044a424241e801780c01154003024160300311080c075805008241d40201840070541c0100708214034800a003440c40b6912043c0d00360f103690a1007110001c103000829441c0c1c01c50071801604041c2d2040c2d03907149110981002190101002089030000c5c290141c4401c481c1d0384c681b10040d00039140040c00324045001d95003000c10281d541c00e001d070106408900480d1000f80c10761030140d0071038000f040d41d401c68440510031076110a483c2c0c082c5103e825440040b1094202450641c4850303c401680000d00035400d207070203080200c1c0d21049280c010b100030f980700e8542003030106003140c0b110481c50b000750050700107840801d12070030084071018400b8440d2044924140e6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 728200053 1250 728198803 728198833
    0x62101180b060f1f032309150c1c020903010510170d050703050a02010b09190c05130506070c09061d0c0a0c11030f070f1403070602060a0c0302160620180f03 69
    0x42540c0121101e21b940c2052081c81e42d8200064204c00c0601011a2001d04005400c000c85000b031240d004a80050030416140c2c24942c5e406a075000e032030190003440b6a090840d03005100580e51b00505900010003180101c20f15000254003600600c50f45426240c0402c0c0c0d10101c89a510840c4d14205540d00e0714000e02580c3c1320901c5062040860781443f1610440e5404980d094a504140040810006000d40c07a100c986e80b000303c0c011110100c0321a980c0301018030700192045890360110b00320900e0706000159030341e2000c50901c03100d0a0b4000d10340d0266142e102c00780080c002c00485c80d0014043c001c20704002380e0508194490684000c003102da4207841446007514150650300300c0c0581e05032483c010010099600c98050b0420030407005800c0702030512200960b907200084c85000072a03221000141d4239402981101d052807100c2281a16480d00350030090042c02e001260107849500100c030200000820800f0344401c5c0b260404040804010074042054080581240503418000c0c8814001506 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 728201303 1250 728200053 728200091
    0x1e0a0c02130e061503060109060503150a0e06180d0507031211250203011503080f0307050906073c03050306030102090306040c060906020a0803062101180b060f1f03 72
    0x115022909403480044001458101401032344410b21840c2031800c10b11880d0b50114101c98040d6540c03d4015866a507089464090b1200c1d0038003c941d4002c100900c0140801004e200390703a42114011290030002c4054106c80305d01c17071414060001145071010100100c0150405071060b13000b1050b141c04c119149210007907400100030905840040d055100045050a0142c04001d400e0300b500950881d20b50340b0303000c7c090303c06c42200d440d41441c0000010581806002070783c4092402401854507441c8a2074003512803d103a9182a43c6240d045043c9040034407245191401185d000302d00b07040e503030020355040c0c96541000d456035505540038805181c880c1c80800880348203500800b20007232200c0ca07143d00546603d8050f008070003113400c01000c02d80403c0c0000e0450b40c0000050300c2004d060710b070078403480416003c1000e135100194204403403c009009080c4c18031070020b001e04d0100219855400170003440700e640408194006c1d884584a02d000b000401e40c25170b9104403401c0c0400c1e00b084520ba850011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 728202553 1250 728201303 728201311
    0xf03010917070209010f0302090c07050f1f0b03070605041502071a091809061315090809010e01090302030a1b03080d02030f1e06060f0d02040b1e0a0c02130e06 70
    0x18101c082200420352030b204000364010714225844040c1e581c10354003c100480340c02413088540e8080014101c040000030042c4011501c0c00109655144241e40491054580350034260300d512030030401d060185103004a10b1800300d445546806140510b4044645441646405240c095010742c440010356000b1544122244010f0303110380e280d03140300180c01c00143da50071064580240e101e076010041c3c1c280c000a0708a8200c0b01084003940d0740e81d501d03c1d0400300a84400150302c0101d081210040800c400c1e0300103003003021401d8072951614042c1800445c0c403040340707101c060351503441282503078017242d91140240140b4a010315405101070300c1c1d440d50b114561141f0070740019580d001040180022124400ea5080911645d42d100721b6148504c040001c5540986050722480000603103c0b6941074031000c4411081c84034805545542c2c0d0703100484143e4020440312007011141c0c0200f81031070000c40c0b00b150500000b41d120501c40d13540903000c1c0015455022001046655036000745041602c0c104061489 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 728203803 1250 728202553 728202593
    0x7051203040f0f0e04021e0607110a1707030b130f081305040501180506040b100c11030105070f050a090b0316030b09010b040603230414120a0c020f030109 68
    0x103110702d4002d80c002c5104995000c1c0b0300140d00700c034082c407203048044201c0341c109804850035841e885911041811051b620040e03142d100300d00207058020012400452001c5a4007111040803ca50303480310701c4141030f0000640c0d1681c1c1c210000501c0000c07561044035410000c00c4101c4a2a00481d0346e503098440c42d0080309550306500484e40741032151040d072640c2c0280c030b015941441300c0d526090b05560129800200021815290780c00901d00d51990f502000c1c60810003407115445a40c00750014020030200d01040d1800e031210a0305d001e09040c140642030080c42d40365915040b0840d4034500301ea480c0c0181c043c550421182140c00030b01c20000d0b1001c0e502880f106484001a00140350001c0c003101c81c1825003501820154004008641c440070130b90b400c0301c080c1d080c04203030f40d042000c0c5001d48500d00340d03078121020f05202c01d100500c4a080141c1e4400350000e0202c41d81d640c0204bc4091090040e462a200004c5400c2144170060628004441c04001c0290020179454095070b1072066140044440d450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 728205053 1250 728203803 728203807
    0x2030d020705150108030d0c0e010e04020307121b1e0c020d050c040f0b031011030112020a03020603070915182d060806010306050f150f1606090614161107051203 71
    0x51f418030306114920030b0395168200301d00543c07042070000c0c000f05002986244125404400102c040307000d02550981008024020026a0a404210900c3c4072680d8400000503114003542420f140112800c00d40c86c401036207903403d001c0311750780c20840203004d0354404880700d000f45815103059403181e0040c100310360b03020100420001c0c1c00405040ca00340001c1d440034001410400d100b403032400180102e9043da41a0303041507078021740c030b80085511100254002500240e001080080c65540100d98009407901c204688035408400c200031500c1c9044d0200c151000480741a0800070401c03c44041d0807902c200380006000b12060302c29045c0751030020f41c0a00080f868040420030590b0780b601c00c40026041c203c4480034059030b01000705800110150400f02e10714400200323150a94034902c00c1e40c400c5108032084904400c114907052001d0001c00804940960801e0101d02d500d01d00c6080030303031080f1941d0b038216900c030107800301c2210410f550601902d49802019004981c82c1c480c00096011705010000440d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 728206303 1250 728205053 728205067
    0x702060f0f03040c0e0c070b040b1308070503030a0605061201051c02130603020102061008190305160302010903120b131a0a06050c07080c0a03030302132c010e0702030d02070515010803 81
    0x804000024030100300410101f00302070006030128000d940040e040000c400e2540e81d984101040c4d00b4240038058000e0f000801e09a08100700000150b104504101e001d00070f403a40c40e001d010311030040500800300d5205c0b80340103024509141d1040c20060103d4652000002001c1e0046456003800c8817140075074680f20321084c4290350301003001c41d4001c00918030540c041e03460842c106840b0208002559802c0c0042c1003003406041c81841514044071880d01450703103400c05485d0107802007010740412404250708940350340c181c0d41e41788200c481742c040c007504c00301d811020120054010710b0044660700c2e081040c80710401d400c0d204c003403c44004d0036198840503031346c4841d180268600b8500d0f501284060b80300c1c00c52100340303840d80921101169894200540c40d00d4150404100406003600183e103498141e900d0100075007260306846980040f0090800ea490742c0781ca26031035161004481e07550240c1d004200d040303450b0007681d006200c000e00550650310300d00320542080c06503032803e902c081002d40c00404c0301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 728207553 1250 728206303 728206319
    0x111201020d0605150a0e0f0406240302090f1309120306031103011817070b160320160c051305241003090510050a020a090902040b0702060f0f03040c 65
    0x148015103c200c40307100001c40b0014040584d8804c0e4a00f410030485175481210030303611441e040543d9100d008200b84482070712400717035241152408210144880c0e008051046c018028801c884040c10040c050b020040240d6080c0011070b2030825488401c140ea5040440100740d0001c0d8a00419403180d0700452854914140f0f80400c81d581041140b090340341c6020042c0c2c1c3c014100d00c901c90b0660000703c1d22054054441420418010901d01038400c550890410108032070100301088180300703e450421034654144420b14540111b47c0398400c40341001c10400e085064016215880c86119513038801800e40c849000c00e21000701c40400a42c3c0310740301c20030301600750788146207080e0105089141c20034a20075200000c800701c81042c045018181d461446105200c4180450080c458202d0018801340c2000e2000f1002903012440440c00100503082c0498258054000c450445044101150820101c3d808000c1554400c070244030b04004204071b1001c1800340132000e14450341c01844003101d1035182200f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 728208803 1250 728207553 728207561
    0xf0803151e01090e3310031b08040f05010e010902100503040312020f1e04061407122f100c050f03040204020a03180c030501201611060f0c070801060303120504111201020d 75
    0x855003d02d41002d0385a001c580a99040c0c8ca035074241881c05440380d07180c0c0d003001000a10021400381c015400d02d00706581000301500424015032081d9580d041c0941075000c12500d90100380c8000700011001c20b0701c42d000e112190050321001250920092400e119020b24004410900d22040040d40340800c040040e580c00c40d103000c0b05d4255180140b403401901c0c1c0e4034514880380302440c0c06c050040a029010441d014801c1c074042200000000120702034581e00340584e20302c0f54500c1e4141c500d040c8042c586003207203c1d2054448501c8003504907400e680b2598200000303900900300c00300c10036941d41d810505003001003103900e882c01d0003520001e07101c03419407d00509441d49041454490000c60b8041d03511520b0407401c481001d03c07a205c80380185213080c64810420760f84c0220b06a0300110100311900c0d000c1903c4020001c080568048512032951142041e09030380e2144009400309a40900e038403040240e5030405603203d840f0740b014649449a4038001940110070540358046c2d0f070341c0401d540b152034140d841 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 728210053 1250 728208803 728208829
    0x190203090d0c080c120a03030f06150309051e120c0f01050112061103010f060302070212120a030e010c0905060f0904050408211b070f0803151e01090e33 67
    0x1741e00c680c005417440c0f8140e03880d40324000040c101a52040c0c208401030040d403080014103014141048070000602005014100880054400d0301541d07503e6450300e032400400c0c900b5508c07030381e0180c0001551040e00c1652504400c010a040b80540003042448280071321030240601000f550b02618420981022811180c94185951920074204014841000c03400c4001c4129609407402680e1000a0300c08103070104170000c00d50116204a80710421840c1d080030140510800c540e908008000c09000c0c010700b601c50010000380441c07032150050141d030070003000030500c51078101c0881d4545600c0c40c003c201100c2044400b90340384d020224418500f5401000550400041361006400c103040c0008080921006190910031340840080d07580100942c1c0004035900b250400242900e91070070b0340d00d2113203590f861f48941b8400c0403221880603108403038031204401060103035280d43c07440e41055050480710002500c240d800c4024440c80758668201d142c4096600720b000484444607036640004c1c4103040203160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 728211303 1250 728210053 728210059
    0x60c0a0506070c0b13050c130e01050108060711120a0f02070e0702030706050c09010e100c061d010608060f06062809090c0509130504060603200a0506090105190203090d0c080c 77
    0x1030905c8002c50000034010f116800100c510039030894100310100000e103150506c40505509000c00024018804070341c09104400e11340700e01d00341180e41ca41042c1c403040c001c43c540f14189014008682c1540c410b408084400c1c4a600440e510f203500c5940c000c01f034042c01c803175950059100007040d10400a02d170140e140c000c0f4013607040a042020450010b0200c07849040e000f07028044400c410504c80c0e2040c014842117940182c800c05c20300c11072540110091070041e881400c01d41c200300d0001060b24001540c60700c11001c82041c0705094807644200003d1f85c0c081c03050415900906e0414001a51446003866182c070000e844041e4094540900c1605540401c0c07101400d0040501131100a034540f032400c070003070145060000896948030b00d0500000c15003900050600704601e18200941c00030801c4414420204070f40e580707816a5a00e0030000144203000006d800100d0074080c2c884000b0b0142c10510304100c044c0140d83c01e064000740814020315150764240e81d20a13010408000340700c01444131490201080d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 728212553 1250 728211303 728211331
    0x20f0a030f0314040b0a111606020d081302090703050f0117070501030504050f07030309090e01060f120201020f1b01030b2e0c06090f030216030b0105060c0a0506070c0b 74
    0x68850803001c080c00400902440861201e6242080010089601401c0351607162034840b1307070026001704290310241c03c591841c822400c4180d00c40d1040c0050030200e0721158001d05102c084124111824603015001c02d040d61104039041e401070f520780680c584140150f03178001a83c1d14ac0b04102443c1120180d01000c81540c038412070700001440031804100380e40003802d000c140e603103039803800c04d1402a201c201c2c00317010b0280e0800030040541c003904c840202c07607903440c00b40b0070520b80c1c40007542284c0e081e208a985203c4031040410400301501c50006d4104e0050040c0c4260b5100c1c0c41c412030030811401e50202421400c020220355640c0c06100e01d0880040540381020300c0c1510b941c1145082c00b911003030080b000f0109148400c1d4500c1000c004507610f5120704148108403007071030800c43c00d42c00c0300c8040380075004900c0142d03004034142090cc800c07643c0001c0c1e4082964a00818840554000a80c4c503980b401001c3d58100440c004120fa00d014070401c1ea6004c055081a041180318900003404c1341c0248121 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 728213803 1250 728212553 728212559
    0x10b0d0605040b3303160b0715050112020d11040603030e0312030f070e1c0303050f0c07150b04020403021f0219050715090e0f060301200d05060f0d0807020f0a 70
    0x1200700f800588004c02800c03d14040e40550009180400c620b100300c85003d505e030008211001c0321009004c4080c480c4016081a00b40e40300c560054400c00d015822440c1c2400d08500058901011001c9030345002e1000e925600301a03501140949003150000c1e804255030880e190400c0c10300304900c5c130702901c40e100414214140210502c2c0741c410050504404c0005103041c3c45c40319076600142c80210000700c0d0b0f03000c0200d5094500a800382004036014031081c19a000000d01c5d0b00c101e0802c4236141039010381c1c1103007044110740f01c01c8010031003c0307401750704940d00744400301c0161241d4450b404444045480c1191800d00900b0080c40c001f91286503202c101e214040c03c6001510025801e025102c0340d41d8800035210248800701d0700b14620760302132000d038189603050180c0c00301c21860344d0f0301810b030a900a2158018220568201035680c00341d004000e10104201d10501e125681300b9a040790b00140240302ca20003d00c0040c94102e0140d5065485420001c0c8000840c549681e503406200d6051311207440b030b186 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 728215053 1250 728213803 728213851
    0x90c060a0507053f12040507260613030c15060f030602040302040f060f09020a030f23010b0307170a020412050304180b0a030f050a02030f010c0809061017010b0d0605040b 75
    0x80c4104810100003605c0c040f07010003000b4020507000c0c0a9404540c0c40402c031111008003041c41e1460105103d00681c40412000c00000300c02110b820b406071078040541d50705665809025105024400480c1c0c1c0e00e44010505001001610009601401c00562110304600400c000c888841c0300d1b48915614140b400c1103044001ca003208112042c80c940180c0750b001c8454181c000d8940d100c107c0c11864604241d03020f00b44c0180c28005c00ca406640c000f54016a25840c891079140300070350341d1a0105003189a950440200e1031540c65001c5200340b40507080c0761b500c4200d00740c21a80002e04a6032a0400b040511081c03243c807500b41400c20038004144440b884c0c203404941030a4041c0405059200200516010b100c8100a08090550701a0440b042181568030241c000c1c4088100040050a40b1020400460001031130700c0c0940322001000c1491403030508074040351308a01d80c0300020b40d500c42d42e601d10305a031580d80c0c2038402030285a01040c280382502e8140190b590080085101104070030021103003030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 728216303 1250 728215053 728215057
    0xc09090c09090601260a020d0e0d120c02120304030f080901051605070201021608100605040e15060307170303010e0106031b050a0908030315040c020303090c060a0507053f 75
    0x86828204103020182981181c480807003810000009042000c0030300040000f03580c000e02300503490a5040001c0d0307225608094684050b10859800540052010885d1640c5540603512405190048641c0c07007101036442d17000ca4204441c1a4085003e1610020304290081001548010b051000304014070307007050b03124040c8640c52500b400b00400131030624210b90007007100c6c00c1c0b2648000c40c0d00d00040c1d80c2d00c4070300f556112040c3d248115981401000a1507082902442203d2000701014011092070396100c484030301e00062090383d0520581100003014101d50300380509541070140510b0341d82d030600c01d03806200074061740002c0c105480d05c014503043c2001d0b0001d4415548aa143c119503400e0108411a9124800d1f004a44240800001c3c0204035040c500078000604050703400f80190782d844042a601c90100322075440704c5401c81a0903000510f003580040c401d258407400c0c890b00705441c54480601d060f800f03410442056907034500081e80045a0400c4503101500ca0075031800401c0c1d501007885e00d40c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 728217553 1250 728216303 728216311
    0x140a080d0c03030903052221081801091d040204060f1203030e07080304096806090f122502151209010203160507050709050c09090c0909 60
    0x1540d070b044e450b0170148600c0c11503807000c07451085600010381d10380c0f041c0088a0b540c40b801c28150598a403907454a0259002195101d801c030180e9801e100348040714040c000343e0507000904202070900b0118250258002e1040c45042c211481403952403e0300c1804210740203030308052030300729500b8010440c100c005402aa02c2c25810321f4007040d15a4041a01481e0801070340001000d03001c0840c021071050141e62111009d0284c1104980301e41d00d00701542c1500080ca5110300d4409650b20100220303141c02c40d0002e14045440c0100104007070184801034011003000054154280c2240c41409552030040141541418480b000f0b011840200c00d07200c0300c3c0d0b12a5034032a91980c501e131303604c08600d00300c460041c1e08040d4001d0440b10024110024000596114031400400c0c1200d00010500700e0005109403881752401400f5041e420704030030b9050b10300d504034020440b076500c02c05c0d002041c10a03250041600400c01109079035101c070749000c00c00600400061030344418810a0100401940c0d03070503049600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 728218803 1250 728217553 728217557
    0x613080304060b0d0803090a06060902090f01110a06050f0405010c031a0f011202032a0c0a0807060e010e030415051303030f0c050118150e060106030b0a030b01140a080d0c03 76
    0x14a182107804503459121030b9001030705c000000f10400a555102064001c0154406c030000c000d40c0c0d8507040e0b107404a001d022002e43d040309046100320307541e5008440380b01000c0105000c4542d120103d640e00c80c240c4d48105c480d00095200b45090004200c002d021f10300e401c0303c20342800e202c1d40c48521034001c102611010300070b208840200c3c0c40c004990095958903030b145a448000d542e40c3c0303043c1c003180000020714043c0720781a013241c603200070000403904190b1b680b80000700d02801e6266150388504449800c080f03000c3c2c1c1c2c03407940d0300e60200940300c0c240b02c3c098040d1005800381d038507640b400c49071030900e010044007070060010400c05540c0361044a2a440217483d85400c11810003c9220310031036080505040c01411586000080040440080b140d280501e00c5441001210f0003040120000d54a5440390100e4540c800b0005128850103030304400309883d405440d41d41401d0740c1c1e866014800d0400c0c1d00104042e059841b24418500b0078142600240c05250002e0082400000009005442c81d95019007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 728220053 1250 728218803 728218811
    0x12020303041a13020d0b01050f030708060a022802060405011a090f1b130f050a030b0f0903220f12030203070b220b0603060907050307030f060b06040611061308030406 73
    0x40109070401c04489425000303800c0410814446c038011085010a010311403040042800240b500c0c6800944082a100480080c103220740351b4104000107900480315020441180c6441003885580350300c1c040d01c12483c940d00401d131034140760400900310b618105681c0015101118140c6403502c54500d100d40244451855410f5a51183e8000102880391012104000c10009020505003a918582025a00c01c0801e18030803c0d81c450801c4081500c0f80300060811100c000040c0c0c14100070540c1a074010311060a9030b2902d03800503030314030181031080700010b1810681c64007404090903110400d405004040605c500c0c001080d24069a42d002c0e03584000e0141c01c0c0c420001d01d00c154154000b086418020081699034059032030460034043d0111500f0740a032141800150741c0c1340b4009580d004884015014020550442d219010451848002611080e894404034444c03030711800d000703200510307840d070348d401c1ca120180240f80c2c10b01c1c0b0301400e81c2c2d4400c0140890f10020403401c0c02140d8103d580144002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 728221303 1250 728220053 728220061
    0x2010e03160f080f07120f0804060b0d140f0615060316030b1f1710050607061104090c1d090c09040f0c110708070b070224070f12020303041a 62
    0x1002e660710705800140b049501041c02c10340c043c035241c040c1805900c541d10309480c030102130204a48191001d045540050916000700d0007180c03031580008031036200600400681c80140d110403010409815107442c050b404110010a1650103110041e000a80044c642030544041c0000038503078000680007800004080300c081c1102d80c001e9001420740480034018030703080003c81c070b039075201d2104d54a0300d140071900b040300c101008611502403034410202c50803041485401c050500c001c540007000119442c2c0e6951140143e100745d40800b80004100d8402e002c1181044040f00400c81252100300c4810341001e005c0d40c1d450f0307585822a00e58070070180364009440d0401c0c2c00010b0094091110341e0740c80075107490303d0300c1c6841344d00106000b41d44050004542515076101e0580782c0d140d409201d08a4809001e00131301c001840c290191b01008e55070150000d50360a90400070b11030650100b80e007110a40c0344180c041041146902c1c0042c601c99042c00a0b40c15890f19858041e000094030007101c8080d400c850001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 728222553 1250 728221303 728221313
    0x1a03030301260a03020c0103050c0c0709110f12060a05031605060d0f020c160b0405090c0f0717070c1403100e0f0d03060905160f0f021e0d09050102010e0316 69
    0xb901c0450146022030f1844940c5050107900d91000141d050300003030800c0c0014210507400c0e0101c03043d86c00702e4001841d169150030030384001019504998041ca010801c80d42e90701d1000540a8508a01c52900c12400e5042481c204111400c8903400300740a90004c412103404560a14260f0302255000d56009039900c807841900b0004241018007084038501c0424400d1400c035002030701e140c105458099403c10151120b08090360f9010b18410203034000021000070306003042c414060980300300c10400705400c0440c15a9030300c0060700b0920700800c146001040e2001030109001c205d0000306140500c50451201e45808261100008040401920b44030309684504443c1082256044c9010006450740200d885500401074001d510130070141c01e047c803010828a001317400744184280c03001d07280d08810300c500c410159094104401d150301076000f0194191515185000e00340c0c0d005281c2c60107407240ca1a0b03480007500d8600c180e08418116890528610038456000088601001541c014050302c1e000324682 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 728223803 1250 728222553 728222609
    0x300924061f030213051e1e040507120c08040b222f0303040f05090a0603080d0b130e120d11040815010e0708040602070f050609030d1a03030301 63
    0x441d800104a0018240c0c0964554003500a5045280451090329035a0b02084507080070340c07015460310041e03038240941e180741c00b1360800c02020000660a131401103030360000d800c0380c80464034800401e400307074401015002c0d0792140060315451428371040f0b0742455146c0054110009050143d400d04169207074111204014804a686a01040010030482d0303c0800c40b0f41c0c0712440a60300c145a1920890000c00d03c0d01000ba1001d860049017260886454035040004842001d4409400a5525240130002c180e01c90014200840b1102c804243c80c440c01d8148441241511040c1c85c002e0300e4049004540b41c1c0c041210828040d40d41c15a07900c591403203000b0350080800c1d02520701c0072540060001540c103004604890001c54000c1540002c0c2c3c0d0381d26080e40c0c000300c2150280001900100054002462039000d843d030380d4000c511505400c3c0e5980d0302c2e00e1900205881c502007030b0340041000211f00005000701c02001e050410641e0741e4074003000100e640d90006009620200c039a2501d82c1021480c407500b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 728225053 1250 728223803 728223829
    0xd08070c0204092003070e070302030403050d0c0302130506190305071701030b04021014090d110d1b0602010b03100e0f060a02040905070905130903030230092406 71
    0x104003c0100c0b41e1410310716424880c40e00c80c481420394402c400051030081002c82c203c4808484001690b82c2d0800224000d5100400413414000103008484c8036006a20901802000a0300d0060f40d0710f030340c3c404d081000308184c1e000f80c0c4185070403c0a01000303800c14414124100c42410042a9515600300c00d845900c170801c138400c81c2040000002003070020100764140214026a452050000e903113004984404800c90341c0c1c036800745e040041031203d003004c48455100c14080c0000355001c03c29900040d460202206050310304058081c10100d00b40352200c004801424580000c0144031a0314010079151000300c041d044480d80d54580315000c0140901c0074014402c0d6002c1500da81e441d008100302d000390041d020310311b08185050006050180109a60000d56900070044002401039440210180c82e240308210101754003402102541a5003d565000030f40d0520f0a408002d800e00c4101e20071003e0050a0b640c041e402080d181440f032001a16030026080d40c0e001281856840f0004210311000d492 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 728226303 1250 728225053 728225059
    0x1020307350d050c2814040e1609080a080f04081c0908010b060d1a060c070611070302090610051210060305060f2206080111041d04050d08070c02 64
    0xd0030715554030394a500508164091420403c00f0f6225913484400300e008200040021403254480811403114201c0b83c44840c904030b1802c202d03000e10a482001040c2c11030b52240392002120014041007030486050b00000d02400d1911030b0b8040d140c1003196644203035603030014000071070005090305020480d20032140a424802c0454141c5010303d0072150505003c94404e0300020310090340450b2000040c042d0130507919004201d9820071401102c00b0001b801172a4184161030701c44504824035403503000140c000285d07607c01078006246060310140045180072280e1055170058601800160342d0b800d5901d40010068a0681c007120000c3c80c00e0307801c1d104003420000140021004c00078841d00800c1000c0585000e41c0d400d10079030b00c1c1c0409001303680c40c4c0116090b0344502a0040c804d2140040303c1c14124007480c541c40800c5550f941c0c11032030708580e045080f80d959000c001400b844401e032402e00782490414445800f000307529082c1c66640c0c039040c2c0ca1a4107802c02c4400c10100c0d800b00c0c4985000e00d00c1c0ca03001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 728227553 1250 728226303 728226383
    0x120203090307020a0e01030f110d020d0b01090606021207110607050709050117031804020d0b062206020f030904050717090c010905010f0203090405090a05101e060501020307 76
    0x1096055030340b5004070008030f2003440e018202142a44001d04414122580038107003481c3c50792a60784488502c00706a0358190050700e0541020b0140e83c58064a204181c0902022111541012142001d540c000c7c0c2000055600c0015408442070802044440c500d4200311940c0b10840c540c00010054414410f01612510078548045190035480d80498100c1e60201d4200b100300c060418800d4890041184692582010912000e0b280c00c040d0020420070070010000518500754a00065a98000120b400440b40240d00383e041c42100d40803803d40600714a000500d25219048c1c0780507524418504003034092522000494822070059102014611500d0140c0e030080c07814100441d07403641c10030406800036245140006141d4010090050441100d44c091450a0300b00000d000140c200a0000c0446214502c1c440b00400e805100d845842c01404502040054103031602d141c00700781c103d10b90000c951078050100440e0381c00204840403245c0c4000c11501030f60031028450540c41441c500324442c81d2007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 728228803 1250 728227553 728227561
    0x506030d200f1c030c0309110904050309030a06021306030905030301060507050c060304080a1d010c0f02030307350a090314120f0904150b040501110f010f050f090f100c120203 77
    0x6022580444090f19a02001103180e0400e003103003031b155100c0300500000340c041c25a0b511400c0c01a84a50300c503014004880c80c20080700c000c00e240600e081c0701034851a80c04902e01040e04641c01c0590002c10041c5401d0007074810644429449207c10b1140c902401000107900003089014425450303501001002180c5030b25003810103400f554006031225001460160b072005030440143c000035644c48042c0d4644005c000c0340d0341c80102c000c8525a00766407600c01807000100046c442441e00c01c07060703400c01d01c0d000700c2ca01102c0150001200052550804074003482013210b4207a102c0e0103207048030380226200c405141e040031454184580003020810200000803103041044460004004070b200684041001003110511240c103541507000d1802d81c650f04010411840d07204150160074400004262000354082e00b010034210ba2050b4003c500164480040000510402c80c0c1c4030360050740d00d0b016000030841480c00b10f0701ca51290000203034045d560f00040523814401e030800708100740c4400c002c40d0369080c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 728230053 1250 728228803 728228833
    0x9030806130c0e010507021201020a090512010b1c0f020d0b09070801060b070f150f060513020910180e0903090301180321230402040506030d200f 64
    0x1200e8407402007004261003000c00c001c038828008026860703520f12840b0368219004582c6030f171007418240c0c0d0103510601d1901d0781801c20300c02040d140d13140b6200c0080d4180740100b0300c1844034800038000b200d41d01d400c00c0003002e616070885860351044100340f844940c00191074a004e490410180c081d41104070111081c0820081030390f982e0040384403904031100280c0c0c4030a41d9080e00c0c442c0c0125880e5100a00903203001800d981290003642d031055401c202e031203c110a001045800c1d200e0b80c02c0310a501e4241c00c21042c203240e403807034440700034040003503151000020204500c042444184002c2242030103114130000d03a46a2003201074184007400c4c1c283c40c202446a50340d2508200815032280d480c08c40c0c100070003030040c021041c42aa15495840c2100303008000140951180003180341400d1310344601f0b95500100940c44150540701d41030307001450400340148021100300a200c076001e030703000044502d5110b8200b0900b4104499a1083c8002d15440003261b6090881c0080350070f543e0b20031180b030f00600320 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 728231303 1250 728230053 728230067
    0xc0c0803070f0c170a0b07032a0e06040506090f030f010906150f030308071b140109060b01030e0703150b0904053a2f0a0308130302031204030c060903 66
    0x64003070300034400f043da1914800c4000d4080b184000f411a441800c0213800680c03038080441c1d101655040c0068a800386c000c154034003082d66681107240f001d01c00c030070304072a41d0840440d8054610503603815090504080c04600c85115514859220300d0003440345001070341d81080610000301400009210038a42450010007030b150328014540340300001ca4012a020082103e62411207805640b0503403a03460301c00c01503ca030303a1400c5001c15401d25280d005004154001400d0210040190000600c0b060070b003000800c40703a05a05080c10035050100001186600203a24020b49400c00304503803d080210118400804a013001a034100c410310017000184800411405018040084c2c0404101ca100340c2d41d1034000f5030700803500c2c4010f91440e04007507881e00c02d00707401001628001503000c192001070708100c03625440e006074000c243e12012078041015841241070740c01074401d40078540b000d21180e401070b40700e00400c40c540c2002c100c000005000c6c5407280c00000e1182d500701c042002310014500f0000c1200d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 728232553 1250 728231303 728231333
    0xa0206130e0109020703020303060111010e0313140109060f030e0c090903090931080912010b0102010e030408060f0705120114090924070c061d0c060c0a030c0c080307 73
    0x8081c1d540700025507039415000315800300e40e243c2d001e5407455540100560b40b05000036050310781da40d40d400f030102c1d0150041000b00401400840074107032aa25010030b03049940c00310303076025041000d000303010001260003408002400380c0c40c1c14007141170102c01d00401c3c5440038460078141e1081c1e60006020301800044014410050140d903542200c0d500c40a220001090503800814a42403142c1820b102078070390308000241c3e52107196101c0c03400d2181c0e80084c0750b6080440004c019a50750702c200001541e02441084c900032107010145040c02c0c03a1441403600d0b20300082070003440581c06400034030358a21032422502018580c4c5030388115561226501c003041d0304403a402502900394480400c2d41c01c0343c0020302c4000d2802580603601611a240681003500d100600100144024503040380002141409030741c104100300c012072424154400000307450880911601e902a560802c400c0c0122040820060030450b05410b10303038100440e0b454090320034015580b1540f980d000108416082040e5413901200c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 728233803 1250 728232553 728232569
    0x10b04060e0a06090905070e040f0b0301150332100506040609090209190b060d0912050a09141512060a0b0c210415081801050106050a0c050a020613 65
    0x1a288000107114264001c0d00416001c95902031341045501184c0d04a00e0788040107151120044588002082c2039440e502d0480b44810340350591001281070911803c2c00c0c40b240c02040001076840c1d501c40300c040c8803104202c00c40200f000100e80420750790000d103442c8920240400c5a60604003084404010282a00c03603500c22814040300041000d641e00508800380d40080c800081501da5002d2109841c64189841d544a80c40f8245803445603110300103042c90414042e404503282c2814500481e202640c04d0424007488002c2c42050440f580c8001c420046d200c04241d2080c09030b54000010b4142c51290740d030b41d100e2140c0060900c1c100c2c410328480c580142019101c81d0310300c40c0c448041085d00d010700013086c071195000f04194503403203007805c650459a001c10303480030746403503210811840041c0d10909424041103000042c0240704000c01705502d4036005e28402000b0315410440014039910401c20100f0070480c41c3c81c0c0405c01e20406020710000103500a2166a840e4801e02610a00014511580c0c031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 728235053 1250 728233803 728233817
    0xb0307060c030e091b0918010b0a0311070309290304030e0111010b060a0e0109080111040806071e050901051912140906010b130b0408030d050112230114010b0406 71
    0x466400c003011305034000ca0350aa0001c0415071185d82907041504501221030b80704c4840c02d4803002569010f4042e0b806001c56480c140c0d074441305a080a41540d001c100d03c02c58080e4100026804264000403c006541c4401901c991200c0040040e0b6400c4100e5220f02040c020008140010160000c1000d07070032800a8841c03068039018404050b0072600e41c0000190050030400140244c644560140004a01d0504149050907245e2011508585001414030710740a80098288500501081202d62110b11131800750204a202c0d144400518803001521044c01400309500c1040d80c05242a01c00041046000d0005005003800040ca003095500400e070b0003600e07220840004140ca002030501c00e00e2500d0080009034602520b060a66000c00c44181c60360600e41c002180705d101810044c0010013405000350344641110003500d040300c406902008819481640b4000081c8a0f200300025000319122040c00b0842848001405000f20403400e0010198400010074010082000382c02600c1245d5903410f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 728236303 1250 728235053 728235077
    0x90c0a0e130b27030a14070804030f033f23040203070b0a180504050f130519031214130f030e060301030b04140105070f0806040b0307060c03 62
    0xe88424080d61540140d4070610185804a880658603940090018002c450101012072140c240b0004240342e10801c2d8200140940090b98005800385003840e242039050300e044d110fa23440c00300302c5c4600e200042c02e0382d62000400c428540030710a03400303800d00301c0e010400d114030b11510401e0125180018050004540c10900c280c801058880c0350912a8120b8103801100b5440c1d42c00000795070010400ca9051141c890b01082d542c0e180c00c050300c081d00d2180c4880340003158104000d44840065004a40141c0ca003c0400083c1e032020f010045c2c201c40d41c41000034802d4400c4c1070980c144440f001e4007410645003022540101640400e900440000500c000c2102c094503d10107182c014099a40944285984400001003051203550040d00c03840ba081020305c030f09094002c150315400903030082d00e821000f10300708001d0028426481d4011200e081c02004980380c008001760051880145081c200141c081c0001c1d41e54a460344800d82d8110010f045562031540c46100804141c6600c00480008050001c1e174 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 728237410 1107 728236303 728236319
    0x61306050c0f0c010903060507030b03031b06180d20013e0a050c0708010e25060503010e0403031b031d0303010506090909070905090c0a 60
    0x3041d40311080c05484900741009030960500c650001190301d1500d80e031011022044d02d40c0300200080a483d0f10104500814030900070740c0d090301c0005000308600c0c184d8140c040303048442208403041682d9228400240c0c030b4841224440a500103141039040e14021600036440c1c0c00010205484840074480300e5086d5980c860714030003010b4034041490204055880c40001c00d4044404000304a4200002940c462103001044001c03c1400f08840741e001c00c0c03e0100360000e00480d0001e10007000c0c148036061311401410040403910340c030361807900903444140001100310f8502d516024190b07031070409034000c50200100120201942d44802900100d000070304c0e2401121140c7e40080e882441000640f8103840d8040620303c40d61003400100050f9485104442c80c80505881c144590b4641d004038070f16201e85901300c01425406c20b820030004007000110018881c41c221220310341c003a0707203980e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 728057553 728237410 := by
  have h0 := BRFrame.cov_init 728057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 728057553 ≤ n) (h2 : n < 728237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
