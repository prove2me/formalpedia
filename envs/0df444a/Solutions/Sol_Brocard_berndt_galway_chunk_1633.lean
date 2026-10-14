-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1633
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:58:18.311054+00:00
-- url     : https://prove2.me/submissions/21b3e848-e46b-48d1-b288-5851acc0a372

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 293525179 ≤ n < 293705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 293526429 1250 293525179 293525203
    0x109021605100e06160e060a0c12030f0b01180b030907030b10050f10020a020108041104091a06010302040609030b0c07080304050303190b0117041a07120b090609010b0913020a0e0102 80
    0x700319078040c500581c00180c080d0b5584001d61f0160b440344c3c0170075810740300020004400b074942950040344800d495171580c41480c481024020802242c02220011121282060b1440c48014003008090100c103003002c0240da8400250003c85400688a56510a40301416241a05503e29003c428080703850481d000ca0554901500c00c07500b2010604030083d0745880c0e0725406418000c0f40c1c40494184540341d0300c008210000501f00344081511468903000300b2294040c41051202110b0104590390b10030300032202101c01b19901c0180040c11500d503421040c0d8044c080c281c03030340020890f8400242000000c2d5108030b01901c0515100e2500f4951951032200c0030b82c2d4608003514201402040d41e8214040508171103079900038540b51b0395146015403042c0c082945030711003a0f03244820030108941c440004400c803000e00c4014072101010106000c0010400c2d80d000e5400780b85100103000070341c848006845990f100825058010002e494054200d0f80810316035400070301800c0e029801940c0401c0030b1424a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 293527679 1250 293526429 293526451
    0x21c05060607080d1d2d0609060f070c0507140f040b0901060507030513081e0f070b071e030306091103091506010519090f06170109021605100e06 64
    0xb803290b40d5051458803410513400c042e60383d1113415002010350700070380200d421604402c44001005a80603240120000701a940b40c441c00007044030b000480208640d40141a244018141c0f030303d80e460020b00c3e29400910f18410828a00c00036408514200b0911000300502c031603d0b000703200c1407070a00c54901c0961000c40d00903810081848110740b2030540d6541103030440c0c40c0541c2c644070705150480b105d01c9001a413900b0b41711a80c078003080503000440c03040d41c1010305c0001403d1120100015540302c01102e69803020b1904402000c003d6070b000e4000400b007485c03084d4012603400884944d895039070305400a040d030000b651b0b02c005005d00c0109100394005d01c1d003801c500509501d070000840383c0c0c43c0d00b001c015940c010710040218005902503130a40358400d01c13626001101c1c10309040300414950240c8206070100360410000500c0e6401540140c0c0aa203000410078000c1e030034051182d01039884002d1140d403460000c0740c042c002c1441848000b041d01410080880d841d80c40c0804070b40350050242441c0400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 293528929 1250 293527679 293527687
    0xa051c15050f0d080301030503030105030601081b100e0d060e0c04020702150d090c0b1801090303200f01020408030301031a01060203180f04090b2512020d020d021c050606 75
    0x40140e8450650466000b210071190031407000001c00c0d40d240c200f0720b000301907420100c0080200300011014606940c0142c040310116a6184810750741d40c1d21144204e801d1800c0c4c00ca1042150401c0720340c0780614a0241400c0c0d0b641d90081010825446444400384c0c0d625591300400d040d064401c0c0451340f40f4000c101c40540c00d2402075000504180c3d0881c0c00c600c0c407942d00207090b00703c07403000b07030019030b25a0340201c0f100e141140d071090b040f2170b6603020960700d4200c0915602580b000f90f00411507002520b0309643d4501340404040c1d01443c00c0784500400710f0091081c100002c1000200f4002040502000390145460794918640002882d035034480c0c4940c1031108400500c1981d81c000190b81d02c907840660091010101c00001c107031104901c1e00102c1d0810308124600e818411403554803401003003c030b000707051412214001c0400364000713007104e0300c0010b80c0301031505002c02090b0003400c0e8511840d180145003040740301142049030703c16000003202d0200ca0b4113204c040b041520442d0743c071a6041d14114a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 293530179 1250 293528929 293528951
    0x11030610030b030f010903021501050a030b010e090c03031b060c0322031101060e1e060907050d15030309030c090b0607060f0e070b1b070e0402010e03120a051c 70
    0x5030000810504155440c05804820340d02002420402d00051000300180f103101e04009440311900181007240c1c90402c800040d0a05010f031241c4101c81d044a020812a402c04d4402010b400002d0641100c6100f04c1d20250b07440c0d541440103020104015404009a00754000e4035402c0240042c40306031880c0341030040014109045900340d0000208032068030b0125036614050b00c1244680c27003a030780c4641c6090004640f4442040c180c0340607100b09036910038030901804584403c00c10449285030040c40b480003051125000d05c02400308545e0202010603281c82c800501103480c03010b5401a00041c1c03e40c01e0420070702c4203442c0807a0140c90031328000d110f4100707c10042620f501c5102002040740d9030b1051102450707200707940031440e040141e2040c0c8204030750744c076100d0340320b6005001e0f070401c52616036450000c03d410000c0d40404445d41c40b120601c055840c1c1d00151a038800300301045800d07010318601340040d83c15500041104400341c0d2640c81d00c03005441152040310142c44c03050344000745440c0903110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 293531429 1250 293530179 293530189
    0x212304060f0804150b0102030408030f0307030b03191b0803070515060303031501122a020f0f07301b0905043903150f0603031b0317090604020301110306 67
    0x6500282e9074130102d11120748000403407440c40f40d60f220501d507000c00305010381e200d410000158003c40c000c0d0f505000300413800080503190285021070412034441300e90700a00003070000d826202c1c44914860407020f540c0e42c0700f44031405d5912400e000c4445400c02c584420038038040c400599008402600250700f07501c1d004402c0c0c5004e50200090754103000c8140310707582c5401444d4000c141c04440d20407188c0c400422140e140d5010140780c1a44501500801c40d0781012500300141c0121050207800041403602c0ca450208100702c00e039094652a40c04441015600b80d0107090581483c0c6031241d5203c00110045450003404e40007580c0004020350b042c0014130012543c1c0384200d1075000301850714612012001080e2000d44064008420307142c6020503000020300821042d2030f041d084226805100f56500707401c03044d08490003400000e02241c4400c040d01c0e104451015840b40192207410215414100320300c3c0d01081c04c4045410a0166100c0c404120441c202030180c020501981c10a45003141021800a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 293532679 1250 293531429 293531453
    0x2010e010f0e151006050306030a02210d05030c0a0c061b12050c04050918010902150c010f180f060e011103060f0f060f07030903120801031e212304060f0804 69
    0xe0200000400440c900395402e11501c82d06903401000d001702c41081904a607603330141040000400d00500130300c0311000d4064812248220fa000e0300c0d40d4980445071800b40c445100035a0242c0b40585c5c0c0300000c41d511442c0c021500c561a9640d210305030443c007d0090714060f10303001000c40301060001e0008002ca03441300e102250b0081607045c3e0b800d282041807002d160040075104c0c0b01a511948031000380d080c9585410003800102c003601d00038456501100c1c03041e429540c0c1d5104c58040c0b00030140308840072030030340d14620511900c9500003058a103580000c0c2d500351400150b500103080c0303000040c8041450060015600c0c810280ca05803201e0b062413000820500410070822034144000440c50308051040c9400009903902180f19032a084030108002c00190090000700c48901a00c1c6c90a0b68a0888400345032401c1c1c0d008445c1e40105c8680c00c056007103252580610014088031480c1ca2110714034031100c0d00748a110300e0360b80c20380f5146029001090303040840c40400502c8034040600010940310f40c959 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 293533929 1250 293532679 293532689
    0xd020c011409030601090b03010c0203130e092104090b040c0806011116080607020607020f0a080a0905030d020d0210202109070503070f0815060102010e010f0e1510 72
    0x60a070180c0150621000d00c9041605945401008000310380d04940ba480065401c106030020841002c4d09901641d0300d228801c502c001c1c620f200f4008100c1d00f200014501c0e48108407c1c140d4580c03c00c0946002280302144103480d40e101d00c0800c1c207100f1f25840f403140da005404100c80500c070082d0b055502070100300c0d0140115041080040020500000030411440005002c68807020b10940e5500d941c0d445a6096407100014003411010880040c800501c1c80b48a0030301c00080c01d0301c00c61660700c183e615481510101c051181c0329000140c0341c1e03408d0000580d00e80c900d8018185407a07103c0300090800800284010070345180c481c08c41c10411f124461016100480381016607900c04000740141c03c40040d20503d104442c0b84c000300071010202091010864605900f100c0c50651100e80080c0c0661403801655000d0780001c808074282c142400d030f029080181800002504410990030f1030030f48243e98000c104941c0c80e08043c1807602c40c100b000029001e915607000c401400d000b10341c04414030040c0b00b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 293535179 1250 293533929 293533937
    0x103052b0e012c15040f0b0a02010f0513060507020102030c0703030b0625060c080f040204020a0e060d060f0807050a0b07051513030f08040305030a1e06090b0907020d020c01 76
    0x14400264042c0310039580842e02c1800c0c0c503070030300283e0403051441c40d0001c10203801501d0268107004004910002c0c1c0301941c0070925614105130800c1034966a42e0044100c0c0c9085640706d2000c001141203a100d500d020b20718129400301d48264500717044007a1503024181c5400c5a01c10010031007220f10000955250170340c14600810400100c000040c0c090041400002c00030001801c04155848815100d000c100d126203014048909042c0050303601c1982141c051803014040701c00140140f900b40d0017064441c10303500700808604400d0300030036603c1e000748080c0c081c031503036480061000d100c0c038107042c00090981030000c0110509200c0854071041992040c20a07682002c10000300b0440180f0801c0780460000040c00c10310300c0e00807801202c00101c03403021b5021504164118105901c60b102c41d521494040e00c44602c3d40d1101034001c4014101c0f40d0a0200c10540c07140c4280b28041940a200014054014003048004002d803c00c00724910140001055610088025003a1500465018003608090030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 293536429 1250 293535179 293535197
    0x90303081807150206010f060c0201023307020309190f0603090312020705031c0207020a0302060903013e040303080406020d0e0109031110020c1009170a080103052b 72
    0x340c03840c50220b15800072401c180c50700c3e0000040c03940c0000e40038100c4103400e10400c0059a5500207640090030b010020b401a0050910302c40118404001c0301014410040b115003141100c141285403e10705031299001604006140c00d9140f0b8003602180d95500d02c9901d04541601d00b5108074003005142c030846042c5502c5100280a0502582c6210b1050350342da075041d0755070381d02440c0c2a030b12a030106c880d4801c5466a803000704150001031099541d882e074045c00c2c81e8019801e5400304041a002003030600d40c15900c0d00091480384c8540740401d4202060a10030344a03000b0841300444101030140c003036a1001c0c1e400d00041002c40c1d0300c0085550401d400660060703882c2681013628000d4061700000d00225820140341d20300700f60740b244100050b0585401514000785940291b0000d030320419002481a030300ca506c50040b1201181c0c0b007000c03400c0c8103598080a041000c140f10000c0d8100d00c00800c0882c80d900d0040040c82010301000c0c0c803200d0500d500082e03440001081144030261000a4010804000c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 293537679 1250 293536429 293536471
    0x2300c2b0c0303090303080a0204270e0d05030a05010e1314010b060a02030304110301110703320406030c080c070f03271a0702060f250b0105030c0109030308 69
    0x90460640560040c811110082e1281809403290341c45200c12000030b008000001d010301074510030b80c1c00b61204c003007002007a03440d030f081000a5402041820303500d56543e15122503204a00300201034905080b52202074507803502a5080c0d08032401644400381842c400820405014104030300d03104003945c07143d00c00742188400d040f8180100904d15030b154100c00c0c0060103807011500003000e0b5100d40e100e4103091411007002010300d03082c1c8030350b180f00900d400024420000024000d00030b41c1d1075a604006411480600050030410240c5000c60f1440310460000b4240140c50b81401602c0400026080c9440d45082402d0225001c4c0f01e40710000d80003060103815074040600c40e00d00300b00d906064840301c44104e0610101148a000d09104012510b10001224074044ea02d000980792001d80040c495030030070902e030034502c0480c5d200ca009850354092002092400c0a111001d0840d05401010030140715030511050610f09001014454140a101042000040c1e03010001c0b0394801c0692060a44c40e01b800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 293538929 1250 293537679 293537749
    0x1060c05031207120e0f030d0207150216140109020603061509041b03060609081507050412210513061d060d0b0910230d02300c 56
    0x4031111103000e48600c00380078000d5842040010280c20026040007544417140030b0960f21440d038920759202e900300b48412940d0714810340c0a4440c41d03001d00c50f6100b01c0c0b00d140d1a907408a9100f44500344400c1c80c450110400d002099003100303020010a0b008000c0550543c000888a000c0100700f240306045a804400403c2e8001c0141c0ba06001c010b40240039055220fa0f151b01d482c5080100b180009181070000a25140b180c01c3c110308130b549520161107980110040c00e038410400610b5101400001c0000080003002403800240701406101c0c0d40440351300312640080c00000c0c101002041050505c1240c00c281d83c1e1360120b00803210a0305101d0b1000c542003800003130400c2581707a040c6e800781c404590126640000d0f0050343c00e1150840718400d09642c0e04201c014006d00034001c0d043c4440c0320b11403501c0c6032410040803084240000702030140112076a4006188090282805140e01811140a60081d002c0c6008602e10340580301c00303800720704083c60100780002e40b8100901c10303550f0a01c90301c1801b00d0034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 293540179 1250 293538929 293538937
    0x7020d0207290706091103031c0c09080f06040b0a050105030d270305031207260709030f03020f010f0204080c010c060605030303040f0314070f0b0402120319110c01020601060c0503 79
    0x60b00d448551160041e040c04401851a002d040d03640100c5464260b601d40340200031142c0c8490000040744c8840c8c0503443e083c0042c042c1443c01c03418060034040c0400c014904001c804800f5080e030000f0030300b62800b03240c020a00c030009046c1c5803095090900500580d900820300030715800325841e15450403206d22000070b9a40260100030340800c3c42498001c02402800f100805071400e51406032221500c4010702161280c0c01c510000782d000201d50070030103000c1d40c060348641c0c0000e8146040001d2a0300d1307449030100b090486d002107025a010310100c001200c005e01a00748a030b50540c40842c1070600d010241d40e103c1544c0b40c881810058080880001c0041036401040600005400c50340c0b00d240a24103101044024081580440c98903100c0400c242824000c41c2e10081d480111421501d00d20354480115035000785c801c90b172061540044042c0344c401003028108103c10503900f030518010000018040900303034451b005907038008201d00c0c61b00c1d0360009262170450b0664900208188900e080060039409 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 293541429 1250 293540179 293540249
    0x1a0d0b1e1503060f060d1202101b02060f190f060b0403050109020a0b070f080706020d090302061005030303010b0a08060d0618060b090906041101020f0106180507020d0207 75
    0xe0280c14820035005412541c4002501541203410648820240d00c42240040315595070200780c1140c100001618695011410b402e5401104c0c1001070740306c0c038142592021042c00d1540903684482d0b4004960402045d9009a90801c0000d01e609081d080e480d0102006c040c104101a2a451359840f04120799000800520ac03603070130251141d850307250841c080c0200c00003c0c0c0c400c021040300400e1860b2200100d03540326030301c032008a410012643c0c2c0c1c603850b0741180a0030b82d2015801c3c0200c0d01100664000c1c1e4528a210364040c6c503107407400e0740d4552001040d41c0c01c418080da10500045c04549442800c83e004400b050030031111503669400002c00f09001288002d0a41e810f00410700c441701040268154014030803602448a00703100001e010181500300c400c444281d1000c00450042031003100401c01080c010f00c1529145141018aa400c3d44d41590100040e045015484026043c0b0781c403501d0740040b41403001e000744035207043d0000d5984407213020b120a01600d50b400f04000c010b030030710f010840d14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 293542679 1250 293541429 293541481
    0x306030a231603060c0f0f030c0302040519170a0b0a0e03070f050303060f040209090402040908250b0705030402010c030806040204090e0a03031d1f0f0513061a0d0b 72
    0x400c45030301650080407610080350100c1c200300da01030420f0b0103a1400b0801b03007410340d01c00001030308074403089000d443c11650b4001499070801000c07030030b5160901e104500d25001d44820141c1c40c03505031230615840c400741409804d60040b000045c0058540481c054000840e4900801d07044820001b9070304610850340300400601c0c81c3e4120004010022025510a0b0011104142903020440612040e4400c003c80c550b80001c1c07840004c1d005103081d034807400c200c034000d08510b03007028400203090b41d48011416083c00342c0f0b60021103007010451917101441e8012801c0c9403103810f50070700e03500107080c0c0a54680d0050905c14010b000411940310350381624010403400038140a00c00c030040100d9182c107248070702600000d00744a2008a450006a9080b003425400801031851240408041d441c4a20300f11460070320a403519658030300b0448500605000d2010003000160500d4145001c000300ea40a07030400b00740f071054070b4070380e20079594824400e0112a0860304540b85690b41c0f1031041d03003040f16181e11103460 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 293543929 1250 293542679 293542693
    0x1c0203060f09070801080c1005040603051b040f050a1a09060307030f06090501170106060915030204031205040e0f0106050703080910110c1005091e1501031a0601050306030a23 77
    0xb0304d0384641c1c1c040c103c81d01d040640d03104052442c180002001810000c502049041108000c0316100b90300c62540305554a401c04405070201c00300440c40d41c441d5012520517803403d541440746207444008070005202c0143e034902c4410a84c40d10360345a0040340011489050003100044085c0d0094004d0a61700000c07600400003140c540d240c040042500303000700105078480b080c400c031080e50140f256030141e40090321a102c10906c0c1a003685000c058040d402020150207110001c006000c0500c0d0703400141c0740352900c40c6c441f4101001d4007502100107004000c8285034100402c40d0b40d803c41c1c112000c140d05840c20000c0c594507100c280d440c101d40c400c00712030554906a10008054502800382c4880d44104068a1410041d1426001a5082aa180b50b19a01b20701040c1030410001100c0041030740c0f0b6901694065851460400b0051109a02c1070343c124280c42d960043c407200000c40103070f0098007428000e00314205500401d95454622000408111200e204240c01c41400040018100c51090440d804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 293545179 1250 293543929 293543941
    0x10c080d021315020a06150e09010e0c010f050f070204060e04031d06090f0f15030907140d050d0c0528061506050d050403091a0901020c03031c0203060f09 68
    0x80d44040d444141610484102044010402a500301c080e500f41d4010a00100640c99000040034840c90180b002c00a0300700010740359400005583c0700e649814000141000511140f070300300100380c1000340c100005402100c9505410609481c10342c0b200b80000d070f0300e4948070700c0454001c0600d508020120b020703500c10003080662010114151803016402040d448490304140005401104280f59201c01c680e07a44800c40e0612141c5040800c2008140103480c00f0b518844c1d6601d54012740da002201c2d00010301c1406852180b059054469000351038040006035252185070325074a0150500e42000748810449091160402000030141e001e4100c00e4a01a042c2940755100d07200700c01d08591060404405101c4203000c00b046604680c101d8940c1482d20000001034402407800600c01c0302808840350b808103480f40c20a10050841d500340c100f8540d214282d1001920b1301c000d00f00f205210f80e0040103c81c1200070380e6404194200003642d030260722902d4010014141458404055030440000c0040181d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 293546429 1250 293545179 293545181
    0xb2508030a0605062b0b0a0303020f0c0a0f0b070501061e03021809121b0613061401080c010f020a120306030b07020304060e0d060e0d0f030b03010203011d06010c080d 73
    0x3000e805684420080310f82c1e50700c184401400340309050f030a000f034920301c1d000000c5004110f400c6201000c040000c0e502035000300040c0c801c0300d21303001175005071f0140d0008401090100494607080108840340081c0b2840c1125031120300515000300c80e41004049180000c2020940041c00074081d1ba00b01c0100e000d58041c0000c58546c0300b071006a01c01c6030742003548016440d2082802d801124008050181c10b444003098401c1540440e240d40a5084400c010071100c15061015500034110380b001c040d80700040f41016015550980002c942401c8040010864030200180011941c0b600382401c6106c4d5040800c161700340101307a00060310300c181041a510311150315070b01800c1030b00c4c41010790741d40d01d03280c0c0c0200700d0b624011405a04045105194144078a1900c2e800305090b641c40b0304c10105144406c84441401d1042800c06d01e00440c189440d01c40103142c25004204c191300065008604541c500900503403564140d03900700e040c803115140404c0d5164460807424201c0c2d82c110008680ea2103010300190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 293547679 1250 293546429 293546431
    0x311190e061309080706091b03060b0f01030203062206180501030201090b071518081204051b01080109020a020708030a2a03230c120c0105070503100b250803 69
    0x151055003080c1c0e52480b00d080d0381c4108240d85800400d002d0174603c0598038400181403602050b22144070160303580214039081084e04010310700c100800300702050800700b8410700301c3c9404911814140144100651510b0780b400d038080904440e209100804000d0115034020500e981006041034041c09541144d030080b904035078100d034800c0e0780d2003800580c0c031010010700340996000240041140c0d00102c0202199410442000c891313011120301d02e0507140d40d650a2540454122056540701c502004244a820f0000d5080110046004044c071b0b00c407000000c004131014054400c0c4070b1f44c045038207600c50b8400c10045000e443c07a101181e5445851120140c0790304407a04201c1200504031085841c88552030b01400c940e940d1645802650f5070104418600012150700c0d5610f4040041c40390f012039150800440c1d0201100c016151f503526000e450590075503100814100034400d0401c00d111410724645c42203006c407183c990820361540100d0104130034403040c3c5403c1000310f207510489a424018a04015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 293548929 1250 293547679 293547691
    0xa0209121c0804120c1a0a1e020910030e01060f08070e09120406030b04110313060608030c0d0810150915080105011407030e120a0302070b0f040311190e 67
    0x107000010412901940c084400600803025080d01c0c03004180a250032104c0d15104000880d071a0300382c3c0401e0b07841207504403158030308140c0311010700b01800d0410612200c41d186110b015031504d62020003154880d51400c100c0010140c2c1e65804007030b914400c0d400040036062010384002c1d841d640d0901c0c0c5aa400c154040c110394501c8501c0441d01c00f00002581406210b0b200d030460381403502e400426030041108001c40e6800075102d80c00c2002e92111030000714421212000c1202c0100000d0411004640301608a485140d201300100502800e001407074040c41959443e1003504e03696010f91036210f011560b401004003030048442c12403040d070080118403d03a4840c0180501b032035600b4030110342500080c8603440c0850042c603c10080300b10700c20b00911580c0e0107070074110621310285020400412400c910703d41d03917410150f80c0801701541488504010180c0b642400c2c24102a0941868144100c2c032000f0048406807900c0340c1240c03211846007480031001081440807a50320003d1240c100011501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 293550179 1250 293548929 293548963
    0x2090c130306092a150c0203010e0124080304030503030a02090a0306050a0902121f1d030301080c010905010212032409042a080a1b0314030403030905090f0604050a020912 75
    0x140741a6008034900d011244154202800809413050641c6e90001c10b40090341c05540740c20718a07103200c074240241d5041c24403000b07030102a506640b10384107060303a81d40c200c40010341042104002050000042c3c83d0000e01090340141d54045100002c0c88601440d4402401d2030b0502c0108042180d544d070000e4101d034000d45141c1118421000c4c41e58683d82e180000c3e000380c200010306072817088181e62040b0341c5550300e3b501524004c1242c0715a946540c10990007070704194003500000d0f80c0fa5074880c490b0f10080c0020300051500103140c41120200c2d0000034019440340342a000f421703035292155030400c205414003030001d05a9040900f4840c2022a03034a415194590b4000110014200c4510311341003100c10103c0a0302c106800742c0e40c0e10080c1e2004038a092079a42c1900380110201e20344412106413022070000031545c44d880d501d009049100c0d1a40851700c180c004a00300925901840d5142e540400104d4000403190307964101d500080c055115007641001c000b290044002d103001501e1186440a080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 293551429 1250 293550179 293550233
    0x6060c060a0b041b27030b13110d111201050f01060e1c08270102030702130b12060a0e01110a1803080309010e07080105090712110402070602042102090c13030609 71
    0x4403103480c055052000501c00307c500b81c00108084041500351035024032070486008540840c0d03000035142d52040c4400c1c1d0320300c0001c810300c017020711b0002d034040c4c44d00b00904003d01032441c0203c4048281c00051140d0018811000c8400d211a541c60902404060150a803800e5034441d83c01c6c07085075a0024401040840c484441340c22400d001c070400204002c405034011460170310b499090110b540c0140c03509802c3c4649500f0003190541e20466030340c1001c0003650041c40c0e01e151040d0000140c3c0c0d4603009504840c2d240c2800842d00840c0e01003140c1c1038450394100000601040328580c03910082a51000c0c0200c03202000b8460b03180d4040d00103800780307401141100e41850302c540c801400c0380d070242d03a003044592000204111030081c890360006002d02684814000092035000b19050368040c140c101c40300c1d680060280b080341e460b42c0d146c4401c900d03031040c619008111940860741441c005421444c00402c04111a101860408200005181d0020301804002c000c2c0c40d04400c0c58200040144115180d15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 293552679 1250 293551429 293551487
    0x70b0705011a0307180b1806011b020901171c0201240b16021203030f061005030f0c030a24050301050106080405070b21071706060c060a0b041b 63
    0x4403150000c0c00401800c580b900d40038040d02000501c1c0b68414040303842e5011500e4079a10110041994041f83c4607000b050720300140014407100c50130880300c0420030030100000c0584c580510981c150390790180c415282080e14003c192504035020081640c001ea00c04600031090360640007043d41c2c007415051200701005030f0400104655850190185421090105000310308540070701c4110a0300292441800b4240d10703008505591003112603000b004034030310501800742080440c00c0c41488151070500d08600300181342e80d01c690b00140c100c154290011001c14002440c4c0d90003106007424a00c07400c2981690034002c200000024450148a54a0130000095141c011000c041c802e80c0c1c00ac010304089818541c00d002079406c0a40820031000300407450a000d60b61904625004030315546501031f140441c180840c130646402084070303010322800c0c40500000c0c400001e0464001c58400c4012502076900d00104000345110540b04c44003168112450074101d4110b0b8030003210104c0782300e038081100343c46 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 293553929 1250 293552679 293552711
    0x30c0c0f0b090f060c031b070905091515060d0f0b04020301030f0b0c0f18030c04021801031a04061e06090303140a03060e0108010204060305060306010608040221070b070501 76
    0x544035403400d401c42040000c6240c90032035078800c90044010311090130000429007051460308a4550307040c44128142056030f54420422100c0010030a075035003800b19103400607250b0388602c0c0800d10a45481010404181c46203140e58640988110160105407105103400004c0c025040c5030b2407001825180c007403410581d0616000b160305076034104544041039600c0382d030341845004005041903101c103c1403188610703d4142100a104c500b0030024044900d4804d60b04150403e00d03464544c81c807441c41000740094030b68010a064a01300f1090074002206490695010001e0b40d4106190760312910f040000b09100340b00b000c031800d046010035644140c0c1da484030303000d03a460f820b180405404500349118000c240c0b200c0e20024204010689008030b030040d595000540e000c2001e070001c081594002c1000e0155940c07521440354007010840081c40c4c00d525100c00a0064030024001030701500350f40b1a1100c550781ca940c0446030340380f528800c0b6445030350340e51602c00c0503030400703402240c040d400e141c0c4882c003503010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 293555179 1250 293553929 293553959
    0x90f02090a0509010f0e090f06070c02040b03070e0c0f09030d0203030403020d0c2d0f08040504111602040b2e08060118051306090e06040308010e01060801090504020103060909030c0c 80
    0xa901d1184866410006111561200104008100d102c2c8c09464240e0302401c1c88001c4c05020b95894241c200b02040c410081561100501039000b644100b02c1089590400b10460f50410030340d41290341d55400000018140c0d02c41c401c2c0c2c05805224018107a1292030340000150311450103030b8280e0714a019404412611340b21145005821200442103000d03500c8256000c0c0250007415684109038071500342e8807622820406c030010307640c0c5040440d00700110304090140e1070960040a10036442c0150a03005007100844040c8040e0017a039880f51001500d4554245c4d4048000094a00d0324211100742c62240c40b14507403020040001d2881004103695500400400303080102501020000504180c2840340540b038000c80c56120300d44a400002c1c90a08620500000040c010040c1505103405d00303020345101e0041c2c0c80707440442a00401000001da02448c4039056558001000c00e254a650004902400c256003111202d64030b8a107400341050b80003007801107034910580205075400e40d070300c6501040d020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 293556429 1250 293555179 293555189
    0x1120605060a0612020d0e060a05240a180605180108070b0f0702040504020310090309050f0105090a0b03070309080a08040308090613140307232505011107090f02090a050901 76
    0x4208402811011140c1e009401d140b10b1141000511507c80710700189881c1c2e0a444440c4120740d41c0c0244820210001c00c0b50b8106d01e00c4103e21000d00e402c40d00401e1145103e84656950b566844480c184d10750704a4018100070704004004c1001d00b448a503e118000400f0320600c01c4900c1003041c001b800040c4a01070721600500d5856042c1007103280d4081c403000d4000240704030f80c18090b40c80d1700415040c8a02c40c48002e64002c1d9140303035a50b41400c05100f1030401c254006030501a0501c0742200c02d9540c0e41c148015901c00382d48590316a201e02c8025030141807040c000412a54001c00c1d442e5001c6e61181046110314042d541340907446e100d000e01561184010b58041207017103c086022008100014003030302400801c1c1d411245481e140c0c0d12400054080c5080071801c0444103985d031400b0390003c115001e10758200c0e62190a40e0145111940200b442c01d2041d1410b10251052070700280c1014403241004001c0700405228005034500104001d50000012902c00d00c0f4526001c1414241300a2043c141c403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 293557679 1250 293556429 293556437
    0x1030903050405091e0703020d18050304060f0309080a03020d23180c060a030504140d02030d0b0f0a2709261909030209070219060f060e01120605060a06 67
    0x1410030043c0f00041e00c0c01440f11030f03480b94200c0017005440103104842c1c4100e085940041c0c550341d02c4080c1c7e80a4441050081c014600d010f4002e101066010084604607007541c18919003541c10b00100707a003d031510150151201001140c041e6000d0b0b00354000b80002c1045d99800c001c081c45000b080d001c0417404811510b0381603840000268007207240c1c5000a41040141c2c22184e00101c0e500001d001940b11083c10000251180144010403452800001500240c21302920f003413486010700035664080c8010960f4070341e813141c6020080c0d48a44100081e00040a0800001c441c0c9545c0c5410032042d12058002c41800500b042c42a280121b201e0281640d900446655011550113401d40002600c2200c0c6c0d0071295040118041f000140040040c0c005840d0f100d101800d4554010094502001840c1a0a542007200c0e45440504210f840724000b6900c204c00044500c2c0400c80030380102041c0d00b198080405000010641c0d41d4840e0070718000610030312090000750740b158144640c0d408184a04c802007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 293558929 1250 293557679 293557687
    0x50a0911040b0f19030506010b07050a0320060f0f09120304020405060f190e07030c0215091609020306100f051206150301120b060307080a03030e030409061e050103090305 75
    0x2468241c0001c00707040001003512016203450783c0010401c00c4c2081c007141c1c40704103c07603081081240078404a0300400d80822442d0400b5580d03100c190315035180b103200504000c151000003111280c001504450070380b0ba98100c41e002d2901b400800141b12055803009400012403000070b6004500103055401400c03581603460a50b1600e0342481f0160001a16243c1e010602c84c100e514503032524038184c2600c2e0024031000c0402031070b1049030b10310b070040600003404060901a5400600c2d400049006003440789061101d02039483c8600b260400c00d80314507520031461502d5000800ba68542c000d980170300411035820882ea0700b00350301914551071000e694004544188800002c40915601071a8000c1001c0c0c842c591b14000030b0000c445e6640700f41c01c42169804a6401c480600400e45400c65006200707400a10fc0e850920360b90315520f42810400608041c2c544001345114101171007074900519041c0d070180040358030f0f41c00c0f0640b8101d403821603611040c000100000c096129001d04160950103446141c90 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 293560179 1250 293558929 293558963
    0x70c0302010b0f061b0307171801050301050d03050a020c1314100303020d12020d090c090e0703020a050d14071410030510060f03021228020705030a08060114070303050703050a09 78
    0x2d80c5d510748046440b24001405420049440c82420816142440054540d500c85606182030308281e015030742810440300b032005101315200c0708090200d003505030800a40710080030300c0403032408105000740c6070041395041b61042040d0f000c0c1c00c00e501214170989080710f41c0e0707074015020096003100e101c0030f40141c3c04a031080660f24022140d5112038501c1200242ca041040c1941d4025101181800c48211440d07110400038048544107020711280e0203030107062441e00d90340011704c0c1d101950080ca8841c0b403401c0550320400200d00b804003d40507030482560012599a005d10380e40600c080000781c01407910a0888c18594420310600d032140e03c0032140b000c04103080c002c2c1102c072500c1d8896201c041c1542000521501074000701d410b4454400031903002a4a40044448040c824102c4070400000f030041c0a44c2c4000707080407090341d80c124110b02e050030181d95550012651441c05c500000090400010701005050341900814410011600c041c40161038030b0740c51310200c47c050310000c0e1290303ca0300344c0000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 293561429 1250 293560179 293560207
    0x4021603080c0c120406200a0209060d0203070803090405070f020a0f08072109060906050418090804031a281a04060602010902100512010b03130b070c0302010b0f06 72
    0x90841c440b00181802c12101044580c9000c83c940b44005a002e0046010400c05504c0006031300c56402100084140c180d00350085540ca080707184001384140d0840c80001c01d6512242081100e06400034229030b9800c5d030350700c403003616a070103880c01d54000ca003441c0004a08030302620352400051810741c0100800d4000d42c42c1e00704a00c208550480344600c040000b2004601e09200109180c140f094402002031640300700a4440107480d031120007400340b059810481160024141e9003100d85407a640300c0800007200c801002011040c00007072800101003804824880d020100381441551000e030318200340c45007440390705070400c103002c0c400b007030344045d00d04041c0b0281c1c40d048600d0610703c80403c1d800e03102000c0000b0b401d58486401140050b1354450041d401d5142002c0f100a0032507030381c10071030b1070803124010b5070140c40d0301405035101c140710003c045040d450306807000d60070054004031040401d0030a10070042248030440ca00f9001582021011a014900f082c00c62203011f034010906403910b455420505 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 293562679 1250 293561429 293561431
    0x20c030f18060403110901080d021203061206130606050d0c060507151a0307090b0d0311070906060512060306090606041d0601060f110d0509010c050a0c090f0b0402160308 75
    0x456088084104015502c42c5000740c00076500c6403c090b80c1003621101402130300141603003c0b40c215404410b80c21708081c0c01040b025040741d202d00da6265250b8481c004901c000b440140f854103170344544403c21150b074081c0113178856980e00c03a480500c07071540d451041080702c050360200a80b50726042e03e0200040e501440007802031605c41d0803800801c0e0791007400b00c0111760030310308038503010306468004241ca440c05008072800f8000c40b2504000400006c6d020421110705158001c2c107100420a2000c03080030100040c100501c2e0b190800d01801341c568100509580080030356007150010240402c241e443c0c041111440b03050050010500b550350802048060000301810354180c8502c82c0b01c00b078040405003e164041d208076100d03030103013815012000b030041804200d12621600500c031307034040107a80903003101c901000c00d02e04103d0b45807044c24050b0403d41400720040c646d03071602c080000d17960381607007005041d900f100404018113078013142440241d22403d5400030315040700792640c00000f40101c0030b075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 293563929 1250 293562679 293562697
    0x92c010308041e06050d0c0e100e0f0405251112070303060e28020c0f1e0d08010501030c03141302030706090b0f070c1710151211030c130e060a020c030f 67
    0x750b191405050209001c40c5042e0031050002b2075134080080d50f4100a0b02700036106034103840030402861b1080d08036410802d98040741480902200002c801140b081c64240030b40c46c216400c0d5001540031007101c4486130b110910460219040040c00598035410a5805100e8100c2d0016500c14540c0110100b0441ca00c2c54140c940c0e0740e50078807854540c10020000441007038207940080c06c1100200d030622142d004d140c400c203000c50b404445d02089407540b01003110b04403002801c6c04141020201c0d800d0303000d03000d0b00030034124844240b4100050030540703420086166000b40d05880f8001e03140c0008036040c507001e00454034090400c11941c0c90764400c400007003007618010075140e00d0b01c580315034500c0c4002c08038032820304695010b0304101e50095140c0c45410041d807260802e01840710b10740f540740345107040b004101601800c01804442c126450a200c422501e020041001032002c2c40303446a04010000303a030007074003540304040000f011a400f6108490b1102c0c6884000d6050000400510307030170398000c90748 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 293565179 1250 293563929 293563937
    0x17040b0d050421050306040b0a1203140d0c050715060609030f0f02030312040b010e070c120c050f0f150405070e0703090c09020d0b090403092c010308041e06050d0c 72
    0xb40300b07500103c4280c1d000c03200c0c80b203550313690381c03030030800c04020035508800c003040c0c407602410004201340200061482030003681418044005410007141c1900c0d400b4000207090414184003049030850303484401014072070320821010142d102808031000491b440c0740543c0b0b020403804401071001c01d03c0704281c0c00361a0311400101111146aa010900f1034203c20b1160300014a50018801000681510f180c050030180d94038001c6481c0099005001903c48000540101ca019a0442013a4410015021400e030004203c40309108500106561502464200840b501800301c02140c1d2032805005240119000001070186504015003018120000360144040c10f503075520481c00a00712011140c020200d030200162a0702e0810362030030683d500c90b00c000d8803841e02d00c41088002078010b80c0352400e5038802d80400c10b601c0701c400c854409030401c034071030410300e40c486400010410003004010320944a4000b1600d10f01d444081c1c10380c4c0c0c2c2006a0007207001144050049010310140d0f940522000081898 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 293566429 1250 293565179 293565203
    0x909060f0711010204031b06020727020f0702030616090e0c19170103060614010e090f06030a021201020414100807031a0607030801060e0d080f030403020a02091317040b0d0504 77
    0xc0c0d209800c9101808425148040b4001001540c0d01400b2b00b900070304411910b01114400031400d02a05907445c40300034049a030100e100b032040c0701c412080d034901d158090100e072042d04050101044201030544000c00181c01d00c00041402260011468051f0754040d001c182000c40880244002e903804070041c81c2040850b00d11400c2001203900c0c981e00840c02040300040396400c000c0d000349406135109440f810f0100c9040003c1681d1114200d1f940d1261001907a500180c58002c0028107041a131103010b035000c00080e10380d182c0d1402c10350003001240e0b12402014454060b200c248010717460740b20042c1000c40c3c5a0000a15500e020360407140d5000b40302c1500c1080680f0140c00265990455401035000a060b60014400c49801000c0380d26a848212624900031085640d542c1070340c42050b0b0700d00e038580808008101054020003500300020b90081a00c40d5624011001d00d8900b01505000c3d42c0c0026a141401c2090380381c00c0484042d01c000c455881d01c0c00040700c0314040039080c0a072045600c0e6602007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 293567679 1250 293566429 293566433
    0x31d1206040f030c1b0812030705161704030c0503160302030d050a02010603020a0308031801110d0e0309040203090a030e040504080405040e070b0a020f01051509070c06020f180909060f071101020403 87
    0x5544200344a5005c0040400500f4964018a8131035080714054002004005101132240c206098032140400482c28480c903e1840c9440894800403210ba642c00000114021040003004140d030425030301c050341210150250028000c1a00b82541b00182d0160000401c0c005000d20440040044500700d0001091181c2e41354049010540b244d40184c907600004000e1101c0c00300b150f044183c11a0108c8001d01c20041000c581e0455803048400540450303507107a402d60000702e13042c000e4030402c01e0001c008544030302c0e11030250358594000144c110001a120b0940c0382c07541c5024400c140c003550b04140c41d68200f50030300003400010485030b4641000b900c540b82002901050b018000e00d90359482d980a0328684842c5e902c51829124094150610003a102134585581d0b1100c02480d81d20003010310f0081d20860707807820001d0007407250350100c120b41321000441800a0081000e2907218000588902c5810707901c505140741c640c03000f40d42000c05e50f80c20501045640f03219051198504000b44001458181c0c2c039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 293568929 1250 293567679 293567693
    0x8070b0106050304060506010c0803180c060c010905191a06030f0d020c3c010908030d02031b03090c01081e0f01050333040f0609031d1206040f030c 65
    0xd902203000110b00108100412420740181a0000ca0030300340f103020307000c6581e645143c2d404001c003050b141d0701e07540800718a11101000301000050300505500d5031402d281200a0103060500307401c0d00c0c1071107080c69910200c825131500c4c10019401100e400740c0032080d1800c0110314103000c1c2c0202d9043c0b00e40c880d28002583d061220180c02100d079001003071401c11210502c410b00f043e001c1c02800c2222012240041c1e4001e500c0d607030948007541a43c0d401c002d5601030050f10107c00c150009034440c80041496440034800d5401140681001652a0200014051007000c540300441d0032000700d4100d02030300315413540103001c00b60700581c0c80c500800d0543c0e07500841c1e2100340b408490715110352801c0b8004201c50304051000720341480c0301960310940420314a0602100c0c3c0c82d900c030104000c0340040009400e200d411002d0701900c56119509020505981c00d00a040b030122140da4000b00c0503820011074280307085002131404660030310152065580e0b0781c03500007558040120540502c00380c020041c0018040e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 293570179 1250 293568929 293568931
    0x209060d0f0f06080c130528061a0f0a030504060b0d0c030b0a050c041203021507020312010b0405010e0409080c0d08220f080d1104080c03151605030408070b 69
    0x100078000340340681ca880d200107403409a03010904903001002d40440c581c50329103584102160300d603800316403900c403081c030302070040c0703401081420b0b03452100308888550000d07400c08000c41b8071055442c4c2072600c1c2030440040c0c5200750301c1040308941c0300f0030914076094001d0b00500e610501508000602d0b000d2500892428004182d04954480c440c01080c030402c00758903509500440710600c20811464800d10b43d624911503030054000c3c5464440b101c0d42054420410481000743e03d4001c0c650354100850065a81d0b049529000170000c2c0000002c1442000101030f2811035005035662803d01c20850280802800c0f4400141c03000c800030415819500001c00c084e82d100b4015542c1e4044078070b4070701c0e0405c158041c826501820318201c166004c0104d045071050204450300506825600d4a01c81549070007040c42e800244c103150f2000c0b03030004068401003101c4940e240242c0c10b81e000d094099040c0440e02d04115460000c200785203450311041c622a6028580c81441111b4181c545071190715021200d241c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 293571429 1250 293570179 293570201
    0xe0405010e120c07091503080d1e050412020a0c06110c1e031605030604061d0105010306150b0310061404030b010e04150504111c0b0c09190803030601030209060d 71
    0xb900048020181d5401c00c009801048041001c01c6240a000702104113071030b6601c000703402402d0100d81541c4c3c094480d80640956401103814584008111407a0342c003811b001c650580e103144594211421050000c0382e15084198030400141c086420000284d0346452110f1110b80184510205821503455401d04e400c40d200c0c0f0380340c0503116910064200b518005941140d40c003601035404080182d910001070094206a011001050070700079a032030400403103006080550b0725800d1000000520410742c3c400302450070a680c20490994840307045280a21094038a8001803c2c045000c10640d84598800c13403101560061070703460542d40742c603a6900e501e001e0300030000c0c401c011418801041000e090f60a62a9100481880720b850f15842c0e4240e030301c421111290040303083d0701c03031140441c0c01500300d181d100c4c0c1e03c00a81404d82c00c0016148400b90064520240504580340c2c492105800d41d609181c1141c081c03900543c0386503260740044001c4d4025100007900000c0074440500304950500074016941 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 293572679 1250 293571429 293571463
    0x12f010f0510060e040b0f1906030c030b010801140d080403080c010b010c02010e040b060f0703030605030f062221030219080606040302010e030f01020a110f0c0105040e0405010e 78
    0x112a00c0c05003101c0700502020051129403104000f05900805035021031340341202c1c00644400c02002151000d09090300744c5505c4244122042c6041d82d204000005603801982c01300152031501005a0840300c180780c040d4085402c0703000420240700390b130215039012203020300040c041e00e5080d079400b2907607005600112600c050100e1400c0c0c040409110390400406e0900e0100d00d500410780004c0c08060409040a009548820220142c2d031110401c40f108001c83e480c11a03919052070130001c004015074081c2c9813090141d40001c0b401c0802c001751140c010308041da204044800d12030304886d86a10080300c00c0b1040b1654141d4a911034046040030060704003203880240e03844409022008521052811103803d200081051141e142c0700c1d40165000e030395080c24408401031344400000c2c90405003114001096000141241103a94001640d51440700118102c2c2c100c012010710f001d840d03104004030303940042d400744020029448400381301382e0000d018400004094001d104514145030020402401c84 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 293573929 1250 293572679 293572691
    0x70b040b090d0e09010e090106080304080a0213020f19020f060126010504030219030c0813050a09022704021902060105010f08091921030501090e0607080402012f01 72
    0x149080c010b8401044291a1075103507511034000055821606010382c0300c92581c04400200045400d6002c138000d001c029044a480d10b5a034800c0d160340740600c8030304034040c0145015002c1d0040041c02619041e44840300c440b0f09180b40c021143d007035030101f054084114856401080c0c480742091050502030400140c0340710702d03100e44982160340844075060300e015a0785842c0400c03000c01c1e03001c240004540144a4404c85130400d50508841003c081103010b4280400022904003069142090f0006c580c001e884985030183e4680c0c00208902410380d0741c03410b001100044550140207090a8240d10000038001810300d407031078a01100900904036200c3c0941e00c03c0c03005001940e0440302d03441540d0424a081105483c0040040e920b49003280300070002000ca55904004010400511039680103440c0301e082d0041c1200742005001d0f1002b0b200d604440c9261114108584002040c2c4520950366902c86810300d40720340c1d00464224907151002c540c01c40003201c1441188000b44501d00c2c07848003240001c90a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 293575179 1250 293573929 293573941
    0x3120305010e0906040308060a03080d0209011b1707150c020d0e0303070203070510090e0c0910030e030a0c02152208010603020901061115010636030f08070b040b 71
    0x31100103820030400e108060742000070724400010710941c8164146444a5983c40d20700205030008601d8000400210002c40d04800011190340a000f14100c00d0b03071406810751062000d0003602c00b90010282420708840c50039440742c60713104014820184243ca40d941080e1941c40800100d0700510301074001a00000115080b0b158455101c0c141c00000b24051841c103d40d42d40000e5850344184a40b6020b0002044882050b0b401440080700401c0c84503640c3e14945000b5402d00f202e90301620520348039007001c10203141d8152091180c030047d145010f0082d40f4107104408195500e201c0c0c2c0e81c0407640b028000f00785490322100203001d0258030390f42c801c195040800004165586414035004038500c0d0b89000b40400159035040c04481c1152580c0c180100c0381c0280c0b51403281803031644144e140a604400740002910780e40800c0c01c185d6502001c2c182c04201c0030040021030b1035240c9802f6030351450b4100b0340a20219600781540030394944100003a03443d10440380d4032840180c40858041d1a803500400070840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 293576429 1250 293575179 293575181
    0xe0c09060603010f0315090c12030f090303080a02180a06030207170903060408300103020112060503060109020a0512102408041e050a05030408010609060311240301031203 75
    0xd00020111403003811503040c4900c15140180c41c0c80003a080e4080601c0d00c22100307189601101c0c80680045c0103e14040e15050141d00c0c9460f8000d0031400075060342603980c403483c816403010741a03a5060fa50042551150290500a504000401011280e040701402000c2e1f5403051102c008010507100980c48a00605010041e4900c0000380366680d9010414010295404031342160b205600c03041d450f4449020925800c0314000001c501c00804031946081c10304241c0d4008954101c034803d9840310424510258a9810748002d0b00c601e43d01030303001d44014096142c40d6000342a446d00c01380740c40c500b42440780b121340e0244d0300300392500c2015401e1000b041c0100c51124084240626880250503042100d20200800018009201a10980c504da2035020742000d030300074a044458100c0101d40d012501420801d803280d10a108031112580b80850008411300c4500030b00d002c803a04204500405034000c803e021000c881440d15241511018010a14280300c40c806540a9800340e032581034410000300005d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 293577679 1250 293576429 293576431
    0x1b0f0607030e1b060d1107050609100f090b181513020117010f120f02060a030e060a0e191b03060b1005040b07020d0309170105060405011e031709040e0c09 68
    0x40c00081d000055804140c80310012200100340d0172100161000c80200340c01354601403100002c15500404060082d2500d000a415000810980d400c001101e6601e468408072294444000c02c0d21841e200041c1c0d40d2220781804144848a45042d00c202480e150404020000100c0e0806500c2800c81044c400f036582c49000000c402840580c4400c8035410604148039110711445200d0040e441c8640d44400c02615105d00c0d0303070242d400b82c0680e49601100001034068484440d15a006208050020700b00c01d6040c012544405005c002810124040840190110940e40425190114190190307110410301781750450065000341c0c000902d1929000411440d5680801c4180c108107080c4400e010390440d0404542c3c40507070486000c130100c64180b030300f92100342c1d180d8849412040c001000c64072808041d0000c038400c0030100c500300850380e00c403008021419200c240308a643d440b00b12051000402e031041407142d400110f03455504005400f0005800e031121082c0c00d00143d002211034951500b45800c4403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 293578929 1250 293577679 293577703
    0x70f05090a061115040b0118021b0331120f050703081c060509160e0301060f030c0801200a0c022106130201050d0c050405090103060506090a020901051b0f0607030e 72
    0x181e00d13035003010740311001d000320180102e510b00701084280100d5180d0076030441d440e002e22810707a6510092001140c603142d400c60f0500350814006d94405016086000203002d0b0307000c1980bc40e003601941401400e02040b0b12402c4200c6500c0c84046140c0081801040100003d5102e001d2940d80c6400401d501c0f4904084d00050144807030404105000980d0ba0756843d5030b02c101409161501584c4100048482030b049402440d01546000f60104100301314200350310039607001d01078a1500e10392380c8598a00300c0c1c1c0c1007104403464161040390a5601c58003a0b00a10310001c20340707003094080000d03400060400710210805090205143d1440000780004e00000c3d92004101036003040d18002500041c20038840d00000d01845035960802521150151003582c0240038084d05a416543e10307423420200030300082d6107841c0b00e071104030005a40500c0e18021201000c1c4184d40301805c0c40504030110a100c1c2c0e41c1c3c1450507641c0102c0b040c0c01100201000054032030901b5030f6011031541618001241001106254 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 293580179 1250 293578929 293578963
    0xe09120307080606030c0d06080606040e0303190203090a2001030b0d03020d030c020f16060215040f0209040c0312030c0305010602030c0717031303080a080112020306070f05090a0611 80
    0x1009001c68200c82c40d03a612030019280160740f962074003000c010380d20038014240315141ca0058045107845001401c00c0c0b041c88143c4003042000c009144465603030008890707044181c810612051103082040c0c0280d07400c61128801c0383d49486440c0e0341d8900c41c207084c607009100d1249404030052550ba044c012013642881c2a614071156003001e0320003e40300c1c101e000d0f030002456210f064081019200700040b00c8002c40b02410340d00d8030401c007016508885690f124000040c41840119881003146500d0395006e43ea2190071014208010350900c900144000c1c802c0e61100140c030000030104a0070042c0c03000c050a1903500182c003080d10000641280c0f4103800001c00c66000740800202d041000500310140d44a001c1807020000b80480d15030b165200c0c0e4207880c42441c0464200000700000758000d070507121100e8503000302e40e0382c0354060311010004001000c2d40c1580300001040b5910b00890300300000d0102441e0441c0342c030201c4004103e204285074000d5000824801d400041c1c0102400500d543c0380640369 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 293581429 1250 293580179 293580181
    0x90a1a04021f11070602060f0109060506180310020307111b0f04180804060f090902160b0a06030803130501050603010b010e011d22200406030c09050402040e091203 72
    0x41411010214000031002100c100c15035203143c00f8454050303400c00c42d04119440c5680b6821300948400042d91400030a07400302c000410000f2b0180218070590344040c05007401e003a03c1094404c000c020303c10030b4a4041c060480c003040205080d0009502c5509182c482e0601014025082c51400c181103809000032005d00505001c4d42e0342d890100140c001c41150040343c040039000b520410225604002808014002800141c05821481500800c1c225868507181c03560744c4d050790400d9200395211f095000e8215114080003451050200307400c801a40c00010b03049841c0d55803010598801c0e1287c00260300000c0001041041c00d000302a0700001c250003c1c848050b81e60000380c00000040819418000d030321961201e0240c3c00c841e00602804d008110f406d00f20060070402d0b500411040301009001d0030b00b0161860f4440242158100400c04180d071741ca40752900c1801c40040c1300003192481048110701d8005165136442c0060009090800c6480b03403103041200703d0030700e0b01c09480301e03030108100e00380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 293582679 1250 293581429 293581433
    0x14030c010c0507360e100903080105100318050304090c020304031a06011b03050904050c2b0b0402040b041d090601180b040207050d0e060f09040c0c050303090a1a04 72
    0x1c10b05000b12032480f40070a6188020860840c1c0b50b540820303841c1e06034031300d4802e0038070b980f90140c01c04a40d60144c8402c0e115080300318942e680c10f4400010000e800304003403c00402207400c06a02e8200e039a11503250000348106640c20241100c2d06483e020b50703a0780d00108082c0075441051241c01d4049107140000d514003455030b558081048600c0c0008551844043c00040590340244d40311001d420b50900c3c1d051448085250180068111142d802d004928240000c1c203004901000c94000f070051010003042205181d6030b6295008602800030005600c81c0e821a29648443c006000640b119074061515141080040d40c0d1824070031101791032140d06142807011031080171500358196642001c00c294011412404a0068914401d071690841d10004844041c01000304d001210200c4079602c003010750a500040006a005020108000d12010000f02446107490342c4521100b10003030408074104080d0b611414159082160040b6864200b424610104810091241d841032041d07007060040341403036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 293583929 1250 293582679 293582683
    0x90807060201270c05060a05040317030f060f15070503030405010e01050606070f0809150309010b0306090c0103090c080106030b090d03061d040f02040606020703061b0f12110414030c010c05 83
    0x4002c10700782100301290f18003d02004030901c0c0f020b4200070340580c1c0e40ba144c3d01401807a0303920601c02510b000000c0540c0d000c1c409420803c0b0790180c1400f0300c00036030980341c4d8020480c102440d80710150b81302c1c0c26101a00008440440a0f041040c0950007943d104c9c82d240c05c0250a42c4c02c1d003203210382941d141c4810000c10b507481d50250b462103030b0020f11900300b40f02c0c07070b00d4500c01a110f403000c456401001c1c00301009000c1d09420081d44200c850100a1040d803100005040d511502030b40d80f40302c160001b020618141d41320358801e0b0340300c42c09100c28440040d9a50803403400c40c1c809070015100e6005800800c20030712020401c000ea11003c1d49010050a890500b81844070701e0a220b0071903040030083c0c0030400744000701c1c59015419800070300821440c1e07174030748000e51b440349588001c4a24900380038648180071100300146588028030b8071142c01c03082001800f01c4145500c4042c1c41855540c50744440c1d080806d410150018141d1520f040d000700081f1400c06240409515072141008090a038001c002440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 293585179 1250 293583929 293583971
    0x901151502210307110708010219110c01140a05040b0d0207050d02030301030c14011e050306041508120f190215160f0e040608060405010c080f0705090108100503010507090807060201 80
    0xb46030100d502c0d11052002070031b1002e5036000c9440e560022846003e000d4030880205864460364584654403800d0114440c3c44060051032240031800310080803001490403001011070802d14500380303240507254081c0703040036040081c120300b1007a400b00e02c1604211003000000404c8000d400114110361441da0340044441c07182c02140e034006038615800902d640a41074001c1001c0002c8008c4400d01c003052001001d540089503030900c540d00f07100e544410700540700c01802c103444981c8090500810302c0704001000340e0000e40404c0091b503003085107103840d002148007002042c0113503024104000c91040000510f801c060000100c1512407083c03d11050b4214074002001030181c104046081d41c082c0010300140740070340c800c1c10340d0300410041008000066102002c0041d1075141c01400392207480360500045070031204070011034800c0180e004c1a40c094001d10794031007040804240351a071204082401d64000765041c00210f4680302d010b015000d400d01408010f0101ca1000b000880c4e402c800a90360030710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 293586429 1250 293585179 293585191
    0x4230309010509010c0503070609120f170c04120b090111030601050d0b01180308030f100302010f080406090816111e09042316140f010809011515022103 67
    0x100040f00c071200d0b4040e50309010025041402d507038445401c0c3c200703034000c1e214001003213501c4906400c1c1600101d0040b03242415540d045c0e5a80f10705c4071103030000c0d0a04c444015144100741d0605100000703481d04161400900c0c1031150064403401c0c10201c9429082d2aa00701d006940b0400031b1007005141d0760b2100c240c1b1241050702d01c02040d16401c40740160760b0528501c01040e008145a240403041c1b02682004500501811030750791010b40c1e42501400c82002d080c0030003800201034a05054a9500c1040c4468005019000c0029035014a0361941350b07541c000307081041c8880c0c00300313105030900440360070700142184199418092030700c92443c0f070084074040c3d4611a10400002e0080741c01c0c018010f60090304489800c0b11100c2843c000650182c0c2e481071140542e06200741c404002c500c02c42800d086214121020744800846603c0c03034019254104000c0903074140e5035a40544120030340322032950703400805c0c60500b444000e03107061328001c0c20402e80d80c249440482d184011b007034400d03004a0480780d10078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 293587679 1250 293586429 293586437
    0x1140411090703060305120403050c03030c1c090b070309050f0a080c130b04060e06151309020c0f120405040e031207050906190206191503060f021c02030423030901 72
    0x5070300c0b02800d07070040c032203600042c00c0ba204190031a003c2c240e040b002002924002d5045400d606928410165284901410070103140c01043c3c0b00007a00c80042c1d2700903104002c034240f140e0303115214017a0b020660401c0d8410b80c005500305204110a05124004902c0100107862201d0304600702030081c1d548901071006140143d050071200400c015040d44000503d81000303009000e01c80d84c0c0d080800c0194415141184030704140d58243c54402c3e000e0f0122122054600081a0000d1401000c0303802504103400f86201d50142c9684008c0014040c410201020308491580703032a6400c00051004949408181500c2d6504c10000010319202c880400c0364031581c503107032040d6503001d25004981d26024a2030928551320070b90712110106500420034511405007002400410b018107843c0509403945440d00300100e140300c0d0310620104907590080040080300d150054500601c0d5000910300e0002e009404410076408010300c420410030740b0041d0000e509101d00f454000c45200b900c00d07201c0c42040380320323030502c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 293588929 1250 293587679 293587681
    0x7230d110709020705071401050a020c09040311150f07210f110a020106060806010c030f1101060810020c2407030506190801150806100e0405011b0207080114041109 72
    0x11541040001c1c060410144250f440d0704071032520555071900d41c0500010b40310b00c2c80b103081ca43c1d4440c005a6054900b0b690041180700381842c1801002c85006d0001d80400603400400140d02000300031801c540c04205460789910311348284801a80031000d0465001c120405544404c4200540002c00409520400018030036031410445401040c10b000324100307100c000700b10024500e0301035110004072202501c41c1001ba540710001140c2c164440f40c4000c0c0070455101042c4c3c1503034401d0b620504642400400080c90f503844801c590301e003a0400b185a91515000115851605800e002120803001c520311140101d5030400c4402d8400240141803400305075455000456035030340c146590191150303804000d03101603280d0075820b001c2d20a4000a1030145115880015103010004050b48501184d1040603491800c200321080c810340c000d0001c0c0c803d5034072200c840880d682a141581e0129403941c00401141707217001011803d54000507450506041c0320801c002c04144205d0050680300011117400080e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 293590179 1250 293588929 293588957
    0xf220203060607060606170a0902210a060204090e2b08040f060204031515060f0f2c011214041e1505100b07050309040921030207230d 59
    0xa9026100d406131259007001d50004a00d50041c4400c078800c0038100714000c1564a142c070100540d400c0c690000e4008560789103c84044050107500003500c02842c09540f440c101301e4540405903041034010070403950381e03054900000081049044440a0490b0000306c103840c8003481d03403880c4401742c00c01e28148824140000e042042c0006140e0441d80d102c041151902d0b2641010705141460b44412044189062111200e4044d03e600320000c40781142d40c0d00c11405a44038049400c44070010802c400e1108810300c2030308681d20301001620b81d07050394048910780e1021000040102d89000c002020301071600c0d03030303120117100f84101d01c0d0ba0281e08048a18010700701d80c0d0800300d004a4118018221802c1c0244000c004d2105d0b4010a0049141c80c0e200c406032515a481d0491030310421000900650080101019500f4103812040b03c190240b00406074040844841e20110b5014801100c00241d00041400402c6280117443c0c0b8001040c10052510207500c04102d6a602c00103c1914280040d01c068091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 293591429 1250 293590179 293590189
    0x5040f150909050a0c080d080108030c071a0408120910080702120901050d0e0703030e06090a090e030c06010b030402010201140402330c0f010e010c05040b03060105120c03060f22020306 81
    0x950a9004d00c5400c85e0317130b907a21070450301e9101000302c0314000f510305d07400015038010000580b6500c0b00704601405600d850320941c52001e00050018542130b1006000020b540b00c0300380011081038050348041a5103480190070408000740d0701c0341c02400d212076034045c0a0782c940d0020350752400c01e4120850b00e84da0382c80b05006071042d0050440040001c0e042070f0303078001081004203038081107920070340381c4205509010040009130300070642c0154108030000010026440c50707030080f000045d400401c1d24500003020340d400d42400000d17040000000c0002060004550b070921403401d034600c2e00056020b0a0426500040440210700006400f9207648e42005940740300b03240300c603051404c04005080e43e98101c0052642c031340ea86510070342003652030200703001d003c000c0600900d4403c00c1603a8480346018100042100107030000340540f0304114040c0689890310030fa0018150003001c04841c000d40380d290010803c11503800c40d5503818010b02c14111110000c1442c803403800030307612103502c025840740c2d00d00b40854 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 293592679 1250 293591429 293591443
    0x80622060204060c1103010e0309010810030203150f0c04120803091005010f0e09071203110a02060307050304050f0d1b060b0d0305030702060106180504020c031e0405040f15090905 79
    0x24010601c00600003810303d41041054100510134900c555008410000700360890b540c620100500f6041003017007000c3c070741c41621580e0b0b1107810244001b20300394882e0003182c03900550100700303078000601d80305000003080340c0480715901294107080c0382e01d094103240b0b50020b40c1440000c0103007250303800b00101d24410024803c0c6490713605130080030002d43da510070090141c51654480c1c2c40300f00c40800080b40d007030003007c02c80c1030a9520742219240e001e15155011148040034128120807402230025a00c01030350348000460003000c2c50342d210b6460f4205410000c0c20000715050114141d4009004903402c250458010809105030414905070898513040c90350203494901c220560100f40e03002079101305500607014500171496a0708580c3e00303a80300d60f025504007440726020134501ea10120204190302d00b41e0010010003070b0741810340f810481801203050070500c1c0028a407545150214051255042500c18030740c03400400403090010181d04a81800154524013540c081103450300c00034028024104071003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 293593929 1250 293592679 293592683
    0x90f092a220e01150f12110607201003020408190218090109020f030a020a030b090a0b160e03120702060310170a0203010f061a03090312190c090501051c1d010906060609080622 77
    0x203c0c20450301103070000d6002b180d844200e1052a5003203110003070a01ca031007601c00340c1d1a13600c02829500c14891284000c0648110100d90141c850840500e0315440301d505107018800000001c222121a0303c1002180307040605800c0c0a9030008000c48096a1341c1583d0504694004401001d84c3d141d18500e01e0034402c2030b48002e002d502d0f9400a0090b8040a41d1244680344416514612a140d21104040d25600b1754851400440003d1124402600c0d0a00c000c0da006001c10324078002c91503131002c0c040c0e00f00011130f520f070800342c214905841c00c2d828280120100b1340c4441c0703403c1150904014240100003203000703c8000000b4007000040c003000c0700700100c80d41c15603540000f00007403601c2d050102081015007040d440075030030200e5005140b030040e008042503030816114a400c1840e104682004c03244902c111442c03458903894100c401040c1c03000c955040d03440200021551601e181071044c01e0b54001da002d00200847c0d1101002035250102e2180e801065078002440201050742c1400c40080d01d144d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 293595179 1250 293593929 293593943
    0x1009150903020c030102040308120108060f0f06060909010816170a03110106091503150b10050315120a05060f070c03050d0209090f092a220e01150f12110607 69
    0x1c4127004090b4003411001ca010340500d10b071750f83c0303070002c0c01c2c0c13a008190784c0000700070368417400b15040017100300c0c41543c0088003078882802c02d140130001032800b0100707034800c594940002c080750401203020f254203409040f007508008401c0c94030300030700d80d50380340d80c100d0180c10402c00610381d941c110404e410510050003442424010001d031141c0c2c80c2c1c1140c0092001325130f8030b1401e600b03801d11034485016190300840002d00e420b1707049409034800c0d076190344000c0c061440c41c200c030a00e8811594500c10148071062551009011f031000e07a24040f840d00e03002920b040c0c2e85548480030000703820b600c1f41032500c40e282d1525081c0d8170350640ca4111000f03801810b1301e0540c042071120800601d0355404140078400c4d6800350841d089124003180b01c0310341c5042800b080c1d0068500c039440d40140d00340f100315080c07400c1e4a0b072000340214422058175800c848910000d045141d45440c0000c01c1080c01030f041501802040c00903040c010714160740d881944d10342800003024100d12441c0c1d0b00d15680c405050701c03940361f00011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 293596429 1250 293595179 293595187
    0xc0a080a020105090f0105010509150607020301050f0a0b0a0b091203040b0c1f05060f040203070e040f090314040e070f030e03121b13030215070210030b031009150903020c030102 78
    0x10b030182600b15414019841400c6112400e10014060541205d034050b01b65003007900e0b40f12003452000300616016411120420800300141c409111f100d1040c0200030742c080321404c0068400307058581050300c075071081281c01014070480b070042c1c0458003501001c60742c8a8500840384510781c11030190782d021180c2010b010801581424020030508220801d012807804408801c11048049440643d4010341002c02c0f12a81c407045d0601c0c3c1d005540009407420034080c0c0c82000400141940c0c0444c00f0081c4058841405108054121030107a140070f14407800e140c1010708011300c11209520080c50300081208210700495881c3c0654008040a4404010707071f50780e5600d01222003120f00098510050000b03400f58003085400c61070081c1e41800e1040f01031140d10300c0c0303142c0030403440c41141031400041070800c00c2800c0059494261b4170b615401c481d04e0100e00081c14104060038644d404c04501211803c10384101d00190542e01035401c031b2800707804000f486100342d0030224602a03100700c14540543c8001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 293597679 1250 293596429 293596447
    0x71a0403020103053105160b09040e0c060f030a060b0d05040506070315060509030106092a020a030f180902030705120604091208040f0803010609090c0f090b0c0a08 72
    0x4020400d50703000381c03030500284d01c8420050740980c00200c404c039202002d43c1d80d03841130704402c400a600071501580840302c1c2122078000c3c61990118a511090100d0000076200c00142414000c0350710600c4c901c0003401d16110100080307680351152061981100b00008006048081698019400740c076111651507280d26408440da0020007044d00d040c2d585100324000520340521a0040c181c5c0c4008007034201200915207001a00c403604000390a80c0e15548880021903044818030801056450002c0c03102d400003d14410798070420381100071001103410106165011035089901004060540d160280021021048110130a580c03600403004c41d80c0000248030401d82d0000240200d0316124150442c240c403074104000071582100e0300100000e0f0b1103295081c5903801000180e0344140500a40024129203554842d585c0d4801d8100c0404240010010b00c5200514820240303584186e04040080c0204200f0180c103401061080740118039000502c4440e40c00f050103c10441c07a0300c08801d5480700004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 293598929 1250 293597679 293597729
    0xf1e06020309010f060324020405030105090109021005030601170c07051c09060c0203120a120f1a0402091e040f0501030b04030f0503070e04020f070b04050601030323030604090507 79
    0x1903902e0002e560030800302c2d0809000920a0104581d804890104600040c8a0a01c00c1c002482e50f40e1260300c0e400c0c040002d0703e407008e0186a12501a00000141d01407031841000940005c030701c0c40e00200601031080109a0741c1001c183c50015011850741742e619a02d81d400b840440c85079000003081400795803c1c41400008081c9841302806240d1034010750703280c4801c01200c403900c000f50080d6065003c0c1c80a03014011201008016460079464082100d90307040d4040403d03500c1c144040481c00e9902c1c1c00701d5000c00f8210400010382c2c4000c4a0662421354401c0c0042e403078040034805002030a00215045000340d407268400400c03c510590240300a41e568144a6078a8804542c10360100c0e00760f001440c00320b0711a00469201c2c000b16141d4810880e008400c0c840290800138001e0b88500b400c2109401003901c82864038411071160006050960452034010003100140e161218036081180c1d800d41c0a106240540f07a200900351400110980e05090007442c14460303034004011074580d41040700602100b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 293600179 1250 293598929 293598931
    0x15030c031506040b0a03290d200a08100b10020309300307060606030203040804120f200a0b04060c0803100f0e0a0c08010f0312020f071205010b0402040501020601030f1e060203 77
    0x1f443c0d11040c1c0d80c0b40420781c03485044407509550000304240d03000c0001d10307944020180a080c1440c05048892110003058031460345400c20021075202090440c5c62580d280503e04a0300381c240c0d202d61030080800b5020350b80e4000c03484058401d00030b03998000d007002178013960094464608103c240342c0251003c0b1040d01d90340824416621a0304102000c10030301d000c2d0003141e00950341f1615051901b40b420f01c4401c2001850003044404103c245183d0000c1107a0000440a01c2a41070440d118840b11108001208050342c1c0010b600c0e000030700080150942104280303481640100705140c0e0703941c5d0701c20b502440040c2600500400c10910402161244140c44614030482060204100c044502182911103103c01d00c0fa40c001c00711402e0060001525a80303503e019000903004442000010780155130914104e034002e6251004000d4000061182c00d001c0c6141d40d200c1a1400c40c82c044c20700c40001e407100d80501014241404d000c800c1c1082000c0d0311842220401121a030584a001502d00305002c1c0d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 293601429 1250 293600179 293600201
    0x211a040506090609010b0d09050a0c0620071e031209030233071a01061809091208070507080c010b0f030606010e0405061314040215030c031506040b0a03 67
    0x11a110004807641080e01819000320340040120425071b01c1c18507050000d0384029445c0c3c030f106498041003000981c080183e150328500c5844504103080c01c10714020701c12280c800c51031400400b01000032044401c01320f130610941d03000e04070b07111100c42075103280b00d910000366100915002c1110100b60b510b42d4891100c0342524421200310000e10b4020328500a03421980c15021808061802c1010512b018800207103240c80c4101010f00400303a0080c0a0524044242e100b080030036140c1445000794401c3c45c0c28030000e4242144104031350141525148003804a1080175803e000d8a5404500c10b54011010389000c0b580c0071f850641c0d130b074207100c402178040d00c00401081e003d4a800400d02e9072501d400704645202b24010394a05d00c41544030820840a0603002d410550802a040980c0a00c81c0c442d0050034542e1440840102c1c0b10f04080c4144008102e420390064844c001c14028018540d0402040b690000c1038001c1c440000d0a16070005803840c862076002c42c0030040e0000b0000702e07681e010b401001200ca = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 293602679 1250 293601429 293601431
    0x60d06170607171e040b010302012c0f0609060c01021207090b0d091103070e1504050f010303180b0d05060102120f070303020c010b0907020a0507050d0c06211a04 71
    0x50140312141e50302030980e588004900b0303e07007541c0001514030024036801942d001c1c0a100b921215400644901001d550507a02000c400c00180305550b0020344803d03500c02d401c0c8880402680321190b0f40600102416164800c0880003440c000c203a0302c24040e15040c030350040c0340594880020a0980c001d510165110800f03880101c005108540030389002d03011180855509490102c0b0b15a810f801000084da00301c40e80d01d0343c8444000342c0e4070100304610180026100005150a10030785400311034003003080c0307548141d0a1104004c80403003d9600030341180c3d8581010344540c59404c811039590316030f0303401044445502040c640c11000c865000030b4001c000c02e80940b80030491045200c5030a109071035002411503070412107000020311135801800d40d55040c500025001d070032100042d80008055450780f0060b4041f0030090140081803140c0002000300b00c48400700040036a441d04441c00d078600c20a01400b00e0403030890984c24644214110003241c8030030810400c074441d080100c600e0408481c1c02d01407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 293603929 1250 293602679 293602709
    0xc081617070507050a1805090f0d0509090f091929070807090f150c08040803090112091104020c100c0908010f0b030a080a09030803010e150d0b0403110c060d06 70
    0x541404e2114001b56101103081509000d4503d10f1800603141c0548040614401c0c030061142d02d18040c000d03090b41c41141d90303486030b0b0340c400e04040150914002c0c0130040303018120414040301c1c0c2c0000544002c05c0b45110501483c00301039040070760f581c41d100c00e003901c800c0d49070a03e031407002903140814500c103500301d465501c0591910241251032060034040c500c070790030040c1418840b00c5047c8290408428141c80c1880c072240c030700d036940304007901300381e002c4030082c0c1c00860301003d590380150f541018610800350400642c4516151704003070500302e03489280601d500140080d4580c0040c001c0624964000c041401400702c040c3d4002c0c0040003d10403a0007a51070265450045407a6016043e50440020020100b040720342d00e5280c21a8440d84548040c81442c42c0300000040104010314001e04503603103074103281e00d003600c0f012100100441d04a445908044004000540603001c0140c11a4051401c02c404181d4000340510b002c2c8410f007810750110f00861074029003885034000c0d6003a104010914201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 293605179 1250 293603929 293603939
    0x40507020303090a03031a120105073902010c06090b0403030b030106080a1103070e07030204031a09151914090f01150e0c0d0f0c08090c010c081617070507 68
    0x403404103849841d00c51300010901400300b44070745c0181e60994444400341ca0400340d96030024400c61010144640d2594440c01080380c401d400050007007104001600b03e21050806a91660100c0140707504a12034400780541172041da480340c1c010b5805940d00000070048250203080219498034215421800241000d003140040c1c1418083e510071242140000c201503d1141e542070644082109110380511a6440c0020700001058415000d1901c9440050340c83d0300b5400c180c6c900034501c85201200004040a01181d035000060540d0400b900006842040d25010200e0b0f1140380001040c1c21002e081044001c20310001d105c406002c1c00b100411220342200c440c1e10130f8242c1f010000b0804e954400004100325041c0500c1c2075a40c0b094030180041d14201c4111a240121040c18684511032607072440211801500320164076002480b2100910600c85d10f00d0000b41000d4906100908041e404102c9041124003074150340c2c18154403580207015110000e520040c26081400300340c620340320304034000030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 293606429 1250 293605179 293605183
    0xb04063807020105160503030f0907090908030f040201020106030212030904050603070e0c18040513051005090709020919060c02100f0e010c290720030a080705040b0c03030604050702 80
    0x14000505104142400c80e42d400542e02c03500b184500c0400020380f2404c06000032018002507200b00f00d500485079540c100300500c94a000720b590002c106851520708a040070aa825068903030240803030b034101102c2d581c0e41c80102d02501c025030009400a155002c100e45014010000e048000e60a4908000c0e07551303400105595001a403050fa07034030404003004640004000e000420600e545c02d00c40c0e0a00d40142e02c003043c2104d03001c40360355002d1941400c1d1001044405c3c40217244802010200740203d0401100e840d41300c90580c4602c0d004284e000646649030780715201c24812292101d038224840f240d03a0349018011103400c0c10228840c202c140720607114280140e00d00005910035a40f941160344190b001910f00041c3c0703c0c0b00b940c0144101030303100126031100c00444912550201004c1c1c86080503e8040d0240d40286501010700c031900503018039a81d070000603942111c1c1540f40514a0380c480d003009460b584115000a007141000040880ea000c000200131400b80c9002da90410503550340043c102d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 293607679 1250 293606429 293606519
    0x180a0515150d090c080d05041505030421030e03041401090b0a02070b0714032209230414060711070e0103030503061e030a03020a050615150d0b0406 65
    0x100740e10020300c03030504503841660280d400148645012410240c403080304926140b02c035420440020400a418082c0402018102c901807040d4105582581401c0d5540200d41420b4980ea240710064200e141130814444d410107200043c10406880d6500d45940d51120344890f0280300c0c40c04100510070000f00c28139810121410340b0703a075034082c00c1442d0900350b024036180d100c0035090300d820140e00041820700c1414030040000703071000c071810035607103864a155800e402c40c81d41c00350758142d182c1403100401080d4410a5201c0c01000b00e031031600d41d81c03507262460450740000b15144143c8104000c1296440d02702c0b801140000310303501220f202541c5d4100060120304240402400141c0030300214540d8141744400702468aa00c1301ca5411845122010900d4040342078002d4005034000703204a0140081804201e4001c404950762021800b41c0d100071445403803442c1040b941100c0000b501c11412a083da20287d40118020014040c482c0e079018a110452a039011400001070744515010f0400c9400c0098 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 293608929 1250 293607679 293607709
    0x4050c101716140a020c1f090806100e06040f0612051006060c02040e0f03160b0a0c08070f0905030d0c0b0603160b0c01020915031902180906180a0515 66
    0x18080c4803c03040380b00038454004000c0c03c81507100e07040e82108a0f81d45c4600030b406502c02003069016041c0705c0c0500902015444e4020740c0d8580002083c40782c0c40c0340280c400425900140805211602c0b103201003001880c8102010811901d4440040f8007100303990552920180101c04440c4110904680b0b03504940d5244591000310300c4000c8414014107282d080500302034a041d040d11041b00032840300d00c3c21503004000750008041c40c0300000081100e142001604030603004020061340c03020101c00b616600000d803c48043c400f4140e48015513511401c1d9000107003030042d05459a10400c424044c10150620700100c403a004170740b0000e281d0381000140b1000003e55040d41800c3e852500d0b440703150646c042c084440c500d5400308485183c0d81c1f990400d150460242140a9030741e803070004a140554004000300c4140203004201000c0b0540241450001d01300d000c035840900e5858010000b030502c240f05860307122181c040307004c0142c940c07542d5010030700c1030700071a0800c43d1040c0402c0030421008000c6801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 293610179 1250 293608929 293608937
    0x50d140a02210d0e030d060608041203090503190206160807090302150c01020f0405030705010c081903020702040c02010f1109011e1808070617060d060504050c101716 73
    0x5284110702d01110806000380b5220309464141e8501d600c3c0180c90b0b1034048807000b0f078400110701c42c04207500d104500040c0780130716141e03c3c20304040d40e6454220b080d5603141c004068031144401e0600505108803140b15030a001e102804520f0f10401030346601d800c41c1c000d20300c21000ea149020581c003990550b44120241d80d202d190290540e400c00140b440380c034040d4416030809100b1481040000d200030b00700318410340708047d160b901c0d01e400c152405003660000340c1000034000da85000500c90006450311204000400340e25003007400d104500034040d0304000783d4440d0610700034200f1160194032502c00e0341003c510500070041c0d8002000d50a00c600d40d131590000d200b8104041c0310b0035250300c2241d80c0000c145801e524691090640c00d003065a150445540c0e90400101040102e400000c0340d410307100c611b01d5040c0c01d4600368000580b581e254102c06080030f43c03104005410070000b0320108001840007071900710341001d05680200803420828101d40a4415200071620720200309000c1144030049035a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 293611429 1250 293610179 293610193
    0x506040503060612031b16060306120809010e04090b0a150b0d050421080106080f160f091a0d0617032203170a0216080c0d0804030f050d140a02 63
    0x34010f01d01155814130185000c14800c07680140c6182c9121a090518000145840b20307100c0810041d00809901100505191010401c4800e102301403011103d600002990b4035225030f0380050310180703020042242d1191810141c10100003030b01d150a800340c40c04110420408a0007000b00d03c00060601441c0c0031003a09103d00051683c0c990000f80c0c3c080e00c00d5240304c2012091b04c090320f201d1800800c419002c0b030008401800115401100d00e503015110100b403103502d0070b146c014082040c21100130071040040c8001d03540e0106d400f800f9404000c010f17103040c1c44400300c0480d880301c0c8184c02080c0602400c90505800140e8101201c1141070001c48034400b6503c0d0400e44040000c40070b54000035400081c0c080c00d00000821003170140000c2d009403256080d59a00c03a4908024100641c00000d43c044103411201030164190004109a0b0304e942960f03207542d00b1009082000150060f0b0b0700c010009460304440c0d50800c000854006980712041d00d82181c80110102e0103815801076100440041c1d005d51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 293612679 1250 293611429 293611441
    0xc0305100b0f0c010f02070b0a1802090a0e0601030501060515030103170903100903030203010603110a081b0904111e12070525200d030509130204150903060501050604050306 76
    0x70052080351044096945001140d9a40f40d0950741c007070641d0480b0503408030f0901c0c01d002c0c0400c00141d008000410130094a0101c040320266600c00f100064041c442d11400071300000c060b9844103841007080c81c22101d5070f6940303280c5240a03010707501a060003580c07504c20a44282c00e00b1801d4a040e07a9210550194040a1321081481604002c5250340e00d4450440900003603c5d45101d00e0005c00c4c06503401690702c2d0b0400d01c029045d01c043d2282c21302c03400780400c014458258004046a00000f0701768020310203010741121800c05018800d0160351062401c581d11000c1c1d00c2c4d0744024002c0400410042c0700030300780c0e44103a44260084011052900e422180080c1c0c22074451001480b03401242d599016a140e1804240c0c40300c0c0e00000400c46402500700d0b010007035020000e41e04070b401801110b03143c134600a2541d000340540101c029560080102c000c140034501c1458055402030300280000d4540900d090030010900d1034203100036180c0925044c0046103030300701141120141c0380f015004001d161204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 293613929 1250 293612679 293612699
    0x80109300e101403071112030103050a110415120b0c0301151b0b010b120612030d09050a0f0c290403030f1110060503010e0c01080f0a02070c090e010c030510 69
    0x1c40e0001c1040f03061154040c001a4009075000781c2459513034019680380c0c4255541343c0040f0000b0107242c3c2105000400001c3d000080b5045010380c4403250203803400d0348402040142150412915032003c0d031a00109041d00200c40c0c0e0f04c109401048440703115154031090701c10a10080c02140c880c0401d008451880500401c940d5115144440e40c82a0702c1000b0b455482d000c18082e0411507000100040c2203110010096049421210488070250ba02c0c0c81c0d220080d0f80c030f22480d5003043e1219207560600e41804421702000b0201c6801268000c0710079154904000501c802d8020034101100c035112a4040341e9600c021204020314800c1c4141c58182141c4007034540e50009860b0104016441041103400841400002000d40d410301001c2800c5041808040c00d441c0c136403200d0b1816a0200c0d4125080360b030b0003e010b540080f42103581c01202d444104009010784174400015084500c0240c00003003903035050740074030103400e0785400810000f400034100300c0603180c0545281c40504101074040c40080340c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 293615179 1250 293613929 293613949
    0x40e0a03080907050901060905010f0e130c090902070507061b05030315040e0d110111070b0402010c020d0803070e0a1e050f03070512060f01050303071505040c080109300e 75
    0x1d82c04503030360f03959103400094000000340c0041c400074045183c200074035600710a4030b800c0390100c0d08110554030020004149484040c200401381c1d1074075412a00701e400d009064031030140c030400105550b1419a4184a541c0d8821803240c4030004c1d488014500903007049481000c20558040051071541d180c020b040030340130783c4040410b54002d44d44e07240c0319a030480c20440380d070076140f940d190046200c00c0900500d0071a80c0f91404100001d0041001c10000384561034800c0d800b0f43c1c2402d100520a2190010414507009003400401030080082401055500304420a50f4403030111510384405031110404155004050304543d079030342081c0418415441d06015445840034064101c510709565180010040040625669040d400c840c3c1030040c4a0701544800e405024154015454100e1646d5006d01103d017094000388043e070345801090803c01141c40c101d004010400090100c6402070a00905413900302d0700c100008514074200000450403d00180354001841e222260031500031001d010301840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 293616429 1250 293615179 293615191
    0x12120703060b0d050103031e090308160b04060e06070e06120601050f040303091406040806070815090a050901050a0c0e0d0c15080a060506070803060d0f061a0f040e0a0308 75
    0x1407204030200385000c1800260a40b01103d1802045952450401804812108903100881048440f0030710303040e50003101040031294400392041d640d0341d100024450030790032514020800c00407541404240103464114400450080c4191040c03629504015070792030412540003a000017040c00031200301104482516803181c018106113107002044d00125010750b000350070460100311198003d1120034601d411140c8403002c00d071040c40c942410002c00c540d4890008291500308144100000c1e0070b5560b1041c40c00c03410300080c248050341e040024225010b840112044d4000d58a8440099001c080d68020080c00c036001d510341d02507030401001402200d081e410000e0719034801854001a40d040701c40854500c00c0b08940d640f5a09007454905d64041c4c8000760f01091054009000035404036404c1c804032900004210740030a071680e41e500d8481d05000e401d000103454285811030381d4420080b106c268152000c01100c0c06540110140c040000720381c24103484d04555880039011b000001e00409000b030f0001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 293617679 1250 293616429 293616431
    0x702010c0813060f0c0903050f0708061603020d060b0315041103070327060b090c040305030301170f0d03060f0f03120e032817030f150d05240912120703 67
    0x560001804c0040e40c0b00111070000007650b100c4108203003c6d042c020300c0c01c01040b240184c03040900d00051513581d090003501c0f005079004c603460f43c03e000a0084c0c0c1100d0b2540201002402001da0b103503038030390540c0c1007202c84004c0580e0702e40ca108004e1502c1d00c41e071043e11f4407820180381951a0340a04400401003890400c0c0d8080b84d405030000702c1c8420160072512584516004510041c1620501810400103400031a0141051005000044002c030689040d50704031030604003100d440c0e44481f07181100c0d803444500341c2d004469400e1241585500110181da80d807030303003190b119651060040c3d001d071101d100143c5082d003407a9035014030314443c103203410300303040024112802e2402e9040b540c816540e54030040d03100301030400010810002d800e06046503915602c3c00e1113040d80380600c4044040c410040c51601480841c101c9140c1e10b94440031401d080c550482e0407121030083c81080400108003140320301d80149101000900e599200103a400200040c030707601075007042040c011101c503d00018000200385 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 293618929 1250 293617679 293617691
    0x31e09060702120a050f0613061a040c110f120304150608070b091305060d1b0b180a17030f07060216081b0c010e061804051305060702010c081306 64
    0x5a40d404080c3e00c200c4000d14003818020312689015403400c10007002c11803947d00a201041418081a10240c03002c0e6000b450120358090030003591140c001c44140c80303551103450043c1581c0300c00d0307000307003d815000e29080c2150234600b441d644080d40c64952002400e062241000001d0005000140500b12401a0b00380424002d4442500c541400c182c1d030004007460101250120f42807400d1546081c2e4504c00c154101318904000c404144c44005180000e8586000c103409a00d140070010300c942c005005040c2c0d19034540003e5800c000f507240e81d10380001d00c10741103658041008006848481010b0003104002c0d4a81b2403902d551004036008203009582c0282c0c00d0000c8141941440400d400461003080e480d075483c0c2415103c4865803c03c4852440d056204c5103061406076000324030719546850031660552142c40d503503003c8032640c0000d0005a007080c10481800342103458000110ba030303188a4419036250307035030b505000c0f404c80ba149410700001412031380204402902d14103950403461f019250106e65 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 293620179 1250 293618929 293618933
    0xd0e150f040b0c1501060503061507140615010207050306221104020f07150b06090409050f010908030402010207080c0a091d07180e03041206020a1107060306030c08031e090607 77
    0x580d00301152942803900031340150780d01003542180480c05009681441400c5013800c1c000304112a080300d1031003100a40c001800418858182c0340740700c0b142030540032903807540f07040c00b0b80d868122281903603140580310701d69000c50546004a0749030310440700031420f0700415440c04411003500b502080d09442420944003040c10f262114001000007804090707840c0d0742d604461405084000e81240340c0742000345056070b224500d41d41d0074121040503a01b01c80220381c1a0140c1042800c048220501582c25803070040b01c03204010002c400303188a81e000b44c09840032140e44d1001e039601c6840205030a6880f507403083e0103104001d090740c1b02007034503031100c01010800d0400360301e030518102d0035401c0240d580c2d841c0c00003001c0c0c591580c01526403034011980514142850a00c00b844011345514000780210340109880c85010b11510f07107001c48441000444410b6903072448060000c05060006076502800007101045c194030010446810011180e1032401081d008245400c445d04038029140d8000410001480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 293621429 1250 293620179 293620199
    0x904030f210212010501030c020604200603090705010e01052508070614010306181a0619090203060a0e070f140f041e060e010c06150909050607020d0e150f04 69
    0x52034500404006a41c1d6000320715009002d03e05902050406061080c4900c01c00d90100700950000d0f0701c20302450705200d61503000032500f000d9070f00090b0080c0000c0300300b0005400c0005e000c01140c000780c80e10940d841c08280115410712402d5008420442c4280801488403c1c04080c00e1181c5d0045c0200d50400f04282e81d0b031420b481c4c41c980000b240c050342d10010310034845944141440703000710003500d10382c8181540c1c80b140294034250411a4040301c84000802a45032001070344503074032104486c6201e064580d000781d0000d400aa6006014a00003080031030005100c50030580600c1158031750030407a0328285000c582560441440102110050000c0007000092001500241000c50910301800940c001c0800f40030215074090b8041044038884040107907040307512204101e4001c20b002c5003491542d158030046203050f40c81401100d00e84213800c4103015000c10320b64098503030307030742a075840045500e000c90b602021904410362188102140d02c01e015055801000a541e80d103105a0610f59180c000f10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 293622679 1250 293621429 293621477
    0x4020a031106250203060906100603050c04031a07030e01020405060f03060d0b0c0714010614060a090e27010603170c0109140610090c020c040b03100504080c1b0904030f 74
    0x300300f003008148801d04510303040c011103074032242d203800506007403910030024140d07946a07120300d60515960350003040c000d01c1410103c2d4051600205425000d1f4182003035211803040032141840002c1c90404807a1600c81e0600840d0304507003008212a0424110220105403548040e007990351040e80c000b5a500010409980c1d81d04c1030146881c0070352541240c0c1400e811100c040c01180c01c10340d00d000070901420000a078681c2c9182002d403002511482c400e8020b40e2400b05981000032406944400c0080f80291684c40803620703401813000158034007140220609840f003900009040c2c10840c0c2e0303501080c203805c0b005070a00d49448000031810031000d4440505450041600b04000d40208042102c10b000d0949031130010661501c04100720003202000030746134110001c030240301e19160700d4491071540e030801c481948030303103242010003040c186480c2070007580c0d00c41ca1191040d8040c0450542c4880007540342d4031105603014000ca0a80d07912a9400c41340c0b40c1000b001901031111003c61b040388607414684070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 293623929 1250 293622679 293622727
    0x220803010608071e02010c1805100f02100510091a09042a3008071211011d0c010c030e060903011b080604271202030c0d0e04110304020a031106 63
    0x20303040c4800000504c100d08440c00e08c00c407051340000810031a211b000c0200c1d001003552404402c1921001c078204c1c1400c26040e4104102414601444840c24040701c03810116022040108134100f84500100410259503001030350018410001801155145202e82c424040ca646408002d03031384415070703c08aa5080d0000c0e202010030031041d1803003001240801c030304003101c50640180303010240d032000d1340c0748180e1100400b08206109000d4000380201c1da40d006028100d00240301c070b2000e20310058130110042e550200b0701c2c13044540c0c0511950088541c034456541613503031054044113020911045600c4030301940d40542d6900740d800c0782e0007642c1e4400c44114849964040050a21034108002d441e810340c50fa034080b070800c41d521550480418002d0b0981031f80400c03808542050218280d0441c06041408669030250000e10303411719901c00ca110410140440381001112400750304100309000481d002500032092010600115440490303005910304012700303040c5003000c0c03140000300c521003814030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 293625179 1250 293623929 293623931
    0x1030c0807080901240513060e07120b2107061d04090804050a0b0c07050303120f0a060b030709231503090c061903051b0406030b0d0b070503220803010608071e0201 72
    0x500a61501f03840c4200c0448034401c040c0034880c10240d003c2d68808000d040c240c1404941041148118040d03007151190180003000c00c4002c4902c10980c0c0140c146a00d00e0b44182e0082d00c1c004540580250b0350050702c2000222814280002c940500000303004044003501c65040900c030020300c95841d9032225000d400c0924255444000c0c040f0814940003450b00883d2290b00b003480384450000c0d0769026103a20950000c3c503a0210345031000d142d0001d000c60b404c4003103d07070800000c101c0000e0300440f82c50b04940d00c0d0002c01c103071104c1402c207003601c04c071182c0d541c1c51380400c4012800801c0c40c8001c000e550840c0601d801e8403061046900003c025034407100f00c0400440c0659848144140c051003040d5019442d900b202200d400c2191504507148903d000300c40c00c2c1a81d0f02c500111a45071050b50000c81603111409071050b06002300050203e402c1113601040c03140600e090b085860700700f81e0240401d02e9112080d00d0450b403c01405a54618000303042000304103031015101e101c10f50f105510383d610310007900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 293626429 1250 293625179 293625251
    0x3090a031205040b13020d020a0312020706020106033906020109020108070f0c02060d0209040905070e1308180d0f0f0c1a03041101020a0b010306140601030c0807080901 74
    0x1502a1901d1021040280072034070b01410040426070b508001c80e0300003840381c00a010901c20344000b50030b88443d950080d400c461940b401004110240d541c1540720042d82c3c00300c668080d61154200c0c00c0e601c0b40e0000a0441000207481c0e6041c0e502c2080e040c1400c0d5000504607102e24801030720880485a40d400900140e440e110440b055580110740340e50006d003d4030f803601c00940c41040c00341c050010000002d000d01c0c0c00080b0850821030701e030305941e109100103200b8041c8140d981003042d0784800b03070300484a80034035040200e8400b0000012200c1c885600081e44c5052842c0c3e00000d2900c140b07465070340c541007044000c101000940541e030740c0c030001c1d12828000039034030181d00f0030510800047c1c020754110940d148054041400000643e0344c070540c8040110049910000100d06003100e2010041040c0c41038000403041100d2070b080047d0304414010b1420060792408011000da40d010715045011461030030118082e42d2096081680c401a12000801c1050400310381c4a014400d4400c40c0b610710400b56 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 293627679 1250 293626429 293626433
    0x10030b030d052109030304020d060608010c05040f1202030a0b0a15080d0f030c02100506060702060313030e010201020f03042312090109091a280e0a05060904050c101403090a 76
    0x600c440b0705090f41681250300d0328000c460943e49100240002c0c0c400c1080324421000c00000e030300100c01401c840790092240d10940c0b28003512903009405410407560002d4030100d800040807034a1441a600100100360a0b0440e4490030080180541400350880c0c039000c25002003420004850f0050010000034001801400703002806984c2241182c0c007091304001418000a5000504180d03260810400203501c1d100d02c030002c1c2d031501c80c1e00002034000c04040208102d445825011202440c045e459450000c81d2040049080703120355103200051000c10700110340030030300302d175282d450948184d00310b01652104444854039210442c072048d901c03e100003030f000602c2c0d68030401003c005c010b48881403200c9000c05c2d10a602d220100401a405100560815280000c10403040309450041c204850030103078850351503040d0b140080350a00709050604010030030504254441303e1045402201030110203203140104588078403449840340c1000809040c5010865001006501402c40200102548106c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 293628929 1250 293627679 293627707
    0xf040b040b0309100504051e100e01060503061b03370209041512061517010504110111120c0f07080a0b0609070807030207080f0706091407080c10030b030d05 69
    0x8851040c005604203002d000004900052400c08c01c1940c064591001007150307034592919810b0066a2102030500854680035001075001e0002e690040e010b8035a1aa600e02588842040002241c40510003c00002d40c120341421407002c1d400c3c1c00c243c0c5103400d0a0f400701200d4007007900b440051080c540d00149100d294a49031080b031481e50100c985c695a0719240c9900c00c540524801c1014101d50385400c440004204050481da01920704103140c204508100d6002d11b0007800d086908030b030100221104501d066000d000903100280210009084542c0303065846207041c1c0141281c68031f10f01c41c4201c00b01d5245000e0040001400440c0001c2011704510b043c444010b04015020a000b036507044240101c0b40d5001c08600d52000301401c025954101c903140c5151144142f802a0310189408120358041200a4000d501001d01448190a00c060076403001b9407a41030a12a1b071109500c500da04280905103031601143c031804038100003038214844008a0b080c2150644644005400011401500941c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 293630179 1250 293628929 293628943
    0x60906060903050c04090201020c090901050403030510152f0127051009050a0215190207080a0b1e0103150c1706012d0e01020705030109020904080f040b040b0309 71
    0x180340440000345180c0f03a02d900d606102100900864440c00c00341c040d0790007003258041940d00504040c030703286481010280200001d80e400c4001908141c0460f2040c10f000c186001651105174016006080d02d03041540d40315542100060301d40e4407007031031040d01384001c07110724014500030001040700442c0800c1085070b0025101c4040920101d44d0541d800f02d0700000e019040b00102110001d0196124103001e8a02400c81c80025804035440c1260454814400080c180c0304070741ca058501d0b100100601aa00d81006008400320b0394414017204010170b280c074003590307007090aa02d441c1c00c410004002900481800b6001503542e14005800c0004241c0540718040020f401440c01420070a252030082c83c3c9040003521f514108110310302180d64482d440b8060240310118082440800c180d4000c011741601c04814010f4098000c804000400d410180141440568018611034031a51256035001c440d0300421619016010240004500340c84420000c02c090b10084c41c02644910301540319900c0c0c400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 293631429 1250 293630179 293630189
    0x709060b04140411040302190305100204080d08060102101802031605100903020a06030504150608010e0c060c100c05120f0f0612070605030c1e0406110303190b010918060906 76
    0x32070708205183e244c21680c282c0d010b80381d0413655162942c001001c05101c035103064001038024054115018803258845c3e0040044407441800e40b02071008000d810b841100c011078445015030489031940b1014140b40d40300c00c103d5940c0c41c80c600c0c610f10940d0080717842c020080d4180c012144102340c0c240100d01d0810600c46034940245055130040c0e0455020030b80c0c04805106103801c0c591035201050802c14146405080c0e840d20355030401c41c0d96503030042c031800780800c41c003c0d14545c02100c1d0000c03ca420042e049400700c401c8030004060400e0610712440043c43d01d203203250700300213003407102140e80c0300d007003c4e50350040d40000c0035041070341000014888100000361010703102c1d000255034410120004034804003180e0403820300b26181d0b901e880d41028248101d83e002c0c0754072515000300d00d000307141d10406842607c20341d559825000722480c070500e60707920085d01c400040d080e55281c1d68462110a0300804040d44040c9489000c4664aa9601c00c0ea28549409440560b0321030909000056440c800e15001704 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 293632679 1250 293631429 293631431
    0x4050c0a0b07021c060f05060906010509012007050d060608011b0e0f01030608030a031b0504050d080d1b110c03030310050607060b03120706230a0203090709060b041404 74
    0x180381c5810780c07a0a21503808002d000e010300560660613446111400d007100b64001d1014405141d048614500801044030711900c61b0401c00d0124006510030310507a0396840041e1918846c6040044c4880c0d4602403610f80c140701c0c2c3c410300c4400f103015250407160f400d18605c81c032070106185060030501d41c02d50b4501d403402a406070003030500307003041507000500c00f0216a080c0d43c2d207a014000c100049001d4649500064103c0c840028403000103503066001c4180302000c0c80312410001981d000440b01e9208030320a80d50b0061610a03101d0224142e0002805c8000802e4400150203001e5001117503240009500300001c285c480e0b0a205038083c06101c2040d1400084000e1803962600a9048012078181c2c042d9a00403c000318814041040e02d521890703020300c00404407021110600e2012007564080c01040b24814140b00303008440c031514040780d0404521421414801d40e0b140204107000790001828007810740300301e02d00000c0c000e103103125160241110f1094566924100400703010061807810480d8042c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 293633929 1250 293632679 293632699
    0x3120a031404080a0e0406050613030b130c03150b03060420041b1407050102120417040b07021002190311011a0a0902160602030f01030c05010c150b01090f09020304050c 74
    0x3c2d00000498070703152103e041036410000d5280c0440c0c0213028682105802c50720008406c460f4081001e0041c00300c900c140c031408050b6844040707a00420745180401001c810811070180300260709403510524098500b00d00003529601400041e24141d0140c80680380c0082001d41c601120100e65401c0d210300d442540c0510400f401e040d08a801010034080c040c0400044241303071401d00048208961141d50444020b640b1070035002c080303084c801001e8404030365600036074250300710554084082d501180d9050300d82d1410040c25400307120400140920010450061001d04c3c411010041d40100d00e81c0e000c1d5840450f4500d07802c041a086074100d01c00301650400d003600c1c8049036034400180c1403d48a1102c000740e01e0f521101321a11041900c200e00416a50022040003c0c070b040802e4201d040300d006a1600300e4060b5900d00640b290a68404c3c09403017114011403074003400846030011410581c0601d48043d100e542c4002c980c900007102d8000c6116503400005200034002c00f001032164201040f1003900207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 293635179 1250 293633929 293633933
    0x2041a030c0d091523070e0607020405040605150d0803041118090604051624110d0c11010e0f0f120d020a02120606010c030309060204050d060b310207080903120a031404 74
    0x180c00c0c00400c83d0040010b20403441607d80c0360203040e0344196030f000d442840242410724240d4050078040f1454140054452444140c40c038289101d00d9446ea08081e58500c0d50321030b0f0f15a10385024070b52a120390484588402d41c05144031540c6070030305c605c5014000e842903060510f0300c103081c07144032901001407030360340e04003840f04e960200c1525961916130040d210741061002403d590f400b0011420703c456000e0820400032a0b50400340446401d0312840c400448280030000550b58034030104585a0800c44070884d1000c1c41c20b18104101d4010001085003034140710000a60b4a0070b1403903d90400113800030a010ba0450511100c1e40282107083d5000c1c00c5103141100000340500c1e030481000d0100b5860344c042c0c0e000e03c521a411036000e0440500103e082107410300307105015050a1828500885004443c00541c20b00d5141140c2004000c0341c030307550b08001040244c00690005203064460b601d080000d00c1c0d085c0d030204084090120f1480c4010b8442903130040c090100c4544402c0c000d403140c0d0300420400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 293636429 1250 293635179 293635241
    0x906060f06040b1b060708070e180610020114100f0e0115080703090b0c091e09070c0c1d06090f09060a0203040609050a0311010f02041a030c0d0915 65
    0xd8400f2010f010f9220b8481314858896003c0c400078041c0303140100824425165808603400703100e400691940644803901b8424000b1902081115a002c01d40d0840480c0e00d0745081d11003c03a810034903100109143d0442190340f494504140c0b809802c0c0c00d80c64104100c0d81801000010060441a801302803070f40c98685c845545101e005a442d082110070b8000426444c080d6120b031021a80252000000f031804d80c408100c107030b120701e4510344900010002a2454100030144c140e014602908400c040e4607000400d0395105042c41d01225980e41d40301e0003003110100d00103165050f1b042040081240e003040028004c103030f5000b038105803c041d01001006408e030350014100d0380240c0f49000045e80d83d82c42d41840e000410745002d0040880c0108000c00f01490b602915900320804020000c100107035001514004070b2165100300b0f060420040d000186c00100070000d5035015054a03a031b10721306113071440c160b802c64803812000c8030110000c2c12407505600e1284219107800d004402182c4125540080080e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 293637679 1250 293636429 293636437
    0x27010606020c18011e120807020909010e0d12020c030c0106030c050607030c02131107200a24030204050a090603030828050c04050d03030b03060c030c07030e0a0f0e0906060f06 77
    0x741c420540c1401d090015400c40c81d117040140707051204040200d415103040300c52580b00500c160310032807020011a842c0c000602ca481d5a140010000301222078804c003080e65081984500c1002040d800c3c0086082400280001c01540d10762400010b2502d065152401040c4210781250380a001d007840901c0000e90020b03900300606030100c4161110305803000540c4080c1440d03280c89400d08902080a0081110300c6640c2c240420020341083e03040c3e060700050000308101d0b4400c111090284000c500107a00460704140207995040c43c02629041e15600410040080c5600c651b41f031507620242081415403101135150000e25440071658444aa204440d014210340086544041d54402c0811070070030040c0201d500622010b840245050801d04014000706120900c25000e4002d038000034980c00425400c0724803d200c412256420f0201903107040755140d0f485c900740ba4210815080102e01032442ca14024001c0104025160082c43c0031a107075820701c0006005180076500410628460313a540005031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293638929 1250 293637679 293637689
    0x50607030e0307080f03190c020a02041d0a05070608010801050f060f01030b0913050f0706020d0c050705060d020c0d030b1302090406180e0f06061827010606020c1801 73
    0x81807001c80796803001d04500c101c42c40280201400104404d5804d030200145105d0300748400d206407200340d91743c001c105840c25884004010b0700300310305c402c0040c81d1580c01036281d82d500080085694071452101864511281070641e40c0c2c3d4031041080105503404056075026042900091000742010308035803501c0000517181521a81038081c500c481d03031b4481c0e404507151460041c251042070521941088414000034030560351800380c80d0813a0314100303000034a1022600c280c0d0003403640c03e020b43c40894201d4680c09040354107006031080040c1c00e40d901e4001d0144070030302e94001640e5041c100c15140c98001e0b03030007402051508042c1046150b030343c0c203c040c249146041e0405681c650750800010028034650700980502240c000d46180040850741c450f001513052041168070003c6e492040c10f50340c4000b12409540b20f400c0d404509420040c07259101e40085180040d82c41c0c800c21142400c072840c2c001c0c84440010381d51110100880d41d4104852252244242ca078a400441c1e040356200c1c90342014010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 293640179 1250 293638929 293638931
    0xf03020d0206070c0609090c0c0206030601050306060408010207060c0f080906010303050c1e031321110414040510060b040303080f07230c010c092411030a0306080d03020705060703 79
    0x2803000c1d521054119142c096111090080e903079240c02015103c1c200030b0283c2e0000c203250280315010180035001095206800504ea1811135540d0f1004442a40c0024204c0750414024040010b510100b4000703004080d01c00c0c800032404c0481d04200401c01c2c880b42e440c840400c101300050015100c00031400b541580d0f050700c0c21503561000400007514012941a6034600072180058410308001e01102034000d5151108184401d81c1d6246441c1c4407000103004130642150f080c585000000d130418800603c190009480411000783c40c0851540c505805c850a49854010b5201034020386034a02c50344010b803207080602030a003130454400620880f001000c8080b207601c1c1401058409000743c072aa0074070103c182060216500f21280c0042035044103100032001d45c00c010840a08074080c40328a02500c3c210380d0b41803a40b110207540e14000c61203501c0c80106014000c040680e0451b0140000c0070114481d850201c0c01d1032030b000c4420b14140900c3c0c90407003010310502a00e070010b01c010401c07a4016102d490 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 293641429 1250 293640179 293640199
    0x100f0c1d010201150806040b011703191b0f050d0318080705070e2401020606010f0e01120e0717030310031403090a0906090c030608030a0f050415080f070203040f0302 73
    0x60f8010240350400481c51406440d00294803400084d455106d10b114203611215a6030710041e40c055200c4184070b16403a600700740072218200f00501150f681680d164503014191540c3c5c1410600030400003082954405060803001081c80410001d484c80b41d106860104085107915000b409940c00c11000144100740001e052414400200940d5014000c089607103401418400c180c043d03500030542040162039040c1306c090420f50b002040c101d118510686450008414021084070401c5445024505200c029440c50319900c3d40c0d481410030b010400401490214101803828082c2d01a0017818034860703004208000c44074029140c500e0803070754000810360034850504a11070440c06000f0b00750760080d00c2c0140001c1c1581854001e07034100c074680c0504206400e08220101d0070344591780a0050039034801c1042090040c4240400641c01900b450070600303058031042a084a0b440e400c14480001d0300f8001805040b40c42d900d0300613046200b600045180915108010500280d2448040d100d001c81c41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 293642679 1250 293641429 293641487
    0x801090b13020a0203130806040201080a020703110604080a1814040c1b060b01030b01020c0102070b0c0a02040e16050628030209060304061e060f0e2502100f0c 70
    0x81d2490750541070164195110b15408000030b550742c2003c101c0101c40944031400007402c00c800b00c0e16600684d01a500c0480550707409072188084c0d40080c00481c2000a8030000c4a4100014404d460160344030320000d0f603030360000f601e00500c00802e4054462602118138010450400740804010380d050050b0381c0031039090704401c0c1c10f031003505821905441201c0c48020060412660b41d02c00c403201042601c04114001195004a9840c045406051f0150388417100c140301c641c1c4c0410103010890400411228024115800704050715415851090903a000011500d80c107001e4114a101625080c2c90480c1010b603181c4070442010191107400301d18142d811032100c0aa171107070701101d442c00030142007203030b81e810603107020401030240b42245204c581c0b0200380e5030a802d100c1d0003144200c61240d000740c0485070900c1e40c0c101450030007404070312200d20201c1580420103101c41a004042c40d058020f0007400c030a601440d41921110740d034002e1683d1402c442d400d1429000455000149454144020761040b18 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 293643929 1250 293642679 293642689
    0x1009150f080112050a0c0905091e03070605040204060506070b010305010606030e120a03090803091b0126090c150d15061b02040603050115081606020a0803040321091b05010801090b 79
    0x880140c01b01c90004404034500d030039074100c10f005240000441c1c00c4054030450401030b805d5007845041e488c0e042048408081550382d0030180d040b6000510010b41d0315617820001e04c00307510952040b50b13040303000c0c0010010300c03170b0a200f04001401c841c1024089140000140350f01c5154055440c0c499400200340e62000600c81d91184458660146880380d40b4209500d5080d51645a07034000044442d140003000001d52042d0f00d01e4427000f140701c8200b200700d0000034100c503d8a030000e003074450038400e03030380484a00d64986429000b1009608446583d0307481c2500184141ea000c00d024502600801c00200300c11940410300c0c50b8408202e60462040000c03600c00a4054440307640b0207042ca40c01e00c0e0a000c05c075a25401c0c14000c0f100e94030215061f429200c28031b10018480d43c130591000d40c01c4032240c900402e00e0700004541c0580f10385404c540307a8800303680c22049180d6118818180707666420000741040011141740c500c2605002c614141d1902e000002010020b050160703a42441c0c552800c50016120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 293645179 1250 293643929 293643943
    0x3090c03030304031706040b060f07060b10090602061602100e010b0a1401020c04050408121b0301081e061b0a02010b0a03051513030906050304020d021009150f08011205 74
    0x8010152580c07420103040050815042c0b2450b00c1907035501001103480d51829218100168074064980b900700600d0800c1c0e40b5070394000740416a5201d46a040f041e0503643c1c0c0e4000120089139a894407040f103414098000c0c0760180091010307031030a02c042c2180398040d40010740d802040035241c4011907110981081240980341030300c1d6085e000700d030f07158021420801c0800c200b004004281e084940c1240d00e00108402d0ba08181c6016180c403108000090fa02c0d1511320100354407040d000c0a00603030110540e054091540300340d0002c0d004d6040b00401d00c1c07004400c110004030380c2480500915550800f00c48040401e01c8191380004246400903a1080e128006c0d0482d0210600051a48443c5545c9041c001e4582c02ca103d421916031401d5000120003040042c0c40d40d010302e815a80c1c0c01c0c01c542c107104050b80c4550003e0170a82e80460080704550060303480c0180c040d400c0c00142d0318981e90616000300000c01d2000e00f41c8103410720007907452400242d60711201d014115048111031003644806804c0079410300c41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 293646429 1250 293645179 293645203
    0xb030105010914130807022e0804030809030a05040b0d1107080306040605010c030e100912050c040b040c080a0c0302040b0f090111010b1507021201021b0c0603070507150f020c010c0801080c06030c0309 88
    0x40b288180f410705902314627002c0c4110b022741c0f528002e5603a076945180e1244502000c03007004c542c00b88002d104000000300030f095508414240001e00d180603400e0b0000c1d54105100c111400d180003c00c010740b070300b4207014660040c1400e00341030340d0410302c561b000703408001294942030060040340761081005104941241c02003200c0e12003144032218a0501940383c1e0900301c8110702590900400c1c500d03d0500f4401c05a021083d69901c042c2074948006581c05007044030403d5007051340a01011400305d00f010014450300103d0303600180e540c0340b4080090140500711500c007001d80d15120ba100b5960702c0ba0b0035500514154208460303503410280c40050085481040d400c0e11a40c404100c000f15210070900d1040307222200d01c2100c14000052080004d248011030368480014014004400068000101301c0c85414003e00013041072411020040102c0c1c0040801304403580d140c2080c43e4049402420480c05810b03400c015184080c0900c000c00d41610020f0110032001c600000040c02c000024085000488 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 293647679 1250 293646429 293646499
    0xa090303110f0d0518030a0f1211030412090803090d050316030e010219151d010c030501050a14091303021014010302090a0209010e040e010b03010501091413080702 72
    0xc2e84003440c2412a0001c00590b0202e601d000c011031501100385050028203c00c100c011860316408100c1101c080840315080024000080aa41d640e9100c80c012941c03042002d6001c40e4407272a242c1040c8503509104d004080910110000c1071040e10404803c8901030f0a041e00e50415904880c9070151840c8107400100da070446a5900f074004166101200103043c1d00240e003240c042d445003107496070383e050301c400e4018240b040b07042c104100601d90741c200615a02500500391142c02d000e00680d070a458401a01c000040d90301c200511091402c1c403100406041120b015066034484580403d0408c003002c1c0c140c2040b4168000341104062003080001c007109005001800000c0010140e00202102800102e2040891400044038000d082c801d40305207001c16518116401100c10502005058240c1c0f0280c16548520344840c07291030034001c1c03900030314907410002030b100e05882250030300843c0030b0984c60001c0404185c840210744010240c0c2c0b00310f601101d004c81c1804a020342c1c1b200441919a030503a2070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 293648929 1250 293647679 293647687
    0x60f091a090301060819031d06030a060905010911160f051504121e0806040e012903030301060c03050d0f05010303030e060f010807030314090d080a02120a05030a09030311 75
    0x100301500058810004103500a01c42c0035210742d1000c1e01c0b80c68140c04850000502003028000c06d108103041c1c55200b0140c035110010384401000b02d401c039441158840001c80c1c680c0000c104440326489950300518044c20b041208060a4042d100d00d407040c072800910402e0611801010700c084076548501032075101c4d044481184c1180350320060298121000c3c1c528050407055020b840340164141500c04400e0000302408a690303a109485c05903016040e50307045603542e00c8000c3c86210134460003940e80b00b000051449060a00e0319040300d074040c1e201072406078006000411a081c1c0004800a09560604001e03440b48810020040101159150145020b00b840d000009260300755002055018603d026940c0355610003602580030703a801e201c0e089281d03024000401c003003441041c1c0340b050b40c0c0300340c2407141c030781813804001440200160f90203603030b0040d00080129903036804110035410820045100340c141140c0480241103030200921300c1111584441c540e6040510990240380ac2d01480e620705512 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 293650179 1250 293648929 293648969
    0x305100b04080718020414061b010501060c1106041d0403030905191a01030506010902182106010e011202010f020a170d0c020606030a021009031703100509060a060f09 73
    0x1540034244150a0100312560521400d84203a008840c01e9511f11a010200e45591100744803a950080b08540c1c0d801c44172942c03001c80d0030000c2c02400d001f0b02203640c03036140b404868184400401c80c40c02d1641c2c802c01c02040204560108182811252107098142c65940ea50b01d040940250400410003441405928090188202d02c00048000c55004000007001c5000704130030010742c0c0000303000140165022100401c48940d00390014004142081400422105d80e0400300e180d2051008032540225100403071107825150411016005000220b042c0502e0b51600c0070101d483c421241c0040c1c10001d85902142a507030007000135013001d80e070100c1c16000c01840b1000c4891250000f00103210410f04046c41001103a100291507801008010041c1c0420001c03582000100c4403241c030b00c1002c1c080103040c0000800d2419540c2d1040e00c0c03c02c0750706640c2c1c4c90300303003100c41c0245003e030000c40c0300e645800c050101640700c415061090701c2982c10005c0c90f240c452582035038048029400030080d00780700202000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 293651429 1250 293650179 293650183
    0x809030f030106080f0108010b0f0f060903160501080903030f06010e0607051c1b03200a15020a080109060e07030c05040f09060503071415090a0506030f100f0501050a0305100b0408 79
    0x446038400708985c403070590700c48118500783d4100c2c204085e482003080188540d54542403000314207199004119501e86001c1c0800700b4101105402042070078075002c40b0811071543c202c10b0301c1c0d43c054000d8000d90b01d90701d00940c4c1c007440d000c0c4c090259410044200b0700b91003a500c4902c21903200603080406c031001209514052000c040f19800004c00103000400c44801c050b817404122003103103525480e448101601c1114183d000d83c20708568030554400d00010501003080d50344141c00300b00c510b90016a903103001c1900501201010385c410384200c0c1c9080420054240c0c41658181c00004034600032400c0c1d84462011140c07809513401440ca105500c030000188009036610100403250294160b5089945e00c0751114028100714018a410010851200003280b01d040003e03c4101320007040c2120b4a0388400100384140c0044980c2502180c1003018040d90300b940c1c81c015001044040c80410b0740c0c0e820000020031900420380c005082c5034880010408400040c0c1211014040784520300b52650380d524210383e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 293652679 1250 293651429 293651431
    0x2120c0f10060b121003020d0302071a04181802090910050a02280c08120405010e0606101101112a0304050d020609031509070609050616030809030f03010608 69
    0x2904a11030308200c5091007185005000860303007820245030500b403100d00000c000da0f80080641c038240640b060040300680c1c60320070300c8024034000d034020311205040c040b00140d4241d03c00071076814038406110800100b0525252000c0060100c0b5002c01c500118055503018001e064000a502108000c20040e50010004498100580d68074080c0001d4503003003030f02012480707101022129000480c28040c07601c1c0c000800c05000c090300340342c05a9844999101c2c04650b0700040203540020b512032090006120090098502082c0c008000d402c450400c1400a2421030340b45106009100b203020f04508030306001e41c481145560302000440c0c1d0707100c1c0003040c20003076840d4040c50b0701400000f01c03003082c500c80c0000958055943c05000d404c00302d502a0200101e5800040c281c42c0c0c0b40c402c48544104150410604c40c1c022401c000040429a00309040906a2010368025a000d070b101402054900c40d0440f254081964041c100341186c0d4807492a03140c00c5100d025240c00c90b2000003c000910503500c02801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 293653929 1250 293652679 293652703
    0x405060d0902040c02061605040f06111501060e0a0b0a020706180f08010e060f01030308040f14010906060f06020c0a090f09051605030106050121051801150510110a03030c02120c 78
    0x12142c6813410f420123984501403801417010500324983c2c00d105003030223607803082c0105a60408076204030785003042d1044540c900360045000180265030180b071500385070305d603180a03003003c120315410140164802036803100b80380f04030020440710003101488820001011400341290051420140d503c41d1441c43c060b0051600030741140c400d03040051900b2480404090580e98140d4410703084c1e480e60b8988250306403031040e0035182c88801c00b0450445c40024446c05524034420000400d44618110050051810f079502c0801550003480002c1c2c8203039140d081c00401c2e00d03035903180061200694500708004100d0040020058072079140034800091101070501c0841e03e0803402030018985030001150090410445800f1409215107184644402500410b41c400c0110400d07041d605190032900e030a407550f882d61400e440000140a102c0c90030250b0317082079840894101100001c91000501d0365802c8260409030402d5074800c0103040e668800c0c0203400c80036960301d141645404030205096210340b840b51030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 293655179 1250 293653929 293653951
    0x6190224010303020a0609061401030f02040609050c0a050f04150503010e06030d1407050c1306061e050403080d02040b12074e05010906060813080405060d0902040c0206 74
    0x114100381950442218141c0c0e40c5a405040642226541d100107040c004508540060311100d031030000b83d50004001340214050b96201c8200c6103140148000c88417550400000035081404110803071a100c2e003150484546413034825a100d102c071101e21040d02594100c00e5404100c1e240b40d50103c0c0d8840051810303a40459000c00031529014109035892503c1d20702d2501003184082d1800c7c40d201e0f8030020f0098903004130305031060740601c83d0000f8280044d03828600340040d503541d42407051540c400a43c244003105407039402240d80b002c0c00c0c040c11500691000400720000002c00d1100e00083e90151401001818091a01da510350720755500005021180c5100003048070002c1c420040a00c002c00901400200c40d03048005c00c1c41102119400e161700c0514400e1007030088aa20b016400c3c4152030092a4180b00001c07c281455001452000c1c0600907000c0350b2103040e01c0e9401300311210116000c45038100d55455071030070b12960b10000340841e0703040030b50701c60301d800c0012268035004544c80e0b2140d103003046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 293656429 1250 293655179 293655223
    0xc080c070b1c0612020120070e1608060a120312050703140702030306090a02030a0207020d0813060215070516020310060524040902030903121509070c11040b061902 72
    0x10302a00302c42092044d91540d009001000000d540120001880e034421a410726411880581d80c2c145403030115030005c000f00301e91a0070071903a05962500540c5020551070045440c1c00d10100150070900103002d040c070085030500c1c8150030940101d55401c032100b40c0c1c40d0305000c00d103080440030300140241c9411403a0407030b0301030005003c54030220032684205001010780e039040d02d880305074600942005100e001c03010750030409040584d4810394181c40072031041c8c1d5455502c18071029140107c40e001c3c0d210005540c003664940380d00e11b84594116500100780d103030250719810300b06982c20126042c804065010702503c146001091059006541030b501d0558400c10003600d00b0000c001d0414010b03100703024510087c00b041c010051150020358021074500e084a0800440b0007032039451b42d030107541c0740420f4503070f00c0b06400d40340c1000040310758404810300701518902c2e4a80c03030380d8951008072000c2030b00c203990340c00d07040c80f17140c0d50b0409403105d4254400b1001800c40742c100c0081d5462820400107048d00031264 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 293657679 1250 293656429 293656477
    0x3050d030501061b0c0906030c0807050607030503071d090108030a03062126030c0a0905010e0d0609030c0b01080c010e0d080a0507060f1121070f0c080c070b 69
    0x100825040301c50f550740d890b0f80c10a041070b00e0400c1c0040c0e010115a00070401d0b01c0000d40318020300545000d140100e4418078180d183c214078500d0034100da403280c0c1c0504014007450300032076006021703298407640b1070402440e41004040340d20462501ca03540c4a07440340211001283d541e03000000740204600315201000502e8641141d1940810740c03a940640b8501541150400684507a80c090b5440ba0040720704c801e0030003404200c5095400440c1c0b030030590744010070300040c12680011441d00408080c03d0031b10008482c1408142400b658441c0641015104c801c0d000805110b00d490000103900320340400559612298441d032180c0510440500003819604034011901c3c00c1d80b0341c2c102c002e600c20003c92030128030100a82d902d40001200791106583d6000035407240000340128120301c08803062469481d0031418802114100d000042c1025070000301c10422495001051402c151240d8103101d680b6243ca450074100f07a1090103140c01d42e6020b42c0c0f1000414090503400307400c50f07a140a41d007100c844225 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 293658929 1250 293657679 293657681
    0x70f0806061b03090d08131e03110f09040804090614100e19152010050c2106120d080a02090a051e1203130e0a02070c0605030103050d03 60
    0x40c0c4040354010002c2044654102c0b0025005005039420400c0e40d0400e0942c50002d1043c544400040d1040d02e030001f0a200c5c00350440d14820302038110f0074016031211209900705541c0340f0031400010300301c01800301030707410707550310880c80100e055002086e0074182e2401c0d1600d019943c002c0d1042421540c00c01c0004110441603814107184d51002516022703200030f00c2c0d403044800c40d07038248070303135802052441400b00702c0c080c0201c141024280e000000c55200c1c0100e24002c001c0c420100c80e19040001950348525aa00085100b80100200e014003003a03549a03004008440e02c00c800c9411420b02061524040d09141da88000744100021604410404910460345845560907486040043c40c00d10001c0e81e2000c00d9800761100703070b50282600c2c4203e503d41c07003c205011400c2d039250000034207960744501e035450f22103240b82030301007140055814800030190518070400e50b400f41d0031440e02d0003800102200e08550540f201a40c100000300010fa5a440d00038107241d00070b0009035070902414030b86056090103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 293660179 1250 293658929 293658931
    0x903050c120a020402031012050a0314070203031605070906170705030309060403060519020d020c1002090604050d080706060f03060f0501050901140a320306060a030f0c03050114070f08 81
    0x3030180001c10b9195080000941c0014103005004103000000b0030844090f07800150054880c030000c0034400c0e182c1c28091704144144290f003038031402c00c01015005032000b0068541200914032a075080c2249440c1031030810841d500020a80c0b0b01d8038500184d0080d0081c500d050303561a0005841700303103443c2d00506440b0720407107068940201d001c201c03c000041d41a80708651211500f1426022600b80b101c03404283e903c8605a480180d40100312800541000d2162403600c0318070001c21480d01e030003000400c8041c00b0318400c2a1041511645401c2400b400b0000c444401c1d502c0f50041000c10380344c000c1401e0b02c0405000650701c2d546042202034000c0480d11a8505a402c004c141d20402e80c40d1192100760752400031b19003038100215100002d540c001d0b1401c2d1207400d20701340c90940d0030380c2c01080b4004451660014030b28840d90040d410705c04141c586400241c2035a801c400c4000501009080000c9845150741c0300622a61801c40c402c0d51f150400d0b00e00d6801102195562100f100c17007000b045400e40c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 293661429 1250 293660179 293660209
    0xf03030507020907020102160f0b0906070207180902192607030602090315010e06011b08031f0e09160504090b01050f1c140f061501120b0d030903050c 66
    0x20405507015140840704154882503a200141c900b07007021581c0c5611031113010007110344000710b029420400c10101e501ca030344403001c800100114070700850000d40c0c5000e58441c3e500c100740c1e22448070000c40304c1c54014031404d680151030141d01350b4410b0b0b4400d46503c640e20814039984d0702480007030764500e04a82050701c281c039848003c1281c43e046858810095015400f4560300d880380d208010710701000c1440807402012081c03400500c81c9003440c00989151000d504d070501c01130b5a07601300c83c0000d010000f682d804c0406030100085010744031400d010a100d951300030211390342580042160350080007803001505c408520800c460969034205000c181ca10807940105034410820041c000d41c10300701c0f5180780003500144210b58005080340c03803152820080ca015a400003036025038403940042000010300c460040801001c5078a0800607403039242c042c0d80030507030400040e80d841c800b1001a50700004805400109100d14811245c6009482001184400c44407401900306d008441d02d00000c02020b020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 293662679 1250 293661429 293661437
    0xe07021002090103181410090c0e0c0c07090c02011b080f041506080309041104031e020301060312020c03120a05040e06120f031c0504020f041e050c0a090f0303 70
    0x80600364030040030350002050a4101030303542d90201134407650110302d0800c0070300640e44580e2035500003a20a01700403980d51003900040c04c2400c0070000400e030b201c14400710703500f52040880e00d0b114040070522074460102001c4080c0308100700400c84e48030350f900c0b00c00c011074035800030030002440415803600c0c6021112000e02143e00f80c0f00140060008006080d88248038003007013050801c01c4c1480c50200c4901e60881803569101040509207030a103031284402c400140b510b420304261555680004882d0f6180c85400620380e00b50505045450075041140a0750740280707443d44007181c0080c02075030b81001803002d0344207205600d691481422814120303a0b208607039903640d41c0342a080c1815005c1401000d41019040b0b1140c3d150b01d4607201086c0480340518071420090b5603210000d00051400c1c03014000c0109220307207000203203c010b0f900c02da0303d440b01940a82c0c0c0411000300900310801040c60298001c4804c509000c01c001480c6030610050001c824141c070ba5184854071608000001c00150100078045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 293663929 1250 293662679 293662693
    0xf06010620010902190501170606033c0f060d0c0504180803010e0103031101020c0606090702010b031605010f051201170f16030c0503031c05070e03030301030c030c0e0702 75
    0x9010041c0000000d90000465544215408201100507190994200070b103c10014844e0703680c03141d0000e060409100e043c0700d41342070500c0061134503c400760a0480c400890090380c40041e100c40d0500b03140120180d401cac0e070000c000d4019511030301c10487c1c03415180c903030030300000305980341c84c4810441c21508031003030031889420041444010f210700b01202c810b422181c501200020b41003402503018000240728800b1a524503d4082c1c2119807291400d9810f90040c44105181100010010381c810f0080340e40a00a440c0e407d420790040c4600b03136107950140145800d20703d01c426500421421600e0aa80d03ca100102c90141110039004000003220103031010b000401002c5003100d9138221101741d00c815540e0081000e040340d85407181c0031040303901c070301e41e4010200b00380b103c0039017000300424007500514900180d0680301d02000c044030784000c0d0000c1c1c0d10804590a18804c1070540c0510300081c08681c0d0700c3d612420444807240052004540c00c00400102180c2da0300c1440c00a402040b60707800900300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 293665179 1250 293663929 293663957
    0xf020c0a03030e03090916020f031c1104150806120703110603040c0b0406081006090e04030c06020d0204090b0a0603090203072928030c0c0206090604080a0309080f060106 75
    0x161251008401d000c0c80b0910150002d5070342c6c0f2a1440c0034040401c0904102e0b40e08800280c149011030034644031030f13041401500c0307603240c1001d0404c101184903240001c0c0c00e604202c02c40d01e28060b5030040c0d20350380000e8410143c5280c2024205001e10b2003190f88406164031150903907951781c1c09000080800211119074000b5043c81c6000d503410505c5407100042c0d0603100c0c50791000da034001d644130100042d141c1c0d060090019420030410003600f514544200201c1c14111040c6035000003030002410800c401617203d091084a50503960801d0407840f00b590b5807075486d0b2030500a41042c0412034490301c018403000880034007274820100800d034050003a00c5503625210740b80d05512040700d40010040e2140c049205001d440800034429055440300f031545030007071146a200d01d10900083c01c81418a001c4811410307541100103609100e504490481c3d40c0d4500700045546030203140d004441c03500c04c51021038201604091002c06a48480003100c42901c0c0c282ca21a5481e482032103802d0100741c8007444030750 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 293666429 1250 293665179 293665181
    0x1b0d090e0c1e0f071a0106081b0a140d0209040605033405100503070315050f15120a050105120705010e0103050402120a0c0602010c0c0c0e04030c0b0f04060f020c0a0303 74
    0x84a02c0034041d103007051084001126560f001d440c08070703000d48085280700145000010014050491840d00001c9480d000c100e4501c060384c9185052074a590200e100c0b007140e0f0ac60350296a541022244040c0c803480e056140702c020b5005a440c0d14451420008040740d1341c04d0006140180c0b11310862032050a007401408840c1c0804a00003403041c040e0b402402150617101c1c05042d40e1070025503501e083c1c1da8644000020105c4000845000c2103005006080025a4a07a180a6100c2c18120341002c2000842c0580c000184281c2d100503040e030400e4010811069030540c049412908190343c3c040f880d501802d00681c850f40e0b0f0340101404580003103503e15088d482913101d9503015102501c802c49400500030034502d805032101c412580310000c000c090260301e50a0091424034441418659401042030b030b00c41c00c000032103000780d00c02048110002402c0c54410100042d21039041403d0420904003600b0341a40c081048405641d41401c01180d16202c588901c01c4510303040d503000c007808042c000303550214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 293667679 1250 293666429 293666467
    0x61203090d111c080a030b0d0c1a130b0301060e0d0b0a022b33090e0c060a050c06010608040201080a09020102031e0706060503150c0f1b0d090e0c 64
    0x282c00c100c0c80c50f82003a46041e100c441404450003000c1d030b036440d40680c0000070162a4040080c90041c80b90002200c0060400b90740e1900b540c900c0c10484034091000c6100c568117009100310104c180ea0100c60010706046d0f00340056043e20181e54034006032001c04824491890b10300301c402400054004000f4500d1000c680c040e01c076002443e43e048100101000384000014800808185840c3e550a802140c400f900e00e1046088400d00704561a6050f450305242400b80c2584607003030030307141c8030010669008070038420b5107030000000f801d054803154840382c010b009810669100706280b00b043c0012841c00c0c054212248141c3e816551410250342d03140d58040034001d42d00c0201c0c10b5200600c2048005404c050100d007588440e40202a00c4030b100303041c40f0b0309032083c617440036010782c00c80303203642c0070703105070007150983c000001c5c612641e40d8006244641c0b845e1150340000c40750628044206181c00c0c03004a54904102d4055841c4420641c6640701c0c403140d090300f0b0b20010340c4180d080014410b9034442020382 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 293668929 1250 293667679 293667713
    0x106031b0309050309090a020306040f18030c05031b060106020f071a0d06091113090b012c0a0609090c08090304090b061b06090f0f0a0f051e0303061203090d 69
    0x43c07803d000317291021070003c0006450311226280c000c802c00c211428207202c0d03040c3c0f03912725444c180404142070b405110140300070322025040009220020081c00707401c01c1103a40c2004001d4180c040003001520154480c4c00a024460050054001180a4203000991242038070100300203402e42207000c00b95800c8540c014041604e075551101c0b030000c2c6c00784040c0710b030024403e290490070b41c2c0d0340c1483c01a1240552142c1004d100b240c608401c1003042c1c0d0b0310800106481c646034100c952031410f41e211602c500d9809020b00c66115034407460208055900507503900440d00107010074408588245029a10b4203021a954842e542c001d03c03080040d074819030403502229801516140c81c001030f043c20050000150a942145c030742c00001070000c1d01c5410482c1142d0100c02101801c0d401d01000352141d150884810044c2498040d130540b1024001c0c1444141c400144800500c1c038800d108208840d140e410031030768107201c0c0c01005000e640b109008401c4a15040c0e008100c2d0500800c1580c171500b00289070580 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 293670179 1250 293668929 293668933
    0x90909012007030c0c08010b010e1912020a0e1509010603140708180a08040f0509010b0f0306060c030a0c060501081504120e03070e040209012c0a180309030b0106031b030905 76
    0xb00108100c5c110a00c054034000700081444042800003511003464102c0e080e00a910800318181a60780340d01c0e840b030076100b10400c48480305496000141c0700103419004000701c800301e4018000810342941c0c4034080c0020a544690040c3ea0f00c241c01d0f022580c9280c541303903415460000084840340300e000c007542d202c81d8400d0b040000302d4602641e14585201d91508440e40480001c00340808a40784510700c00614040300d000ca0b056040408240150151041d05010700300c002c0081802c0d07903507201c1551400d100c40c200b12034641201d000000d101c170b01070b01c2041c2c07103540c501000851601004940030b01e01000d4507070720741e8203034486942d04000d4461800c020f8081041b0825100c909940c24403005c1c00400c80030030381c010310382014010050000410b80c0400204012802c2d00f202d0b480100354040214550800c1c000b52035510304548802900c82c2c450b0728541d248140518404064121000e04281c9000780417074110341c0e0326860150100c5001108400354000c1c8011024100d1348250081625a449082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 293671429 1250 293670179 293670197
    0x2030f15010207080106170601080d02070b0d060909030816030509151f17060601020109021003021819060e2b0c080d051206040903050406030f0b090405010209090901200703 76
    0x740c0d45c2150700741d40100907030004d00e550f00d0403804000c0080502620350040580505074803100044d5031041c3d00e1080308101c1d5000714800080050340d910601c001c0a4203c0244001103c614008099a40403520b4080001c0702d414006030b00da102c0c2c442c82c1e1142203420020546001c000c01a00200d0b000240000280b10b44201703c3c40c00d02c5505400b620092080303451407002e0f8203010301d4482c1001d00052045045a25201c025000360760307a800c1d103106c0f0340c04074140141c0d1020101098403401e51101c044039040f124008610849203c1381483d9000ca500a95030031040d820503104100f900c200f09809000b50400b13000e17466140003100c10f00c2c002c0709482244082841b0759603640e03990400d031501521401003040450302d01450b14141410341d07880801240c0c10410045103a0f006083c80c0601d0160004140c0c4d22786201e01241d0301540105a0901d004200c0c003d5840c01d407800c00d01039844005058000d042e0702d800300b84003d4050003480124001c0303201d001c285210480c0c480e4101d0304032403030603810811850 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 293672679 1250 293671429 293671439
    0x102090a0603090b01120803070c030e0409050c1206060d290f0f06030c0a1a1e2d0d050703090803090a050705060c03040b0304020111100203061302030f15010207 71
    0x40c44000420080d10007084044090030040d011a0f0143e01655909290f410440c0c00115040200ea500801d036060800e40401c0034101106e14501e0000744035081032a01402600307018001521030007000302220020440400102c0c91a107545c800c2e1800c0390410449805000010190540c0701b0413143c00f0414403a07800c0d496100e200c045141910610500707130740380341405000d060751200503a004109400030310101c201c1c0c602050b00a041480340c0c0c0c01a002902c2c200b1000c503024001c40b082421040402c1c0581c2c89809980c08885c1d00080c03000c0c14060742040107440000c04403055041d4605006c2200781010f0041403000003420380103112008265a604403040001e11032000340d4041c01c110700081031404400d01d4020315081554000c9403184405019a020380c86000040310195103c04102c2a241d07110791006898210b0250310342c211500a202ca87e5005c0e44d03095014501ca0b583c2220071582201010b05010120300c401e80300c06d0042c0b40f041300020081003910200710205401881200c03080f42c0d0316 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 293673929 1250 293672679 293672689
    0x203010b100c0b01050901030f0605090f0307060e060105010305010f031707150b01080105041116020f03060106080a0b0409030f0804110306090d031505030a0f0807050303070f021c050a030e010209 86
    0x8040e5441c0881c201c00041018080c20101d65030241500355007803101035055883e9000602114a0000c19058544000a020440600c00c100036a100901265103880c180d14150010300f0554440750041c1c0300303040c0005915882405503e0403946a00240902d560454840b0113074000b030340d0280700c2104c60400003400000c0340c003004580c2c0b0034645200000c07003100d150001425144107900c05440f850501108908101241044031404100d210401d80b20710010700c0885c00080d92500e44591501542c000000d2131600b113401c1178031402040f00100960f08100c0204011500440c4000d4000740514000024060090402c40d070420300418100c3c10802100b0006803030402c040743c4000f00e542090a810f09000d402d40614107908080d0102c03000002d040102107580c2d554901c034003038148070b11034281c401402490012100c0701a0001d059030394901c0c101030301400390f10100c070b004001446040c2003121807900c400683c17a1000c0341d5680300c40c80d024440200700c0107005130749000c4081355402c016900c102d81d03071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 293675179 1250 293673929 293673949
    0x3030e030a0306050112090b0c0706060b1218030a08150616060b01020c1203030604020f0c0102070f02010905040e0d05031005041b1106090307080a111f0e0d02190203010b 75
    0x80d941c2e0124542d0705103c00101120404281900c03802d04100c2002c002411121800c2e03401021940699180e02990074080c02405155001045080c40051809880010320480c640b042c00501c0340302d21001c0010400590780d1268100400014a0610207c0c58040f0548621070301030300300a0000e070400400507200200ca02003120111b4074203980e000500f50a51b01404100035443c17048606040c2034030005c000d6600c0b4440103214500c42c03940098822418032413201a5016680090b00843d150304c40b80c6000c001481100c40160302090802c00d0014480c82d0074010801c051503407030007510301102851801e56450f0006480c41240034100c6034080b8080e250344c4991a0282c01c0c00ca140f12450550010207850055070000c940b03074941000c4108141e0110000440700810341c806182c903074600421501315124281240742c0c61003801f500c50b04103084400001225688100104100b103e03101802d55590384004401d070500141c1c0006010706040d030003980c0218001c5001800105078002420002082904 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 293676429 1250 293675179 293675197
    0x1216080c0105040501051302150a050f0d0506090c03070f0e120a03091a07080a0c080904020d02190905030d11010f0e06090d21020903011b0c110a050603060d03030e03 73
    0x3649100f00003d000c03090007482d800081d5001480c240310f0058011807042c0b107444010f890245070000340051000c0c80350084034100c030406114940c41d1040036200c1000b07082e0540c0c215100d02c02181c040f9005401c40350843e0f003d02c41c5611412a078a84401c801d4582004009026500210020300102740035000c1c0a482c910310721139541d0302c10990500c030814015000e00c00300c000c03040c01c1c00d2020200140d00281118100c807041d09205042c0c0f41507280841c03103445503080103a0003500101d04000d0b00361880d0040c0c01c6d001080c440f0400300a000306000c49447d030481c030a4640c15070002d5498803059000d1003e2840714441900049080701900c90f540f0142c82010620300500c1c0d12070340c10821400d00a101c04890b03030030709190032990000010341d100c2706001c4105c126954640c2c00185810503507030951010314100c1d079558070315803100e1342030501070070a10900105481a0309030b20224200c0b4942490800251100200380a045440d00710070b0010081608030110309050340c41c03408030780010702040070b011021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 293677679 1250 293676429 293676431
    0x619020f160e01140904140709090f02010201050619050d030507021905130618050c0c07060305100801090807030305070203070b13031e0c06110f0d02090a0f06021216080c01 76
    0x54540b05003001c1603441680102040d0188001d45400d55032590385040e013054000351203006170f802d603035000c0c1d0a28000341e110b000b1541ca409000c008100465200000c813038003d030000c12881c0e9441c01440b010148045900710b40c56071000381804103140401603082040d00030325043d81448040d50126240d0b00d41e455a041d40e41580318020803461901000441d0a4130200b0000d00c01c0e41e1410203090341d00541010010f030b000e43c40b54002050f980d1040250307040090320204407440c055484501400405058450403850903814101048600050107110140c41d404042540b800500740c600314020320f000b80602045020400400c40821140070055024182019804820290710b01e400790500880403120742e5181003181882044a41101c010113825801a20225454220510055442c4108000030f18071807c0810910702d48800e0f6409402ca880068440754886620b54000004103a0b56201d034800503846160070321340042c00c100c041c1164103404d041d0f0050705c034074681c2d030b04801c4d410403800c040d241d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 293678929 1250 293677679 293677723
    0x30f02040306050c09040b270c0d02030a0e0709060f0b090109050a08030d05060111060412050415020102030901060f03120309050313030503030f0106110c09090f01060803070c0b090619020f 83
    0x2450981f082981880742100c00400b5a403a4001c44402142c50244007901000b01c07000003211b41c05007030100c0d1416800000210340e00d01d002075400006020b810300c00d9400f44961b48010401d00504e10540781039480a41c42d0814003407514034144029800950000d0400c12032400c00900c1c1d84400c00c1c404003800d8100045c544404030004504120740e03004100c18104109002c0d0b8507229a0b0100702c09800907000050041d50b08a030302010f45891103250721440310b40c3c501ca01034800160b03040d4007441c0101e606030003d2103419568241c400d42c04d4040c2c0001303000e200c2c0c0c440c03101c0c41301c2d4041d601004583d8401c900703aa0800c0f0741c1c415070040c000303a00c3d807066900e50000402c00000b4280300c0704036405405141000071070400b0951406a40340b00d8217113520301516041003c618182c00030402c101340e8024004c024055a91500c0301c098980d040103404456030344800402103500303070085054441303107080506030034146000c02e1140001001c18501246c29400344242c1b00e03410301020701c02c1d00c1c204001d03c1d102d4184 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 293680179 1250 293678929 293678947
    0x9020c010b03031201080c010503040f060f0b1201150e010e06010c031103130302120607080109090212011d0607090b0702062104081b07050303030f0601021608011505010e10030f02040306050c 84
    0x308005601c7c4141008010810032001894034900d00d040c80da0000c400088500c11200b1000040000030050361b8007044011001140b00015003245074417080030302800d03454556404004402002c22b0107a0400b21030310307800140c1c0c1948214038200c9002c0c020310f4140b100c81040c1d500b00d0300391b034006105542055040c1d0300900640c2883c03403502a607806c40c44020002e905e4092001811000c06005000038503846051240075941d901c0c4000884000b02c80003013021410520203240800300c5800f14a40c1801742000040380305001d201800c0440d140045001c0c80c0224030b50070400e01e580102c00d075203030002d560f41d000e56060000594441c49684100e6940d581e610120028441e0141d402041d1241540100010310071502d020051366000001451104820b4680c1401070b4140408503e44c0f100e60800c0301170004c3d8901054200f40c00d02c42c03000c014602c0d21515440116084141c0070003007a0042d20007180d40101a02c00d6012020b0418a80801400c0c2034880d510242561800d07501803200107030102d84885 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 293681429 1250 293680179 293680183
    0x1e0615031009060602030711040b0d0206030a020711030610030221061512030403020d02041a1002030757080708120a1b02030a0206032d0105010909020c010b0303120108 74
    0x1024041300e0000b1805d0880070384d22000e8586420003d140643e40310004d143d030320b841e000802e0036010350050181c0d0b2240382000e40000290400501034960754140058610a8100480d945002d02414039000d9801821902031105555500a0400109030042c80300100c0040030320000d030041e0f0358070045980c0000c401c810000703065002e825580c5a078100700020070050351281031340c0c014254140e601040c074203c1d450131704107608002980550040d20803035642406550110052281911031040c1036202c1c43c96081d60310401d0102c01011450715140310303004081e20320701d0345a8445100100707600b01c9101941c41300000f21840990140c04564003004041c000c18030180700c41100d14242e44145401c002170004000c10282c900250700e000c0c8000c0d40080b00541d2800d000251580c0e4000d85400c0e43d0f814021716040011039039500007010300c1003180b40c2d40c54000d2907442540c101c034016034515019904082070300f0001e50220041505c030303642c1e415603080f10b62002d1018004840301c4000d010260340c5820440c038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 293682679 1250 293681429 293681441
    0xd0605181509070501110c030601030305030130030c110312120108060601020d0f0309050a210903020102061914041b0f050114030703150b030601020c0102061e0615031009 75
    0x4141c1010345420411002000a5801c0840f0024a01002640c9118903030303a003400c00381d00c0d0250705400ba100001c001d040d0032900850403620b0080000c00308240402800703502172825400355030740d0810b9049100c0404c1c81a804403210f2030203030070346134542950000020300d016244030101d010340c8004201d0043e0352140524060041c012940500380514001c00000e484484c000b24203005c1c80800944040361510130f5202e8014a07520a0480f801c0d002c0b90b081c8901403600180d14001e03150340c400141c8060b5489581090210395042c1c0041c0600e031103610400115542510120140640d0b40c000d46450002c05c4030102c1c0154021703199803003a003450986107800c4030400d070030a04007581d480310200910390b8000703e40225401040d1b02c41d03840c0e44454000302c01810008c0201700d654181c00c030300414600a070700011030241000345c003102d00116420005a031501c004454101c43d0f24124540c1030481c0d070000000560100d0000d042504c03d0444032042c08154000380c8100e01034004540051003800d1407440ad003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 293683929 1250 293682679 293682703
    0x30c030b0303040510051b01140a0c050c06060f030a08070803150910152c03160f09020a090510080105040b0916112a09010603110a08060d060518 64
    0x2a603c1c1c24146004500e904080d07030026002c0103000115072080c5201d483c410780d050412000240b0035031102204d111803c06003900d0803114640303030a494101740780c0240216042c03552004003070941a55100308111020250060136601801a01550400680c1000c014500c1500c40c80590303881c1e00700f002030a9426003d0609460082440e1400d01c82e000d1300f400d1501b02203490ba007050b6200032940a400300c45881044803600460424558038280c0341e01e401c01604500801542159000000c01d4009074065500b40319809202c404000d00784170a5103d5002488004041e040c800d50040da0740005c11480890a10100c0015503010010b00c1146400d0082e00351190040391154500c1c101050740c080640b000d18466018441c40c242c0c99071041000388021050120b40c1c400101100140e0070300d81c81c0c00226844094843c2d04464004583c45000e4420111040e05500e1303102d0601e0145403081c1d64000c000352074541d01840d0030364440d0004e501030103814441e201c40f406240d440316003002c1c040d2801c0c00440c24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 293685179 1250 293683929 293683933
    0xc03031801060602030304080708041a09040c02160909050304050907080a0608010c0518010c0b10080f06010f05190513021233010c020303030411010f170a0f0f0507030c030b03 77
    0x100700b007040d44c0001601c0d003082c0c0100c501c0d0307920361941c5000c5110f84200c0d84814200100704000c03141022034000a0954040c0075141441a0541524200e845000001c0410307000020050309003c80d030340d16403250071118803400c11a4501a180e900080c59108201c98450015040300200302c82c172245ca000303450040600e07900a00c15000c5900018094cc050005840c088819194140344660b100310744060030b194001200c010141020510807490400d64014ac40040c401c81070703000c881c03e90008420741201d03070130111480744905000c01c102d082d203c0c4071284122404800404103003035031070380304072001c0540035400182d13159446a4502d123070000043c0b01031100d58548000f103c0d114806008050302c0010844118104500d41d001038a4080d22400c01a40505c404410081000001c151a080216090321b413032003510005101221203180c8007144020700d04604021842190454100540c0c0c0c0380e40460200b01072426500710740031030b4000ca4071030002a440d1803071505619014818038901c1901a00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 293686429 1250 293685179 293685191
    0x40f11190c0210050306041808031e010b0301050607050f060108160603090201090b0f120c0c01050c0403080406120e0109030f080601180e0606071506060e0a08151b0c03031801 77
    0x2520940702c00145070500134001300050256031103510031310000d9144000310354002ca590805c004685c008403100740ea043d0100055400c1003200e030900c0c40c1241c8a0f480720624582c01c1405208054001503130459003446000b0303012041c0741c401d20003103001c1c00034800140030000f60700ca01e50703255404c10f52011084c545040341e160b0150742d224080100307560320340d0b040e96680c8100002c41d1543d8415600c543e5001c0328080240561000a13200410040a10030000c1c0714a0301d0700e460982c032511131440010b02400040004000c8240500e41010076104001c00018854404a141c1401c0d01c80180b000c400043c100503400003078941200250390011000e113021072800036600341d46801c0112501400c0f0300720a202000841943d00c40084a18807035026a130402d95080c00100c0c8400f0302614000d00010440943c00e8070050b0900013040c00072200401c1c010321103d451400d0880d001e000141a082401041030b808144a116403030003031009066510096030390749005070900307460410440181880da41002c2c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 293687679 1250 293686429 293686433
    0x5070507120c06111e19060902030106050928060e09061e150d060f0608060a050c030709090e2d07080307050a0b100504091103190201021902040f11190c 67
    0x4503280a61014035030440b01e5035445c3e10841c50112800380e98503503030411003e60003c210b11504241886842030b4000e11010340c8500810041d0101120880101c580a280190641100030181701d41042483c40002d103031130319040380480e044000c07100c62440b68803460078004000c101c21001c50078028042c3c001c0d00a801e00c00440380d0785001e15803c103842080351051101c244019913110f84050079035100c0c100220b9680388200d5840b40401c9994842d198a40070008000e00102411a44640d0880d034034040c0310350905038050b009080d80158445544a4621403080b00481c04011105205241e20490240c40c0200500762407c1c07a01e410009058109004210005100060b002440c5a114114142d9981ca0b021014220030701c592025030320074100404c003c10322112802c14240c440050b019920946091101204101421b243c000d00580c0108400041100d40c040d0080c0314510003040070400410110300340003a41c480b0500d01e50403050000f9440980030116506040c80042400c00090802c42c49e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 293688929 1250 293687679 293687683
    0x80403180e010501052113050d02070501171504090b010f120503030103080a02030d11180906130b040902060c0c010e15030c0a03060302040c090e010807180c05070507120c0611 77
    0x10301c0fa032414801d011603028a10801348a40034a0040d0398400d1218624100c958543d0350414140155064040d498803200c6461000c1480c0c1d00381c0d201a100c811041c00038401000100600500a5000aa0620640d4495a15400f55224147c0100402e0285504100d036040c10341d4610303070003002c0c42d18182c6404000542c0101c1501c2c1100c1c1c02a001e651100030461045e401c5100c1d02d0903440060303250a50302c0d0302548800010b084844030364000c072483c0d10000010f220310010709803980341e800945002400720303418654000c1095500003801c0031405115a9020071842e40101c8041c0c400f50700007000c100c0b915640503d0690407594121907401c2d0721407908840070910b00c000f0303103403c1d603600f400509071030080c1c040d8029100079507001e8030030132001715140c1005105c04d00130f011749095070390480000103100382d002031010107407035410340079140000c5010000c200400c0324603914014010180b01c148081035003440618018032009090400400803840d06d180400c600c1c0c1c200a040c8141c084044c0c00103800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 293690179 1250 293688929 293688931
    0x2060604090512040839040e10060e060310150e091203040303020c060124031e02040602100507030c0c030e010201090b07050a0905090609060d1e03080403180e 70
    0x58600007603408140c145a400c081c0c040402c1280300750009000243c80f00001090a0100622407050042d281c40da044110104901c25182811801544010303006107130607072141743c0c0e100440c001c4031604404810558140c5501c1c0d0312205004507080d0070442282000d0007889603c90686000700424107881000540034071540c080d0022562503040000c16043e010070021980d0402021016124034091500030040c0d0300c0017014185c18000e000c00051503551491640c00b1601d1840208d861461501300d00710b0081040c07010308006000c1c0c161031800c01c005a48000c1c006000c1641c040c007101d00004140c1001c0da0f0303014003494201840c1081c509095548044007a411a60501d02051803003044c10040303015000350321025000e10356181c1803117107240d0407000410b201c11085c1c440018541d6030300d08100071003200301d81f02d03500f08034400002981898241c88562a180c810a0031a1401401000b032034138010940c02d0840100c0c22181c01e01c018142c1107411032540804220710f45c4000e42c02d005030481c400744 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 293691429 1250 293690179 293690191
    0x1090501061b140615030c030d020709200d0c021204030218070302310b070b0c030603101401030c0e0412050a020f0a290c0301141f030f0c03020403030206 68
    0x2c20402084100950740d848803202440d032004890480c10081d42e801e80b440b40300c4031914807a10424540452074240440c44242136922500500445441c0940000140083c40505042c1c000e40f6089840300c0f42002d4040d081c6242ca072980010300d80782c0410301916010000b10969a65041480b0420042c1c0d9405103000c04105804020301054461200a0303007e8080c07280c8030068801c80740000c0540600110725104031050116014680c0707541d402c2100c0a504c01c0c0c01c0003403c4500d400700001c120301480740003140c104802400300c80d4002894602002202c02c07107003a01110641c3c0100400600c007110013440040d1a024140b02c00e10b0410703603500c40211188480c40d030180b1201080d542c11641c0244008031310b80340040c0c196404594030786004021100740c0707c00220030280320895002c44c0e1484131241c5209142c603031000c528503400e241048880307076210b0014070381c44461007003030001480e00381c044030904185a40300414400c03221000d03101586e14103615502003602c103000800209074005001a0081e07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 293692679 1250 293691429 293691467
    0x506030f19020a09050a0c020118051908040b0301030302060f010b0c0a11041d010b040f090209150310060801020c070b0c10090501020706140a06060905061207120e070503060109050106 81
    0x2001480410583d840551208070356900d071030304000e61400c00790865540501da0740e000300030f81292080307100304c80020310741c01401070382c0701314208000100c99551580c50507004000e09030520b650f44210f220103a01c242c0048005801c403800340b10284504003151409041c5600301c0d1403d00920044aa0780d0310f036605000703490784090b05004203160315990f00010200885002d6190b4141b03034040264080c0155800850040d0714040ba04a69040c162091001e00c560041208543e61201503110080150700c5074940d034580074a4144c5d40e8014040d00c46c0c03400030803072580050f071100c10794016942006020b5110b80140c000402020014840118a220001d00344200000c3c0c41681810010700a000d04200142400d20345540080d8030f594090059100c1d02c801c0d041401501d03100c0108540480081c466550094000d0003443d03895850b2032002c070350020042c5010821000745040b1601600c00310110807000d0340102c00e06100904007840040c0c0074140e03a801c28881c0d949000c0b001046038040c40d80d0303000e40c4c3c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 293693929 1250 293692679 293692723
    0x110d0308071b170a08060405010e06270a0c18030b063007032603060d032709060b040f0501180e0705042c040305090102010608070b0a030506030f 64
    0x10840940501d5100b03a04916141c3c101401c00a414450781e00540d40070300400c08802c0080d06c1d03440c1074000c01b4103803540c0c4007240310192036401c188800a450008007844015640b6038205c0001d1213a0a001d100d1155428081500c842100018040d088881140001c88038810b105001003241c000781c7c40d400281c15181c1d8818982e0083c50b18070903001c8117001f44c0028400c50b0140308403903000560340b0152806580c00b5610321000078105040288c03400c050680114092001a50504d01183c4100f5801d00a0401c203c3c0d9541c288003081480910140403242851422414082501140b0495024003c264805454907080c1510364441301914071413281005000d00801074007404c00d4000000600d03100396003e016040882c0090820380160191250364039042d5070850225128021641070000c40c080300302d070191115101212181d010303582c280d040d9900c81d840041c01c50410881d20004191007140c40303480d10465040242a00c1002d41524809d070b00250303078a050000c010900c94088000b0842551030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 293695179 1250 293693929 293693957
    0x80306040e0f0703230708070e0907181116030c030201050703020732060c03010302040b060307051c0b030d03050a0501060c0308072f0c040623060705012007110d030807 74
    0x125074611aa030b0b40040c06541d000148031600048c5050640380031a1030b03400c5e43d83c0d40304071160786e506807441031544140300c0e25460707a04152658000003040c4121142d1b81d02d4403001030b016580c00340c2034241c1100010384001016040c59420f100d050f800281034074040d0700d0010765450340315414401036104282c03904044d014170210242183d200410b40f1180b429200e0703501d000403034a201d44e0000d1005900650400e2123a01d0149403500c01c9a124000c1a12072505004072001014900c802202c103c2042c80e81d900500e526542d010403204050901d1075401203010320304842030500f69601a0b000c882032101040610380001e8100b550a58044400e2a083d4072003020239200c010300740c0c20180c03c941241084030312848201008a04051015004d850600586039a011440d62000c140303500138004810503034032014203241110003400c0e0503000d240086a03d01c5c1e81449007001429105030041403850000390f02c000c1000d910f58180f5000c200725141e00050f07a10b0744000e090650006e15a10030041c0c04110800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 293696429 1250 293695179 293695223
    0x2206031b1d04140f06060715050601030b030601180b09010302010e0d03020a021c03021c120b040603060203010f0f0603050c0a0c03032d0b041e050402010219080306040e0f0703 77
    0x441c004020030030300080e40e50b0203840380354050039640030207280000400141a400c08104640324140e0010403500040c1c141c000e003600824000d44402c2c101600c032000081e0903501040304d9800f130b2810308020600c0034100c0d81c20204450803808907500480c1640010400350303810550600f04010162013511460700945012402c03c4500b01d0020740c04a1070b000001c41d4207040d100040b100130300c40e800b04d428515071448005580d24580c00c0400008401586080000c1c03401d402070220768030003800c0460125125503e21060740c200741c2001c00307151542c18041126080740d0f807040d0f006241a003010051410019a0043c5901c98950044140300c600c01241c81010b01c29400a114039a5001102e114040e01005030382c0b842e6221000107101c9410201e06044c00c2c60f01e481b0301d8000c14200b080e503800350388002c0c00e50400b0f028020000c0c4d041d4040d00d586d814164400c0200c1c00c4078a80300300311aa42c0c0e85000340800046880348050000f050b80021501400c0d003c0024000b42901d070461171312080088000d990300c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 293697679 1250 293696429 293696477
    0x2030414010f0605150717090a08010534020309040b0d020d0b07030605010e010207090e12160201080109050126120a08061c0209070302030c0f2206031b 67
    0x100607601e800c4095444a007107601c00d105488088900da410403012040f049a540141603025040500011101c8141d2030600d000708810384000e085180446d5568010a0131103408031810b1380050620070b030074408500440c00a6041002c603014040c20050181d200039034074002c0c45e8207907000e995180c500450170355800b03e80d2108130354014106401c000c202d24040701d1014080d00d0240210341804004103680d801640d60800030401a8001c04c840b80c6131103a11805455190007440441c01030491110703030745c10700200034071140744400d4104c80b402c030706440014401d403816804086a20f15107001031110230800001c42801c50500c44403604803100043d0101e080082083c075000d44010700040030501705070410426407098608464503007152100c03402504140080510003580b1a81c00130004d0340780c2c2d00a034050364010720f154218074100020411394010550249c0ca0b405041200307000d03c0c003010302da1016028042c0c20035241c02c1c00034540c8044410030745c40b4001041c401f407000c50344070081c082c1e04451487e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 293698929 1250 293697679 293697713
    0x10b040207080a03050a271b060203070309081c050a02010e1b0a090905060402060703030e0732060a0309080909160f020a020a050f0f04050f060111120d020304 70
    0x45586641d180703840000e607405800e010380468203090008000145a00c98a100e4a00320b110710300d07174035142248482d002002070004031940c1c10600766150030140740c0c000c00409482550011691a8664103010306140f809501c01b0032980c2c010f40000c0810200c0300d0020205d100ea605000c0d840e810080b000782c1c05801650012181845031000d0003540c0c58034040088a905000d8843c003546c191100400d800351688440081c0460b808180800c006003000700080038140c3c081c2c600081d0280794024410300784103103944044030201113400c4190240100d000d11010781582500d1805a1078065000301d00940104165070703040c9980c82a620301070100c240d00320f900500004140c0c3ea0a1700e404d04482c0800e41c01184850009002d800b1400b11040c00001c0006032030b40c004081c1803005c0d1420013000045c1c40c041c00415000030b2400740082c503507140d501946008081c01e880f6001c561031b04c0b00004021b500701c00302c01c00d001d9001080c002e146903900c804032084003174840700241c2d4035910390a02ca030890034102a8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 293700179 1250 293698929 293698931
    0x703080306180f0129040501110a0f1b060f0c1b0b0706090512030106090504090609060c020c01080c0f0d0b01090807030c050108070c11210d031410030c060c020102010b04 75
    0x200b2111030f21803030a4605880d00030031848803003001910b110281100c20014007007a10300401043c0500d6001307103050052542400120303980c142c00e640d07130901c10600f0103404903204a024407400b03815500170b00000010300100c3c40c0650790b5500d8510018141d035111fa1000c0c0c0740c038142100100210400c00068800741c083c2401d4240e603074400c1d184c004000c3c95071290a4880b405443c0e1080e00750705155003124100c0e0082d56400b07104908020401004120b2044101d0709281d5a10030080010390718002d90300020159009088002c10680008d05075403170003041c0083e064801c004105070682c09005031495081d14900c000344141c1c0d9900107846503c10f940001c0b480303100d1134070000100444503041d11b056030003c0c1e032040040d460f803400a440ca00c4401c00018801e40c0c01a0300c01c8103a003480d02107505174802034004001c0e1031040703443c0c160904441c010810000381c2c03170380344404201508140c82500700c2c4410650000286c51a103402424a0f0705003c1c2c07004204103160054103582c13003500300a152610040c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 293701429 1250 293700179 293700181
    0x806031603150e0106061e0c17091305010605071e020a080601140607150203100329060d0f02012715020c0102011415010504170a0b0f09070308030618 66
    0x240b0340012401c005560808074101107120507030200c1030207201c04949680c1c0329800e208000000450307030400702c411048100941d40546001150b0800c515102c01014513055907a10405481408012001c040041315014189030042000b244c3c41030807600340c5500002c84d044581601c40030341002000d8120065404040c10300302258100740448c5440c101d030704504030320500244a80c103120846c010f415010f441c20a202009801007402a002198015840030840c01180c3d102c4da182e10300200448030340c811070300c0c80015000b0085141c02207950040011200b4490080d01984c0e1054190009000241005108010b44070100310503803a080c82c0b0f03410080d8030503130306896011602102c0c2140304a60014413555400c1142d40d40184036642ca00341c4080c0601e03c807540c68540310030903044808552410040200030000e50b9a0000c2016102004694090410790034641481138130340501074001c183c58280702048c401c2d6100c00041078021654025105612540d07540c000445100c1000701740c7c0f16000c500b48c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 293702679 1250 293701429 293701433
    0x7080d03020c060a06080a140309130e0d14041203050c0616030606080609010b09010207121203050105060c03030609060607050105070f020708031804110c070e010509250806031603 79
    0x3070040c0c00300c003148404494140c1e40e0001074405507802c2c4e10034107001d6042a044500400c02c842c80380310403420080c0031079113490343c03130408160b44d030f124410706041807035035a028001452801d00ca80c4c140000940390000c801400000c2c0042507104078454004034400f800801001c0502038820360303c94416000c16200c00f0b02e0300b1615001d21407000740816000a14010002c9081030150001c40d001e0070b0090180c05e06603080030a030b100240c2c881100075056114040c000510280540002140e103442031502d07040304001c80c3c0c005001c1e030f8010780103107100b48010f00800422000000c21340c0c0c3d014a0032508e414264460102061041c0301d03404c40a0003650806041001c05504058403140030b6a0703980c221035025540d01500f03501c070700401c54541200c1da41620911210701d455002032140c900e48003610b61a03c018008418038143e40303940200901c0754040010080d521b401345050b03030312a4201c011442d070a4010821000c20f9444505540c045c0106030010030810b0b1000c00c0b2200071504c03004003d0040307544038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 293703929 1250 293702679 293702681
    0xa030e0a06020415050c030d05070e030304260f030a0e0a030206071b05040b0102070e1009090b09010b0d08090405040c051002100509010e0a0f06020d181e081b07080d03 74
    0xc2c040c09900d90706a4030840000780c81740f811034401b10800009941800101100000078000240c011010004020200d2403540e4041c0000c1008116070005040e07014060062035580319200a400344080c2c1021100b602484004800c41d40c2420f00c0303142500080702c00000060a40c402600b001c0d411141c013107072490400c00444012208000c40402200805907079200b00410b49546d41859401600916000c00900c0c9815041c2c48d0421003181c29181c125881c0d0000034104c8401e0b282c10b80d2069281018010351840a2054058117401503503009007035000d03a101c064440c403a0181c50750185075a000054248401e10342c00502a00005051010941d0310341d0000b50b45050b0184840e00740c074507080111b030700e4003014413840c03403403505290103448980c05075102d0504402180c0c1090350020780820001ca18a0910300c6681420710710700500c03004008071820000900508060084030142c0210064800b01d1920420380d901c4980580c5042090484001c1e03180c103050140c1d101c0c003000e20904485808884d01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 293705035 1106 293703929 293703937
    0x604110d0f1401141b070305091906020f0c010908060c090d0c0f0315020a090509090313290f07020402030c12040f350a030e0a0602 58
    0x200381c0700e140042d01020520304103a50345450501201503082c020681000510303100b0070381401004058160b42c820007802905004003c00d00c1d24156454040785410b800c035850791100c9084c0d4441c0040d559176402940d2242034020903030900f0440d44101c2c42c41048403246030040c90715448018045106a1060054039044545000804085100490b10000500c5113401040c41070b80f45081102d031603110a000e801c0340d54010040120b0040d0700c0351100080c0c91044950b60581d440700001c0e00d1641c400d041081c0c83d400341d0550001754898107104600b0440221140d44280d04000001504407803103881019524110288014405400c0641c05160b01001d051203840c03070407008282882e22410b088504803240640071300f0030404c00c00143c10201c120b0344142103109001031165100c5206002601e6045c250210205148000521039000502440000707425100398260b02e040072030180d48 = true := by decide +kernel

theorem cover : BRFrame.Cov 293525179 293705035 := by
  have h0 := BRFrame.cov_init 293525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 293525179 ≤ n) (h2 : n < 293705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
