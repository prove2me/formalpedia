-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:42:44.164986+00:00
-- url     : https://prove2.me/submissions/1aafe343-4b15-4872-882c-78fe141b49f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 560431654 ≤ n < 560611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 560432904 1250 560431654 560431679
    0x20303070c080d0302070302071401140c06010617040803070c140d0509030c18040f21080a0e0123090111160618030509010813051b09090c01021e0f0601 67
    0x152242d000703c0301825280301090b01640030368400540541c02050701000900f141c22041d003008207051501c1c40501002c808403594a400c904403d04042e80300344018011a0b40000c030070308002a0b0741400e01000e1500381c2e186002884024004020031010381d68030410840c50820007402911500191210149200f400a005411012069109200304841e0b940c0034100b08200030829800004682a6551030751100c444a0311103442c100c4142c0d21010b5030030464000f010f0400e01500c900c8e03a804405044c0703150848180d038010080090f1340c0e403400104900102010400303122035032081a0f00741c2141d48003604540140402000c80c10280400a1803859244c0c02c0140c0b1001148903140c1002104034109484c1108038802000502060080104e00d00b50760241c1b102d82d41c0440c2200c08046a541e80d42d90b041d05210504294040400c001045541c503490010b46650740109140001d09104810000003503403106030391010b034507120034040d110410600610404244200000444204e540d548000400300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 560434154 1250 560432904 560432909
    0xa1206090312240e2511010f060303120b1c020f1002062a030105221505042301090b06070605091507032f0c2a0d0f060216020303070c 59
    0x40d0114502d0104803100c46100c4c00c2e00641c41c1d004881800313242c5043c010740b20880202d1601c1401030311401e85065010034084d41480c0c00c0c0c50b540c0410123914514025040c111406c01c51511103003000102c10381911203070007003271f4218044d86401034040c40302e00224104006890b406d5800c0040f5070807203d4625000504a030007040f60b10101c50004d1130f95010840c41400c080100080507204100401041c80c015402150004222117a445002008000303881180daa0358001c1d450a01c003040704010620745840740620005040340701c910411500d0840500403801402907000d182d60702c03070400d000c64880c94155007026500003005c11050515105c4180d84000041c0c614403404160800111451701c00d01079001c0e800c80c00084000014502d948030480c80c2c100c40d8103c10066001d100c1e400a601040020510403500d850200b50070441c644c0b07910307141c1720700d064240b4000c1c140c0400d11800508824806002a60041d45c010f850301e003031011030b000216000714083c0d030612011810318148269880301d0005c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 560435404 1250 560434154 560434211
    0x409050a0c09060516060b0a090e010501230108040f0309260105060f0319052d0d0503010506071e0c0602010507030606020c0a030201210504080d0b0a1206090312 71
    0xa0302c1e0364408003180e8600c00c09460001303500301941643c001a102c0c0c1c000e80421040140520b1409480d6442441110200030010915a4540d001003120040800d682c10b00764019205640320000340c040040c0c40c02201410040c0580c03280c510450902d441103140340040d1042d12201c4440859001c5c0d81a8543c000750000100e551070000419a14500f00805410881014014001400000f40700200c40c10b40c45d034040d16a802849504140c0c5003034070454422845880b0b1000c000749a14211036454100c00400c0780062140c01c0006202640ea0035003680d03819548800020940c414a588161080320741040003401044116004191a80c043d0051886180c05a50810a50b541c5039801c03a50346030002d501c140c021003140b40a1025521030035000d1060401824108801032805501c403048900031102a035440714003164032070b14200b007409640e8811008036a0030321020b04101d00510240c450300d10007003103030383d8503005001003501805610014001f8090204100400000300da501200c03003c440e00d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 560436654 1250 560435404 560435417
    0xf1404020d0912090621180203030a0306030b060a0e0c0a170c030a2016030c1712092b1115060f0109081216080a021c0507020f0f01050409050a0c 64
    0x24658820100c01d400200305424806948084545070340c01001f0071009403500000b0303404000e02680701000203100e22003560360001006071545c1416826403c02400c07091259000a0041000600f42c4090750b411107402c000c00c0303a845000101c2a501000020042c0490300074a5080026600e103140c0a9481111610b00c14820003188003490f840350085400a0307002e10380180104002105402c3e10f2100c0700d4800d003014141c00a2584030f5507109100b100880000103000075818100301444103407181c001e90f0303200040a68016099856164104000c2c0041001350886400000940302d100402d2001d41000d054480d016102070700182da40c2821a4424022040350880c0c1c0c0a5512425540e0100d5401c217019144141500c01c6a0000342d10480140c440d240040c03a21002103500780f40180700b0410a03800504d2042160481032042103518030000007840380070302c000700240c3c5403600040c50032001113070812110002003006890300c1c016600244e011601d81070412107105815404031400942c161540c0d0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 560437904 1250 560436654 560436659
    0x1f0605010f031e050705040f03061b02061b030703021b101b0e060c01020910020303070906170609040c17010209090901060308070605040501060b0d0c0e010203040f1404020d091209 79
    0x1d50680321900b50303c500e5400404011030180d40d550b4000c1d900108203141003458140c0c0d900724200c40c1c1d07041e5003064445503a00c540382a14011000b10700f02000ea281c0c00503098520303000c50200e16942d19040c40c401e00a00001c0000c2c2d10074800c0c3d04840f030396407041ca0300101d03049603501010303034a0840720110a2010310b4845c0003581c82e404000e260f01100701035943c49882c1003124060102c2c54100260410f103e43d001d0200300d00381c0e590200040705680c03031540210340380d2525410041402c02c9603800328007401a804103441c101045200300581c4100c05941e010355a459514241485402c698020f000880036014154415030064001f4201ca01c2c040325802170540714000d586080761000e1000601da403000b0000706000884a8000d183d00c14082c070300002c0ca2036500c0c64081c80c0343d80329078070a414455544c1380c40e00c0d08a80103022290144800e00c011410310b405e1039601e95443e4814082e43c00d80c0f580190400b006da90b1260101e41d10707115505814412920540740c5034070103120b1003900402107001d08038003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 560439154 1250 560437904 560437907
    0xd0203091e011a01050d0f230f1506070f060501120623130c030203010f02040e0a2007020301090228091503110315010f0f090213090e1f0605010f 64
    0x80c1810590f038982d030543c4803407606005540a030f0103500710060182c3c607003142003d01c1c4c0c81c521030805c62202500008403000d1180982004103d4000c2c441c1440f140541705008503c81808a202c0e8004410364119559131541c0c02c0149000e510700a00801213400c00e8008516400c1c00404401c1e0140309010500041302d0b500b409607107012004254180a04446c00094260444001c03052070f200d01801081c001c1580f2074001c40d081d00c42602e0403410311600024204640101c0030390740c0d0f5118401c80030400200c094003a0b00e040240112185140c14040071034071100f955020b60107002c0f0141d00401c00e60004101d039039640f035002221310400c00c0400801c11700059500071030094112407e40e501e900c62032103080d5501e170072040921516686d014880d90345803041c2040d402c03031001c1c003a15a01d10b402c3c0800d80b9040c7c000310400c0040e00714010780d50050040002a05030041c0302c50030340c0c060232000306d41030002d40651854125a44210f60455101041101c501c21150b8010021307503200781d0b0380c4c031152801000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 560440404 1250 560439154 560439161
    0x11a030708061512010e01051501030b0d170d05090f07050a0e060915101116030c0e15090a050403030b0a0305030715020f0f0c010b0f03030a0c080d0203091e01 70
    0x52050a03000b1a0010b914007600401000c41007000a02e2034203d40c0c0d64200d00c0c5d085030007217a5100c625a54030b0b030500003440c0c991620b02c0c209010900c2e080c0089489400407030480c13042e050b401814035a10521150012031100c094820003506203208201c00d1038103030703e80340d40c0702d031981c80710b40c1c5600500c0c8020440381414541c18058400c0b40c00c80e683c16858a006101340e03440700911011886861004202e150766825030940100042c0f0740e20140300c030350113142840c140050b580c140300e00103000340010000109100a81c40840e0303030700c0450a18a03550810b00c030001d03100d1001c035030380d00840784005c20003450143d50105000d64005d507410001d01d4140010b001201d0a180005821a4414403142d03001589181600f107903a0ba022201500f025142c45400449404c60189480551008104030240540904c10345991940c00c0b0741020a68140d14042600d80c840d1285e20020840400311300808c0c06002d0702213401240440004540c1d83c50300d0340d0859181c3e03002020b56840000e80040500b0588030500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 560441654 1250 560440404 560440409
    0xe031009153606090803090607021612050c0307030b1f030f0809040e033105150c16090204030501051b1801021e06010501142104110a0305011a0307 65
    0x10302007038000140c0114040c44070301d031240400800002c41c04002891070003059240751050031955200d0a0001c051810b110000303140c20215031000086404428021828004803503807010310311001e05007400d149040c4040c440d50340740c00d0f118450b40002040301410328130b0710448006a60190000d010784601c40881044c0c440545250804070480740030418040003400482c00044c4002400b2800980c410700307640269554000ea450305884100041c5100300d0001401e02c248103290011905100c0002c26500354040164040712001c10b4425004808000281502c0002d00c6036004440d940d04818002e580240401c903465400d0201042408081d41c1850303685010184e242810070f0380310b250092010b080d410040b41140310380e201c0041541800f40214241c14644405050b40f5810180050107000c500d646001c0040d20801c0800303851061081c001031243d0701d4480d410700b15111800c00007081d950022002c1e0b4008820310002040142c15445044260b40c440603104c509200d6100b0035403204000c1c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 560442904 1250 560441654 560441681
    0xf030103031e02100203090307061b1709250f0b0406030605010e0a0504020a02070302091f060f0504060f0905041409010b0409050606101707090612050c18010e03100915 74
    0xc00d4201810581354010356803145004017203034201400354a1740015034901714034040000001d003554181169100600d688103804905400c480c900740710315015503c954401c80b103007409441c80c00b01c660b8204514101030062181e004044c90064031901c03203810300d600900c25100401e20f04035000505501441c0202c1e00b0030304c004e0004404904d008280006517000030a107801714001c0004c00300042c2d451903044d03030080b45100740c642007841042c4141c0004080c650051010b100e030740901e03443c101d0f500c1000c0f501501c00c1440c152040340d107010303400d80703001c06540c101652003818100c101d80407640200c8810f115014110081c0034481e41e1500380411594085c1001c1e181d070f00310000050075410f18410600b070072a0030346080000b40842145051140740260b404000082000c3c508220107070303204560380112824104104070382d0601d040e800580340301d1034144030a0404d0f0107010300c209a020300252804141c01509440d0f2000341025101c00412118508803a01d1070b0b03403e83da03815800c2c0d40c0300741c17003900284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 560444154 1250 560442904 560442913
    0xc04050f01060804030e060405060a0e030105070201060b0304080a031104081f0506060405040513140604060c0e0109050d020118090c020f0a02010207031506051003020304022701120609080f030103031e02 89
    0x1310385007102d5404a0301e400d1a0024801c110001d16600c2c0c4030014541040240d0b600c0c00788400001c1014203544020704424210783c100b4400780020380740801141d0f04a540168104e40e240388058040e006081c400103400822240030500151186001c00d0044e02c0202e0b81c030f0f85803d03198902072650b003110425950f0a070011800e010602c51401c1603800303aa041010031550059200c1195902d064036500d00388541220780111080c841081110b000301d001000d180c0c104050041d0b1490002000400b40b84102446010030b14a40b205590203416580b544c0c60148038455502e60701c600d421005420011764010040c400c2c1c0318a1902c140d400f00320200550b134140e001e8441c031031842c1c0ba00fa81c1000c12801d030a010310b03138440000603959580e041d084008581c585015840b0f192074010890014241440c121030404a2558844000c82d1524100d054815555803030032038007950b0030a14001c050f0414020b040c000001409051600380d04c01450480e40709580f40340106908600e8041d00c80e800200a0025a10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 560445404 1250 560444154 560444161
    0x90601022b051b0d0f0e0f0f010c1b0501180308121b13050411130e07020c04050915010803040e06040203150d1203061a030a0b030309120c04050f010608 67
    0x60400440c101c0c1c0c001c0c0d29040d420700c50945a0200c110080082e0035045600280c2c010503050781003055184082c10606040810f45070602c04511801c81081c12039100354403800000c030b8160300070440c84801e940c1040c0c101005042d07803074a898500905000300c5011404c004045504552500d15510a1325408507101e1b003413161030f04000b102d8030000b40140900b80504642c040301100b80700040c7c0503100c000310641d01624a8042444111544000b0300b00144504101429280c0b050401c000e003241d458200046c620b94032072000302c3c20320400389007a80c6e002e41000f082c00200440099500d01505102080741b103166a210311040d41c81c440d0381b00e0100c21900340000503000d49025401795a00080e001140081c00540e10b001403000c411440c0b040750b040f420b045101c1a01985481400081c00000d030404007444c0501000003410b020052000e015a516403862106e1a1824820b45190082c0034200c61858a50f4103155900d07284c7d8881002d002e14640f100041c041e1034180c00650498072503031140340d09600c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 560446654 1250 560445404 560445463
    0xc0b280504021203070303050109060e04050d082e0503070b19080712020408031206060f0708130906120302010c0c120e15160204061223120f0909060102 67
    0xc0040050f40e10072051a0460f040c5182400140212032081d0307000106581882c62a10841f0800e030090040b21030321204001c0019000920203244400350f052a00881da94801d251200d07031100000d240305401c02c52a0b06901c10140e06000081c2c4034114241c7c2c1c0042d0310780c07071201d080d4010740551501c1c000e94460f000740b049006800450b00192549428010012150f0452082ea84070790300c030030780f04d87c0700184106013031400c030a285401c003400305d514a10f480d401c1c041002445c041c3d554040c1c010840000c070680c1046424030110000d0544060034818140d4624007600b1101c5c404806134050f50a100c031510420780720f440c0c0b03200d04030341c0030580b01e50301043ca210032101d110b10740b803c040d0844400e00040740e1020100c0d006e841d112001709540401c00000384140402c0ea0100d51000041020303070036601c0700042c5042c0084009600a00310720310b03032481c83d0181c07915000c4400191141035100041e10300851503d8401002c0c41e42c1c080e1140100c5844d01070049aa600f01c00c0c040140701c00360510a0346251 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 560447904 1250 560446654 560446661
    0x7020907020307021503090d090305100b060d090f03230301142106100f0f1502100608010209180f0105090603070305011406011403100b090a080d0c0b28 67
    0x240d0740704580c00c2940070350201d00451907030414110016004010444c82c18020402d00001010b0b034540603602501d917a4900da0303591405903003029055240c40c0018000d8440c002035603e0b45000e01000d01040b51075040007146189a440181c1c0001c0440e07000401c3c144600c0940358400302e55895551441c0e1074500d5890003a100c81859642c003501c004d21102520828040791560078240c8000340c0307441d05041404042c0200103034045030402580450801100f10410750040407107844a50b031003d4000e40250480c03c1090741c807401d41200b40380501c040752107041503010342010101550805c0c0511024031945944c01030841d012041d104541c3d005000505150761610740144026048a9000c0e0b100e035503440c00d42c1c4d0703003c46843d4201c00c07450800034a507a100141c0c54819040812003840c500304204035074660081d60250014110001070400025242c20a00000410011059400d155520400101041507059041d0382c8521640041807840d043d84001920410810140440b888034071484000a07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 560449154 1250 560447904 560447911
    0x10e0d0602120106080c160f06050a0e060615030f060d02030a0302010b040b220c1214160e2413060e030114060d030809031209060906130201050703110709061503050604050408070209 80
    0x141803a500d100c00004109e030140724051030b00301c0300118a260f0689a02460128014002c5120b8650b444890f075140c00207408480d007040f28440c0a0b1500e94440c0301259101409110003901031103001d803844149035040d4880c1035603510890b024804e20f03240d4400c000028100c840d0302d04101c510b6102403401c8030410307840211b02c202c42c4e0901c09080200400408203c035031103541000401d04000400c490b0480201400042030309038141401c0103640c000225161556100050520408503005070005400c01702c10703100c07482c9107503d50351000c549035803004000407590b00003540203600b170052400362103490130000c074031911000e0304100c15191251400c41e8004005000c40000c3c0c00104001400394801c2424a8031814a050050005040901c1c03001d18140c002001c0d012040d01c100d02c2c0c080180c3e4480301b00d4207181d81619040882c0c8405c040810f0400c4801d40c454a8400e10b40000000c0010580c1c0c0c02017480306c041c0d2410002035980e1b07000e0105460040301c0c0140b640300b042199000507d01141c80603003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 560450404 1250 560449154 560449163
    0x140618070518070216090f05010504020f1204031202030103060903110609060a0c09120b040b010905070c020d140105010f0512071410050403151e0b0306060f010e0d0602120106080c16 80
    0x400a0010781d080d0030b01140390003e46c0e207161035141d2141c05091600819004010650b021450060300c0c0000d48083e0103a90303d6034003540406400724080c14030803c61803c0790a0100800c42d070380e594038940a03004020240c011000b00d4172006260106800104420b4840c0c7c4510b4060007181d540e540c0e000c0000c09898442da01032014059001c0764100c09a840f00ca440c81c4140c00755441c03410301d400e08908400b0160700c03140405d07081004014801d0f40c043c0c1d0340301030640d05844900305003400b49000b0359403c03804980381900b07600e09000010b03214001038481d001c440050750f1500329910700d400010f44030b04843c0642c00140d00300c0c0d41d620055007800c0d160218110141d2401e203040507240d80c0d8041140e00c00072a0880c080e92111040d560051695000c3c44c1124042c07101001303550200c8000ca40c5030107008202d10710400d10309954800590054495080410000305800c182c1002e0f481c200c0000c0d0401410414404007880c004196030380120503007406400c5402101d400c1c10752910b010a88012402d20856 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 560451654 1250 560450404 560450413
    0x309060f0a090c15110708010b09060d1208150904050604060e0d020c13110d0c0f170402090a0f0c17010501030608071a040b0319051b04170a1406180705180702 70
    0x43d9800006c1c820b4078040c205000000c6071380343c0000100424414042c04240c03044501129010020315120b0700348000b10f006061916003903450480d85031803c3d40e00c0802030741080d510001c02040000c00f242d81480780740b044004218101030744840a54540c0c0b1414042c4c0581e000350361485442c03412034085400c40740c2440e00801c040c09a0b90a07600d968011640c0c0d02c007001c0e1600e40010b03441d40c210b413031246070040920b4070104a0800b10101140150041c2c030190190b07401601140b0146403c0e005174203007104d1448d0501412029410081421040c903407045130100c007410003c5141d41c4240107038401c0301c0303466000b40080c50500444a150070f101c10541f100005040000264003244540078500c074428103007101c04030803d4038be2520140c4400503da890356003298022103041c40d020714180c9080d100c01c3d0202100c00747e0074004a611745011110058064401c04400e050300c104001000d41c426425011203445482104020b5551420b031802400d502850031102000d0011031003108036803101e01403045a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560452904 1250 560451654 560451677
    0xf0501030522030c0b010b190e03010b040c090315020a020706050d1b0c020414092a030613050f010b0d0807031e0801150504031a1b0309060f0a090c15 66
    0x3540c1065800d002100881c0c003612580092042c5c6000043c010001d1420040c644005800225125200c0c07940d090705005000400e000d00d602c09500c10082004003400c00c000d40003949001400400780c0340720498040310b03003100f641452511802500c1b455016071b00140889814944155610f4102c07403071501106a561107007101204a110b000511161070f034868a80008007070050005a820700000407200c2c081c0c120501031030100001d1001015048801903000d05240107408804280180191661500c149010301c094041c0c0d211005100e14483c008a488102081d09a5821f0303825540f801c0e82d01ca110300c0054000304280f91300410b8228424600300d60190f030420300c2d00030808001c044802c0042c072480010b000c25540450a900d41c0c50581c10130368200707032441ea21002c1ea039404240007042c060110f0049040240c6203018103441d59a0300011a88a140045039281c4d128400c581180341300704080c010800328031541c410b4100d220b4104a0854850b810220001444220050340c3c804100011010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 560454154 1250 560452904 560452951
    0x1d06060c01060303050406110118020105090111060c090301060e04200a030212160801060b040b0706060f0311030d030c0e0f030c0423010b0307230415030504150203010f05010305 78
    0xb403801a51003604c4071501c2d1400c00700001d0110104c1801f00c1e401b03070b2402c00310003007148807030070351031010381e42480e2441d5548070150048039483c0c0c14400d400c0c0b0a204540030300c51056580b102900e0460400c0d0300070002c1d07a540c6c6101c103c4041d425140501000401707045c0e1485102c0650494442d400b020388801e42056580c2d01090f82601100703140e00c403907000030508640180302942d100004190110091240c9414428000d226118610030310145441c0080d059040104d503401040080011900140c0019900e04043c0000120034030b48a10034001d02242c840998040d100700e00164545c2e0343c8103c0101541028002403c0050608a50606c83c07008082083d0351540221082c160020f514881a00c00e0404610b50662060b00513940c3d8000500070486c9080d4024040c5806400501d15140405100b40c50801948103980104c4402d40031460041c0c89150540c01c9540214491842c0021801d003071030540049000c2030262100102c503045c81017110b0341c0300350030440c0c0002800130a002d080c0305041c117 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 560455404 1250 560454154 560454161
    0x7050c0d030210050108060c04091e0c050a020f011109040c0c02030d110c040902010507031b0f0308011707050a1a04091505030d03140f280f060f1d06060c01 69
    0xe00320010b030300c00c59800c01680114040d0301d004085140c002c0200c1e0600c4241c0340070600031805a00d00c081d40c0d0b006c01e1120180c40174007a200424911400708881c21480e01d008205510400c404009803090a0b402825a41e0501c544050702c00250062030034000d4007002c01c00a003031a401c070641000000100400980d50500400101281c16155a0201d141140b501e41c240803031500c000748900d01d0000c0b4880035036000b00480d10b80503030501d418400103010b0000100c1c1d802c00880c018141c02c0f1700008100030150081c50550580d441c16008a081c446c1000d03000344c1c1c903813250003400d0b00003041120030080781705081450041d5001c161042c9060645401401084940300c50010400400b90b010801c0300b42428000882c20003094501442081148100480c0840c0c000c0c0884055100000c00911154a2805d24405204d03000d10b860024420300982c1c0b02c0540210a21104418035040c000280c940215103030a04a507400c0160050147d5001101003001c040108010340bc20000c000c4142c04400a10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 560456654 1250 560455404 560455429
    0x5121608010507031508030403060914191e020f01140d1503020a1a0717040b07060504030311120c0a0c170304060506040b0d0b06010201110a0c021008041707050c 71
    0x300002072510b44201e006003580c0c80064111034903244910144083c2c10f021085400741c0e0340290380460700c4540c0f49451a0740864411524078107021740b141810110045030400851030b4014180b5070110300884443c50740200b00240000e501c20608a403c0ca519401401301c0c826200b8422600c90030282c5030144d0400780e0b61100b05222801d9000c99041c8114604220345101500f02d82d02c08124102017003105d02c10522031740c0c07400b418104121403400e011540721000c45014058882d03000361a041e96242143c0984020354044000c0303800d01020712002103848003074031410889a00390040035260a070300c128455101c00451f0703042121066407400803480d40700c14844108891601c440c0e03240b9060800a00711800070744164482c605005207200c40e5520007072a04030701030304203035140300903195000141c1c01041d200c1c810000f9041c0101c1c14081d581c2e040814180050b0090701c0070240704000c0201180c0100303040f2802403d640700060020809010403020304080d900c15421604c00040110000d0b070f0418291 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 560457904 1250 560456654 560456669
    0x30c020103150e010e0c0a0507030e150703170703020f1c09021f0905031f05070c02120a0201020c19150e04020403080405030f0a080a051c050c041706010f051216 71
    0xc01c010070a48241d1480158454141304035903081407c001c000529a12900c980601003102d45190401955a2049440d03441d01b050f840c6950381c0d80755468068130a4402401c4031a84907481c4002400d42d60081c021100f841d0b641409507840d00d020a0044c1c041d000d0a00c0d01d42402d669110341e0b00c001270300c0d400c1d40e500001c1c90341000700960600090b001440c218141d0010b90180d0071810030b01c40c140c0c1c0170200300365200d0300b18480490180c7c1c031030038212030340803c001c0007079403100c000594168002004035101c001c4e00d000ba402c1d00d41e46140c010612441c403042c0045c0301e01203034000d00e08000450360440e1154044080f03280190300350380140001400ea800580041c0c0f08800000f03020402464100030328074400ca114006082100324540b80c02c070190040660711303070502100140c041041f003407040800c218007079603020400c0325041003069007480c1d400c68020003442011030101548040c0d80040c1060485102c100c2091059041109001b00d844524000801a01c5460348050704e02c1c00c0b2101c100d01030040c0c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 560459154 1250 560457904 560457929
    0x2a0d03020c100924030e1614090c09040e100e1e0609060a0c090911040515120601030b040f02211806180a0b010906031b060c030c02010315 61
    0x8000402c560041030301ca0a20912441c603e04014040c50360a51080398048000304803141a0b00507010380181c01c002c28a02644d009a204003030742000102070780344c1038521103c2c491f005a503865007403107103010003604c507001304800501407941c82c0d180c5a003081e00300b000c0d08800d9600003030840b00038100361403c1c140d040e25543c204100e5082c0c2a4a1130103081c0c0c4900400004120038203006201e5529104064507500e0040d0300c8401c034042c42e074000c1381481d00804229034204804145154482c0680c1c1290207124071400000603c107010021300c03030035030302e071807554401c41d206d651a070302c00560017442c081010b2500182c4500c0302c0070824050344003400c528626068100040003030780c030402d484d410b0002d01c50020313448400112012410700040f01580315511031040d0001c58000c13082c0900c0c10710b04120003001c0645010020135541015008141124410721000c0300e101400210301e0000c070004c1c001c00c0c000403003411244001c2072051880160050042c14000344040c3c050100020005c802d070800c1e01072404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 560460404 1250 560459154 560459173
    0x60c17040305070f0e06060403080a180512010e060a0c021b0112050a090203010c020303090a031b08071b050102030a0c150621020310141b0f031006020c010f022a0d0302 74
    0x2502440c076503000c01d040790306a08c2e090440d9a580d403a80a20440c40301046032040f101d40d21000c164000f14003500009060304101101113440c03c3c060410083e503800540200c0c0702152000010780101c00c040d0352160058501c00d64001000c1031001800c840d014100000c106940090302c1c0b9500c43d0f10300a14038001e011580e5849801031600b507941d540070700c030210352082041040070302c030100349219440e0345441c04e041040d20305602c4610800c11406d01078503034440010702008020400803684403080708030030850801582c9500580c3c59000340c41d0b410022940201c1c400c40020805000d00100240c0144c0015141e40c46080000c43d94624800a5003004c4040a01d1420b44c0390411400084080d14030003840441e080c2030411310411000344c1018001100000d5081d40944840c0a0320449004011030300e440b4079100383d5031001c00520b481103802501608418020551080b0f00c45030560003150028962421040003000d00e100340326040c207048054405010310582d0b41c412024400702d001c0d42c02001301c0403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 560461654 1250 560460404 560460419
    0x90e04060902180c0d09020109211e0818130906200403020a0b1b0a050606120604050601051504030804120303060506030403120504140118120504060c17040305070f 72
    0x1c0019003050f20146000200000108a00d0444203601d0b480c0c00c022544410034070050f1034102d80d40c0c01c5007900c80312030750648050b0b41d048001618650b003e8031000f8121040d44844414414000601400c48041089540c60740307070032000030075150788002e0006241c0d154034880c000111004a001165102d0300c40402003040004410261540004000340d81d180510b90ba0005500030514400e4680d4504041018202286034041080c0300c0303141c000981d020440d103842c01544400c001c6030380d1445222500b038001001c40000a15901c00c980c002c004200ea81d081c40704020381c208414055641c1c015003000044000360303564001d04020036124580220209491402400f5905140c00c514096034040c000c11010aa018140c0310400e2800f00002501d0b84541c1410f1010b10380c074032580403282d0309003a64028960146407078200146c1c01140d20058a045800045426129500c10000055884c050788400300c0ea880350551008480014141c0c0703001d130b5035560303a802c0040c65480b103840c92501400412a10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 560462904 1250 560461654 560461669
    0x110604120e0406120605040303060e130b0c07020906040b031609020405031903140304020a0906180b06040807030803131a180d050304030521011401020c030a03020715090e04060902 79
    0x11801202c040c08003904003400d16010003600c0302c001c1d00b441e4881c0b000c1000d040c00f0380d101e040078040341c4c0c0880e0090310348500f504510b40007290040315845456800100c3d6060040192441198001c04d003191680302c00b02008060202800300e02c0e450301404080d00b50200050590b8002019502800340c2c44503c1c00d0201070610008013182d80161007000d2918000940c0060310808000780820310030f0322a2185c0c000f1412540c06500481d1415242500100b80c42c440c40c4001069105010307800d1280310f8446c8188200f0340a24461440203601848003400081c3c0410061540111840901d5082c03582c0b5482e1640100510700f81495407062010920004508481c1d0644400444400500042c1491800100745120050002d801c001c000324000a04e904000e45810100800e100c940040b96100c0c4050140383e01c1c03024800b800344c840d03908103020a0070f02165446403190550050b000f003c1c908603405d5a508401c5110800708403080b0070108070441609005400740b400348800048030540c6106111a5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 560464154 1250 560462904 560462927
    0x170f07080601050105032404020409050a051b041202033301080a051c030b040e01061805090309040506060c0d02100509030903060417130311031519020a11060412 71
    0xda400500c01446140d03042030442c4d070000710180c80100c0001c540b00c600c3c41e0031004090000c1d0700c14000078000984800c15040507000e0004004104403a496000c040c8580300182001101503200611003003201101600ca90298503001034242d40c20340d145000c3c002005481c0381c0051882c03a0201d0352100e040031003211011301602c00320005000a00c06520303401c0d500c800c0b0308060301c4032000c4542e600c814244260000d4403451000382040c88111403803002a170180065005040e111003921192066425075030180b540141c0003140038510380498a814400034050040102e60050340c02c0210315100b1000f040400740042840c3d000e81056429848402c0036208041d01070752581c1d00c1440300c3c00c2503070340200315641c01c154010034001c00482c041c400e8010500031100442443c000c111000020721070080a40f0740220002c809954102116200c5444581c60685441000403c0103601c0d140c42c904546c01460782c94064200324181e6202c0149041c0b03032190031941110220007444a2410b00c81d04030440b500b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 560465404 1250 560464154 560464169
    0x20a030507020d08061009030f11011209080702060904060b0a0305091207021e04110a0519020106080316050a0204050c12070e1302030c1303030c050706052809170f07 73
    0x5100303c01000082c210000541054807450101c001180002d000701041002140d104c000d09001c0d55540c146421451014017619000c54142c2d442030700d0b40c0d100761059110559001c0155410007000b6000d001c00c0c1d401114410750007a039a2600894083c203140d024044407184c80ea0007180b245480a180740c01d0100201a10102c08010b002040069a810342c4205011615448060200145000050250100f90010403409200061500b00640d010005003900c1c007100780a103250003801c207022400c9454a100300d07a042d420521041c01100303500c541010701d20f40214101c1d200b440300d64000808a0b102a40e85064210000608101c0d000808004a0f4040010308007800383c0d82c0c10701c011555500b52210030544240d80003001810030000038094a0040c0340c012000d0300c10b01c1d140e18001c5e03e0010604000c2e11680705190313002403072a10400840d000300d00e003c030031801121028a0214880307840705000a0901603440c02c00f1075884040d4a40c0f1070250341c040c0c020006203031100c5200b03080104a4101d6032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 560466654 1250 560465404 560465413
    0x3007060302090603041509020a0f3201050a0905040c120b030705130b0102100e0601052b0f051c0806100c0f0b04030c1a0f0c03063105010801020a03050702 68
    0x2942c1c2d41d4035020b584d07000b50003104045028012400400040000f48402980f1040d005030100c0d120154001348000d99040f040d40c24110301100c664084800b112202e000810154000a4402944074201800d44400d40d0704292050548a40008098518000140c1c00040b440a555000000c007405a003012000a4014000080c00d18000c5010012540c0d000b20b202600c4d02d003610a10391081124848241c07100b00708200c690b078001091601c0301c100384246482202c804c002d500c1441e80d2140c00d005980c1d140c00e000c104900302c40d6a4001d00c0360020380140c54034001c10034500000d042195031079011002c650344500e401e21303200c8c0c00c11803540300b0140c0d08810411400d4a2000041c1c0c100701d5981c60941094401e01a940c40e85402c03a40b060301808010020920903210071500030070111014090340300030710510b80660b520340313840c1ca103800202c4500c0c1d482140b1040d5034003804281e00c3e83d2038504078103088160301e8003003009004003511401ea20180450798000b9642c4c0b4900d03890311071160080301c10320162 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 560467904 1250 560466654 560466667
    0x21040b04080c01270b1309050903070209090d0e0906060c03030a0f18080403021207031202010207030e010c02061b070812040305010b01030b091f0e04050102130e1605093007060302 79
    0x151401c0d2124002c900c644640060706c080d90490260642c0020080c1d1001801140707441e050b20b603180e40103004100d001c2d00401c40801c0346038034082501c40d043e81c00d6540380318072806003104000f0884000b61440da00084100840b001d240f00a000a5105284000000c140c50040c8550304044401d12481d44084404d2043c01c1c40004103480112000c6035011203e08603840700305840c81b0b003800007070750001344105020180c1e00310b05078064003d0304400b40640c40341015160784e040107503800145010001e521a00810603a1200d01c50948600f2000c114903003210700042d00d17030f41810f02c0c0000b018000702c001e240104040080010034041c070061a035080c41c0a012207003008000c44c2c0c0040c80a006410090307601c10301d40043e100d0404440006001740c4515140504060510500035030115482800c114a1108045041810f141815000d0010083c03070032011035003010f04440c0c6d82c0261100b1036020b10340140d01c90600202c0c1c0b040202c40c070300d8412401c03461003040c3d0005203480c031b0a511841c28035005100d070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 560469154 1250 560467904 560467967
    0x6090b090102042d09020403120801240503100305011d060901060b07121806030207020414040809060c0a020a15020601060e180a1d01020d0f050921040b04080c01 71
    0xa07212210b9900104e1411161481d2002080c054000881e9144003040c0001444a00304a521550904c1d0700d070221341d0f0340c8800c52035250700a5480c60390810000076100100141c8a00700541c0d100c00b00000c04c4241a443e0394500d0300303589449120b8075244c6105030101c4403100003800182d400250000080012510700150791a16010700c0b0740c003403c00d0b2141110a42068000da008080d5600c911a82c01d00003901c1d8a0040c000f5000400144d015500e0450400074543d4404001409160040742090a0a598004201c1c2c00d91250300d40c2d100724000e92500c0380041e141d201e141c00142c100038038100300f503c8240f40020314103101640841c0810100280580040e1102d80b81100c0c140c0b014940c51348107a48450b9518040c000b41d021844c0d070040401c1828000541c107501030110346400260a00007882c51412034800d591341070302d0500940d0405401c02703108107010002c9186031178450f54000c1c00c140c1d030f41001c24216081640a01312981004c041c45001c2d40c0c0c0300101e1040090040c44074101081035002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 560470404 1250 560469154 560469179
    0x100b041d0a0f03110619060602010504020108040611160f020f15040b0f12040501270308010e0a180609060612030c03030e03130906030b2505220306090b09010204 71
    0x103024200c28a0100000d043c14456007402c1031814840e42210b04e54100a50140d1411100106c9081d44500d80000414050300c18001c160003250140d407210340c640c80e40d8507044000e050b010300d40c800141c0100f10611601024000400040340175560341e214000c4070b401441401c01000d80803070b00c140c40310109403021030f0402080d101078a01445c0702c180c40c1c40505031482d8252003032091200b040284034081000304503054016000440311150401240400d18505c550407000391400140031644100c0107011590307110522940c4240342c0e28021030680c0c07004280c2c40388082c0c0e1890940d055500c45d20018140401c034000c2e20001c0c00219a45500c0c0703516920000c00038208910010704240d1641c4950441003c10003d4402c2c5c0005410340324070459852854000500701884205d0399040d5900001d0010702103094200210000c034030405d01c86911070242103c0315401700071803040301c210990b080d03104c0f1074820700103802442c881d61002800110904080015403002000401240e0041000744280303800070740c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 560471654 1250 560470404 560470423
    0x14010803041a0f0412050a17040503070902070602090a0e0103050f0703020f0906040b1207031b0501051b01200309061305071e031703101a07080901030e100b041d 71
    0x4075003a10f03005450003007400c0b4402e0b54890b031aa0092040e108040c000d000c1902084144150a1003c11001d0015161100d018510800c0d515411000341000313070030825001408164401c010051038100c0903000039800f0300498100013644102e8030018005c001040101c50811030300c0d10b00400605140d640026560041d03400e003a40101c02e0b0704082182916590000111004010071485400b4102000e0582e034804920098520258901c0480b4040103002001810b071601a903ca43c81d0240c0765240651110301c0703641807a155075940b8081d2003044030203406101410b070b4107102d89a503030402d44111881c0500c0500311402002c8032624281c0051000036180c82103070000d484201c1c1141c04600c200405046562018050710310b1710386180a841150801103104624079101841219101d9040c000c40045407030703400303121040400c504000320301084080c10313808005141c00b051039298003407450305001c44141d175204801e880348401205458240a6007401c1e00c1101091103a4100b001740c410f541e42c0c81031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 560472904 1250 560471654 560471699
    0x2030c0a031b02040504080a0e0904020a03141608030a030e01180b0a021213020a060c260415111902181b041502150c190e03010f1401080304 62
    0xc1c200d01044101c41c2c1100500540c005008000c5483c2c9418461701642c4030341304030000100b81805001080ca000e0f1099401207401400c0c1c0364203d4199a5194040406001320140c10311031002d480000007040f80300000a030160b03030003454444080d280c01034141c1d032448001240c0e590421940c2c900c5075826250135401250404c8042810384c84030075143d002032040c19600c80079801c2c4003040000307113160b015029403c1c51094920b0340400d030381e4003011503d000c004400100501496521400304200b00041e000c0d0a00301c4088003071600303a03508407040c1101d100107842d201107000321000000540e0103000d00c040c450800c5641c10001041313580080c0b044503c015485c030301d5040c050701088401c00180e10b03160603d1030402103a0303543c0c0d0315800ba00e401107a00740c1d4014014810794404819600d00200110701941115000c5420050b41001c08080941f800782c82000308411002d42036641d079001d0045841c40d080440300014400e05409800da401e4905804c2405141d000b01300c10401281c486004034841d00f80e8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 560474154 1250 560472904 560472917
    0x16061d061e250b151c02030c060705060403021506030c04050a140c030a0f1a241b010e07050a0501140d09030305070e0306150d030306090f020702010f02030c0a03 71
    0x140c0c607010350103101540710380420140502014088070800c2c0103016401441c44080d5a603c00d030003260003096640c1800d810154651240e103403200351544040645200a0030b840d110844503000c100c040e0003141066840398400010302050540521030049400800c6182074090700d00100400c4e510500b80e1100c50040782d449000030b80d01c030101d92042600b040c0140000d502400c2200794400d4541003505c900701182e14108020f1400340542c0b040d0300c0105101d403522003032030f510f10f0104051442980c0703111103c0b80c004814101c06801079030040069103490070455485040c0020410308413400b100c0204c109600c1500c0610031659000c1102044403424039120905090b51141094240502c9406400060408101307908250b01508034601c034000355a50040403501070401c050b91200c0545516080d0003059081c01443c0c14440d460101880c000c0c1008a4441d5507070b00c40c0c07411a4400303402c000085601041a000315070340640001f41e040d05038802141070042d40f45030107803103402520000303062014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 560475404 1250 560474154 560474197
    0x30412050106050a060c03090b040e06090a090203100509010b0603061f0c060908031603140f1b0c24090303010b07031e08011701020c070317040816061d06 68
    0x3400d410600203007102400799528282d648001408100034418105d0205005c51f002140102c0208262001c40d8108102002140c64030424082e0502c001382108100130b40301c03010030300546c034100710481d04044140d0001a40c0c0c17900c002c8030703400c440310005010700c60b44003041403002d2650384c1c00318030b8058034080024982c802e1001e0001e43d80c860102600500c0c43c0d050008000500c40c00001171403003011030f82d03c41c2c031428080d51000c80031609016a840d4001c0ca074800400c1484080c6980b156009075000f4043c18812a0803d03958000d402007800301c502c6d41d10003004822503c07a1f42103595008070103416030b0604c40c2402d107a45030300c0f0f0105014080b005000801c0c0e42d010b0501c60100305104c10020072002512944a02004100c0e03c0240190b10044034080101c600081c01442203440581a80d0013400f601d40c1075031386015212a5072292102c07420030078840460122010311050a2821246150146142c80c0650203020385401c02c5061a60b14041d4114510645409003200e19814109296002050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 560476654 1250 560475404 560475413
    0x2070218070315031514132a03060f200a23040b030a06140607030503061f08010806090d08060108040201140a03060f050d050706050c030d0525080405030412 69
    0xa0140a10103d96068280001c14003182581124002d000840c0a0102c2290754246450340070066403039a42c094007859122001c01c10001c681e110039842d4a12880380051881d040124509194106840b026a80e05c400840000244180c1c0003400c0c410600b103040400b02e06480348107000d0314504600703015581d9400b14450390300c1c42074200d050048030f07403503602ca82c1c44004804058004039404c000280ca8800003041c100e006403100944413100408407480e01246a03400c6815030405051705411403a280d0b26160350081c4085000401c81c1280c3d1007152542c0b40098076450000040c0500b920358110000410f00a5032101c1c0f00395110f4000c1c00e003107005442c0d620040b201015041c0342c800c40d009010440602c0b0b160f142d0400000c9620030700d4075064007501c6504015180c0c1c040b110040c00c03a4000c4804024150280d0007601c04000481e09413801e00304201400300c2500e4040380d81c41604208920400d0036013000d0040740040f81c88074604541103141a82c1d1b866607900c198010064a94000c00c284130822 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 560477904 1250 560476654 560476661
    0x1104050d14060c09030f0606100f12020c03120f0603030a03020a05070f110102070501020f06070f170103060c03060e060a030602031012300906120207050115030203060a020702180703 80
    0x10788404101c45843c680403d49040b190881e6a09510a001da55801d000388140014540e004920041c0000440d0f04034440c19118841c950414800303200030154184c80066444c0b01030a0002c06c0c080c0a5641d030305142c0e41400c82903000501c100000e400700c1e400d002c0d00351000420b03102c01e180c0c1c5040060703903041e5000050318503000c0c01d20010019102c02044408000c96a8064580d01000303800726225552190016a1100400002d80b000740e8440c2c0300003250701b840f540c0307081650311050804d004c8600c10100c41001500c02600256102501d60b410301c44405e90510a41c8020607900340b0301d0b03c7d9130500c40c00103800300f0503e10001d01016008404907921003120411000117040030350f0b80f040c5230681e500d030000c600715020750b010b49911002c041c90480d040158001203800085a40d5003103803c1e09145050300c1000b24801d0000c0b1031642485140001042481074101d5001c0003890300303280314a1481018a808002001941440d0040c003c50005864492800300703e100400d0310412107a03600403003100103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 560479154 1250 560477904 560477933
    0xd0b0a0504020c0c030106080f060f10080d050c06060a0302060909060a1e08010b010c0308010e07050712020f07050f010212030405190819020a0b01170f10020c0705041104050d 77
    0x440c2c800601086164400980c0e45190101034000b4800d0550718040c450b290590140e0502050300132000148154800d41a030035407091401c001c0c2204952206076462600702560400400b01d0340000e855008a41d080107101c1d4070100849440740384074110b502140807400356150440c020411070020901070f0303a0b625901d4000c0d21002080f0030f1503c50b1444464010855849000d81a500e0001a40c1c1d00d17500c2642d810502c16007549a03280c0c542d28204a10201140040401d820440305205020006201c0c4988042e0010b46500410068500c41180303070803d400d45d401244030704142014250300341d80100304541224081e040c10354403544d9a09041d030600107980114020140200c1c4802c04129202d00038003050388802c0751240301d00c812032070103994401243c41d0281c0f42c00b0f070040041050108040c4c6811030700d0410740c203444030040c07a50406031030240b4052803038040940128100500d00b6080142000500d0122400d1202c8030740d81411340118451402881e0041e150703c8810f00034003102120b4540c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 560480404 1250 560479154 560479159
    0xe210310120c360f0f060b090d030c150905060f010612180f0b25020318030309100905100905060901051b100515010c050c01110106080307060e010b060307050d0b0a05 73
    0x1200108100080f000b4520006485905031520000ca611001903208460a8801007400203290402d048100210040303441400c80400896025010000b042c1300511400320340e10440101d0b01203220302e00300d801c04000915840e0320741c0d20080100211503200c2c02c6e640480070507040018480811130840d240e0309807940070251409420300d4100007001035030345c030310740c840c607668890504d0341c03525a446c031076030410006642001a8411710040c141d00c80340d03100d814007801000b001c983c940442200070850007000e4520040c04a6080c45003040f0b5400e108030b50071034101303091078070ba0030302824440020114003030311018a040040110301045030440f45244050f00c0c6166004440203848001c542c040034101c00c0794100c98088812090102e03e5010311000c102055005014084148000d401100d94581079074000c5207542d00d5480004442d03000344010800c0501421000c2041c0703034020304003401d50b5880840507014000c10020010010b0307000096135045d1006441c04984c400034000001c0d03072403080ea0042903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 560481654 1250 560480404 560480489
    0x16110904260d140108120c070e0a090615080f030903190507030b0112060b0f06070f05070b1b0c030f030307080c0f030141040e210310120c 61
    0x820031610420444d0403140140d00f2134150700401e41c00781c1014005c6120b01c9007550300c0038800348050959000400d5008080c0100026410810348881040e142455605d80d500401c00e5010310105a0901c04002d4031650711005619160658020030b5882011420740c010071101c00300100b04100c401d10400d401941c00c182c0c101c40b156161581812490070801084858500d03100156659003004040309501d10402010305080100c107849400d075144a111013150a401040e10104604144501070410012008210481ca0f40c980101c0c504d030440c0ca01d40d90344a0f5005403541d01c0002030000807a607001c40e9a00d4280300f151919800300c6500d009000c80d00c0642107011002003842103031040c84503007a51120304c40c07018445e04294401d0740c0d09000401d843c0700d40d0308201c41c1e600604043d040701038140201c508171902800b000f031a10803481014200341c0130300746000051040030050311040c80007405d05a071911403003c0300c9603101c5000502c188503117882c04091845805d8201d0001e40c060348848046905903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 560482904 1250 560481654 560481671
    0x10801140409061b0809070906060f0c03020f0303010f06140705071502010b0a06170f010612200304030e0324160e0307032901030206090d02031216110904260d 70
    0x980103400840d003041483c0f0441000048c03403000d40c082c0508980454484040e202d41421742128262040501078043d84540340d24071000d0202040150700802440246c00c038101d0030000010401c0c40c22100c412145001805120017054000c1400d0040b150303020020400d030180010f043e400742068000715641300c600e158001680b26004000400c103144048040031b80d42e52001c009103466031081c007481d80041c0c00100311000c001065405954092002e00a5503000070b030108080d00c1540c004c650072000030b91285040ea8003400c040142403040300b17218444040c10341c0000c0a161415800600300a421440d00440508a6001310703d0b100c0d0b82d404c06010b0390840c0d500c0b401c094060320903c04505660303d042803c078405019000041340d0580b90700a00300d62400544004010700c40e40401000c0c1d0b07143c02403040004040709110010102040ea115441c0540d0300141082160070640f01d0209000f082402c040000003036a9804200d0441810703401d02c0e0a1082c100708600b6036020b5410031143c0c0324504000c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 560484154 1250 560482904 560482907
    0xf060201020a080f151203070b01090b032a090c0f0a1e031806020f090a09090b0a020406080a0e010b060a02100509030a0804060b0103150e060f010801140409061b 71
    0x1807000003807507199041a604d03001c42040200030100ca40000d41d0601d40c903044101c1c0f52104540390041074210842c4c1c10f08000e51034800103488207a12040425035241e00d503554500301885003082c0c0c240500484111000746003013100c5090701c1d1801c1c05200f0001040000e41e11140c3d0403c2e00c4032091140c901c680c90798000040a002c00840c1c0d240c802c0030000441007442018400c1c000c81151840d8440510549030392a5248806034102030401c8201070400e029010345500c2e004104001050054804a00401c040c1092150f065000e002108c103035004210034401103400000c110380100c80c00c4000203102c2c0080c003010b401468946401948200d0010301400c00da64002101e02140540210030031036a21950788150ba288141d022000c04104428000341c0403446581c0322056010040c14081000e44210103160a8050f290f00460032401900f41803000714103000c41c01500030b52080c2031241c03540d41000403410a000c5071040c01442140c6480940c070810803107401615008004003210823080800920 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 560485404 1250 560484154 560484157
    0x903070606081b060f0f16061103070909180221160e01120b0c0c0712030908010b010f0207152105042001080604091b060909060503010b060a0804020a0f06020102 71
    0x1100100060603040350703c440e107001030448039901d0748009224508402614802000c0e0010f200e003003d0010b08280304408640c05000da550b18001c3c60102035982c0c500081c0c003510244c415002041140d103070044042d561401c507240e0700b08032a01140d0030644201e900c8415090038860210b400030900481040011241543d010031058541e0301e0b552100c41da80700ca101c1003043c00041000b030314042100002c1a060b06c1e03004010100700d0300d000c095858940d250164503a4601c00c04508900154088504100081003842003440001003440c2c603496020362204001e6407580d13540100d480c6482508032900c4d03658003a4045100d40c2200c15548080e0030036a08004000345802c580c1544e0b0001c0111050b007042c2c60387d01096400d100d0513110040e842d22144180310003072090640450344103070303214880c00070700d200003044000902285d51000e81716404c1c0703203000068440c540d010710301030703810001160175556a2a05403041103d140c07800b07009560f980e000103a09000d281e80804d46104041d00040740a560640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 560486654 1250 560485404 560485423
    0x70c0b0405131512080f0a08060a1e03060203190f1d061b03180a0605270a12091502030706061d062206080a0b01060306030b0708090307060608 63
    0x40e14007400080d000407a6003901d480000d0354010440c607020501201044800c84480d6900070010f50b806c21000e03000407401a80040308940101b004072040000300d2911000b90b00152500300300b401c10f1114030141109400840b40002058140c0200010f501c800240080c2010080c16400074450110000f101100620b00d001d0314604445184034100d01940703000030340c6030040d1000b46000b1402a03441d040340c096134001502c5400000404e042080ba40c400401c0684051401100b0010b018101900041840740444031112070f4050303903d803028810716021440003c0103401400047c12028109070898420b11507411981c1907503152076031071031815400000b90080c584144000c01c002c0ccd454108554244038800d9060b880208500c00043c0e25042c440303112580300d240c01140c00030788040785800c030701900c2e090b03000381440742d10591101c01807100e10302030a40144064101005030b00d0450301d03080140c0d04020010030620881c2d4000c03515080080044030b101a820400c100f101c5030325902050f03124010071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 560487904 1250 560486654 560486659
    0x8190210141608010b0406180f140910060e120c0604060207080c090613020c0109060e01020c07120c03020909030c0a0605190605060a030f060504050c040302031002070b0601080c070c0b0405 83
    0x102181040c0f40507001c218140c0b810494060300342031601c042107030f10442038003402c8061040c075000020012038440908001c0e0a45810302c0041d641e1715014080e80a074000c01400b04540d01190800c40d45801041038060590169140c0565885000ea624680b106010003560498000900041e9507540031450b4416608640213881d5642d0700310781048000a07003a00e0381c82d800801e207444101025015401001684031407000461030b1813664441404482c00c2041130790b803a9400091110040006102910143c50070001404064810381c842190141450000a0040340e03440c000c962190303010030a4500d00c0c18050100c0301490464a09a406094159040400c001441d18a040300e60402d00410094503006802c0e00d0405142d010203c002e000090700c03402030341e036450102003883c1d1114000c141c441d0494002c09a903e40c55031040c1407400d4110307801380760b4140c414441c203800070762804512074200409292070312481e00e41088505d43c603caa10300c02480c8084d40d0000041030741000002e042121000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 560489154 1250 560487904 560487931
    0x11030a0b0f09120901080a1d160602070e0103020607170f040906050628030e150402010e06120a050c0910091a0f030f040f020a0915120819021014 64
    0x4444003542e850301000c0f01281c0c4640184509143e03548a940000d034420381b216030126500c9100d0525158045901800c1101ca40103880c8a680c0e0401450028004100e180f000f010050310304951a030311a801804001d104440001c0d00d030084c0102940007010012800c4000c940e00c0041085500455019205820b0310787e080210001e41c0e460410296440c070601003200d0000135100000d0441350700368184800080c1541c40c01d4a20320500104400c10070001c088540d064242030500026241e002e040c60803034822601080040c039881400d4201d107412a20381c200125039070711200b104000c01c0c0607098800f50015020284040a03650001c011700c00c4510600510429417900303000500e9601c03900c001000c2c2c0300e40400105070000303180d0020580c441d0103035071001080300301c40e0300142c9800043e40c040035189464040d6280748840030910340c40108a01001820001160784c0c0d01e0201e8048c01c01c0f0305054040c0180c01501d034038002d101500405012400800805e10102780da10503030401550101d1182d00c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 560490404 1250 560489154 560489161
    0x6180910080604140115121e020a0b070c1703120a02130320030607090e01091401060807120e150f04020108040b10091d0118031b11030a0b0f 62
    0x12145010064446007070180c802035a4035100c0800c03032a11061004425942c5030350010071612a2494070001d440ca1107000c21240c182400e1018490a0043d41c42030840050b00e405001039071561064021288165034041e103402182c01d0101c4608003075800b5100c0400808084450044044010580c00901c00001c4102d81c84801031401207000e18140041803400c405800e2001c03e03106540b5100240f121007002050380245030102e800c03c40f042d82c40c3c03070108039001810711a28007805521405401d034451304218084428498284008040c030400d002d001005000c503c02600ca0070172600308295240e01409280700c01c2291540e80c1070104525101c880628001c0384134135040220007030140d50165180060b6031500d88070540d003040c016051401400c0b1404001038840c1640c09075141880102104802ca40d4009203070301e0035a0100c0114070a0912103400f2280040e8000360404ca06c01c0f20708100421003c3e1914007080090380c6003407001c0c0c0c5849a0542e640400071080d03231040c8201d800480c03801b004d8070b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 560491654 1250 560490404 560490421
    0x412140f0a0c0b1303051605102318120d0215091203250806131506200a0b0a110304111512070f0315050d0204090809061809 55
    0x101c0100c0000d20402058a0410020303012001400341485071003400c1809591769542c45160510b08082d001d11004811410032440c0360003490b51030403605034200003188204c481b0401103814038003d405a4502c1000c2a003496280d0911817004080c0c1001d0301120001c5540645170350350320a11041800184039541240c071070b01d100f01880070f01a0030040010042101c44541105013908000c10f01d40e04250410002e00b26651101e5032054903d00c5900d5481090420340240881105d9500740c00c00400c0c00c2036104c00100301c06d0718412048410920b04007281c09034104000c8480321200600140d43c0c480e04c00000d0601204503d154064100440104074a20312030111340902d020888000c0e00402160b012050f0304c0c100f268140d07400840410000b441d0540d40a460f2101402c203542c0d8200190303d00346c0078075580e9050300c80c20510040c074100300f00310b0614050010740101d0000400034000e070b40386d0094004000c150b600b5035556100040185440f1002443c10a000c1500340079102c0c86200d00030701090225 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 560492904 1250 560491654 560491663
    0x501030c08010b0612093406030207021c03021e0303010f08010b010219030302040b0c010c0807021c0c02041112070e04060b07030809120d150905010605031b0412140f 73
    0x8203409450613017030142c020817a180d00c41005040349060700541042080c03c0790084030030080100601e49442035280b0380031844140c013146030000c205042c81004410090b0b82c6010051101107641d115101d04403415103130480c10408003020280030011020041000d005000c400740d4142d031040d50300040c0b102e60f501602c0d42030b03e5001321b4050140c1c1040008906040300b00041c9002d480c001c0c05c000d86001d03600c0c80c8207001c550000051381816550b89034005007180d844001590051507501c0140038051102c451541010340c1c00410a06100c81b03d0f001d48110344407034100c070790305d01400858561660f400c40702c4822507250880e484c0000071400c413505e00180c40d0a11454081e85d5400031800e05000b650356007580c81110185c111825841034000d01c00100551000821070608400404150403074558941600500103400c9540d610782004018807100d64000306490784000040207a43e09280c40c05012051071003241c010400307002401e000a0280b20303000900c6410089400d00702d400312088106400d444 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 560494154 1250 560492904 560492921
    0x110606190b18100807030b04140a02090102010f090318060f0525060507051c060315020a05070f080913020a0f0e19030b04050f03041a0313050307060501030c0801 71
    0x20080c00140403a562120141003040881c0c0401c88480d80803500041d201c2019020700000a40020100701d0002e500d80a030100c403810a40b001d010498441c0c3e0030000d072400092103a0803c540c00701d408141a0f04c00d4001010240d807a00c801c02440d00c540c00c009004503d000f9417400801d108140c00507403548103114501d906140c070b03a00c182c20015050600b03041d0744080d0210780030741e2008401c401d0100d1154804c00e8040e840319251103030b4585030000106000307008001d00c0e0480c14904601040030400d0030b2501d20001e80410701c010f98030001070300d0948181c098100054000d110b600c0c1e03c3c00030000500300038106480100d9905c01c680901803c8081a841040007110000d9012240741c1c0800c0d0241d01c10503402c1034014019103e0426440400d16172902e24ae1040d90701d46229803d210031b00c5014003242807041501b0b00a985000d0034559049040c12005d0349502420718000005a031841c0d404241c80b82c100d03841020350359101707103606024015010a000581d07013001c191000059800e4144103d404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 560495404 1250 560494154 560494189
    0x2011b020a0f030c02060309160815040204020f0f0d020903150108150a0e0d0909060f030f030c02040f061707080601321504060e04020a12020c0f0d110606 68
    0x516510700da540d109142c4444900300d092204c100c0d9032000503039802c0007440c480c071007000c0200b1000b00e1188642041c1c1c1078603070124400313070800343c480d0840300001e041480d4440d4042d140980e6403080c42e65007900d00e00c1459000d000e507801c0821442403000f6181c004007040c401c100d08950040c5001814910152420300c2407811701d40c06825400801c50006480c258800c070f03034600000d6070500403c0c0d414145803203c0c2005001600b20b8506000455035031141c074024040000300809910f0440e5140160b0145959010701402000c405000465071541c1220294203040142440416a5007081c0150308941280e0215140a140d0700810710b80700019007941240c084a003030724a090010300c401d5443c400c5a03031303501640080390200058030741c54041c1c0b40c4050b0105004c42503501c1d86403460003043c208400354143d21840c01008108440b40d44025030800d01d50800740d0043c2e0701c44500c2c104078546402889102d000340070303400d03c02d9002500708200088000303c0c54142d0b1103580d43d04080240b40c2d000000d0031007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 560496654 1250 560495404 560495413
    0x12150709051f110d02011e1512050c0303070b062d01050c0f0708070518090604080904020d050f090d0201050c1603110313140301231b03090d02011b02 66
    0x94802070302c2c1c01e410880c0c07103850424104a400c030011480c20042c03010007580c00350b9150403959112202d201c072003031596078004408200c061003071b0340348075004081032040d410081d000d5814001882414404041002c0b0010103c0b60703204070704e00c1c055105190807280c85108a04484c00d00351080c1e5900130340d0480e04e02c203040f000348855404006590a8008024030046845403148200580a0800c443c0d000360121100a0410302d1a000821001401e03d5440541a18554080c0003554070006030b003d80041e402180301d62200c03800c0c00810000e01071043c0d03954525090800381b066044c80c0c9103503680203000e014280c5403ca8000c44007a400d9030b20988032001c0601007089024071000d0214405603540f0b00c07a140c0741e5241104030002ca40740d034024500f04180748640c1c410401c541040e64200c1c45006501703500a10048009a01a41c0d0020707140c0c5007090b0407401e0100007948003201101c10a40e070740b114036100d900da0402c01c51355540d071107075540d04c1c0001d5861f00804030300b03628240300500e80400d6140c0c000c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 560497904 1250 560496654 560496679
    0x1f0b01110d020c191a120c0a0906080424091203090c0506090a0b1207020c0a05090a0509030408070303110c0d0c03140a0807030201150f06090e060f1215070905 70
    0xb100340c52003101640c42218148134046480c5040014610403020446032054484e841a00c0031201c0c0100503200e0401d02804101034030615400c03061400c00ca8070103041ca944c180c4c1d40c07420200c0303076110390745482e400d17100c542c084010200a03994821a109401a8024281031141e80016400c0b0341440c0f00150420260042c06c00c060309d80395006003800030f80074051065143e40c8125044158020b000c111040c1079241040204240c1c0c1000825412802107030819241c62812000c54090100600704085054503600000c4003004108110f0300123180d9a0215603442e592810000c1c060700c8080100301c5c03640076000e8007203d00d2810640341015945c01c43d00c0f10305050b140da5580c41068207441c209040314000d400380c0902249200024000c0341d40260000700b00b03201c05224003101c00c80b4070340140d08d070065481018800c42d60f1007540c9505481c0011078080b41502d41d0000541212103443d0825840540e0200350340d103043c40811844000c9080c0c00ba6902207484915041e9090019402580d803c00c02c264050b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 560499154 1250 560497904 560497909
    0xc1b03030c030f1303050105090703060f020405090c070c0e18010516020c121218190b1605070b0a0504150c0f02010e0103020706090803061c08030a0504051f0b01110d020c 75
    0x21321a44040c0c190f40d842d095030b00d948450031348004480d2401c00b50030001d810000c1c030002d40502040ca03024040110300d414104000980c0307105d00601002000e0780701003503810030040503011120150450303400008043c6403585920100d07946000c0c010720254201300216102a01080010f61204855005018005159010300881c0d51048401e0005846045039601c50603003150020640da030382000240c00f101100e4002d004010304040421034018000001c208071050012007a580daa507030f04038800401710358904109107000000c4d00511180c040004400010640100003001280c4840030096401001000103940003e014480500100d45e41c14400c001988260704161005005040c0141041a191920f204507002008101c41030240042440006e01d808180c2000407000076103907042501c3c4039650402e150001404444d1030320f480d14007050400c0810311030341380c441c9501c1c0200c2810a15a002c8130303018091541c2c075140480c0c0ea02c01c1e01c0d203010300302246250601966800800d0707019411001d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 560500404 1250 560499154 560499157
    0xf0605150c160603020a0306060203090d021c0510090201020d090303050306060717070c031e030e130b0618040c142a01020406020f061807030b060301020904020c1b03030c030f 77
    0x74803084074000c1050140b462014809900040c01003a9401a201c0036240409001c50f5415003014003554814450000e0542d10315501c4040701d581628030106152442c1c8040507031000300c400c001d10600401014160050480e400104c506000340d088524026071340f1030645424046001c040c00180040000034140d00700a0700501c840d500c02c804110001c452041440825044803408031140000c031002001800041f010041162014980300c1b0200c14a030394000e4410a00c162015004001014400180181c0c50b445889001340c050201d66981c1c0c803114021000c10620718103144901d00d84024003051ba80700d0800002044415401e40b454403143c4c543c4500030b0100c07198104c0700501350140c04c0360440e50a0000d0070060160350020104845a803100505290340200315981040712014414292500010400d040380c2d008480c00220b620f480d400700340684a13070340f0001e81050001681c14070b4150f002a10700702803840400000f8410140d20200b50312403080c0490718030642e009209a40300c64071401e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 560501654 1250 560500404 560500417
    0x1140703090320040501060f020c040e0304030501050c0408010c05040e0a020d2d1113030305030a14130201021504080414060705061e0a0c021506010c0212030a030f060515 75
    0x41401005076241e40b40c11043c40b000154000340030ba000f2503038800b0f08050184030302400d10307401c000d0b010748803040001307569445003061140b141d03454141d9040c0020003401114003464000c80203100301d02e44841c0c00003066000e1b114000031580b0704a07107040318a10071801e50b02a00c444204524044e264040c8110203508210410b40e00c8075540d000da001103005411000300c01c0038040e2600640c3c080829501011515030215007107807050f04101c83c101c0340b031000e141c41003941e9060810f07075140d0303d030024213400510441150328048504041884400c243c1e0b5003503807c145100340d0884192680b9120a402200c0c8155801003000d6020711061240070340200d640d80002401502d4581090450340310070380307000010740f240040b6010b1051058400d0b603100d20950f6012180d16418040c5408007180207668107101c650040344101054045207040e0b100e82241c20307185800074809000452404a59620307030340315081c03140100b80381c99480c00c00040709008100440301c000b44041d0b0300c42044076255013180d0000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 560502904 1250 560501654 560501657
    0x803042904090e010e0a060f0605010306050f060f0c0109030903060e010c09030b090a0f0b060f09040f030f0306081b010207060903051b030f06101d0f060f01120609090c0902070201140703 82
    0x1e49601c176198404101c032a6886004540225038441e820980340211125600018100b41c285041070120703465020700c003654980103540b2142e0303401260050391001c0c05000402801c1e9424800003400341540411a0b8095074010380c000c121092001c0c2c01d40c0d00b01d601800860012a015110030408201003010a65012801d601643c400300c24507076880b002c0807000c0324116081b4440c07000b8013116042a04000780100c20a442418482c1081e0303c50aa0212070404014104000421404c00c00d5100750017100c01011800100d0b0000d0003103002c6c90300004201100c00307006100d03031039000842510a4480c0803c0744c0d0098003070840e00310110301030004014548102e40d010720410702c00c44440401080024420200c0c1d0001440d400e080c000d15000e14150341035010a00c2810078180984070500101c400d4020004071403100401001ca401681e00c0c0360844140003d580c6000380004002101d600a02000380c8a4814001d100d034650f1070fa8400c90280c10000780c001015007010f001c00b402404014a09240603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 560504154 1250 560502904 560502911
    0x40b0402040b0a0915360e0103050d0e010302032208120f010810090c090c0c02060c0f0c1806061803011e2906160c0803042904090e01 59
    0x25182c2d0340c1d070300d80c0c800c0b8000700c00945503160801c500780d000c1c68400001001482c0c103105954544c070403104080c02d40c0b0901c1c0d00c0c0716001c0c583d90080c00041c80c1d998000703113010100c1a00541e07482c1042615404c02202c0040850b0100791506043c0d8800c0c421a0710500008032038550401c1000007034019100880301c11116600104030049810b442070004511940200d07510b5411581054041c80c00c000403144000e0619042c0488603001030b0b001130750070b4103544003090002902c10f00c0d50421107420451480203504030400180d4544201e101190f822800b141c4c240c110303000300d0021814001d115141210745011000002c01003402445d002006101428013000c00d2000b510705540001c0c21100407203039003000548055251003040761140a081081c1c0300a408035a14401600102101c02410342c0c60310388900c0b00041c207050383c244e188600c00c60294201c0300450199880d01f030202e64941c4140905244040c500e28a506500013421808508660010102c1c0c10507150480240180c0099050328050b5500e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 560505404 1250 560504154 560504159
    0x302010e01020c0309120705010e0603071e080a0c140d05060a09060b070215030402030a4706190504051b0307030c200712030201020c07080a0615080c040b040204 71
    0x1400d001a00810f40101c000e1550b808070b80c002c0052545040071070003d2504113860400c00c9a0700300284458070034054505a075a41d07035081c0110744100c80c0100e050424a00c480c501c0d9105035002090922440d9884010402018400c4050341c14240c9000100290303441007205804518180e000785030007810180c400441c0c251100940d00695420781c21904801e0000b248180039884c0005225218501d03e200080c51410f154000c25140d00d160f64003c2e042c6203408220783c2c0e01201e500c0704440c000b460382400030302c131900c00c1d40c60711a4200882194913501204a000c14181d14021200c402d0b505d940580c1e40080a141906210141400030600d1070001c100003030702e802201eaa00e005510650066500180c506040c11001c1d00c06403803d6500d072a00d03021710b010940032100024800e810b5071a020b07200d41120a0781c2c50700306e000e40f00b0000300d05040d020380d031400540010300041d4550340c1442404107004451420120392181c40b118441c51015601c90034200140d802c16070702c8038015000243c0301524154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 560506654 1250 560505404 560505431
    0x70201110607080a0f06081902011b080408150f0a0507020c060f0c0106061107210519061406010c290c0c15090c01210501030b3907030201 61
    0x4003200c905003c20000c00801c443c9101d14415035408044e07100041210a05069009547c4d8031075900740019900e12203007100c2960700030020041000541c00006852450b21700d4540340940052007040128400d0900128403468004845841030f80b21010020300c1e80e803600c40344000351001510f01c0095014460010766a0386070704005200d90280080e00654a0b8001441070f0300710b40711035101c10b04001d1400c0c01e024030208085085002c0b0392009500101c0c500920340000741c4502c4140008285108003049003030001c1e80c0d040200611406a00200540041c007000c0040041040340c45500080560308041c0c0000c400100080c1301c9042c1406135191813484606468440c0810b88510701070043c003041e0403950b44020401c10f441c0d03c1c4210140b150798103001c0d0089a1350b001005c10107041c4140c0c0a055903d688003849051a2001c508809110300e59481c1086e0102107070583c0d941d81141c048600010300d4007540071203500b020b03001d25109000c3c90f001154070042600181401c400719502c1d60080b59085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 560507904 1250 560506654 560506663
    0x6270504020a050414090f270a030905030601170a02060d09050a140d03090c12020607080a120605060c060106080a0b04060f0f06020d05030a021303020415030b0601090e06040207020111 81
    0x1030015840b030f29661428031601181900d1004100c0b4400d02c55401003025400000b640f8a4206410840084070441030781805039450003040c0c11812140300e1051407000389a0311589c000219503050307064526590702c3d00d24140410301c802c0d02d9207074141d200c16282e10050600400521200da080040000c80d0095a59017030704260312501c0555410042c500c011807a02e20a10100404602c1c5040400c40c01c0b600780e0380d00c041050a4419503410051004499042d52242003ca07a44284d0000c101940c1d1a00c04401038010030f440a00044400d2500c00089820b04200c0101c07002d02003910300a121036131822800f241c4020300103040b40e505a480d0b52568005440e0b1303015450181101503900f030710045c240070005100c00c04030303408601154071a0080c50801600b000449402006101025990f100c6410644210b9101c0ea0b100a4010386450b4509210314624440d40040e00d10503100328816440741801100c0c09a918068680c1c9040e81b0700c080b42d958034140d8000d0020310b206041008012200b45081b0f82030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 560509154 1250 560507904 560507917
    0x2d01120e0105090c030d09140d0b01030501060e0604060e0a1127031501030b040b07230a0f020141010b0c01230a1508030a03140906010627050402 64
    0x580d107400c148041c080e4140704030310700800d045d40100740041c28440001c101d0521031040001500c9400c600350407580b968803107400c0d190303042a04034140b5603603880c005000309803511400f040300e240fa002003440343c42c0c01c0c040d200072030b224030301404295162001000014821081001c0401c002000103180303e465400c03d400d04101040035900b940383c2c210091506205400d50a002050740480051001640d50a01d1541060b004440314134559181c120981e007258003411354032420700c08005402c12441c0800c006100005140c0d0306c154505015a509909a44c0350709a080700321940c42c0b6550505407c651030800c04c00c9110f00c2e0203040840c3c100340141003800d00b07030842040e00c1800205c1c4407000c0b100b4000c2c542c615070b804004042c100c880031071045e00000082c00e00078026454041041c101c9444041981c0545201001e9980d10800100090014070104030611808080440092081c06010441c981281d43c640c48100300c41c487d002030301003243c0041002091030041c4200c0803903542c40ba480503009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 560510404 1250 560509154 560509181
    0x6030204150501031d061602031c09030e01020601180e12161b03020a06030b03030c07080706110c0a03120c0506010e1008010221100506070b0f062d0112 67
    0x4003900704400101940c40000c50405c40c0d500450341c0c0300c0080f000081c09980000c1e01d00e08030300c4a01d1200740c107c0c114452904499040d4012000f0b041300108641d1102c2c0b40203220303840c0c4008544810005a0f2545000d110b4604c0d00d9000040d01030080c90b081e0004100140b01c0b00998014070389a07555410941c000421490142200a44103010003102e0039840c2184d40010054441c0d80c2d04c0d41d80040c403240441d004a40403d5140c0002c1100e58900b0803e079568210340320b0958810b6900e6000e030303a580d00d6840c8540c0303001450080d4840482034011804e07000c440340c0036001c240503c1c20f47d00c4008481520400c00360402011540c25408984240b06072400380009031041c180c541840720440107464400d400c000400c0e4410044591649200d00303400d841340d40c40c10800d01c04e07070341d41c200003003d60f10079640415005140010028100203100321070b14030403a28a07a0445e003d8617070030107003c0c0c10f0b00c040841640c0c9110580c0100c290b91400603068001c0f01b0145404040e5540d0741c2410380548800011458 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 560511654 1250 560510404 560510441
    0x170c0f0303100f180f090602070303090501110406020a11120f03040602071a0a0e12031b011409030706021e0a050703030b010f1b05011112090c06160605060406030204 73
    0x5000e1242e030150030b005148448180050f28100040e11150a8030031541ea044140e45285001c0714801c0d60300200045908001e0840d101c00d80740c10041d01601450404503020352a0080121448061000752001d0301e0503580104400d00250342e0301480521200c640d40d03804410000496409a030410100307560b000c1071806036440324545400680f401c5141e807c43c5998180a0080e09006010301d01a558400e889150001c150b18203e0046915880071001160341e600000480c1c00710500311020719031995a100008005441d1a40446420404107070f07000c0400b6042007100d60b0104403aa00074021a0312002244098260244d8105090307a020144010208101042c10f0081c1509841204850b10081c00c1000604400b91002040010410391020628056034480701c28480b007540801158942640c005a4415003940415081001220804024030501001009504003031040d41c4c010202c41e4039003105035040c1d540d01c0002d828014400d0303070403564402d000000b6981d41c0c01510040441c040c8000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 560512904 1250 560511654 560511661
    0x50103210918020304060609020a050403020a1e12060b030a0c290405010309060b0d03080603281e02090a05090d020a080717120421030e0a170c0f0303 66
    0x3440005250510003090286600041003801c0c503180300b02c604040e0b14600141d0300c0c0c0e01c070f182650040442d9041800190b1000c1444001645c0010060048e81c1c02290007600311603460f6800070504001d0300d141d0000245001c000c000c0d0280070124032921a11030070001c41c01400f00c10204e881c01414a80c00d480801d81841c042207050744102210408800503002c000f0b003803104858101c0e440c8240c0c42050f0415942d840100c050140641c400d0034210401070161350894041c1c10014000a8283e80c0b2911038016140e08080d56103100d00a50000807081e403401e46071702080d440d958441e8141905c2642c440c4883d800034001a0b5075030b00194401c1c4001c0f03030000f81504000c1c940c40e2030302e03040b2104501554060302603000070410845c291050305070711203c4455900c2e440300c200807260113603208080d415070301c110038041041011411198030004040d01d01d00400007c407412003d80342914411085a00078908800204550403080c00aa68448061a01e00a654610360b4901180c4034030401c003d40011044c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 560514154 1250 560512904 560512943
    0x50304080c0312061008130305090105041d0612070609062001020c151b04031704080f0a1205040b031305010e120d050702030a0504091a0a090b0a09050c0d0f0b04050103 74
    0x20825194103240c40c0d2260300e80851f454103d0b0070003203409802d1140c0807030010300c581c1c800c500300c034040d01d4080c05402e0740c100c4454490300f83c00d6007552802c0c4100340c2040c2c82c101200c000a234010403608243c1c0c03100c80b0a032504405850703168000007404d80e0750102d80c0d440c0d00212003d00040481d0794030a402801204244400038100403000f070582044112081c120000c031052100179641a260420070071031001c28061207018862045074404034440c041c818003980d5031003022403001d2159000741c990251690b40284125020f126500070509407003000d2003c22003d03049034249201d00c600c1038000180000b600c0c00518034100d81060402001c00001480003040e403014080c0640141c410300082d418501d00c50070143c250b00442c000c1c20045940c0761045c030207a18440c00c03c030345400000303020144503940340c454800240581c045030a024030180200000ca4107094030410348242040002d190920b80c400102c00c0c00b0300322080c061905e49807102d0741d25044d41d03141c3c0304041c000e51180082c407103100080000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 560515404 1250 560514154 560514169
    0x5130e04030e04270209090102070b010b030925030311210903011a01080f0919060c02160f05010e0102101b020d0201150509040213060e01060306080109050c01050304080c031206 78
    0xc0e0729513801110701c40d2603000140311032901d6411241000e9507658901c840e402400740480c00b800c540495000090395011071030003107005010720010b55192114000303102072080d0750f03452400511010303c201007002c24840c001c0090106900b000340c8450120710694600c00c0e00c1441400f100403200024100344600d000d200e518500d54215020f0030300031120f04006402c4550080019841c03004200000b0fa9041c0300340200a014007841c001141e00f510a414820000c00708000d141002d4817460703000002400a181805045950761441a1103503810a00112402c02480b041a81940b00345907014182c4020782c0a1503a1810144040107086103000744004e1401d520343c5030b11425a45000407090580640d0708441081c0d40c0240c803560210b07151031010410704a554244407101d1840c20b20b01103501d460500d00c4604031000c6d45d509111113612070a046080720a104d20080c09a84200005040d40d405140655400f6008410003400c0c114146040c50543d4440031000c031030040c40000700032551810300c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 560516654 1250 560515404 560515421
    0x1170a0c060f1b050c040e160b09040b030c0f210604110114070b01050d0f14010603113715020d030c08090303130203031b011d1c05130e04030e04 64
    0x10111000c01c01d203610791584981c1407544035405540c1f03c00d804501c48004100825609518a503040c0216564030707901182900038607035051245090040d544664680098260540b02c4001c1c0107448405200c020071980d08801c44007104810b4050a810300e200300103004a40c410740c0214500002c1d41100d00004001c0312030081a4a0b015605103c0000400d00c8250101e041d0358090f94843c240c560203040100f072210b00800010705080d0b00f40c4034805108419006107003268071580500106500d504101306866080000410031184803015004c0070810030240c81031503522034076021041544662061041c814206089405680001c02e485000c41e814407601051118524051555041104181703849200140140558912050b0344600b90355080c0201c903c18030100d09440c0c01407041d164050301074022050703181200702c01d1203265401c02c00081911300040100300c5241d039410400c0319007591590803111040709031404c00c44000c40c00c0ba00c001420390249009032035a0015035901010001581c3c00007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 560517904 1250 560516654 560516687
    0x60810110c0712060b060a0c020f0303090102030a0e040b091611030906040302040f0f02191d1c05031207050c01050603150c0706020c06130203120306010801170a0c060f 74
    0x40121090480000c200e84040d26900010f40b001c00500b41802406450750300d100c264003000000d070180c143d54003d803003040741d1032090b0b0340a4407494034001016202c0c0684003140d03016800410403e6000c503c01d00b640c080e00b04000b400020250a9000481d0321514121107142403004003000d94140103401c03450703c00c2d00b01c20700d2008501c1e1284980118034140118172000b4083c1380c451550086650003030304800d00b42a0351000454450008206008401c4a103000c058003003200c030803012241c070301d0441041004d07140261000c020f100b508102c22045100640061f2040d010521603601030000c0140740a018034610342e1100e0300c501c440c410142c2121005494641b10364003203180402c2c4c40e800d00c070070140e2002d20388003019211001401c211000e44503040c8000d6042c060760702000394218420b005c2100e03460094044566484074000101000d11069540a0124245000422007441d090f081d0740341034450481510703100c01f2265a41141c25a054111802043c403041c08010101e41c0300340345100c4103071311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 560519154 1250 560517904 560517907
    0x825030822030302030a1803020309040b03150105060322030302070308010e0f01061b080c060a05010e1021020d031e0306030c0e041103030a08060a050402031e061306081011 76
    0x52001400816501d004020300341500400080e0754036881707600041d4083d408036400c40389801c1c00e280081d100c0e80303c000024806c034030f002100e00d0f080c1000545000d2030013030031072044031340d9003040c04000c415040140045103d042c00200c506103845043c10544041d4460344015031280b02d41d24015213070200582200500400482c200f00203000203846040c112400b9052010300d003507014154211840d41c800d4081c12404000803841000c0c0d20015009200d0303d21003008110a90726007a441c251510290f81c1860302d07102017207042c0300c500c01d44100e051110600c03980d1032203452055400b090f40201041010f4000c02c440c000749151024245045444006039072030100641415951500c020000c0783c01000d501009020014041024513688214400c1e00141169180c8090310300c010320035001102d803203010b00e4412400103260700b050b000703690040341c0d003103803041d40c1d05000c0c800310301c0c49240100100c0d80305000c0d10014001000130300c6100060000a0080c03d060154848500b0581d1444455240710510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 560520404 1250 560519154 560519191
    0x70f06290603070f020715020a051504080f0f070204180303050702010b13051506030115030605030a0308010b0702150a0905120d0c140f070f06120507020c0d08250308 73
    0x9034042181d50085460070503101032104c0303038000c0b4a454003a0300082805031400740c0e102031464000403080c24203803041040f600303820f11045200c1444041540c000388501003d1082003018002c10015240c0400fa50103040d080400780d800143c103551204428502c030002550012041c55414081c0c40d9011006000034861100010046802c20320401c00c0c864549542c0c101040500440d808095170b000d40023000e464403541c6030318640020f40300314812000428600000000c0d1403c0c00306005161035013645402e071080e0b19181c09074042d50b00002049034010300c071884903400d8051141c041d01c0700b00c002c2e80d03649521504100c14003501c1e80002480d10f2250303000b848141c0c000c51b40145003124441e40483d404415840484a0900d400100081c0c1039441c001c2c00c401041143d43c50841c030301200e41e5540c54901028026a4080c12600c09070395140050308491620344141c14221442c141d254401c0f050586404891040c0404100c094420031075030402c003203007550a1651001c50720750002d4000d001000c9400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 560521654 1250 560520404 560520409
    0x9110301230c07020d050303090c011b050618010e01060e15010306150509030f0106090b0a0603050415110408010f060311030f030403110a03120c0209101415070f0629 73
    0x200c0040180d0b201e86400a610400c40d1210403030a281c00741c0c007108036034880c1002c02e120b03521094008000b500140102c1011032074565140d410041c0c150304040940100c0d01c88032a0008054003c99038000c1d199240c0038400280d02d42440750720001c1c15002e0242c6450b0400041400c411180303007400034100740c03c000c414000ac2810406030341e100320060405c2c1d543d503806107011a0400c0354002c0000c103294642040029a41c1c1c40750481e25110342c0c201c652400081e11201c080d0103c4200746c501521202c4a81c420444002050340b0440b96156540f5445040660f14170710203007554400c442c840909900c40104004225034007684081441040703006c0c000c1110038040304c47ea40d00951001400701902c01788480d11540313860342d015011b10b800c4540d0342110f4554141c0500b00203c512401ca0140380540c0020321030352580e1038074030b041d9400ca010348503d81c03015500304040c65030554242c003400c0d07408206580018403100e81c0b8040d007601c80c03407001c9051711034001c5980b14100c448515802c0941c21444070756181c0e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 560522904 1250 560521654 560521721
    0xf081b100603050c0111030d0c020a1b0828061e0e100c0309080d05060415080105061305090703080d020c032709011d040f170d06090c08070c03030b0409110301 70
    0x4480c3d88c90005003c9056030400c9140c01d0700e5850241080010b120b5801013400040e039110180d0b0b9129080794004aa44d60004140c1c40d0740c1c4145400c0c412141000000207161a0000304500b0308101c0401d20000d00c151800040310b0507000c401d0190390158100080b211014090070840e0040ca0800b0440030001d0b4075081c18501c1030303803482a80b8a40d1080010f80f11390b225880039a0344110f0a2521059684503140030f8000c010540f4031910074200803169107030070400c0d4003c040c41100b420014108041c070b159070303500440c0c010310750740d81c0030310707024060001c04d10001c20181c00540714071082c070400a13107003080c01450440e1441d010b034002d01c40d0400601818141c54890601c8203072031455504265201d081041c01c83c0b540c03002c001c0030042403114100c82100b020380689102880101c04100150359801034030f04031140040c421002c640b40700b0005070102d01070300d01c40550034083d09001c207007a10500000750480e1828002150342220030882241d450400348200980300340030b10540c810000c00c0c404140b410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 560524154 1250 560522904 560522917
    0xa05090106110106090f02181219230c0108070c050d050309011b050d06050a030507060807090e04050a0b0c090a2903010f09180f081b100603050c011103 67
    0x18440d55a0b907001807031500758044001000300f0081080340e03103000341c3c1c014003079442030b0021400c0c0034100d07060f0030300303480c212071201c10b0207412000502490146612030311003c03904000c1980d00065048046a4142c0c04064907001005003401402d0400405000500002006011041002a0035080c0c2c0c00045000035490380004590a00e59100d070f83e5800e041d401340c404140e0018005813040090301200350054054403801c02c120305e013400401d88840502101d80b00d0f52001410300c0c0d0040004020003070040888076040040c1e843c181486607150045040411002c0c0d07800ca0f89030388000c810786d0030b0000e02402d40d07401141b80d070f071003500c3c1251140c00a441218640184440000c1d1209002005d90010204070000d0101d034043c0c1c0e44a40c2d480c5040e100d6420140b10b14941641402102e5a04a02c0b1160154580340c0c4030200c0003141001351107449840d041a40d0038603908892406e600075a007800c00a0b04445d0a840b5000325545042d4903000b8101044099180c0c148500015450501d00e00030090300c44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 560525404 1250 560524154 560524157
    0x3110a1b020f04022b0e07050d020a030b0106020318060744071406060607060905160b18030706050702011d0405070507110117010509090a021003090c050a05090106 72
    0x2680e19040c000203520076850440b250b806840040c0c8005443c0720f0000380c2c10070002c440c184608074546656124140c907100800000b05401c01e031010702107440c0541a41c40310174006820100d515480f991004100c6d58281c01420140e800030030849581c0f036900c1c0a3307002104040c9d07035003400c01801e0b6940d20a0703401508c51146c0c0e0505141d0030310154220000031440c240c000c80145070801c5050708101c0c501e503802140d081d9600c4407401d007040c42026000070f035076000e5200036008501e0000c440e00ca080003410400c4084030a40518a1040c003a0307000300d201c1801030144509507c0c0d40d0324103900e50f0340203104407260090081e080384100f00103045d0130506070742101d902800e0a103410410b0005603070800310740d1590140c0c01407410041c030106a900a0150601070710030503a41500d03000c1d07100152160081c110003a250304c0c80800041c4010f040400c1d14070342001c5000200c54401034103a000455840c80c0200c07081c0007994a0b68500c003030051000110006040c107448030344071282048042151694140900300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 560526654 1250 560525404 560525447
    0x10909020a0b1b1914060903031b0408070311090609010e01171006031a0106030b060d02160b0109020c0c370e090714060315010810031401060603110a 66
    0xb43c0035602c1c8150203240980010556015541003004a201c1c107840304420b5801d40307407503038010781d5a0400060140c0688001c100035402e581e01e1030030178018180c0e02c0113601c4038584141300000301070004001b101c0146128190720381c110001c5000348590000001c4c400ca00c12181c4500400201d43e004402c1c0d81903c02c0b0401d402c02108901c0e401625015801c0d44032507007a8075100c400024003003540201000f030018144010910b1345e03a074108030141c5852006030760340550100135040104441c2c0d40100302445407000c82002140c150f80710604005400d9200d076000a4002440070143d40c018000c1a000100480d640c0e44140010020f4819840e541d200b10034610701045120204134244003214801040040e14083d0f5a1070031654082d210b810b030348150144514107007031a80e2545041e105691060500180030f000c41590710b001115140405014145c034042030b404044081149d002c83c2140200c40d02001090891400c0d4000b011101210141000c000081c844000c5040d40195038000300131143c1c4032030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 560527904 1250 560526654 560526667
    0xe0703141b07021e010f171303110d020a020307050103150927050d080f04050c01030f2c0d0504050d120302091002010516080106020703140a050a1a010909020a0b 71
    0x1900c1c14450030304081d40c01400c900d040039070801211000360f013052007039031007030780e0710031805c000340d072a2015002449540071002e00041c5400e507850005004850203868005110003d528489082c110540303c6200140c105100030407d60a007040817000a00e42880c0130400100307852085103540200e4099458150f03129030b0904c2c2c11001e07080c072082c450078584001b001c3e400ca2601d40b00b550b9800080700c0501081c1030304000780d20b00300c03006180342c85181c00201800000800100440080c2411503401c03100aa41d1040380041014100751950350071038040d40c0143c0c80c015803280c43e1038903040c070b2003007001c202c2e08120600071a1030355203200128582c4002e0070010215a4907041e00a805190109a0082e486120720a17850740d0540090740140004440070703003154000082110380303100901170140981c2c0700305c00810009500401c0c030a0340744403c1055070005403180d038869003403116041084c1d40d10550070306412000c2201c03003003890040184001c20000d08851384c2c089403500e0420710508000d0035000c1210b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 560529154 1250 560527904 560527951
    0xd05040c0f1409100305010e060711010c08060f12010c020d12020406020703170d020f04140901141e0901030506070f080105010e151e180405040b13050703080307090e070314 76
    0x113880c040c552102c000c0c000c1c40003500215944c1e510807a107510016500e8400c00380410301c184035000e14100c0680c0d90b0000f5580d61320902500e0242d050782150403001101529180000030300ca00c00c020503155001c1c0c8406051400024400a4074030901c0407860310400040128540006241041304c0c2d121000e4461521005120041801040c2c15441402d0000424801248441005006030780d03100c040030228000320014480415424000d4080e84c090745a0901820314007403c8c00b04d0441d04103584c2d42c14904a001c0820000d15080e40304035038952048061014098100e40e8440395501da61030440c401d90b2500700002c00190201d180280181d1030020070100f4000c440e8119005000f4007601a0700002c40034001d10596489090b080050180c030301c0100e2814501401418000c40e0054004c8010361a2107500a52481c204042142c040c800c0300c400000045400300550f101d96803d40341c083c4c4451400d1200701c203000b0000e260b5801c040c038000d40c80da040f68003000a10703003203450100344110031100c2448 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 560530404 1250 560529154 560529181
    0x11a03060f1f14041118060c07090612020a120b0112080d090c091503080306040b0609120f010501050d02010c03030f020f0d020c2418030f0d05040c0f1409 68
    0x100688480340340b03400840c0c0c00c1445001c1002c91030781502c00708120f24100c070100100e801041d09005019000b9080ca1600e4039264000e442129105015600059038490212044480540c0600f1442102001943c02d503d40001070f42c0c001d102002560807520744030764580e0702c080c50501481081c2070018408400340050142078500c1c072a9040070401002007582446250545644070323000c5400e042c003240c02a8681d0b00d0b8200780840313a11505903800c0d81c59030000c10024003c2030304003a800c1081803100804603a030b941201603c0c0d9a21802403c45031030b8071003000f4250750050b0003d50091241456200041c1d071700940c82c4440540524000070701d50207081841002c2d01c507801841e80c4040c00401c0008400c0c056038010312840442500300d5501c800e0800302c0207078840040c000240000c02e031800095640e04031114051140b42c920b41907901c0d0660b103004200042d0412400070f0842652401040304010702c0c240c4030f202501e900300d2214480ca24000c6c03600000d14a02042c103002e00071000104000f10203000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 560531654 1250 560530404 560530441
    0x6070507211e050c0a03140d0203130b0a050408091002150a15081204180605180402130506030712170307032a020706030c0512150102011a03060f 64
    0x49088207050100c2200400301803024401024500190428582e4680507100310341d09540100090710f40c00400f41c500ba21051481400e415010324200444032460711188019846030000b402e6010310344502d0305004400c030b07000a054098507440c0000b80700101e0300b620240d641d00c190460b918011250740b524228102998155560040d07a1103000707101d800590b680100c0d0600c40c25101c00c11040d65682c91107503039820b03c100c6952540000704414000c0001140150f41d0540c078031140441c2090b90740000c04c1d00d1007141400c0d20103c074003420502046244c6550001c6548041352414491800d000d17001030f48403243c0d440381601d0030145030300d00702c1000007007010b0050421200f9400ba8407864402d0000c1c01030011560342845070100c0d0a95003940414801c401104a080e550080210704d091170000e4009042100c1c8542c103201d4144000c051104000807a544104801c0040d66030030342c0380100190a5588107150321031101c600300802812901c00244c95548600d204618502540310b10000076074000000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 560532904 1250 560531654 560531693
    0x103020112050406091401230103021003050c0c03030901022107090e06041e0209040615050d0507030204170c0301060914060607031103040806010e010e01030308060108040302101a0906040207030206070507 90
    0x14500306d0010019482541d00c00d01e10001403017003000c074044c14650543d00b400003c0d4412040d0070141c0c4030b00e11a505c60f03580403501901076881c00c0702100e03074917145030412590002d150390002151450400700840e1244081c1c07146400010500700024050308000d03a0b405a04500420300000031070703d90710fa4210910303c030440006245034400002c0d220010390f114002032401541000000945440401c0a1103501a540e9413000d040c11000c00402010f050040c00190801d502800003048080b034905d103030192807140800509945580c10245825030b1800d900062800f450b19500348551060329010981c8103031304580720769480f0520300d000e4a9000080e80002950301c00814041a003020000c0d00c24166040322425140b1030b0781c4d44034030f00c1c0882d409002c01000a0204c0c4040786d0385500520249801c54480d0060703070403983c1001022011520301d00c024801d04980b418820065043c40c03081c40750402000d89007540b4000c0540c8002e5039501011f0405010020000b03501c409002110031302a0201565 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 560534154 1250 560532904 560532923
    0x1902030c1801030c0e061e0f120a0302070503031903090203070b0720150d0c09050909030a080c070c03020118031e030315081b12010e060403020d0206010302011205040609 75
    0x40d4200e01d8044042400122082c6001120100321801d0310040e071803103004028011803c0080c0300c88602104010360050603081130206001814560f100420100b683c4007580007407403582220b080013494201c681c1e010601a4004102c004035240903000c1c0006c01d151a800c1c00b191005d428030200786800500d42c4003040e58000410400108000700501450b12540030142d9030101c0400d5040200b5003540f210300c1a4048810040780000700b98541010640c0c1003142807034201c40390f940700401c144003000c03205006c0d583c00c00203207490720a40010303005801c001c00707401c0c032410501c85941c3c6280700c1046000c042d0500c00b40496100410b80180c09000c0915480300500e425914221510610791200d9101100480e042c01c81d0107200d4801521110308480c0c03260002d1842c4c41d106101c0781000d6002c4a00e098002082d120003565550090207a0380141028071f000b480b052601d82002410888080000c40c02c540002e001080940c0c0c0c0014000c44080b60880005416150b84c64040c00510141000070402d040703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 560535404 1250 560534154 560534179
    0x912070e13021005031003020d061d01061a03010e371e0b1305130209100303091a0d02030a091e0201030b040903080411060702150307120209031902030c 67
    0x19110440c203000d20944600c20345101c5800c00361100e00089660100d14101c41000b04090719043c1c0341275145e0b0f4016100064860321001030700341002c524085480d1b441c1c1d101c82040107000380c408410210461202c10403400c550420300618642c900c0580602c0b104055000803c5000104c080031007151035403801241d0001e0001003550700038080105054020f080741000e601581082c501921140003802800c03a184450700c0004d950080101800100000d0511208140162540da101c03030700070f605050b9403a541503d9460020070780b01c0740e03801111400b001c80c4e40c01c007250010755054560745e110011014be01c0c0d0342c0d9200380b500107011170381d000703003440d02003450305003080c0254a9164a824000ea906201c6a5036010030700090300e529010017000940c1200c001404034101040703040c48160010102403401d1150b40000380e0610380316010001421000050184c542c0c4c101c03005c000f403c05508400e50030035101c0c00c002a04c52000c042007800940c521032001c001c55030203000d141e0300c0d0500284010351140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 560536654 1250 560535404 560535421
    0x8060f06031510180903020a060c0e060c0601210b040f030221030603010c02030405100804060f020a020d0e0f010c02090a09081801020f0f061801090c031a0f09030912070e 75
    0x71264410014400c3d408060440b0040d1350f030080c00001c0c0d415400420714100240c1d20407006040c030b110a0001c0100080b0594010758946000b000c0d0025464018139507541040e00f02d8402084068004200340d03070503104400001e0100542d01d41c450b81090807005c4408590a060381010010701d4954250b141c1d10390036014800780c1c900514018a0300b90001c0001c0d91500000380c0c1c3d2031040d4064250711aa11a47d02c0c407400b8400c030f211640c024441c0300b002c2540c40b034810900d8241d800450022015030403205003c610268441c900c61407200c41260802034103101000080c04903081e514001e4000c030650380c005440300003290800c03040c0325484079103d41c0d00c01280c2d158000c4282c0440c40e1500500800c3c0e02c0303103e50040000c3c0e003048500c0c0ca5014041a03204c201280441a041803001d043c195242c120141c08110b64050000086006100c0d0441001036000000c00143c4000c1803078218241640501140410000541380103035030a41d00c401841c018510002d1600301c481d4001c1c0704003080380d410400c048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 560537904 1250 560536654 560536681
    0x301050a02070b1003052505150910050333090a150e0c0a11070317180415060302090604030f080c0111120703150909030908070f08060f060315 63
    0xb1070040a159816440d03184000e40a80a2444050070f640c0c003e1000911600201e104103590030103040618140540d2071002c212040a0800c078400420800f00e456121420302e60605056401c1d140341240c0b9501e4105c181110124980c00d50345940001d40342d51801400050101002075030006020711098034040c0b280718050010090207013000c200000f00012030300c02111910340503242c2c154400c1d08180c0618401c40d2501c00028403d0b01c50300c5541400008a420f80400100040072100c815070780d40c40719542a0b91a0b080740b0591401580381200c83ea103d500d00070f1102094403003616000d6560b106110020f5428061508090100100341058508004100008142d5602c03484003d100d0b8058400515401b40942007988042c002a81c000844443c80fa60003c13910700b25116894a80a40b6145a0421501103940450100740c1900707060103004010000b8100400c0020001d8030554103100c5601c1e00c8050160001c16400341781c0011440682d800d10144400d540260642c1040740380c002c401d4640c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 560539154 1250 560537904 560537917
    0x8042a030b0f0108010e0a0302030702120705190f050109060e0d021201020d05040b0a0203071e0519020604020f041509021c0207080a0801051f0c060e100c0806030a03091a090301050a02 81
    0x101c0d8a00300070b185140d00003140c0c207c503541d05600a141400d40c40e400340003020060200d59a03081c010701a000c1030300d5032100080c454541781245582c201500345001304024000e00d4210311b05103c401441001600d1b80f10440541000c400e039a104001f42c01440816802d20008086840950010404100540c00796110611440c01000b410400c1c0d121200b1380000c81c0710659903940021407004424114180e80340c00d0703490902c81803401916000c409820310156551035034104005802280c148010362600c07004201c0e100c9821a420001408030810500c0704203254405c21184580204980700f000320015260751103031048810540d40c4000e103141c4844294046072091012402840000c2554140030900600c001c080d0010346940e50410316041e514943d00c5d240c112205901c480003450048010b01109c03c118040c030001240190040d000905040340c01400d05000342c2c002c124400100781d0001e0400b080b52000c0b0400d805440c1d203500e4503074041c8548039880d81c05608105c20f0204c5000c1d01e5000305038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 560540404 1250 560539154 560539169
    0xa1a1e0109180c090f0515030601050108090321010e0f090d0e060d061d010e0114060708090406140427030c02010909020412060f0e100213030f0c08010c08042a030b0f01 74
    0x2150703110947c07218020202c0860f42c1c1c0642c8a01d006000d594084d50301903400042060443c0d00b800c0d4641000030000000303030b010b4040401c6a00c010808591030030600c44d04030540c0d5401301f2652400544443c3e441060200000030492071950961f46a281d95003140c0600b40030f40414000750b51651502c440e00b8a03501841c42030b105007030000080c0710213030200e00d90580340d541121240d80020302c401c008071070708461820303618460204081e1400f0380e0b40f48110700040100c070740b0190700070840030304000131610780140500d9080c080103040d090040910700d14881c403d600d404c2141d0364210b81c1c00102c54840c4180c10004a44e13200140104554242071240d00c0c0483c07040d81d09011081804030001c00341c804601d1100116409450341d1443c1c40c5031074000d8940c1d040240c3c1d144a10b03c2c2c1c0d07a12401504109444152a0140c0041742407000340002c1c081e030101c150803810b058010b81840d82c0d855443d030052880c00d040d10b800c0f11100c000f0b03124010f80c00c0c10045402460000c69410018200f10783d00c1002c2c460310700c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 560541654 1250 560540404 560540411
    0xf0e0a080106061407150c1407110907020f120705030f03091c09080607080c1c1406030706140c0304150e030f1f0b0604080a1a1e0109180c090f 63
    0x1500b004c1d00440381d195034000c0126400214510b02d01018162103911541801010315542036880b007100090049180154619105030b4461000d2005148001d8880030864000c480220b012a10002d48240480b33024600340395036882e5410600e0550040111448072100d00205120aa2000048258034003219041c019841b814907c01500c5107500e038881c11642d501b040c00020b031080d00a112069100042c10b50302843c1586440030701200001c4002c0c001c0b0b4859a5405416210404401a983c085420f6000f406101d061500240c030b124821150010b000e40001041a9011003d000741d500074449501c41a02c184081040642050803019443d03000c2d11034601d54034800d103070005101450b00b4010400c000109030318846480648809034145030032580c03c01000070744582c108400d040043c050015001501d044001c07251480c3c8018117082012407142c02051000c2d0425403079035046a291900009140d03160981b1140b02c001100e5016000c1190400700003615140c54000c10100d0070702e9482003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 560542904 1250 560541654 560541677
    0x8010f08010203010e130f050102030702030409060b040302010e0d06020c01053c01051950120c030a0605071101150603051909110a051f0f0e0a08010606 67
    0x118200c3c0404d200314002580f4600c04280221500008903071014001e010004120b60161a00381c20380e801170b142140183c2c0700240030050032145200306005816001000342c82c1034507540000f02000c103510310443c8038542d00d242200400140c3da04683c3ea8030f940780001d004610702440300d007001905c035601408803003200c0c10101c1081d58003d8001d011b1000126894032b0180d00740070602001c4c0f0442c0865907840700300c0900210b1945204810040950485402406420300c003841284c02c0304032903420501c951007049540104111549100700750703401c5c10f4074200c0010f02015041443c041500200304c1d014011a02c14030140714190700700910030030b0603440701841c10041c407407001d00701c500d07860090440780d6480b80248282c9120b90001900840c1c16000052801c0c00c003d0030800f100c0740c0c01800c1b100004500c81d1030620781040d4001c0340050004442c1324060031070110381000001503481d41142001202030b942d043c4140607083c1041c00b4040030b8100c0e00e4858035504258000d28190040c003001c030721070318101e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 560544154 1250 560542904 560542919
    0x4030905150c0703031b0b010b04140a0303080705031312020c0123040e180607030b09010e1e07020304080d12051807030b0a06120b15061e03040213090308010f 70
    0x480b140e00707519000601009182d61011a02c01100c07a40d9550940541242100411000003c242c0030340000b440491350369180c40c82c40f240794040001814061210f20604001098001d00300980c000750905001d035a0b0b698804448244100f4640010600d844030a04107864907800901c01c1100d07002030302c401d61003210b07802c0c610f107070b1290305410003001c1502040705001024088090301d800000c460351a9820f1550100510300700381c000c59549000981d121030170061864110b80e46801890107107105802c9042c04031981e520191100d220000891610740400e02c12407080044400500011090341d0401810880c001c180c080c0c0020384400540c1060080380d20041c9a0000b40c00300400380c0c00401d20725265940e100b170380440050004a40a0f940c0d40005801040354a54042c030303910401c01001107141003403400310080c180000d10350044109021050644c4001a03082d8004010713520b00b161a0341e01ca01c00118821070f01c202c42807115080900f043c0c101508244500d041c2c0386224000c0c00340c26202d219 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 560545404 1250 560544154 560544157
    0xd0e03030c07031d0a0305100c050a1b150c1d040b06090d0314040906030506100513020c16091d010203060d0221011a0f040207050604020918060403090515 68
    0x200600381403420400036000901030702d1100c5184031500540301e401c0e4134440014a070b03812250f2060b1099000160304031b00c00720007840390954400060521030b04104542e000204a602d034180c10030ba001601d03000070f600b8846601e503401030348a21564203012000e42e01c24000d2401c2500480d03c40070149900c0a0030103403825024001e0040b101600f000c0c2000015010802e000c02c81c02c1050381401115120050926210301c0240702404140c400462420b01d140742103460305c0d40050a003500c0020342c00f0305000c29600d201820130f40b4400320304003503261303000701e4a01d07418003002441e803400036065440001900f48050f00700040d00d580800c1c4c40c1c100040710590081c241d20040b580240c2c8180c00140020040c0703445900400542c0c00807000c000000c090210590841b10740060304805039003041414210761801000680714004d095606604115041e59420b07900c00018000900c207110f004009402a0881c00e075044042e55880103c0d0b280c3e003090f0502070720a10050281703500442500d954200c1c60b811060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 560546654 1250 560545404 560545411
    0x18070e010f14030c09060c0a050303040c0603050403141b1e07050d0b0a0c1710030b010b040303080103060e0f1608010b0612042315011d090706051317030d0e0303 71
    0x200b0035840d5640d03d8400181d2988980e016075031062040c031410071440010050400b0f158450030045680381003e08107400b1000312030384190101403d106c200b10000382d002491248108681802c2070701c030794450010200000c0740e40390016480c0700d80202400c030052983d0a482c0c1d001d2425054900c0340b41c50b801484801421100d019011184c030304040f50503c001c561100d035034880300d89054450005850490700c00c80d403080e03c401074109841700086c81800b580e05c40c1c403801840000d00b058501032861750b01030720035101480040c00711503552112000d014001c2c000c0304045038a0b542a0752400c3c502c0a414585041c0c10302a2040940c6040c00003074903418400d040703074038200310403110501590310b50303480103410314040b102d06640f40c034000c2c8450381c680310030041c0c0521118200b243c0105517040c0035030742e403440140c46511660300f4220f9040c400190000300c0d4070810345031030703140c6980da03120320203425400c441d0150320403112400c2a0140d02142d40c4080041c040d203041001c014400300780760084040c1e9a00044d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 560547904 1250 560546654 560546687
    0x504080d18150c0f03050405090f090105071d062101060801030501050105100905060a030f0515010815010c030c0c080607050d0b0d02060904020a0e030609330c0918070e010f 76
    0x74030f402c002240070203550301c0c030052180c40c0c601d04d4585c586010502c149000c0d15800482402c5a06005040000b0f0081c60340c007007180e10b8003440640b20624800c0c24400c10b0f000300e5000360000a01c881c502d12148003510f40b01031011404100b503594401c40101844001d1100396010b510300b03000030810f441c0c480c03109543c40440c1c1e940c06030868240420046e69070300c00b1126000385a6109820031501d842c5000307644c89100b15032081010426554005403020f00003d03d0703210340210340703124a202c45c0c2c0c106a0000741c40b030f014a411a454000d92404010241d504d0300000480c3c800e190401c0f40040e0700000400090700c0c0d08106000b41e40301c41d000d000c0764004101c0f00962204090040c140c3c0f504240e80608121031081c94442126a0404c1c0468180b401c251001900b58101c070211003040704491000c4030004004421081c10a2a1890000c11010025103850181000012094800c0e69a68100c043c8402080c4150145042c444006848845143c3e60f10707021070061180c2d50200717401001c0556886015 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 560549154 1250 560547904 560547917
    0x307080109081e0d0507030f0b04050c0301030b0c1c1b020303240409020402131a0c1b04020d0c0305040c0506040f05100507080d0209180c0702100504080d1815 70
    0x40300292002070f10440280002e83c800b80102001203a0f207001e83e501a81c082d4070009280580340710080d06981580385841d0090742004140440d40303070300700d0440341166003000c9818855110001441030900c90703c1f0505c01c485240480050400d086540a603141c8114003180485940b8054800c0c0d8a0b03010495104011075003a01503041c03c3c0741c0c83c004010310072200400004541009600183c100c1e04414440301620420031001c0c0410708002c80c1c0305110411188825003005100c460f082c0da50042c01c1e560040125480040c0c5102da02c5503015140c107070103000000e1142400a52000340103020455007664882251000080e160a00c001184c0c107803207440d00780f030b0303409801d02e018822080036035540141002810403038000414036210180c250b00721132130000741c4c0c3d8a6034001000341c50100c0302c1040c40394240c01010700c140c0c14030803801c8801c459415100c1120310061803e090b190b0340201d0303011200b28051201c0c184040340c0d0000c20b40000348201103040341c029880c6c2d0800d001401400b41000d010421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 560550404 1250 560549154 560549167
    0xc12040927020d060605030304031a0f09210f03040f0204200a1115070f02010e2a0114030a0609050a0207030c0213150b0a02010f0c0f030b0402091509030708010908 72
    0xf0180d0541d141d07a8007884001c17503000d80e42d10100b81345900640c800e071182000c004100b5407210100261541150105900984a007843c503184c0361586c080104c14941000040da041d0a2400550140c80d50300032011070349a1245421700b000344008500102c102e01c694034005040c0c0004042d4402e84070112001c0c4130310303800e0800022040e6181c2241c510f050245101c0d0b44407484000307040940c100d115161580e10503e03e100010000b03800d4034441d124010894010540059941010851100c0313810480c1c2c900d0f002d102604001a0340c4540d010800400d6070354000108041c1c031100d0742205040b60803242c000c11540e5201000b24089001d4000018000f0300006003d001614107a804919201100b10700050b51581840f03a00503e03000310f42c04000c1d4403202044c50428540c0a21510703c8171000920140b1a440010000501e100302000c2c08205065a0780c0e68107402d138940741d0680d4801c02d4003425002d6852072800541460740c000c6842c5a100344191940403a1103c1c040c016001003580c081c0d0310318100074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 560551654 1250 560550404 560550409
    0xc09050f06090409030c0516120816060e010c020d030501030f02040504021f1e0f0905010f03020c010905071e0b0a031a1c0c06030618090204020c1204092702 69
    0xc0e0226988424180814a01e6a541e44a040c444500c030381c0380c480c030a002600d443c90404041d10b40c0140d40252856040000b009031800040405500000c45da5480c4e00d82c0180c490380025916015180c1450700e82c0c01120b5a03015400540e45002075001c54022800945044040e26401d000c003d0004450613441d000609040d080160054801015414103080c03c6034070a940941d0104004001150140700c140c88284124840c030090180349000e0981718210400501030390150701c1800e04004610319070806182c82030741a05c0d0441031400c000c0c0451983c508000d0f98800c0503002d1034440300140702b000a44051a086202d044840c0b07050068140071000c003003540100794100c1180c10030a40c02500b40c00320794810000002d0503030000754150100740030b0304145c031031090745400200c01d051130418107110b400341989074920300c101c02c0341c00420440e1041c80407502078003071000000d2061180c500c450f030407481c40d28054020b89030416402c0042c4402c3c80c96144542111600f00010864002004400360 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 560552904 1250 560551654 560551669
    0x507020d051c020f19122006060a0902030f070e030f12040905010605130614161203050601020615190b0f03011706011206382706240301061d040c0905 66
    0x1b000c941482d0084c3ca005108149901310312507003002042d04010204039480c980303c008035001d401281d0046045182644021910303503400352508040c0820010008429501085401b034500d01510035142c281400001408040d0400d00504403017508200c000300e0b20612800c00c0d140e4418103a0b01c00e0700380601d42034054544541512271800c40c44c000300848084041100070a1803001c0c8a51012440c10300201030003011110050105411900403c05005882d1420041c09404000c2215411440d40d0b43c00d41a602c1094564004a0b0400c0041100300c07102c5103080245040326140f010803100c04070b00850003903c8080074000e01801d08507841d0b021000c245141d008150403201442c5200a03101201c00703241480c850851502e203003036060154800300341846140c80007040c2c0d0540444c2c1d02c1580310f203464407107140d00418050140c40c020b080c40b55209448071072040ca502c0810a807541c0c9585502d4001c00709000f0a0300c00c84103d9222070b2441c8603040500c50700900b11285c1c2c0d41ca1041504280c10000d65 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 560554154 1250 560552904 560552933
    0x209010b0c0102040305120901180f150e040c080906090307052e06140a05030102070c09050403090e0106020d080f0603100c11120304060e030a0f0507020d051c020f19 73
    0x1299404d10020000031010008101c440112203842a01e55040c0c000040401d070526500741f611001c50801000740c032403041c1d000c506403a4030000c000140c03081c0e80c2085070080740c2684016402800d00d0100b5510310340184c40e2a008540728401d955407075654801903070380c0b44250b203c000c03e01e81c8a0030115a03484804403406c400e042424421080000c0c208800c00d0a581d02d030340041041a20304c2d280306440d03103010201440240313429402542000406c1e140d80494501d0b0b0300c203488440b900ca0001500309031044802c20050169a68640c01c0f42d40c555034000e544039604201c890100340c241c070204107110102003269100f20002001000d08004205405d400360160a1a00c811703c182801540060081440810445000803400075120302c2c140c01d004080e11030110802700c075904100078401000342c0c0000c90007480040c50401d00d070f45199520215110a4840c5006081802400c80d20001400040c41d405403244c0c0c9607003103d18100d80840c1d540e8079031030b00303422400d102114a02c0000c00110024440045e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 560555404 1250 560554154 560554177
    0x4030e090c0c0312060910050604030602070611040b0406031413030c0201050c0d0e040b06160b042915010f1709030f0705031b0105040809040203090709020c031201120209010b 77
    0x10548600c4110f4915042801d12105180c0d08034200310640c01c0c07032102d40307030b0083d41d43c1e4000098a01c0c00d004583c09119074040a4400d640008895091040b2a040211542002a15146e0310703581d5000d644499001402842d0000b410032555481142440303212030b00880c10030f821140c40460710b607415501041902d108905105003440301c00d03031801c0140f288000c0100300c0c1c0c440a007030403031200400040b22007941400e807180e907041c0201031178442119292441c06a000d40c040d201600d03142009100c01c9084007510070050b01440307541e982d00303003090761241c0540486070040528a070b042005583c3c0c204100b1280c00044d030070382020101140c42040f0380350454156002e683c1303001d68148103604960b0090700705807103d500000b5440724016641b501c0e6010141b90030001c000c1800c00340d0b5034264600c01c04041c00d2250342c020011504007103090015034000c0c6110402150f0b1624810065610307504190001b500c007118500c00024a214800c007044215a0300810b06c1440e0780c20b0820489040e0800b051900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 560556654 1250 560555404 560555407
    0x209091302041b020109050708030a0e0108041109070c1a06150a0302070c0303021606020115091a03060f0a0c02010525180909060e0a05070513020d15140904030e090c 73
    0x828000f5114541c424003401c035800425914490f060151402820394000030f00c99100b045a40344c83d641c842c0790000c00100918094000f600e550510b180008001400603030b005440c503040c852983e412a00d11040940b10f040507aa802c0105042e11048120440c0c02035001200209034035005890320707004081c00ae0607420014141482d640740d00254040680080700540e101541c0e0900b110500343d101e900800042c8002d00126503c48400c500e1100c03203120344113545490300d500d14400418501a81c5a4076006812118203203082c3d04e2401012900383c3d00b58100901e0180746a0007180b060050901c07a8150780f003031170788030381141d0f03400030a65041c0b403a10010402c007010300f524004080030300310340201007024000c1000e00c02400d028085030f00c0f203642840300e43d001110450001d031020582c08201d620407543c1d0000a100c04060801900c207084241c2c0a003440c14156915000a41ca400030a40312020100501403c2d19014065071940c1500c000e40490001c10503402c2d50f140962519602c500120b5045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 560557904 1250 560556654 560556671
    0x90108220803061c051b1c151e06050a06050c06220807080304030f080609060904140709090c0b0a05120a020417032205210115030c1404020909130204 66
    0x100030f004048003114240c01c69108500345891b00d5559181a80c4200e0300c0802e07180115100010b40002e16000030074002d144915030a01e03d00ca039109110300c0703007214450f075a02d42550a0801c003c2c055400f03814400d955600e0041001c41c49a001d4559000c8a140101060703202d002c0419130100c00e411080e2080300c4240310450010310790801425819219600ca1a22401c1501d00a400484441e0084041050200c10806c031030f40c07480151384e0803c1c4280d40191440e1240c1c00d0148080d488401c00c14410b10601900091290081d400391156074051102500740c103840e6001416907108410820000450500020010100d042880350700b002c0302540052600e95a00f0715807220718620b201603646a000842c407101c0a6042c10602c80d5036402040d8651891b030b0030680043c0c5075001000c0745c918070a00141201001c22720942c4070000944124440b024141d540e841d000b0005202030042c80d4034001402d165031103506160003034a01e02c034030090803140d556131100320701c44050001d07140c00e0740d2064560201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 560559154 1250 560557904 560557939
    0xc03040803030f061906050706090516031b0b0a2118020910030803071b05060405060711060408091e0d050610170a060b1305070509010822080306 64
    0x144020500e0300081c40c0caa1618000e8405030100050202c1c0c00340090301e140c1030000c10700c01d940d0300540c1e0142c1042a2074400c181070003c003c0c00f6255004207070f40f00e50700000800e0702e00c202e824002ca80c401c140c506d01d4410740f1403030320034441881d2103803940e400c8042c403401c0d0300c05004200f800410810160901c0803201c039003a19409035401100c201c1c0031006c81050540035824021009079110503901801550103240d69600340c4188002400c2804200104403100e81c2c1d81c1d2450241c06440d50030034200c81c080c0c2010300340503440b014141d03040d07008941901918101440c001c03c2d03440c82141c014000d2410540e4920600c01c0c1e0940c00200f9405030031007104810080d6548821501080c1e0040004040610b004100b441c179201c0c0c160041502e43c80c0384010320f00b00c0840020030801c016403140e808036401a5540100721314502d14203825a0b00c3e810082000419907101d0080c0410b4602681d03800056101c2000d20740042c1041c0e80c88c01401091085684040f4000400440e04080003070001c1104030b440d000c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 560560404 1250 560559154 560559157
    0x1e05030d060b0912010c0207032a0816060c08040504090c090509010c230d0207020303070b0a09030f0f1d0303041d04060b0103020f0a0e010201090c06211b030902060c03 74
    0x2240c0100c1020440e600f00c0e041009550400e07504c010f000300280320084001030b566485a1100030300c3d50b00305101107040444018140780c0213440c10481e03225059203661040380c039200b0748100040304d85246c04002521621481201410a4010301100e1400341400700b4040a4203202e801658a0300315607000203026080c074450170344076204250000070800704005d4000d05c0ca195003400400310754281e46a0381a07403c1d1500403100902d130b84070f038012303543c01191022030b04501400c0c1c3c0c00b5041c00600c070304100036166550412070f40140b103982c8402d803001c0c00c81b90540301c10340d12859041c00540012074040354080c6559006d00184401800c8a05080e500d01e09050500460840103405280074001c0c04104203035400f030403a89190900341035041c6610911045250b0080515003410040c0e0320700780b001564000e40c00000c01035001950f000000d906d0328005010019001c035030340d032200800301304144148214402c00300c24170364802c10300d0901001050100d0280848031420b07a4007140c100a040c0d0400300810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 560561654 1250 560560404 560560409
    0x3141603050624060d0f0603081615050f0a02030403020f163803100e160210052208090306090106080d030c020705010c0602070f03020c100207031e05030d06 69
    0x1401800c680ca030100030414016a50b01c44811000d152840b84405a03440100317407034203481080c0780066091440311000e409040c0740d50000c0d00c000301c0010b40489484400780f00c04074241c045c0590020030f45419071801c003101c1048800070012903201012a045407100c0c3c0080d074001d8003c0c0704690500144013101d80c180404282c01c14042e0814810401080700a1000e007000f8001a403400e03e0b0214101500741c10000001480e04411340001000409804092088001030050030201003810b01e80000b482213080c4609e0750b46030241c0314127100d040c41c4401c01e010f414440c450a10404040708444820321200b075860303000485900b40b0601085c0115101004100d100307900540010882c1fa140c266000d0030210090300c0f1404250402050340001500012400c013102c10a20f005a0a041c41d810403500034000d2110041400e03141c200d00c00c05141d40003415a021120441d05061100007182c010390b5285070910004040707001281040c10500c2c8000b40507880b080c0220b00b628542040307504602c08860858 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 560562904 1250 560561654 560561663
    0x10b0904020909150f1210021e0c07320906010c051f05010e01030b15010507051b0406051909020703180609060206070507030203180f1203070215040b0403141603 71
    0x40c44084c0ca64508079030101c86510301500c241e9117035013101080380d807900400c105c50040d9640010f44100107644202c042040c0f61001e203a880c0c1c07110341403d880f0341c0366441803240600c0031048680b41c0040b111221400280080101000300940801c00240102d03010001d10440c1806001e4a220002ca001400101480b4000b008030380009908845054100c40d011b0b00032074410400701005000181020307075550340008006034611020b41c2c042004965922400d20014110b000b0260301403084071001280e440d1030b100494003401a541c4a200b0303c500045969802d03182622703641020002154954024070300ca40c000e00d40309441071240c031600c4084000e1507108100140e02c94501b0002c0316070500605030802c00302d1a0091074110b42d600d00039a82c0c000d8140e0100301c4540d9034903030000d0340c2d683da40c2601d030001d01400f121451046403095030f4881e0064103003a400f9030b44200c42c005d04801d1b081d0488050f101403c0b01c450803e0b0541d10f03158001c03007c10000d040144900e0610107500c4840c4032000d40114800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 560564154 1250 560562904 560562931
    0x10b15030a0f02030606070f020d02130903080a0b10030f020912030d05060603070806010813170c01060906080d080c0702130b19051018031401090c0b090603010b0904020909 76
    0x2800da00045a03207080c0158640b61050003480f0b943e64850041341d40f05a0421440307881400d503800020b0642071a400001e510240d0100c80410455030340c3c029408641c02611038002c540ea99403100810b40b5103210000703a0250420039200c1c182c9009034041c400300e450000c80107052030302c80808a902c07048044111a030962020820b03a20102079801400e620060644400b825070600c05005130001b28060415810f0103a00c0000512007241414035909594021095140e107070000a00720000c0d92141d00c54031101d5003410380c00705145140f401250f0480324407070000c1ca40c0412403442120200300140c84a9003445041140c040542c0d901c00b0080008141980d00080f84c0c17038124100841120700c12903282580804031030130490741d0380d940c042480120a50502c48851030490100c41070b801c00310f1b000140101c11205465100c850150700490030f051090040a001e191145410019800740d80d072060f0740407204000520181c40c4260141c100d0442c0030780054104001d80001075071801003200d0f40501d0222 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 560565404 1250 560564154 560564161
    0x220905040507030b1003080f0c19060605010f02070302060d0e030c0a030201020d321506031501110f030a0507022d040b0f01020604111801121b0e1602010b1503 70
    0x10150180d811003030340e8179029915403855540c00c019019003101c1501d0329001059160800d24140401c40120344402d00341582c01d02e241c0340c802d00801e41400340c1e50001d100132041000c1c40c1d00005441c2c041d02d0f001000d040c148010454004c3c05010b80720100c02a9020070310100d841003a041194000c03042c0b0940025032a40c188100903070455100242040460b18002800525060f01040b803501c0c003102d511284203180e41c0c03081c02a0b080b2050031103041e00804008100090203e5a40c20980240d03000d0340e0750600244100e070500c1c0e8500a0300e002c0c01903a0801c00001204030301510060900c5440075001003108040c45105603201c4101c2c1004855040c00c0b03c41c01203041c901440f420700d034200f0840d503a001540c61200001d5858800802c000d2512604140c04076444d647d11a132054441c00e081c440400c1503031200c4280d1000d110100d411100108a20440b12104484466440c1641c18004d00100305540d0f402e05101e0080e8200210015075680f00d00140c100c1e2152065000300c50095100e40e5506d09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 560566654 1250 560565404 560565413
    0x40501050a0203061003050702070b130807050d08040e060112020f0a0f0f0c032a1214070209040f020d0501110c070f080703240f0504140f0322090504050703 69
    0x5034000c1c80329145502c104104103440c3c2c0e0340300c10407208035510300d00005c244d40c680006078075101054100b015001404191039100c2e181c17070300e04c0b6001e4446440c1500c0c240c556510904c070000d0101180240011018001806000c2440640ca039100318149022138074201d003148040120f80c000290000c5401c5d0019507903068a8200103402003a18441c86c2480d003101c50031200804e0031601d240d0080400c0340c801c80300c0001c9000c0030700e0404000203d0400700c2d83c80840303152020b144110021158040340d0783c0c21401645103180001d941c2003a4003d4a541c00799078079a5645d8401e0001c02c50103d0340b08048041c44000714209104850100800344203003969104e80801544c034024195000203800c040350802400130795001300e00395044a41c06420912001c1541440700000c65031035030031f19500380c42d090700680c1100c03054100a018034007801c4c1250341e1049902c480b40d120310320141502801d500c00c001c1501c0968145000e036000c0d121185039084005e80711102c003815100c0a480c10340741980111018010301c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 560567904 1250 560566654 560566661
    0xf030c0615080d090302030d0318021f08102301110708072105120a0507080c0105072d0810170304031a160e01090e0415060b040b07140a08070b040501 66
    0x20000e403d200401307501e154002542d542004202c0c40806840f01010112100c856284441d9140c0c020004400311000000a43c41290903000d0310001403800d40102d5005240c0f5000281034906080c03420401d4070003020318114541450609c3c41c10054854a4076501c0c0c0e009202900290401c000640f04840c0f50110300409181c6000d01100103035190568800000c6001605600002080301c40c0d5032110311a03001504c0034011440054007503e0300184c880c0000d00c040d80111300c07800c882e49130484c408142400005440c0010b46003038400d50359080030709800a01803900180c4c0801647c40c5121400d89440020349821964808216103500c08036080c01008036071030312620b11400c0d054115650786080c1d0342d020742d41c910742840101480400050444542d10552100c405400302d5203010380d00341428500441c0a80d5008005281c5514010000c00d65854210803074088a0070690810300b0405140c440141c0050000b0b4010401d204041c182c0300001c2c0c920002c1d290041c0100f03141c40b040e10703080c00c045095 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 560569154 1250 560567904 560567923
    0x3030e06071a371104050a0308030601080c04030b0423010612110d020109062601081015060210052502151006091e0803030a15050910030f030c061508 66
    0xd8480307640c503880c0822051110303410015503d80100e00d50b502065552014441d58000641100c84914007100b445140c2000754082c9000383e0302e0941a45d1000320450f601d008500000f4260701d01c800c00308020031141a01c8110040b41c1840b5649205581041c2a08403841d0f540032030a00c2d8011b04502007032041c801c0700d00000c01c3c804d80b00141c4050280c1d000804d000c0312800342c0001d11040403007003038043d4106040345002015a120502d01c1d540c4a070411603840f10714520b43d001460900b8200440c142c01c03503140ca0211160b0360002e00e04401010405009417900900080d41c500b100d10140c82d2050301010003402164103030b009072081900e012101d9a03c124010a1102a0240600d04008441e03004d050441120840c0500380d0001c0600c2004120b01b41c11580f101103944004001c0c0210101c0340e40c04094800ca0618010320560342d281c05000481001f00c0d111502103120390010004108002c1100a40c1d600c80e15000f03001c22490f40e1050300300da03280120300c2608030501200b803141d000100191940c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 560570404 1250 560569154 560569201
    0x9090501050307181b1706100f0c0807080a17010f06090605180301140a4a030409060e0a090f02040c0e06070b1f0f03030e06071a 57
    0x16581804003007903071240e0511801080c04480c500024500129a001c841d550881c1c4a04244440310428010188418901d1034000c0c1400c0d01b0100d022450240e69505c0083c40c1c54841c0703103c05071500003d8440011980c07084d11410400c0080d6000105030900810880300c281e207900c07024115090301c11a1424058001700f00903807044800b400740c02d40109965044903071914115030344801c000c1481e08200320281021f070b0190300f048401c10304141c8282149219900007982041290b11034103550012096024111041c0d2807007540756044442c5010368880c0f598011031821944108962403180b45900543c46114516910310051205807407010400c1d402544da10380a01c40012691101c01210b40f0300c5000a100300c2d596a158501c1c0380c050b03c099004030340002c02c00d0b901c2c1d4001d400c020410f171408648080c0605030f05941c180030542065009003d80d0300b85000142000d0450784c0503100c4038030101145038041010300100b40041c0114400d4100408404240c071420f0809a450488900300c0089005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 560571654 1250 560570404 560570411
    0x140105010812070b0402010903060203040b041202032109030708181801080d1107170a0c0510020304090906020d0501060315050108151e0d260f0a11010f0c020c010909 73
    0x180c5102c44a41074580761030704103c007001152914801079400354550b51000300314030300220401c010300c0000d05280d44a5405849124000f81140300304a0712440359012210240d000300c20858810351140100c035621103420402c4034034008494aaa90741600400140d203498846060380c070816042c006c040d0442c1046c0140c02c5111541000c0000e5206c2100010324030400c01401c91408400008000d60b40050034105000c0640c10780480c90726484d0501c0c09400d27550785441040002c5c01d8208000042c102d201994042c500f400d00b8040c0060107082c050b9001d0700c00c15002e006140d8401c89a104040c020100c0761000100400b00c03a030f058000850543c01681403101c8001001100850400c2403090000c040781c043d1480894400c4a150f6509059201508104608112010002c80c41000280d10080d00303c182c43e1507441c4d07024848184a804100242010288000c442003809500c419082c0c0c04044c0010640c2481c1d005e0760000c07205009000c038010f0740145010082942c0000200d00a02074107407007131 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 560572904 1250 560571654 560571673
    0x717070f140f01180b1b0c0303090603090c09010b1b07230102191b08010c02031c0b090c180103110f070c030c14040c03090201171f031401050108 64
    0x281c1640c512140c07050250318082e40800b143ea215000010700c44001c02d074103a003900e80700c1082480030740001140130f884030328000c14406042c0b8005404a158440200110f207050b680d2030070b200795600f010748420300d50312071841c00000f990380c0d0080303403070103003581c610315a0300c0e00c2c00c100d4607800c0c3c50f4420000304203d0b0408681800014601c5101404449100c014685241103402c0102e2410700703020b000c8070008150400c450100041d80084140c101010103404401a84070f10a59080300c0302c904018015074410040403004401d6031940d80052007000c2000502000302c030006c517580e40c100f1210000000c00000318001c2d0260440f203180060b103400e203420400700360306119003102c9108245105101e0036002c208002044441000f01001d10b90144c5221482a03488207030740a900c05406007281b02e54100b85140078441d10910a01d00c141e5016524600610464000710f020848080c04204841482c07050f00d030820451050100c000b184558a1416240c0804904500312601038021080580110b440c0d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 560574154 1250 560572904 560572919
    0xe0f0f0d030e0321130803030c0723060a0504062f070c150c0b0a0216060c12140109060f030c0306020307020109060905010b030124060518030717070f 66
    0x8490541c1d8107003040321200030041c00282c5030011003000036800e90381c000351180c40f40030341102038009001d182e100b01c81c1540d140c0e04013540341d0108072900380042c0001c0c000100072526480304254104941118544c2c0300b584407501c44d003800c8003112200c041507100d00500082104d1803140707030440c400302017400e911880b0b9000309042c1c20760540080040c9070400710710f6209000c1d00d4900c44004000d4501d001d24030140c403036030190004d080d880c1d050311280125000103180526500884203160006c1407501206056070307803020010704440c4462010412034401d5014002c00521074640d400d406814080071a40c904104000ad49040b42c010072441300d8541010000940b6850307280c02602d41c01200540c890740d40794022401059002c4014042e83d0403e0b00c00d00c14000103500000300d40000750001c0c0251110b4004441c101c0c000504d02c2c08040c0080c8404010b07161007040904100d101c00244c031109080d081c00001e01c2c2400c2c07900204d4400e0ad01c0458000d60807800c000082c0100f01050035102010300d800030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 560575404 1250 560574154 560574169
    0xf06010507030e0414090609060c040b07020409060f0609020d0b0604030201210e0a030f02010e0706122d0203071706030307020d02030f01140114031504110d120e0f0f 73
    0x7004040c089a800c00b00003e90f5180c100050800c00325045400c2c1d8030b4040350f8181da403041562250814005d00c00800c140380020f000701c8080c0c8596580c2c1030f01e0400e8541c24003000b40103000c01526010341d500741c000d079552014061345009042c038500c096225a0400c600c1011900d00782c12041c0b01c1d01e4104800c00c0141d0300b00314500200c0104041c0c456040c2034010656000e848541e15111143c0501c07a000c0080540004510552840d00c0e13008000145915010a03680c0403d030017802c003c81c155802c03541d003e2556401056481603456280c3d2290780216001101c80c4a0004d182c18400e1340210802600c1a13010600001042804188803c207007844d00100ba01d84c03284903406030041d502480900c0c29920308000310018400741034020000346442a462038440315084c02500c06900341411021128500000c09006844150030440050b40b030707640e48c1d0498020306015075500940e804007200c0100f1000e50392203039000b0468842c8490300408800300100ca4081103500c0d4860002050b4081d9503844115 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 560576654 1250 560575404 560575417
    0x15040b06060702060c100903080f10051512012c1003080f1903060f06020a0503042d09090b07030e030a1103220f330e06030f0f0f060105 60
    0x1107049688030001e0022840310700c9203046500481c07086020100700c0c600c02d030380f020b81101c1c0240c3e6508642c1e1109000e6000361a0b0584403184400e5a403007040c0058034261086c007451f103105c24101c1d4541507544410b1300d0078000907402141c01d29585642c40780090407410202c03169016006040c05145010402c070310045000d800060041a80400d58086441c0420120765001d03041c2d207008500e90120080c010041c12450040c0602c0d5031030bc10001801d20700010311503080c030368054007540c145420442642194000c0d030507004040384001041d80d5100d0840c1d4800e1028200728038010510000c1c50810b540c400501401c3c0e00c007003518160a07c1c0c54804e010040e80d902d0540e81c90202000440480d41030310350b02507402802580d00c003c44090300c10304039611107401240d020001c120001036580a0441c020a490010484d0156001d140480c0802c4d2240014a00011030300b0402e00070003100700072aa140d00b003160070b003031600400403d015841080107401d43e1300100303111400d815403a00e100020103500400c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 560577904 1250 560576654 560576659
    0x90906080613060c230c0705040204081905070509090d1103090a0303081f0801060608011203051207020a050303040c0e060f010509130605130507081014010e010203131715040b06 78
    0x2036004143c0c01d80709540c0003610314042540c03940305c4403c1c41641c401d02c1e40000c005455503c10b501c000949800c1c02d0003510116020032024141500c2903d510b11401401c003482100d0794081c900f0042600c3d9110a07103507005600701310060088444508015040054009003140203a02c00c1c0074242107961074880c000300341d030341c90701d401e0ac0c2c20b4451048000b44000b0f003810400009601c0540800c645405501400c100d5030700e595107080e0f41c3d036680280f0808843e1410040c00050b07040040303400ea0b2020007402600036a03688110b5280c0c5000351602c5065410540e0100c2e1400b408000800c195038401241c107401c00006c0303840072801c02c25030300041c0062140861040c0592030f00340c000e0240100a034404070003050b0180c80c50040c0e0307070048048d500614003103502c04080348440c808150880c12103003c540a40d203200d0b0a00441d2003031000107440916000da4500e0452104003e081400e882219160008000e800360f1401c441c805400c8803030503ca500e40601101c90b000f40308010108080110081d0000c0d000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 560579154 1250 560577904 560577911
    0x61c15020a03020c0109122703320a060c080609360d090f0b030106080406090503071b08030a0e0904050a050307200d230f01060609090608061306 64
    0x1072100560103802803c000707035169441d010010041c804200311079610505035640d680e9068000107684a08078804007000c50034880d84080a01c0081c400c1e600000d0014070741c2c0300c0c00c19000c0c601500c49850f2000480d00c200d403500440b80354001c0003000d0080070058006810400c0262800c0b1001c0f441c0000024400c40c0342c0c8800318042001c102004d1104030f04903480ca1640f015942422070903c0e514810104020005400c041c0c000540910f410525010307103941c019000d00c1d5900e40041101e1201e00a80140e41f80c7e84d03030761610800603200300020074916209582401c111426003103501c40c0c00d0201e5003d2112a00200062555564007800801c01e2002c1110380208035180c6044c024504030742c00308000c1c100d04c00001c880c4284004000e9030425298038403001d8030381c15a8203060140c1861480e000412a642d140100d442954018603260320206550085a0700d40031000b061034290703203d50b4001000300c0c09140b0184010403090041d1030240403040c00074152400c20b4252a48800740041d806450286d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 560580404 1250 560579154 560579167
    0x2031908043003300603110a0b0a0302030901110711030c01020f0a02041a0909030c06161403040609020a0b0909060307060206070f112d0619020c010b03030a0305061c1502 75
    0x202c00341c2c1004200c00e0341320102060001d4810b0000c00c0c1500003910295203c040c4115103190101e040740544d20001c0c5440d040010602080d406900054408501c1c1c1d52541440308640c03402e04081d01c0c80c1806001c01c1c030288080402030609110b440c40d0000c0c119003040b00b5030103c800001401c008142e505540014a0b03686034040300d80422000302080390300210ba0003d2010580c00000501903c1d5104400c0c0c9a19442e1041044070040c1c080301490081480b1000809010007900d02450703115015a001144a134016030004403400e07a980c000844050010071054100c1c00e0410340503900c501c2c194000c1803c14202030b0041d43c1e4020082c00314007003096400856810303034483d0300e045910981440464555114681d03141e03416580a100001007112205003c0428a0000400500440308494000039000e002c0d400c4c400a50701000b0090007035034031483c172810784c1d8404000410741c2d40100d13600010300c5c3c104442000803c0c41c3c1c103030300e000b0050804039244000c04c400320003404040c0d01d49100140d50b240c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 560581654 1250 560580404 560580437
    0x809130e03030901050106020d050702130506061606060609060305042001140301030f350a0e120c121506100c02030a031106160e040902031908043003 66
    0x2860300d61508441c0804028080c190205410880c181c40d001e40079106039562200b0111090300403440081d50020030815892540482507205503088680504074500c3d004005144030f0b54904590000c40d0005c2c5da4240c10080c81e0f034031921640c00342070140303014050b81c10309840700c03408020310300600b02000c1104c0000700020f0303004a403004001c003024081140c03a5039680c2000d60070040c01000c21f0340c001206c802c480b40142214442a15011010300d0398140d542d800c0e01c2e01000c660051720249c004c0c0038200d90520030594130800d805007a0249100101281c080c039a040c00566014420000319551021b150144500c031306500603507000c0001d681600101c0256442101d0300c1113a07400194050189440340e206040d030000d100d44400320040c00712034041d2501c40700e207241792030800c1410000030381d00804000d040c5042d80101c40d10340c3c00142120060a44a10621048142e00e030003110b8500700001c00300145803d1380c0722140c0c50b4141d003500300380c01c0c208600036109020100c0d4004040107440407414075080c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 560582904 1250 560581654 560581661
    0x150f030702070e1503010c11031812010905210a02120721050d110301050f1c0629040516230307170108011b0c05071206060504050f0103080913 63
    0x1000390f94854801d5060901c40c205400e0515401c0038040d50920b148000458000c034070082c01c40030514000d40ca48424200c10500d041d00400c842940940c5126440441c2c440900a071800075000d480600784200d0b4200c4084a501444181e005018000703110300c0241c990042545921450303e518203594071402e074a41851000c2030f0211603c040c00382035000030405e079404000341c80c41c4408405c040000940038280042d44d03000034425154048504a8942103c0c1000160070713028840c0701503a00340001c1641d6902c401d40d20031800c28002403048010034003140c05031008604c3c141006440030003031400d040100344040310b0009150300c140b08550702d0340403042101056110301e40d80c40c012201e441e0b00b40810700520a10101505032003c4004000110342c001061055480f0007502112403214940303400d500b5181209562401e40700c03401078441c0022a40030000e401800c1611445c000a0080d0410701000200d0b0000ba09800c0d400c4403110050000896940490703540f01e070116028607401c4005040030f03024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 560584154 1250 560582904 560582909
    0x120c090e2d100506040b0c011a0a090e010207060f0b01091a18011b060209040b030102030124090317090907021c18050a0311040c020a031205180d0809060105150f03070207 75
    0x4c136000007000904801120060032911540d80c000780003030400280c1146144031014a81c0390b01a0700d6413020403004644d58012142060007000250a009407521a40111500986844c0442c0d8079204003041340e6174088804000391594000c0707030084a041181c0d0750a0750194010541e0171400034245070403141e000b40d18120300c03040c1030b80300152552013603d071810182d0009070306540900d04001c07007010240381c18000d690507030b0303c0c2c4401c1600500351800714413100c2d80ea910741541401020440400802c0b4001c40c140002c004c814010743d9200416401c0c401c0b2043d0003000c040440d0440608408070114501c03402580c15a14030b4401c000303000301104000c500c2007650015030712000c8103c001003041003050011000d040c0c101c80401110030b2460041c0d8844050800c01800071326511110701c0c51182ca0b5004a4119556460400003901c501d140c5519105101203100e022503403440421030860020040b04c1c0c00b4200a45444081d01c0e0304e0101006a03024500641d03540b03c60100c00a103036a842000201c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 560585404 1250 560584154 560584159
    0x19050c01080c07050f010c03060b0a0c020d11060d0603122a020619020109140c06070305071104050c09030d0f211401120c0503010c170403120c090e2d1005 68
    0x70a107000c0c00d100d0082003511f8000c0080b0b4109040000c0500140c4103030344e8040c0e0281c2b50780351140510380c00c110186999901c1111202c210300d03401d403040d486003c040c101e07072040361380005a11820741c2400c00c07541c4080c0300340c41c0410044180b454803403400c010091440d070465190b2480003500714030000b1980d00803031000700781241c8540b00751003c2503070542082207181e0280c052210b2451209440a841d0103504825a411003c10000c0c075000900c00c0c1c0040c00d80b00e004141501e09401203100003801e41c2c1c41581c1301d851140003c2402c0a09143c10310a20341c10009a08060006002100002e800e1900018552007405190344014001134001c0d080141c1d1080d10300c10690362076031115081c010080c0c8260081c1c80c010803003000401e071420705205100300fa164a03110380e1012882200113840281c8010012000c05c1028041058241e82500400450120a07102c1a85480c10440043e8541000074403611110201c080705424040d290151424106000684501590303185042001c113645254030564 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 560586654 1250 560585404 560585413
    0xd091a09010b1e131d0c0a0f0e060114040b0f03040209060a0f05060c010917040f06020606091303120609020d0c0201050c030a02090109080303010f0f0b03060307062a1419050c01080c0705 82
    0xc090600411006c100700e034100c54101d42c80e511211041c050b0381c22406000c2072070b00910041340c0e02d580103100e0014600844448a80b5003074503202891000d403c2141150344040e4003009100c11864003035107691344060142c4540b07000c00c1c680b04091030450f0152240328082e080005071805900001e4202c011076540140c024203100380722891b0502164881e100740305000340d4402c00426401c0c4041590703409034500510015164070341d2802d2038602000c823a011001d20100e655108132680da10702803900105045a4016261007400e15500195264003440c90b0459252008012050542d10b0640b41c0240500340c0068507183c0c6600181d803812003e400c03402da1072002000001d001c140b40c172404001d80d201c921b00e00e180310b6a5030701d490901d07000c2038540640c150005441401510312170400c1000410034280d16500281d064070300641d0710042d810b42502c401001c0c00d600c4c2010b84d0104030203800190613190101302e02c0d165403075117900c40d04c00300c1c5524100400301d0041208441b89400f50b5102c46d1f0040144c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 560587904 1250 560586654 560586701
    0x1401052d190b030613020118031110031d0106050f06070f08070206070803041415150405150a060e040c1407060b01122a051603050d091a09010b1e13 65
    0x2c1701000c1010b2040380056080c05003020309008496907034013101d034802c0c00302c40c00e00c03030640c10420400507100d103600070035661b0294628942c24549419079031550389000054594180020310101411056045001da80100320000010b0031402c5035800c010340240c0c03501e0300c9448078800124244a40310014000341d00100a100501c6010005c14403501c1c0c0340c4085504070802e105aa0200043c11290108440d00b004c00c21021400c0c04d812045e072100c200c1c290b82c2d1810a02030001030b810300c0c15400c418000307225051558a181094401c03100d100034a4103041d0720329201e5020b0382005210720310008040a803107010003440e0b64043c0c004120b40601c480000c1c0720a2605014400e4181c0140340400064000d08190321082401101221080c0381d10300035172411121070762410b03a11a072180d015140c4880c2d4034080b2002184a41c00003800d10004a01e5807c200d042401c1b1860a6411035200e040c4a002200520024607040741e00d90b0340c40d803d0036070b140d51030801d081d00c554004200429051417040c4108103030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 560589154 1250 560587904 560587921
    0x2030601180e0109201201061509090b06030106110102040e0109050f060a0602063108120703050c070f050c0415060f110304211401052d190b0306 64
    0x1075107004403100d80c108811140d000c4258244c510191002d02640c041109174401d001d0301e8402c88a00e4000948155140c981d41c410580c2140c0c855400801c804034003064074940d0950001034400289a0748600744800018240014020320041c880c580a20042014540d030018082d01034030010140700003c40d1056a40b45511005820121100348007001c40000046c640d14107135030306000342d1b800755000b4680c56440c8100c8400050148c03030b84151013800d9004c51103020104203120701640344642d50581c1c5800745104503000325000a011171044c94206410000f6030000f410642d41075503002050302c00b0303c1c1c003103040a900303000384480041c0e0042d00702a02d00d0310781c8450500711030407130700265a8250034601c0510215503050424100040b035410801c000c01c2081e8100580030510917603200c62100342c030301c10380e1040c180e00342c0e00e9003401c80c694450042000c2030031410407400d1a4003070042c59031502e42c0520902091000c004280815140c0d81c86c1407840b140009a01050350064054125112401c1940e40e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 560590404 1250 560589154 560589179
    0x21204080601050105070516290c060a0222140f030a170f0c06100305060a02040e0c180d05061e040807031d030a03021b010e06161b030f0201200c09100302030601 71
    0x5903001c05449e059500c45101d4084200c60400f41c5910140549880c4c030f03000c142c06540511101d440d54074800d1440c140000301d00e000d03080240710170600f803010150f03020180000042074180042c40b80d0444016034011400c54a1038500380380c0fa442c2d40c2036a50004031040900d07801684044600b0340300703c50802445040248100040c0c0340540304540560343c03081e80c00e009a120314095800d08003003c0d0302241c211089440a040c0f4141e8200800b28201303c2c1d040030179a40361a80f601511540e000130203100d80041e401d0300e050a01c001c04040c0508915054407401402d10a100005007080b6403907400341041c0c064105500b140020003010344404da030960070025640e0340e4143e400c0d88910b8110f040c21520358062520348881c0eaa0207040b10741000c0c1c288008503c81803103e5015034880c0444000c110840f5000204000070310b1180032850040b0300b01b400010440800c0860301d4035210070604000912810008010000309000c8803400c4483c0c0c3ea45000c0342c04112a030748002c4d09441740703500109046042d803c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 560591654 1250 560590404 560590439
    0x1615060b030f340306090c0c030c0c080118121419020f0304062f0c100e0d0c06020c0f0f04090305090604080607020f011b0518090406050601021204080601050105070516 74
    0x240d045c0050398407901034070100d510b0b118681c6c011894201014002a01480601c2c42d200e01401d40498155a9104c000f82902c252100142c1c00d5082440c0303a80c20441b0002050240a0541c9000100d800282c000702c4c05500c45d519404040480804060723504e180b0030081d102c0b450403004160783e2541d64400c40a0809090035402143c01c0b0341042e07007101c00000d103c08012005d80b5000013460f1200240081c04200b01c010720b0100c0400c4903486054915840c1c401104507601c0c030070405500c0e01440c02600134240300001c00840c0c0704150b902c884450302c0d901c2c0c07400540d04642c01c0b20300180c038400500d002e49251155103a5150081c2c00400e0001c0d2070ba0010441c01d00c1070307245801b40c603d60711902c40300b1400c132840f07480344c40078002d210081c1241c103900c1100038080180080c044190510500000542200c004440455210b500d8a003001071a59040c05090721201c240d1005a040500703010103640c46810502540d41041804901c140601408000130104080e90503009a110b40d00c1c0c0510018913603040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 560592904 1250 560591654 560591657
    0xf0f0b0102012a03020309100e1506040c0e090603071e0e010503030309030d1a03031303111e0409030519080103022403070c060b03031615060b030f34 66
    0x5a01d0034402c041403400005020f88480180e50040c0c0c0200040c0d0083d0006001200b0764032440001c00e00003400e0340700b000030a03c0484010b01c103080c1c4003080c07540c205500900d4a40a00d06002c8001890703600580d2800005908036042e42c07003680c800c800f10380740c412664000c04409007900034501c03105207006880d8056404481500d11a85e8035801456a20701c170035143c0306410fa1042044402801556101a078000030b40404807012a80c402e000a10f1500503c051240700b0315005020010001030b0b5814504580064514409000340004500707010340340202d40360b0040362502c0902080512070300889054031102000445c400100078401400e802c42404200e009103c1010504640d00101d0032001003a8041100c092460356201411140c0d0380c0c9940d42140e015413500495401c5903010f2000c0c1c10415140c0c2a425003161030b40c00c000038920b80c16211020468904001800089145001c07079500014205c4160f030180c0b074201c00d40c6007550350709916554040101c11701c444000d841041d483e1039000e09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 560594154 1250 560592904 560592911
    0x1109040b0118061e020c03060c090f10030509060615071b2c06030606280506030a0e0106170601060507080d020403080d0c0201050727080708060612070509010b07060f0f0b010201 78
    0x4102090740d80311601b449042c0d05511903030010b291a012100101141d00303020740308101092110021170142e00461421502003620796080114034201040b6040e8858421034100c50101c448a1441202e403082c09005010303002074201100b800035090031400c004041300e2503d4142e1524011040c0d02d691608480c1a860040c44004a1514075001500754000d40006010480b88041412000a400d5606000c05000e000c14500002c140d07071050080e40c071402c00201c010440c1000c040d0f001e400c42d411504140c806200c0742e1a803c0c0c00c0d92000615905654050506587e5007070f140c209888280a00440c96243c0c600004010080191b0007006d088500009941402040c91442003a401e8483c11940200003d2400e0892401d22092105108030f44414150310700c1440c0d202c0320590704112039904500a40d612203001d0124506040a489000d00c80d12800b62600380c1c2084000342f44041c040c07141d0b2a5192010401c442400040d60000f540c2d072001d944200014800159014050300030130100c140954613 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 560595404 1250 560594154 560594207
    0x60c03050f28030501062124090b09160503060a15050d0506011d1e03030324010f091203140307091a04030312020c0f15040b01091109040b011806 64
    0x20b8051380e03060f00d1554030380c2440e458410100c0300700d181031224403c103020307203485280b415038102c07416038015083c060340304a05560a20841d4002d8400d10804180500c401008000c0b81c8100c81108040030b43c01481d103a566501e070f80740007551640141c1c001c1c110f40b11840f070641c0c03a10703034001000300400300d2806424040c40c0d80d204019100c4008928252a506a464000f05214a001482d03540c442c2e0171041c1d446400d072040c2001c2891034104448549154103031b848000b2042d0b01100c40c1c100011403d04c0c181c048060030800003011602688211411f402c900040c0c1d4003050b026421038002d05c918408056247e1400d0100102449414441c00c011825a031061524106001e82110142c3e505a290b146104450f40800700007540420b07a520007a01407428a100400d50520000104000d005d400d103090b030505040c02d1443c0c03141030b480300f241036140070091500e07605084240c4070a0b4004071400682c9510712401a140c201c4602c90303040b104406610b0126849030040c03511802c144c8010500d103110b60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 560596654 1250 560595404 560595407
    0x81c0906031811130905010b040e03190c03020c04020f120a020a140f130e04030f091a09040e10020403030210051e090309060304080d0b1801060c03050f28 68
    0x115001ca400c460310030b1980c2c000010034140e0503140c9038a032010b481c103641040e400300840c04964064000302c4282e5101c03082110549442c0c080d00048000d804081c5160010740481c8040100356600614140071701c4030740b04010b00d402030081400d0444058400e642d20801c0070038030f1045901200c0b1480c504c80303103200410b010074403610079114000c0b19500e50418807200e014030450719410602c00044101c1c41000000c2d25002c00d120084020b01c815698000241010300c0c006d041402e0b8000d041003040441002040310b580b00c48900d040c43c489408456580d4030741e403000b01d0b014124101c85101648103076801016440f40641c01801220f010364248c0f40310140e00b902000580d00150750500f80c0300e40c50911036900c42d00d034245003500701d107100707044a28044c9444c000c034803c0d4000b2541a104031002040c0200700c1c0d0006c4c0110184510102c40c108101002801584c000c600107005050030088045c0704041018010341c115040101d2045203141c44000c10150ce8151448468500c10b1149804001c1403000303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 560597904 1250 560596654 560596661
    0x30403020628020c0f0a0b01081b0a09021c0c090602100e03090f01090312020a02092203050306010309021e0301060f1a0d020d14060307211506081c090603 68
    0x1080e29203803400041c000c61050006900421011032860041700a1099015003c01010200d1413290b040d0442545c076003011581845200441c04600308104035200c10300c0d0381c5003a0b0301010380782040b000507214600d100b0342810380c407269441e400f511880c14045090700c40d0443c1000c012203440d41d0031608554130b80e4046a0941d030946495481c00c0e401805503030101d1034410640d80034407806151500b12150340742c49003007001900c40220070168000943c14000e41c00c00c41e0103982d210903c0d00400002d0440709840700c003012030310f62001e0104007011011031880d0703100b604080042600142100032200b154244043c200442c0078a240c401e61806100003a000960a0203000b160024402021b404500b01084030090780b00c8100404040c2c1d0801c213180282030349200f40c00361301c00c2c0c1101042203841c100003403615040e1550482d012194507210401510800d00c0301c00280c0c0b642c414655540302d0f45442114000d48a507070407501e1640105900c090701e0115807010088100c6160381e030101510360320380c01074045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 560599154 1250 560597904 560597941
    0x120c030601050d11030a03090806060f0d030c140703030905040b12150603072103020c01030b0d02040906110f0c06100515072f01020609061e1b0703050304030206 71
    0x5600020010440c070b20f44080151201030141c6030181030752142d8000a41481e600303070305c220041002c0d040d00b840102e400308000b03503000c1026681c80305482c01c04030003e0b03803920712410001d0400c00309020080410444916a803005803a0350121110551a0325021f0f2613140b480c09441d019514055000b011450602c5065002c42c001c2405000e504080b11540050140011b08403905842076060006810840c00515501c4142c0341007003846e2040245002824141150b0a0318101810005180110f540d010002214203a040b80c0009200d90b90b49401c0c00900001410104d03c5400402d49601d98522180184074140e000402e985a5035101401d00c3d81c40700d80780c081c1d80d8000f04a910403103045242c00b002001c3c8640540b107083d803c01c0701e092028052260043e2160f284503800d0800c05000c0d40c0410015812090f8072025200c6850412500c801d403d0315405c0ca01840c80b103450100d0000c0601c1c8640c02c1d4199214101d00d41d84422606014159034002d5a04800510900c0c001920516162549008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 560600404 1250 560599154 560599159
    0x9060e10030f1e0f060504021009030b19140702010b130e070e090c031e070609050907030917070602090a061d1e030f010905011104080703061a0d11120c 67
    0x11580c03681c950150040140540191203543c2501260200d4185002d12030310360311580300030071540707440d10500c240300355100505000d01ca003106051000074048880c1643c822030b00414020504004540e40d070250007410b400d800003c0080c020b0144690b41900280c1d560340c1d0940d2412075094041c9080002c5840212480c210380d00601003e10a441c41441160341051404040321700468504d400a41000d503003a92499080c2e54800c80d001020030148500b50081c012403c1c40c900d030a1904012034170040008000e507007016510074801c0104001e050444060700300c0c9099031600c0c1c54444c500b540095010501341d510411101c4400980903200b8019a620010102048445941808140502c402901081d2088452900120981034034104221a00c0f140014004500440300d41026821180d2200c200034426008100c02e000c0c446001170701c0021203a000300001520501072216840603503036148040d5008000c0c2c0704401c280b041e03400c44010003003400c589440101c1c3c43c2c800320603600c06810301002e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 560601654 1250 560600404 560600423
    0x150515030106030213050319140a1e1a0f1e04020303090f210a11030109020306072f0a020a06030506010c020f0301020c010c05071101080105180604110409060e1003 72
    0x1000620035005072000d542a0b261000785d407511440007d0400c0c01001500390b066400c3d4543d10b0a2044440765165855010f102a2812001c66203c0f0f540ca41000f480c0140c250002c600d60404000c00401d01d80c000820307454401c401070400c5000034014600541d10300e080b030f42040d041c0c0d0b024a01003040f2140140d43c0100110710700341c520070a000040343c403440b01c140e12070035411900e00c024806003031289960f4482000740648824619244201150700c10955009070724080040c00145c030000740c0c40340c008406040581440403959454010081c6040060140350202d03600f01010380e4000500d00c072600c0c4202e94903108643c4825085049801c110303034290001d60340034110400350a01c1078580d0400d02c4080c0000d80351040c4003900f1030942d0050b01c030840000381e00141d81010301c400d07030841c08004002440c2c541503d514000018001c1c41c02201c0c0c140500341200c02040d030704d40d44e0b5170060505a1600600a07203035659482d010b00245260f100b190302ca00c00c80400100450078640650050740d901c244a00b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 560602904 1250 560601654 560601659
    0x72f0603070518310e0313170703050a0c150e100f0c23060a051302060c19232a0303120a0603021002030307120c02030f0301091505150301 61
    0x40314810010381c960804103030740000c0c00802403290401141d000880c0c01d550440401403060080312600c840a80c3d468000348551000c42111801480448e618030075010b4000f03502202d06810700b0b0a80d480181680308422440302041801d040102c112183c10348203888601019605842c0c50700100703c150340c801302403044006120700800c01100c212850f840c0c042c6035580669141501c10b0411561880f64126a04181205040400403580e0008035401d0510140c2003c1c0803c00490007081402032140b0004512a150f9080421103144c404c2c810300c00d000083c031a9070402002605106074a43c0241c1d11007403199107002800110480d24207006000f07220910f60419603904203018668810f44c2c940010010412441c0c5280100e07401000f80e076200081c4a861803041100448000c44031400b990001d00401107080e8004141825002c408230020135202c45d885002c81c214441c0140d01400d02c0340c084004600603c103075024161160a0b1a08580600d44075010048210f152a40322a003544041005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 560604154 1250 560602904 560602927
    0x1030218060a050120071403280f020d06020d05060f1219111e130c080f0709051002060906060108040807030f090906091e051603020f072f06030705 65
    0x140000c2d601d2144010607650b01c017802160600301160b00205224814601c080c44a19041c04518003140c0e0022100c0d04d803407501030580040600240015101d650029511400d41d02d4110021041c0c0d9401301085503203041100c0e105000340001d8515034040c040210300c0c1c0e15141080d4012241c0104070714010050500307100003000382601491011102d83d40483d44400c0c0703680754410303d810341c3c090341a01150070300d100c14184040d101c0d900c04900c0041d4101b15211a409800100321500b0001c83e420889150351401810740350074810b548001d40155040b110004030f40e40c00300d4914044c054400070381c2c1c40b58444000442d4000303429038001e4070440c07040208900180c0031b0b40304074108106038102420600c4d90354401c1001c03214560f005050701034680d0310a1481d1580c4000100203940000d40030082400c0000b01020000c0901d4900c0f000d142c4d00241c0030803407541a034280d45410b9070000031a021081d01c50f2041c94207100b4090a10064840e064940b1040e01c0d115040e64440c841541c1c40a050038589420f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 560605404 1250 560604154 560604167
    0xb09030c130906061d090606090a09060b031207140312070c050a020a03030309150c0905040b030106030602030c0910020a03080406180c09020903100b061e0c010608010501030218060a0501 82
    0x300e007403196803400100c1c00210940204402090320400e050300c0c6030503620005012000042c6191425040401044491fa03180c01000c0d4200c4800c01000507881d05524040b0b0080c00c00300c9483d9814490030110010810f00310000f0642c052103072110880424860310040d41d24080d14030181014103280002601442c4100c800c140042c0c01801114508d0045801050042030941c0054000940381c00104040c0310020425801c450300b0f1502c2013080988d0110300401841c181c1c000c0a1080c0d03101d040741c080b42c4e5003d400c013401440c1c102c0000c41d0380e800c0010742d0b610309501010700380303004280b6407011149560000c50701401298150302c030000b103551907603240700041c40b031914210040e05104004101188000c0d404501074000010016a91483c01c0100740c03920360303c1c021484545003401041c4109446044c00e40d076100202110406e07900d404850390038458003c01c0d0000319103610f480340c005039410741500b08074101c078002d071070610044007481901c03083d82404072a066002a8519001c12482d4840c03034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 560606654 1250 560605404 560605429
    0x12303130f080a050d0605011b1b0e1f081b091308130515042706080d0306030201091d0f2d0417030412030b03010219180b09030c 57
    0x24680d0001c0d81603591040107070001d40ea0b040c001180458076905d146030740e00ca41c03005044242000140407c481e51108070707001080c1001400d0316500a403960b2901c0c0b0800300100501594090100e030303840c096a035134330400010003400000d682250800038190381c012601c00f10300c0001c03221240300403401e0400c3c03103103051001d800d4000340794440104101140094001d4041c1c0c00e110811510043e1500c000c1020070a440c10441e485010704000400180d4101a0b540b102c81d03070001d2125040740c0070101c030b6400500c070550280c1e645004e0118000176240e4150300402c00d6030b00c00d032508645140c80300481c61000c280c07420107212010002020500a005130040e00d070b8000405032428040420480070102410f81032040f59842c250400184000c00c049400b040707a0320516120090706600c0d007920f8900c21041107d589100341070360349415a43e81c0d2070030340444200703482c050202c0b030468440000c010024500403100ca490030100c120b0205410034131204642c0038034070090007080901240e0040140800c50721 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 560607904 1250 560606654 560606663
    0x3150c0d090201021c030207050d030b01020d032c06190501030c06080a11040b0c010f0911100905030604110f0f060901050d0902090907030b18061b130803030601230313 74
    0x3e10210700017008003210400010142d6000358841c02c4d00d15084c1d00d0652180030220616051244195450340d0026001245002c1481c01007001e03050a0b60507041c4034024031200111103184c5600c44201d03103000580500504452f03035902092a194109081280d600703000040070700680720000c000c42885100c4043d041256584002034480c0d043c3e03800c444075409544415640c000100340c1d650b6440c000e08c030711300e082c00004c54140074441c80d640c0c0b040412000050018880c00d101d0801a0f10a849009104043c0c2006001c036071035400d040c18481282c0b01d00e5140e49120760445800004141040540a20b24940190500f810101064010354407900031044840314030742d0381e03205035002d40da039210520702804051000c1d046250541c14007042c03c9000400241d12f0007103c100090f005200011056401894403100a039848681c400326903041c410398003254100c1c0803c600c0070490603c040025030041c1c05c240c84030310703e84100a0071006844400145100403610610000d6400380310800b146800038880d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 560609154 1250 560607904 560607913
    0x3080405010b0d0c060201150f3803060406140108010608191a090105120a030c020f03011a03060a0e03120901090f3c02130e07030f0203150c0d09020102 67
    0x1920102c3c081012000007524024154441048025028402c8040c1000b000d02201c0307101d0305140e000c1051080d148150b0719107002500c6c000410403903518000c0744c444142034400d03100070001620304e0980c0d002034500341d125524090000403810b150078400c0001490684584100f80c0c13800100b622001c500612242c00007900e580c04c0400c503c450301c6180541c0308010814020078030100180414204143c210768010001c0c0d002d0b000c4d14400002e400303000c195061134031503214080da00c042404a901c505e103642d0150b00748003a48041c031001002c5010b6a0070240d0403100303241d40d0401d401303041d0360511034101441d4004000043c8032103810010980d102c2c0e07140f4008a0f205c200e50381c0780d2281d4440312006450384505640c032030012511403010100c0c0d0f00c1d07500c001c0c0310521450030b425903040c034140d030b10007446151241c03080c140860541c0c1102440d900000156000503990781410324001788150001c80c424003030403103040007155000440700d0041014a203e10f0034501c400002c40700408403901c00741c0c1503104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 560610404 1250 560609154 560609171
    0x5060a0c1226010311150d02070c18021c0b0a03030e0d120807020c0604031502030402010908060a0c030b2b05011415011d0603060607060f0501090c080a050408070308040501 76
    0x522000001800c44004542c150f01d5810f08040c003040540c0050300ca4030031155845203100200b03003915048484e10074010390b540c80518104441b05459800800d000c4403420703120004205940c06001903034a01010100d2440440b200c4e40110349506100716801700c1120003c0c00824814540c030503c40d84050021400c42c000b60f251204105500c015080009081004001c096070341807000340d524240540f100350505003140c0c0c9241d001203a1640301800154080000b0741560310031452140100381040595085040c644168009004601d519101090170210030800a042403042c4100c0c9420042c1c114003907511002c1c03a048034290b0301005a44540d00c1c0c109190450741c03000c9a250180480901041c0300c030504800150541022940310465021884510701c503039203030a401c4030750041c0d040744e04695507680d91070020300074114802414070040c5004000b0981805541c0184034180c003030346070b07a0016601c030381b0181c00340c5004450040802000307210b41000607000700002c5400510680000c500c880 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 560611510 1106 560610404 560610437
    0x1051801060504140d0f031e08040f060507021006090506180f15040e060f1b03010b09040b0f09070903150606080c1e031f05060a0c12 59
    0x4803d41544204c0b5038413001980c4810f1750001c00258088402c0c00c0042401e50b44e002603460046821962a020601407a01e95108660102074207540442c40e41e64500a0200a0209401e5100c1c00904101c16a03140c0165400f428610034000b030107140010030480001c6002c4030181c440d0150000303100b5810030301100f482e131040c23040c16407606414000b80450024980c4000f68a05400780c2001d10103071281184c145405400344042c007100c00018169a01410700c0284195013052a04000820380c60510303400580040e98024104401e42d07403600040380e00300e08221420f0000440140c4d05004000d0b601000c4280c4141020b4104540c6080c420007800e4004060b0042ea604140403c1055150011101641c0219030110741d15450381810301821070440c0400180d011100030406000c505410041c003501c5c0741c801550b50301842c440071519003d84062550341d2240c00c00c01440c2c4d150102c032 = true := by decide +kernel

theorem cover : BRFrame.Cov 560431654 560611510 := by
  have h0 := BRFrame.cov_init 560431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 560431654 ≤ n) (h2 : n < 560611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
