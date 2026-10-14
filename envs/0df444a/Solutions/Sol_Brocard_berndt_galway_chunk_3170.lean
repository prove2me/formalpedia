-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:23.458933+00:00
-- url     : https://prove2.me/submissions/a9492629-6875-47ed-a621-876fcf8483d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 569964028 ≤ n < 570143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 569965278 1250 569964028 569964041
    0x10507111c0f210606020c120d05030c030c04080105070e0102060a09052a0616123b030d11010c0c0503191101020a030213050d0b0411010e04050108071d07080118 71
    0x180f001c0c40c2101c0002c5094000540194403042540c6115161041c0610545c80d03007002d40c51503010402c00c20003c3e646032030700301c0210360184a00304240d00786a111000300d421039404441050229505912030045982c0401c506640200c62207014007280031581c0c0c0d8644c4540448440a401134552040314410341c000e401654042e01c0050240d54645072036000c0754000d480203034000c0e5880c0007aa02c4c20070429201d007009810a00c1d0249488010034005440101c00e51340362030200003144c1c0388804401255400b07102c00300c10452180c4d01c40e079040960342c1e801400c54804840b0f80c3e050000511040001440220507a0f0200d0765201d0045d030b50468004007a071300c440510325841510751002800007036103a016406000305444008940120544841c144410701189036000381c44020a0710000d00043e02001c0c0d01c0701c0c0340e20180f4080d10b150042d2808101902d60070303040300c1e0040e086940c041c400710240c0e403c01e41c0301a002495441050401e0b002c090490300b010f018002d0184d48245640421070078941041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 569966528 1250 569965278 569965337
    0x7020d0e0f3d1d0a180e1c0c02040f11212d07030b1203030a0509010b010801090902010c02210c0102010c2708010507111c0f 55
    0x3103141e5034819042c0c01c0b1400c2450310320782000c10701001a0122802225180c0d0000001e84414054071000d08a010b031245240c0651030b0f21116604000c6001aa5100c0079000303442d241c000131503070400e840c100c1418110b01c042070699010304062803070750312a03010546c6500550140c900080d601048075048001e805490304051003058000b400200b00d0a154104082602c981d82d45025940c03540c04480280c1a6900b02c1072542c3c0304010b0703400302800e001c502c0168204100307040004e100d41244002c161224110080d00d40740d90030100c104003146020b80101c66010b07840000070801c02c030854001030300e00c3d981070050b40c0f03030260b69050680446e40150910808607400030f18121034941c0e44080425514071004500300cbc10b0013a00d0544e84154014050410300b452243c036004030741c06e5801004c1f0748200594050f00d800800f0382c640050104000c3c8940b034007a8055507242848100194410f5180010803141101c0d1810007090300c03a4030592020040e0030340080f5152070b00880c8a9524010342d0744202b40307400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 569967778 1250 569966528 569966539
    0xf0d020909010e04033507030e120d270f05010e19061a01090902160611190e030304060e01170708070906020a0b010b09030f010f0f060e07020d0e0f 65
    0x1140f07620744002014810391199a407030350860040c1c07001c40001070085400961510144501185c405c6e141e201180d48900d40c0e20300007490b907011108007481d016005072031b000b044200080c074030441480b5002c0c2d04a03a107106074100c21511407101c805180c00c2003485002e4040400340c00300c142001400e4100310071042c5207500710b4140060030b03950b1071030003100200308031032503807034800e103100d20050188811191758070585403091802e20f0078650340c000c1e5101523540510880c07440420f200182c4d41384145510201c0d824030b856181d040524003002c54100042000042c010090840c10050ba4000201e80070758040d860078400c844d61a000603980750a0b0044010365041c0345e50200130446902415031481100c00d5a200c400ca943d0306c0c1400c6c0e841d6000c120000c0d0a01c001600107000c000d03040d0b4003d008210000c0e044484041c031101c080e600311490381103150700c06600ca50444480d859180106070240c00007008061642c180307110003035035540e108100801448407280c00b125070b03136803070b800401e1810901804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 569969028 1250 569967778 569967781
    0x118030e2407020d02180103081207030b18150d080703030528020d1404060b0a06110a0611070c081c0e060715020f040f09050702010501061407051c0e180c0f0d020909 73
    0x18a04d46072b030001c2854004154110000503612440781c0070b0b0502c000d80183c62601900340e0705d01c0c40410000c2c01071000740e02090340c40b00040585ca4202c04162200c2c024100daa0301c80c600c0e03180c0101035850240c24008c444131a880c00e1600c462105142520760007030f02c000148d407500e41011031001391541e09661a54240705504100911109d600300011541080755442c118940f10401a10415000600c012850f404040070300300185d0f00740e0000c401c16210948142c00e2103141ea8a5024543d0543c000c940d107a00312400300d001c0030b0f6424903140204c8220f400c00c0040404420040750702c901422801400700b103606541c41e00c05900e168104c40166440d01c0200e540d494866414001d171100c6407240b049014070780300006003100d01c18421907058a03a00c8d500d00400c51101503400c1c20303d420500342030344c081c021130344103401100c65051460304090240d03c940b085400000308115407a44102d510030703d208086010411b904070601e08441100f102000c165450700120f00503200240518652250000b44900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 569970278 1250 569969028 569969033
    0x81e09030a02010506060301061b05070b0304030207090b03060c0a03020901031118010206010f03121110050a0e0c0d1104090f020a0806250c140118030e2407020d02180103 75
    0x100409200301c071a0000d0000e621002e0074005544400d1007200001003034030103110340074986c1144141e41d0328051002c640c0b2041c0c80f10b04151282d40181d5003100540c0c403a84040282034000e004182c040101200503184600e85200540030300e100307480072002003540c0060000038503800f0b68464080150313840c0d02e03d071303c84924401d007404400344040801e000d4401e080c00042c0a00068040c0010303a6404040c7e4988403107144000d50300003d507071030040c007035015110028111100d148602c41c4a070012080100d07000c420a0310702400d009018080394000c85a072041e4101094240d4a4109410410b5400080300c441a040c0001c1d500c200d02002036101a5603034001450306000500c51b0b0084e00044040400b503d03050000c80481d1003101d86490100d020400c100c0c020600b10750280c1c00803551b540010030844008031850310050100034044010034020502d20070582410883e41440c802c2040d000648081c1e00815054113000f42803000703215a449207803801c210b40f11984502e03481400300d04188030030758603803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 569971528 1250 569970278 569970283
    0x1e02210309011a0307030206090a090504081809092e050f010509060109060e04181e031103040e04020f01030e120c0c06030f04030804021f0305060f090115081e09 71
    0x80da01610345600f4007002e0494004035841500c1c03070704001001001c090745180d09000c095082071849a5000000c030307400056282e05409211304c074a2241600c65503c018403084c8440312014002880c0c0191250003c00c55002000262040d1001075038100003c02101706400f5422650520303042518a400c3c1401e03c5240c240300605d4034180c80c000c41d03440d0040c0d51500d00440e0200f801e4813a20000540714a00703802d00b820b0551040c0b100a5280040544d12006c0b92100c424014410072000543c0c9619500842815841a0b08000901004018601d01403800d0b86a503045031001c1c0000e03225039111008207400368040e500c00c0712001d18140a0302c040d10005ea46d02c201c1504402c2c3c48010b00e0250a294400b40d14107a400c4034400c03520025408d950f6102d0740c03411103689200402c104d8000d4441140840401a07003c06003003942c455070703030121f031514004003802514001c1c0302d0321501070741951006100403000002d241141c2d500c2481d041c08140e40d101c040c01010300c1d0324403a0b0b482940584040c0807620601 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 569972778 1250 569971528 569971531
    0x804201509090603061902030c04030c0b030403180b04030b0910061203080a09150b010c0b0a090c171207151103041a01050f01030b0102010605100e030f0303071e022103 74
    0x407a501c2070903656203c241610b84504031100113404800c03000c61000c010fa2980510780010000d8002400d00e0384030350320040804520b400a10f40c0030008001c01080503445421038400391401c00e413200710140f034000503803028061808000d25481143c1c0003e214400e0402101017a502010030038080b07290348016049420030203a5003074000445040000b510404140100c1007419800a1036540c4403103504e00f50001010640c4801c2d04201400c100c40c404244580c0d00140103034840000010250320918003440c880c5003503407250144000039581c07110140c074045840c56125106a001071303038540719498400c40c07003526003607401001c0c4e01d4009410017603845680034511070392040c0c021100d00c0807280c500d03001c0928248078180d4051210440c241555100c2d4009450202060002041041e200c00008515604040c8610001014178041855170b140400000141460301d0024603c1c41c1031081008001000906198240c00700d8403051402041c403c01444140710800490341001d0425010060300c107500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 569974028 1250 569972778 569972797
    0x1209020f1e18060a0302040b0607050d110f011506080606130e0106080c07050601050609010c050105010b030907050a030c0902180402030f0f01060912020d14060a0c02070b090108042015 81
    0x840b50040703001c420310001c500d025400040006150394515403c2001404940c540700b504070000b4041d450010b50b0802c403101010001c0e4a8684928800d6a000303460f10b05890840c0c540c41e0306081c0ea00c01800040407086c415a545403400003913654403000407a543c0d20030a072120007078642100c00000d01c030b0b0301c6440281c141e4941c2d0380c4a85c40c0d600d0790600c4120a01540001030103035088800108000e2403c000140448081810901c41c490582c3e280c10342124401d074040c0344111000010000e2002d0700703005104c090402140c82401e8030303007152642440d014060046c400700c0c40c4e001400c9220407100c4e5020030741415004105655901d0a026941c100b00c6040d501c2c1b040a140000020903030500a0a003141683c0070081c1d83d000b610140c2e002c00009001c211800d480b1460603070350080098100340082131160006181c003140300144040c000307141c01425400308000b5802800000ba850382e019403202e030415000408021a8160008a851034400c180350b080e83c41020300f21641030440b0f440340608021034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 569975278 1250 569974028 569974039
    0x1020c1b100302042312031602101106012106021603030b0609060f070f0606030b012c0a090228090510082d1603150c1209020f1e 57
    0x100001010740c02c0e8091400340c840201c03000c030052178124050b1003804a211400522040d400d140052841e81903612a0709100102030b1255990310542c00c0c880f608814041d0b052402594408070202220388581c0180103000d89510289600c0c00c6610094170204d101e941c00400c00c6640300c01660026038103007101c070402c030040390900c9112070480c0b514109448000b10050700d66031501c030514030050746543c40070000300d80e510014014000840d081c0e2158001942c0706500030b00065060055001568100b110021409400140d1498582038034230319254000032120008250380290f07100180f412017001158010301c0390728641d80804180c3d0509210111046e030380041000352107100c15440c614949000b8401c0592008460b0f0350603426078190b4006000021400004901000f8291420801c2520f00c6d414420040f440c2842408030040d092903411850b1001002000c10707640000d01200c1c038840380d4040703440e038984102d0290749030704046401413440103080303c030032720341c3ca15040c2001d40007211441d0040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 569976528 1250 569975278 569975299
    0xa020105091606210f0501060813110d081c0617060c0a0e0d20041a0a060f0201020d090501090b0f0c12040305070609060f0b060f03010b0a0201020c1b 66
    0x1070400701d09441186109444800e481c0e041500030b40e014020945101c00c240c00d51014034504051900c00c842c0c035a1015840410780754504403000300803117006015001302001e40e003001720004109840da003089400036944d010b41e04045003801e8600303001e4907107046086800052003242240fa940d2000c0b0030380d520f030900c44070070f10a901a540d544000440d900c0002400812142c1d00160007a0884100000c00400c1e8801c80d40d07203a5588101e2001a0001a0494101c03944000d010704e860f011f1f010041c4512400c1d09211854040010b0019100744950424002001000400503100b0340459a01400000c4180640c03c0c8514040c2d0003054468810782c0e02e650f907100415444011100114056032401d074109060501e081004001c0c2c071000783c030403401c2c49800c125000005420b1700442440c54021030000a08014038a8120261039191018900c21402002010b00342c6207208140da041d01d48030100a030b01c5452855080c1e00a10031143c48100314410031140109041300c102d03110600c03013002c1c0d27032140d02e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 569977778 1250 569976528 569976541
    0x705044107030c021e0705060c0105070e060913090606081b0306010801110304301e03020a05070602030a0e1c170403050a080a0b1f110303040c03171e0a020105 70
    0x803201c0c0f20700c0180050b08401e180c0794507011035a442e0f5140b07031241c03015036120a940e0000282154000c200112003a51100e01300b012064000241c1c9400c000c0682e03c083c602503150000590300403015200d0501c0d1959100403406001c01c59000c80702070151f14007150720212030b8014054201881d403003507922910403500041079010041c090302c420a80244132890454a55556600a1140200046c503503800c3d921806c0c4100d15100c250501d220300c494a0b4840091183e50904080c480c04d1645801890700402a03001055031100880301900c0d0004c80c01070700e0b030712072440c10303805404c5516000780940f148006181a4072a402d002d40310304409500c40712010300f0703400c2c040080d030442203401401090701070040f040d1041c00303403801c03ea02864110002922107013400000e846000101400701140c04181001d84c08280c01c0707803c1d800c400360018029400c40c507241c0e440000e00d40190100402500c1d81c622043c4910310080180d400401202205020f005022014002c0740c1d0001024180190300b40300c0401d85 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 569979028 1250 569977778 569977781
    0x1020c012702090f070c1209090c0306210510020c031201060216030b07030b0a0603240302092d13021f0c060b0f0a030506040303050612070504410703 66
    0x4400382c0c040c221650b59940c4105510000c08024101c0003844401014400000c821820200580c021510b80c00e4106042800309002c0320310750441750042c50f10300f0a0603c1070005080688080540b8840c1d0104a0151460b100e4140b50003840110450340c004100609008000f00c06841220320440844500740e982d41c100320b039a491160503120049028441c24008501c452a43c0d50340807080d420003140c45840803000c00d40d03004440d44440c0002c0d50307400780c80c0c2c40b08172255400606c0031043c81c120411607085400282039000c010b00680c0502000700c0f62151000303540650390143c000e403550710003000d03d4818413419100107545022407090888000440321901c82050700a88600d0715178070380404013000c2d52420001c01100c15442d40c0041200c003409500e42e80d10740010003030b522900141105080501d0054265074010300300301c0c070500d030ba0340714141000350014080e4212030044501090280c0d4016414446284a60084c04d00416003603090f01000d40720741d4103007600070340d0070120201c41d9640c800440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 569980278 1250 569979028 569979101
    0x305060a1206091a040f0303050123060c0f07030309030c050103051e091c11120c3c0a0507140307140a0b040806101508070c030c0501020c01 62
    0x414954800d4510070216000b503202e0442a03101d0f00d0360002d00c0d604120107610907101120304641d000ca04c02510800c02d03a040c0501801480c03182c40d0b01c0e440300505a03011980f075100c2c00c80a80500741c0840e40000c1d04004214115000701000e095401e09900ca081c01001031209020079140c08180c05000103065220f480f40034883e01140e40000b80605086102258200000c0d002d040148144512039140c1d4845080910901c0410780b03400c3e000258914205050030041460300602c00010700c00703100080400302e410400c203900d211000d40554a80200c0032900540c01d0103030a1070015404500c081840c0002e0b03d0300c00340f03018004540c4251382e0b40c4515044046520b040e1078041e04005800c004050245501150568005194102e0035488000e00f00f1603030440e502003040383c1d00c02d0007400901c1031082c2c8610090201d101d02d00d50301500c40307480980301c039001130301310810404a004d006003803610624106040c2e90348800203654400c0b14514050203000c505c500c5060300c03840780c82c1030490540b201c035040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 569981528 1250 569980278 569980289
    0x70e010f0f0c0c0f06021005090703030503010e10091803081506040521030f04051e0102031918030510060905090d0311071a011d1005040c1107080703030305060a 71
    0x8030715031000e401c591050848608468141c100c400118014002c1c65102c00a07100b0741d402040d00250354050001910400f4003a200f01e03030030024003400400da22504603070640fa00c13200c40810580300d040c1c0c03110522003103500a103685480c02e104850725040d880100b2801500030340d901c0e41c09413031380c44810060115084400358420410001008641400f0801070900061044864819030703454100c00c3c19030b803105d14410a08000058140041c1c50507001011403400b080208011400400e00080c2d0b40e403050160031058000c038003020b1442c0c4c902c240302c1800c0c08515000c8034802c5e50707034918005998603100160040703100c0c1444808580c82d01e0a10400d481130b20480d004000b50707130b032400081c1c008000c4003500c1400700c402084110049034000080d080d0207640840e001e41c0540c90800d19410503188440c0080c28012600705203e400354078121020300b0388204076000104d402411005507001061092560200d0082c1d500000d00c00c40082800c00450b4080d032001e101580c2e40c0d508100030140d650041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 569982778 1250 569981528 569981537
    0xa0602010b01020c100c0c0b1e0412031b021f030c03090c1401021509061009020304050a061a0307060210110c07061404050a0e0711012f130806070e010f 67
    0x300b07440c0b807811041040c005c0c0d071541003810b10008551140e92400b07440c1c1d08140104500040d440490b28813035071601021200107842c15003450b04040c032030a44c9091704940034042141100001503039851812035200b1031540213050700c1c452108100021650620540c400c00840c1c50060100841030090085071551603100c13a03424011400d201c48a18000030341d6161a0451080200f82c40c1c0c24001508000e005159001c0100b02a25080c0c0c242c10301000180c000c0c030000b6005009000c0014400140d9100c4681e000001040c4140b515000d030720304405d69100103a040c80b42d820300058070746e008102a0320b801140760041c0310310351201c644c3c030300079128846481d9034650000313608001c4148140c00050a041041026915095a882c0002c068410981100c00c046204030300348402c650704001c0d80100035241100030300540b00551181d0290031003524008010308080c00a100740c1100f02001c035101c03080c001450a180a80b80d402c400d959441c121005070204d441e00705a4015903006038500401b0500980c2c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 569984028 1250 569982778 569982793
    0xe01051302060f09040207050a20010903121e0306050315010303080c0f04090618050f010311010f11100504170301180b0d060e0c1c0206091c050106060507020a0602010b0102 76
    0x2d200d10b40d800300402e103a800340c0034131542101d952039000410006002e6401402c0c03590b21400c0c0711503d01c030071488410a05c00e0315240c07040daa9070407103910f80031640c00c22003807444203401c040141c81c8502d01d03a915500c045a030160302800326400d0360000040e030f94140e003143d82c00e40b2508152048030b2402e000140120760004009110b5140640007408540303000380c0c901d4242031b0f50f0391b241001d41d015500402e001034108030308035980c00c00b988200c41d8007030040c00c0c0e40317035565155840c0c02840020702c40e2001d04001d0a10340c2c010401e0300480c2000f00c1121001d00b1100480c40e034962180041605a4084a019141c8c0310070116019401095038141d91080294240301a005642400240b411920454112141c490410040340c2e0504c9007140361000a4090300c05541d07081c04001485415905401324440080700c0304000d0380b02c407019207001007425901c05003044000707103044820313040c0c240c001080c540c2404004500198000060319005d44240c41c808851521600c06a090380c16445241303005a00816 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 569985278 1250 569984028 569984033
    0x7060908031609450203041103210903070302060d0c02013215060309060118060f12030504030f060b15030f0412031d0a02130506012010051501030e010513 68
    0x4102440c9200b07018503c00d0110b03d84d11100010b0040c009081d040c059001c01000107020110316010303010b032021809040c801040b035085002c0c008440365038082008001c11070b5071031918200040b001840c0c00514058659888040c810081c20420b60071200550816079042e201080904588014000c0c48448582c04407a102d003090710940300601d00308003e0824080c0c040d007a1580f00040d40a20040c1d03019180c40d40c140310041610304c1c40c0000c2d18441c14648141000039221240d040d900350b8011000842c8100c2041c00c007103440b4022500043c00099041c22050104441e540c404050b0210542e41094074248a2030030000c8ca01080b26002b0f81800362000140010303030301001c1184010908d040c0001c000d80034603501c4103012008072000c1b2056200050300c10651400020304480c1001e12181441a8034250300020144000d911a03040c09081c14516817084020901c20707030303841e5230005070104410b00c0d00d4480c0b0040703038029426030ba0112345841d50241c0304004c10f0040d40d01c00c0004600c64514080303135a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 569986528 1250 569985278 569985329
    0x6140307051e03030f07200909032205270606040f0302040902031507030c08090a05030405010c060b030d030f0f0e0c130204030b0907030c0f0807090903030207060908031609 76
    0x110b4202c1d0345800300f00003140013415030901a000320340c054404000d0090003c0f946070445641c4c440f40510440e01001002690400001164000202d60071410b06040c0070b4001c41810064540120f41d214038880c03040d00700d004240170000c22030180c40400450989031801440554462402018220306480340d05101509203604100e210f40d10280c11280d030300b10403c108041d100400c2e034209000989817001140d02a91100369660408801e0011b860742881c5a960140d4a20907031180c0c90501a907900300c041804096030001d4181c880160a030740060a4402c4c1c024014007113031a88d2201c00b4a4604402c24411032489050400b40180000700398582d0b0507020049808800d80c000340899400700408000142c1c0244c1e40d070f01840d8244c004103030440c2180340015040e00583c002d000400342c00a020401404001010011603d01d171000140c8004030342030441c040d10981c00041e01d942c0c1005028010000103400030741c4205a0a002078032120302000040700c02e51010700c5000c00c5120891481901d0076203c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 569987778 1250 569986528 569986579
    0xb130605030c0d1b11010e10090314040902031006020313091109030f1011120601050307090305031204030f05040e06060c03070506071d040e06041b0909060614030705 73
    0x108a4041c2409440b10007a02a81c4524210481a1901d8881c1001182d081917003010b01161040090007042d000c440b03015590421046030401d400c0c2c54183d0181414080d02814011000c0c6a1410b65516160902c50000c1d500c15121a80d403c045c4460000b1907a2020060710716100100b0b24500200e4600031042000d0141c035481c0c01c4072200c0801021181e907408008240c12450b510015020800450051104841039800540c007011410490303075048081c2c0d90310b03403a481072007420929120345503039074100c465420980000344036110018101c02008200d85405100f94801d584024034464090812a414019403090100880c818404540146010780c0548848002d40d4103e070f007040e1032512858581030080d15148085034400b6202001c01260410380c0303030110340075207041c080c280f03212400580c1d644000704040d143c0e024240e581c010780d20b4110800d20080501c0b240c14046060703141460001030400c0e120340c600148040c4403101260501103880f134203c1c0c3c802011142d00c0d104030116207908800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 569989028 1250 569987778 569987791
    0x140705010f050a030f1805151b0d1806090506060901090606360b04060801080102040b030412090503011d01060806010b0304120203040509010303120b3c0612040b010b13060503 77
    0x849120306c150000d2000c001c07614290140c0010b0841c04181c8900400105000d0820641040c03901c8959610b201e500c8101c41410103070b00400100b0390031808010314150040031004120b5400c01c4003c07030500c5030014200d4012502107410101c0d9990f20301c0b204085400074450800400c0200b00c801c410303240c01d42d42c0d03284d041a00d120040201d40304281c45101458640c1c21410304040c005c60140704c81c80c0d00c01402c80c09231880000031407515080c030310020341500000300300400c16004500181202807055114900909029000b0311507000fa2281502c40c07004c1e1005000b0f0700790f04c2c2c1880040d80140000f00c1e94100e5111800252441e00c42d510384601014194040c0b10030341c4010040010706031500c9204c54001c1d40a40e4801688910112641d41500d0321105054840c1e070520103012251300141c103406c0301210f4124160850f46004441070000f070440c21181a511003c049100e461013480d00040601c0340e403142e540c9040c0c83ea00d4040881c118050310211070351080380003e0511802c0d0040c0001c40c0c0000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 569990278 1250 569989028 569989031
    0x207120c0b0705010c081e010306021b0f010506030c09040c0e040f140a061a0310020913020c03090406060c1e03090806070201091b030206070b070c0b04140705010f050a030f 76
    0xa441d00c1d40d103605684140e074101d5a0741e5403540c49110f45680720660b1900040407420340054490003162558914030f041c080130f00819400070348641038501324680702c0d00221109043d1066411000e003803074020001210002c1c001d000307400142643d45442d2101da80b00d0780d4003170981500d250410b10a140c184c00010001c444c241c0d400360b600740100c0c0790184188100d01040c030007000c02d00708500d030480543d40030b0b82d2280c0f2101e0182c08400300958010600c543d00012042c40180ca5a20100008200c00300490307110705030f5440000d0030203141501100610407404c00341d0303041c425150750f031000300e50341c462542003d03180c4010144260394000a2203400f003900c41c040c0c609911140c1d11010309a06001d0b090300c402000d13079951480d490070068255440140b4440c021100c40d0a540307150081006403007140340003007034154140c0015001c1c2e4011500000c14507040840a103040c80c1901e4107810680303003d81d035402c1c14400d4000004aa62096038811134012041e84e44030308264040310309074040e02c07c5a0071151100e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 569991528 1250 569990278 569990303
    0x5010f0e0a150905030417070b03070203190216090f1401051005091807020d03140106020c060d0908030f010e0a1e050702010603120203120f31060f02030f0a090201020712 75
    0x1a0007003000d00050311f05c100e00c50f141d008684980c9480e02500c1c0e4400d04041c0014010403149035000301c01e0b1b412444050541c100f400201050490520400100d540312902031010007003152425503000010041880b03000700042c0c80800e805140d026024441d20703502415003014600074501c18030140810190242260420300310710b00c04081005011070301800142d118801e0714082d0742d418040c00968020320f050a050f5541442002503c4810b0940b5140c05248001044078072007280d82c1c01003581d40d400c5100c1075140d0030704a4904211003428403490890381c41c45804155565a01c0c80780f010840300304c104621a0490382c00c610000f802c0020065405d655842a000000c10307802840140e406600384c0c0503541d6a01800c841c1151150081c0c0090502070114081141c41c50300820f500303c410740a11490700100d8858100090100300703407140109514246042e1000c5140c0c00d401441c01031516511140b860b54071500020211002e404020340107031b010000402c5580f0200d8041c490281c0610160540c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 569992778 1250 569991528 569991533
    0x31f1104030b0601030b090402011b080403050610051306120b06400905100e0304090204090609050901020703091802070206130815100b09060405041805010f0e0a1509 73
    0x164110358030a985182c0e03008200041584d240c400c011290324201c404500c68206600024090b11194220814201c00e0710b40032001c1c450440103580c0115440302c1100c080c1e00c1c000c40b1246148010340705180c024038544c0f0051741030240038024034080d502209404035010005c0d40b1111402c16001d004a50080d40c01d4441602071030f0b0b0301c2840c0c044a990401404894100b01020042300940359080c00380747d500e4040d1407000907602049082940c1e00c41c3d03201168803100000718904500c204c0e88614407003840080c00240c000f1031034001908440c40ca039820441c0e82c3c2e44c5042c0a081c0d00c0358940040004444400500001411101090308041d15603801814520550302040c5142d001b03072009810340c003102504204c003800402032a02c442000590405950a202040e940c0061150180444410780801e015030346403258401d40e030062200810a00034600b0f8510b040100710b00c0550280c071030303501f04000c1c00c485100034016803105489000040500c41410b445400c00600342c0f01880c0381d020f881e43c090320301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569994028 1250 569992778 569992811
    0x3082e051503241f030b120a15051f0e060411120732120117060f06010e090a090506010506041203050f04030605010b3001050d0c030b090f0c040b031f 66
    0x4d40400c0390b20002100d4100b08100801e0070052110b4103c2070307028841a500180b924400e101c2d10780610304002c5090703196580c94105061980380010400d400f990000150510405001801000b06403402c0011180c11440700f051071081d070401c400e8240071080030501c0e50f40b10342c118402005461040e1600361650340c15212001c21036481c8114541c00100d40d08024810140c0034900502c080e03861025041081010390340c5034800200500b445407007040000394164010702e03075400302c124010305201082c500206010300900c040301081e5224814400085458101030040f00c003600c00b5290302282c001060b990844040d0b10504984203100d00c180302c0000024014000e2034041e0015845041e201c2000d02c40b044803401c00b00030414210510381c146070b414500020f000d2410341300c090341c103002028001e0400f040c2807012548000e01c00e2002c036040200002c40412048184e100f00c00c1a01c4004900307504010990f501d4440c0300c0c1d815001440000c0030350f440d5020344000140b00070f001207a2200c011103500e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 569995278 1250 569994028 569994079
    0x150307030204060314280e0d080a0b010c03050301090c030213060e03100204030206070b0c16080301050a0b04030c14011b0308041e0f03082e05150324 66
    0x1010940115007401016014020035110010b094102e030b0161500103d0086403182c601d44032410a10418401868581c80380c2020501886107c200c944156030341c00024550a03007240c0180d1054646240c0403055031103040e04150302c0b0781542d0b5203821079007480c2080005114410f00744003071580c03c02200007504c2000c80a00c004180c107071590505039810106241c00c2107521508402424410081400140d866009480226401032140b040a603601810407072244200c45681c0342c00b9881c039080400b04281c1074000d505a54080da42805c68079139914030034009000701e0000170107032052001e041c4010b24210342d008016010515180d80803540c0c0e045028011003400d075095002844031010442448090081200d0341010003580903c03151440c6c45d003d070031052010000702000143c10101d518508601c0000c0300d1040d500a1100c0100400c0301200c400e0b8039144a4030b4080c00d4206221941c050001e405d991259400c51000703043c0c0b81c29420011611801840195072010b010400e080c5d05149000015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 569996528 1250 569995278 569995291
    0x20a0305030d0c0516080702010302040e1807081b04090302010b0d0302030403031e1e020717060f0114030d0f1707080a0b0319031b1415090a021c021503 67
    0x3950b0701c224554280c0e09842281c3d6100b8180f080c200401c00300300c229031048144464004c0c100703c0e00d4801c0791004802074400e5500c40c58074100030209008900580350103880c5807a0400044460703050b038036040300f5200ca85a42da428000d000c1c058001005003400d801c0a4030b400c2c86440002055a100e5000944481c07000c0380c19801070784082024820503810194040d80042e01041ca43c204203d1180010302500c2090111800c4035011103084c01924002c00080002d01240d1214134034028030790085542c0d9503000c40750a031000c21504000200d84c443d088050304501c1003c1c2c05130440101c559800e4902113400c1c3c40c00c10401c6030044034a400502d9102071180a00c90719542d01c5042d00344044190151980700310800e00c281c202c2e01d0018803403103030b00394085040380c0c4c10700300700c0c0980705242c640410481c0307500d6020780500bd0b00c40b50040040d00205d8589006683d24400d240c541d225040120740c0c0300d0359800c00a4000c5240c85030501701d0746a07040341c02e10740c52000b0400c114880c0c0303001801c0400c0c0c1055034031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 569997778 1250 569996528 569996533
    0xb1203070308071803030c0311060c270105040e09030702041803020606030d050d0e0f070803030702070608040b06040207050c030a031107090203040c061412010b03071b0b0121020a0305 81
    0x30904056111400c80e070005118981001a0055560503804240d0710348801401e01910070114810940070b5121100304150b50420354046180500381d4440d02d5000800b60f00708114030200310406d0a011051501000703c045e5149c50409042444801041d01d020f0140c103000c2c4010b02c10b51006964a00885030490034122410343c05840034500a0325001c0040c040501c01e1700b00d40c0c0001c182a9010080d500385030b500d03580c0407844030404400141003105007111051540100c0d036011a285400200850080d843c607400c0303840003942ca840480708400e0a1b50002e0070368464001190380d0b4580f03a0080d00725240140d00f9240202031900010f45011b24200d400c50108034020000080e42d4418400c420040c880c07090154694501036031f900070301e41d00a014440074040601070058808400320b090f2a80701503480c49600e41940c40312113250060300125545800140000b0340c0a4408a180c00e9020a1940c0400003051603400c2080c00c0414001107207980c41da1910303524110000d0b946801c00d000045000350003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 569999028 1250 569997778 569997787
    0x3100f0605090106030b1806040e030301170c03060c040e040303061d0105010f02150117160b0910030b0d2301020409020c0105100f1406190e1f0c0f02040b1203 70
    0x14002410340c144d014000707043c82d1000185850b2181071011500d43c40c00c48044086540d0140050014803150602204c0f07848048008101074000f107003055410b170110800c8071180b6815504140e540c100441d681c4030300b03400078001007080113035098455400078440d040200e0081c1c0c9451715850b500c0c600805020820641c03400410045d42c0040072503043c08458809800b11200624552180180610401e42209044021031220310420701c00d00c07000301905074229607040c0c1d55228810007038015040c0b4910a102e201002d00c0000d001c0d00c502c00e8030f40f1029007948000c66258955980d1000c0a01c0200b00480131000030016040c020320060018141c1406c0040c1c8501400d41c6050840b103009013401c0540d03101010074050103c0a01c0358074100c1c2e220358852008019100d020860303a018040d0b2080004407084064404150040500c2c4103a42060f543c280d05080810600d690051594684902146000300c000c00400d21003c84420158002380000c2804a581004243c0c0f4a400e0490365030a03410205 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 570000278 1250 569999028 569999039
    0x1060b032805060d02060304020d020d12080601080103170a09030c180612051f2901020c041109040b0102030909011517010503120a0c05060f0a0c050f031503100f06 72
    0xa003824481d89240c68200054030340362003c55038920031010040d1084a001c000a41155503c402242d559a4080c24210311160700d0720b0642c3d084401c4400c0c0303030042082400003528075481800054100c030380210b0b02002a03940117010310b40960040b481c0f0420000000400310101d0450421400204041c60034010b8000380140d040044400c55004500140c2141004030b002c40c00005404100d250503950142c580c140781008403000f003407421142c2c02d0344820091042e0405001510201c0000e4003a02078a806011241c204000c56082c03014030072804506000c001d019040c240c0c001159150103004803071a001c0c40d00d0025a100100b42d11440a6894108186030341650110400c049000340e0404001d03194146000203444147d00c001c80c844100010034080c08083c4940003030540240c200c000e035800e41c1001407185800c8182140d642c00c1079800d000b01d04400f5803268003220081078000040906640700d4021b42080d00c408006103903858440d40b841d0105106032031045e03211710034400c440040c0041c54403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 570001528 1250 570000278 570000331
    0x61603050403270915050a0603270503070c060203031e0c0714010b010e240706020919140a1d0c07051614010e180901110a02010b0a0e06031002070501060b03 69
    0x2e603840c03082000228200810780b50050907c00b5581c003801c0100300d01c0750704601c0c24001181d581c84c042c0181044460780c1c0512401200502c003141c05054211302c40390f00c0c0c00099903a444160ba024000d0304000c41090000e04195102c0e5402040e0a1522803911500d82c5a9140108500810244076551455504103e60700b04804144140c000e1361101520034049811811044200202002001f8000307600700c02c10510780e0455a00503c020b14014000000384000074240c1c40c00d001d084400c4003561f204028910344180c1e17040031244412543c032a110544038100d8859200a480403038019003c1c0201b1000403005d0040002d4010369443ca522142e10381454503007090062000310341131200c504070ba441917440d0104800031100809165108944945181c1401403814100003a00d80300f010900d04003550b419000214444411900ca90b006a103130f91100c0001c02042c0c80480d49035001070034280800700a60080d01a80c0c1c0508000a09143d8403414064103071700854181e001e40d5040301c101044000d01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 570002778 1250 570001528 570001541
    0x60f0108070b0417010603020d060e060c130302060f09060724021c09051c09140f090718120b060301051f06140903070303200616030504032709 63
    0x550000d15441d454040741015912842c01945140140c42105038041030094100c00010b541c0034004401d64805418808001c02101c039980b0f603980184804507621852090546a0000b0000d03d270454007481d603401c10130250b0210140b109002d909121400059981d04040d040d481e015446010650401c075500004449880100340c1c01e00e8418044420003e090501e00b4102034000100051a03541d9170800340d291038552004e601201000308000d0503240d0344800312038200c90040e0800c18034505203004001b245100b44a5403900401d42800050b03003648a1a4510007031719003c0c2c6211591a280c00c0706072004222100107694a00d079a0052100c5130a09219203030340041c0a000b800c540c01d4854100a2500e1200c0c4680400c101c10a10005100301c40402107440e04200102220540c43d502d01d000707000080390310b502080d00c1880b2644040905c0740441d589200390000c102245003501a003c056000f480c01401c03d82c00c002c04140380356003440b001643d03c1d05802f401260810903918220b9000140c0c2d02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 570004028 1250 570002778 570002789
    0xe0127090e06040510050702031b0c100504170703020f0f0d140c0916090b090402040b130f05060310181d0a0203011d0a062d090b1b090f04110c060f01 66
    0x900410840555030120a2b03c03080d444404204604031590600585890150140540d201c81020500403246400c00300803c111840344072480500001c030301c3c01685030b40d142c0c40080c1d001501004040541d14100c00c4441d509440242924041021a251081018000035800702c1c941c0c0203e00e0250503142c074500c20f56100e14000f101928400790440c0003040a5964844d20039141e50109101e00103956980540e800f600e48c60310030b40d807200c05a4088600c0c0b00724a02c00c0c06c54a0a410a0200300c2d4204001160f2003905035901d00070519261072240c13410400160900f514041c1c1c0c4801031260300b410103003002d004910030070040050b00c10b203004040c2100c0000f80848001d10780c000d00304c484a100810a00485900b151000411003004502500061401d0304081010303588030080720815005540295003c1340112264000e681e55510800141c107003440b45420141418094190180303407030b508251420002500100d41d07a002c1c6050044545c1004000c081690080380810508001c16501d0900400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 570005278 1250 570004028 570004031
    0x50a0201060e19090302030c0d0801030c1a0a0c21031a040218010311091005070b0a050609061c02061c0f0204030f02060d06030515010e070e0127090e06040510 70
    0x10b02c54014040201150f1401c401d0035111062032007894007d20607a00c91281d90b00c2540c201da040c1d180001c09202090004540c0d038450f895021804014a1005040b8035691001080c5030a039000360a175005802d0f807408440310500001c4905008100700700c00c11090046e0303140031504c00d50180704210081900e018660050b8810301c00700c2c0d00111b000029001100c001c0c02c00051181c0d90310200842c522850340815008840b96084120903a805802020002d00462504226841d15a404403e1303840503181380c0c0d488141000424850b10b42080140c1900702c8101c401300c40c1e040c055010507100c0d0000d100828000d518010781c06070505040c000c02c80c014039044021441c00313007143d0701d11095820ba02c01c040d000d0034021650b83c8491580740d01400295400204407050358813041c0c60310066103002d004011240c03440201007046079008007807025241405071500f21440710314600c1c505c8014a086020000c25036035070400512104a031142d14046010030b006420f07540361909000d850100f06042505556 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 570006528 1250 570005278 570005281
    0x62c0d2703020d321b0a05030d080405100c09030311100c09061205040b012705041209090510060513050901120308071404090506010c020319020f0a0503030d020c0f0706050a0201060e 80
    0x101003a0402100841d09a185c04c0e0360400c070215600080b81e40000e44c00d03206203e0401e0005401107449803040e403043e012508088009207544055580c51114a000705103150000c2c030001e406031140c20307000c0504104413400d0f41401c040301000e035400a00903202044040b07005126480d8007070500000302d800d11000740010b0500747e88040304240144030740d501c2d030000d01c0201072002c1d8402055021640300d20078288464102030801044050f4103803203030004210426030000d001e9090340079039441202401c2058007150310f442025034482d4880c1000400707040c4480004502e03680c807241200e01800c0d80700365540403d10705240c041c1c44a00080c000e4410b10550080900100c0b0310401103e00780c0e505103c0202d0700d138540070700580344103c064000a605019a038814842c203079040c1501420580200c0d10304c2541118141401a0a01140242074154004103d1050812810380040c046200c40c0803c076400d60610001e205d041101e40c1d046100060320000e001920385909000d80f00191002001d2140c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 570007778 1250 570006528 570006623
    0xf07060905060f071406011e0b03060d02010210091b0e0f040f0203100612110105090f04051003080c06070e0402030613050a09062c0d2703020d 63
    0x46014801d851081c0000152511542042c5041e641d405621064000c803d41c0e20060094560b0403d004a11070110150b0103040c8000c195004a8103c8000031101d40c50750300c0301402e02c4000702c620513007641540300c1d0210380c0c001d2400c148240c2804034061808220f000e0a80102e907000c1a680b0b41c4601c3c08400301da814060856100c08600340c1180d07010440c0142d03414117201207030500169034000c07040c0500d428800140b00905440020440c0d01c52400c014484084038010348460041d0404190003000d000247e64132410140e00a9400610801442000640e01d9543c410180e2040d00081d1250700030800380042030f0340000a40c00461812070302981117190003004180062017542800d1768540d03c030800705001d915554045400203400c0f520500c01680455805072f4500d04510032400e510030000e410800c04180807950b05040c40e150350320340c030707841354803e01018055804216003205844203000010041e51a0000a1a42881000c0400f41c00071140c00001003940101c01d000491500114410304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 570009028 1250 570007778 570007787
    0x503070b04140316060c0c0b0a0345060f020c0309090a0b0108040609140a03020309010f0203040b03010509060112320402010c142a2d01120f090b0103050f0706 70
    0x15540a4a40506030703241c01c0c1447c0081d550030740d104c0707036149034002001d2484a5142c3c00240c111030094214680710034800c20071550001c01165100c4d81080034001c090350382c07410b440704c400026009050210350100340240440483e442010000d8080e440020405190309101203416407114004a08100e0107084000190000600510040407955258051010025003041000100ac0e801c411150500f042e403401030f40d01d40c459072580d4045070030540506030782c0d4400000c8400342c41a07110160300316403808091000b0210050000c5060003c50580004086814420520510b06118007008101c0c2070003440031003010029024003800a6950070400543d8016058000e0140d00603c0c010446420291513414684100e01450103c1d080004107100d2501403614801100006c80d0301600e010550200b650511a403100c518862a00d0603000e0b10340d80d030240c407a41d01e42e480001c4002c11042000e0400b4011200300d207800301d50b40208900140705111041101145020b0400c00600b802c5081c001d0190 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 570010278 1250 570009028 570009073
    0x9010b030108032209240b09030a0809010915030504110f030a030804171606060e040c03060b0406050904050d090504020903070e06060909012603090d080d060503070b041403 76
    0x41c420404c2c1007110040345071540d0390701c0c01042c004e5410007111070840d82d00c502c92560f42c00d81a040141205010681c3c0c4140c00071260b403204010020074103150701d40da80c0d1000d03400460085050000080c8001a441701004190b00604425580012249460300c0e020402000344980140034208001068401d40c43c00191400c0715605800d0a29060740c1d107240240380c105012006005481012503520f0401c84c1c1601c030208140d100b45014040e4070348600c041c421010040303401600480038444100040340c0a0f9001d0480031b0f00c007070800f090440c0c03185d01249602e02c09880840e0640d020169055090744c0c000c6c05900501012542503240402480009a03a00c0403402541c032800201c001045941c0e407a0310444420b00000b82c00e4030b805684d03581c482c0c00c1040ba00e034000c482100041c1880707034001c4004011140c030028000d0500700c2685264480b4002a000031030625240e0350b5400001c642035804105c030038010441005441e03a00c60a011164140385203006c1040e00941c0128058200301c0d40d50400b00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 570011528 1250 570010278 570010297
    0x60f1403070509121e061e06060a020f030724111801030b040f0c02160302062b14070306060e090a0c18030b010f08061504020c0c0a120209010b03010803 67
    0x107600c807003203140010200c4003031041d1282c952044040395102080c854001310b210592030700030780d10707107513102c8810700c0844104492280407d401c54001070a20328000d80541002040340c0304a800400b00030011518540c001c440588600c64102004450044204031180040b00400410320075a04c45045103070441c01052340551040c40160107002150740b01703611000c608a0014818040c14801310a01001000b2103d0f1240050080c0240c600e5460300d41544401100e5010304200e04c0c1100717091008401d100918030341c80140041340b004d0402c00c1ca8902600249042c0300d1103451441c107006401600301c461070b034000d000b03014681e03000c16419511540c40d603900020440b80030a90840c5204100c8440c0307004007a2002e05c540743e04020052010401d40903050303440002140000c0c80e1a41c1489a071110100c4680514016101e0404100d04054000d841007142c510b084501064011000803800d107100d0304600c10a0728070102800540c941007030240d0060021050342480c40d41050302541e260720031660340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 570012778 1250 570011528 570011537
    0x120402010f020a1709040b09090d030906110a0815010e0d0803130b0f040b01050f210c040f02090301050106031104120213050c0304051c090311060d0501060801060f140307 75
    0x654441e81c024420a03c0c126405010115003800002481000340c00c2a00038502135031808005607618203001132014001c22140005100068003c4005c030058200c0110490b1480d0300d80d0180c0003401c6540c3c015090580c8240c503021003a14000791070750052a08900e001d8104440e012070300c40306440726038040e142c0303036006101c00d952a5205c5d803208914107003409005145540880403c841c030301702d41803201d000e1403107046030565990342c4008001780c03c8450256142d02c080a041c58114040000450031400c520000945011040321000030741250500c0341c034140001d0300000d00b070400b46000c0c412a400b6160720300b0200501048111401c0150060780a0418006007008c0188190740e1400d081500100c0d80710000d00151901d40c00c402102d400c00e031402c5030f15108800e06112203161401c9038410101c8a41e840154251440c3c03035001100101640c032981101c0c0400288022081c107004050207080c41e07031540c1c0200d5240140c001d00740d10303111760003c040201e0f5029204004c0c9000040700c0d0032800e107180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 570014028 1250 570012778 570012797
    0x30b0a140c090d11060a09031101030c0e0f0a03140c150309030301060f0509150c100605100c060b03060a1e05010b041505120109060531110c06040c050a060512040201 73
    0x10813210203a01e0304080d652180c00824a6119076a000d40c4070801d60388602243e0310b10b0000c4100642c103a1f0350b0329450300701091010b013802e80107003081e099100c021180101034211881d96600d8201e48230b0309500f00c25038560072002e2031351220308003403854800030100701c5500ca1851500489080d10b034081800764108100081b00d18030340041c890310595030400c400510700c280300010700d0b0340c07070b9440d50142030240e203a030045070b4003003075242c0040c400c10003110000303008030a01c149a03c01c125644280344004842d1107644841001a61f10200186071040a11640002d03c2c061f001001d19106100782243d40280d90030070340140002d419260039101100c0700c1c0895280b04900160003500e2901030f03e00780101400c410800000c40c0d03030306900074500302c601c10307501c140b001c41003812824200e204a00700185200d82e250100500300c400384d40300010356040002003904060b1a80c841c0e504000f4142d409452400c1c00e02030a0146141424030100203103010b062a52501810f1541d18180100c01400179050080200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 570015278 1250 570014028 570014033
    0x607060e120c010204030c140102070504050601032a0e15070201080c0d0504050705040c030c020307021516051f0b031c0207090c030207050d020c06180a0e01030b0a140c090d 76
    0x41d88022415000160b4640751002d420034000d4101d0312065403c0202084000b4012101284456605006902801e17159003000240000703880064034050406d0750726114403241500b81540c00308040701c03615560046151418000303000e1a200c0819600c0740c400c07032000604060070340381103036a043e9080c20070b0a82c1e03a9070f4102417042c40c0611401d8030021820001040f0800801068000660310308640801c010210300344201d089824280590340560301c03c201d540c01529115007c4000207621116880c40c3c2041e00420003490410480110f84a81c020050425820942400e038101c8403a0760310100001c1c00365000090340d03500004006004c00c0740b15400801c0d00d42c030070300c07850001d80803441041c02a050440c0004009500c140016101c3d4000c00302c180c05600d102083c1907030403040042c0142d044c551000901078030085901c45e002e62180c0c0010000504134900c40c4001d000758014064a202440c185d10b82030244e50346a80c140403041407070800c00c40e0400c0228191040400b09454003a1302c14001d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 570016528 1250 570015278 570015283
    0xd09031506050d050a050105010e1e0c0903030f0c1018030e031e150609090606010f111204050910300f0c03150c050a2706050c0f0303060607060e 64
    0x141c01035a04442e183d40c0041c284180007903803400700c42c81ba030000c008a03a6940c1d91000001025210309818103e0007400700642c02c2e281c907610303030403180e0780103020315080030540022300d941d200380e05400f40c00c040403074285c00c1c800050040c0580c0d42030862061062003801c4001001c0c410445100409025128403404004d80302049085140b405010020482c0380c0d40d50ac01c20342c3c8039a03040304200e41d0003011000038001d04101e080c65004460241c028039481c0c07160401515000c14004c00242007000070301410040c1035042099031b2000101e0000c0e20f649034105800d005810380300408a0001d00c13461b2400300408003a1141d07031948490300580420200f03140300e05e46203840038464030143c140e04040505206010201c513118085070700c038090788050101045594019540343e01215408030310244540c8803801e0160149070303c0800c80d40d2180240c0100300040c3c1b070700c0203001e0b0001000603030041650300e0f84110410400111410800040d0304501d89a000554180b1a00d0802490a521903102e1080c2c05006c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 570017778 1250 570016528 570016541
    0x60f0e041e0e0c310914010218040c020a0b0f0604020409110d0e061b07020402190804051209030c04111207020a050d0306030503030a0e19081b0d090315 67
    0x10300014082c401c007142c005a42c1e00c0103d800c592141512001c913103c0e0040208840c007154640a00c400000c10309042020010044a04156008682c074405a03151450a1009050f05031541c1c4201030125180414402202c40461894080d503010440c180c005c00c05480720282d00400785150340c9520341e601008100a03008a41c032005ea50340c03c1846d01c000c034013000e0014010f8102d8001c0100030b200c90910170285c0e114819184048490701000c10044680140d6004181c8030740041c0001d850981d0010001c492800f00c00401000598030a06100c06c0103010f201900320300c51205c83c0d2a0801307500e0320000c0d4960f58002c40d0a441295030b01441011450818199101c0b0740d810307010350b9a00d03d032030304010b5203035804076400b122113000700b50941300c51901a12030b00342035903009801103082d90f41e4100c004000341034164644049205024043d6000d150310000313820135a01c2000c00c4e40d00c407240d80381d140c040e121702140c50940340e8214801d1005915404041c003412260807008030460075085c0c285000040c0380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 570019028 1250 570017778 570017831
    0x6030739030801090b0105090a0306090f08030718050105130b0c01060306140106080f070804030f0210051906091b1d03062e030305160302150103050f07060f0e04 71
    0x140000103080c503420214441c12608926018490a00b0810046030540f180311040c0c2c0c0e01c441c6050f07050000c00c1c029404450945d1203000e0090303826001b612030408c583c0040343c03c0c0c40001c00d04000c8441c00c5104c1e142150080000b03080c041d0904050443c041c0001e003083c041e04c07000500c049485101c401094000034011500980b040100c4940100f0250095100b40206008204e100e008039900010f80c4140b1845408030703580e2904941c441e43e80c01c54030030f240c105086d404c52140003a2181c0e8400e843c0719007401290840742205000446070f25003004d68050758807403410117103015a50341b1075250024a10720f900049103010107880c0c4200d03100000c00c0740f000c0403031501071003040c04111682d04550132a01c0100b10140451503400803000a0540409107400000c0002c1c8080c0001088140c003031300c5510580c0d1080c01070f10010500710603d01c1190314240e1041d9840c1d071003034254000401050006034058040d501e031400c40b41c1015040500082d0000590364029555241d80000140c07100400f44030020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 570020278 1250 570019028 570019127
    0x30609030a0e01230a26040f06140906180a050a1707080f041406070201020d080604020f07060c031803020606060723010609060b0715050703090212010f0b060307 71
    0xc2c1031243c05045d400440c0d00b00049031042c03142080140008005035002002210040207a5840d561032440c400201107040ba4042d440f020081880d100e0400c01c14440d00c0054010841440c04001101c0d03c4801d00d110080d241e08102c0110011031004102c2a20403074200c0c08581c4551b205000450741885110300141500c1408121b01c00c0c82c0d41602d00400807501c1410132184191031031010004203100d0780388024003681c004001041c0b5180a41862603100390000d00040c200040c803c642d0200b41c3c02550111a0240d44480c0c000c801074161095030500340351480c41c03034000e666907036000e5078607040940b00d28130274600410400c1c00c2000c0b1040e030b4850000070342a00b440d00703110790203020701905c018000c00d00740c107042c00000718031840c0c0c50307041d230341c005412288180d4408550110080144006040c17070003010303241d91500000d610b0b58503818800c000d0f0500001510b1580c000f1000803a8110364000b0310409042081c0220740e58454074000c00399a80030110316041307124840c40e4002c101d200d00c02d0302a89 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 570021528 1250 570020278 570020327
    0x30303090604030806100e0906010905030a0b1806160305090a06090308160509151e07150509060621010e06010602010f1d0d1101061d090c030609030a0e01 68
    0xc010201e60140128800e44460800e512888200845414107403042000038400104c0c025075454201c42450700554181042e008184d1610042402d281c40e82d4820703907a03c0c0340c4605002852041c2200e0081c0012400003801050414120300340c074151180001504141d12240816074901c02840f06c46020ba92060b01007040080d545000f6025000c00c03241400700a0501c5c40d42c0d0350550188040b03990000c0005e184041041a810301d420700785e00505100030188680090554400d0341400090000900a0304104c100d4080703a1070510540700000d15000064110301d00340001754442c503111810300d19040142008006a00f45820300410841d1301030041780c41420000141c640c2c0650115814040c0d0b0034051061101880c4004060a0034000d0300456a1080d01610f0190f840b0b07170051410855443e0011a104c2c1e0f0710b0311a003074490b0b1000869030241d42440113105503000200444e02c035050055000e030001e850204915078590154460710000c1c451000800441a0301c0390b14541c01408802d4002c6015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 570022778 1250 570021528 570021541
    0xf120105090709082e0f0e12041d060d0b190c03090807060c1107080c1201200a0e0411090a170d0e01050417060916050307031e02030303 60
    0x50040a110303880c007401c4500085041580f040304103070300b5124103000518840103010046005c4906030300340b41e1030301e04810707640c0c00015140340902898228610004207058080c400190300307001400c0350b0380e03012000c02c00c0200141201c08003080c3d1188030032003400c0031580d1080041201c15440c00d9008103580c8070f030b60070004042d814401209c602d02c0260790401c4a650504000d0302214108180a80040c0d014020301c00010762980000100302c405280403030036400c40c20034092070900b65030002181030b0006108001305040c41c0000800100380700c402480360208060200881c0c0c44030161400100381c0c0000d90b05030490141e8940303c04d08a01405c10005210110301e0180f59400419600b840703030010307035000107c400425544074843c90541018003c1a080c214082e5081d40110190b40d0500030107200000c0c0f0191508031004024440801130b1100e4503004035a00d081001d02e007880d80311044486800c1c85141c400194200c2540e80c41954844c0f0740111000f07803008030300f1601c0029031500c40042045034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 570024028 1250 570022778 570022807
    0x91b1508130602030a090c0906120209072f010f021603110309100305150d020915011b03050307020c01020f0703140115230303180f0d20010e1e10050f 66
    0x1b1018080c030b10200c811511001440c050b030350f81c0c0c4a0324000c1640d81c081c0102501d4404410f07504103201d41081d83c401e001aa09030803440816aa101041108000408018a60078001e08804500c00740c4d003186440d2008a5002a08544280140801082089240c40314404008682c0a131800030f1001e114840e070000010b01030001101d103103483d40e908244011160411a030240010341c6d0003025220107640d01200e2180d8010b0140d103a0b41000a01c0203000e5911240c980d194260f00d000f641c52a940b86048400030b03203882c02e0300b500707141190311290005d240d003400415408192540710752189544102800e406003d4040c0c503d0140030301001900000e150b0340c94080d115420b0b24038882c0440404070030010035031a40036100ca865140c9106144c5a907581c03400c030001180034003008020040180154035090600030504520000060580c204400d0540c0c1001d07044d0340541e0100d44d070900300300f04084614402c400801c00c6038040c14000380202c06090150717090750310084910540c640c1380c8003011007260 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 570025278 1250 570024028 570024041
    0xe0a1b1b0c09200a0507030503151e010806030d140f0c1207020102070801020708031305010e060907050a080f0a1407031401050105010306060816051602060409091b1508130602030a 79
    0x180d403d10300e403141c50980ea65101a0b40f20f800b4552520f904200031070310143d6955200034244080f160440402040e1640d50707078180c29180b080d008945981c40030000014043c0200900310600c2170341310100301c0c9400c50b80010b039880d18280310746041d911400303814062001400340903044c03c818050108164001a44040030f4250507000b6070032558250755a064090803885030400207007104000b040000c203090181081903c02511440000400c5040c4000701414404185d440c1009500100000c0059107010b4031124050040c04000e17082e00004090150303a984c1700424010850003003a0400240c0b140b051000e04000d68010320340300302c52080022440d008120900813140402e00d0108081004c511419200b0b1007801d040301004080c0b000010144c0d09900491140b10882031070100d00340050300c0e410083c2c002452101c201003503100c181e141c00703c2c40008070710441c0203a0000c21300c01c000c09003804481e4102900316045c13505058031000610329a100d0f824001410711400082406a115220351120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 570026528 1250 570025278 570025301
    0xe120c010327060929011505040e0a09110d05060a18050d0309170f0c0601090207021f120504050c1e031002030a0207020d0c0e0a1b1b0c09 61
    0x2000845210581c21400c01080031541096415280301c600004900b9800b1114440c000c5c1c481c1444500e405055140494004216250800c456001000a01c40140100740c00d00c10a081c00da0a02d401c041d0039040b451001040405041c4d115180d01c1c007804004c0c070741301c40581c4010700051544007a50a0540c3d40b00b81c00c1d80c040c9a402c0c5050705001989500c200ca200c00654040050001c1c03516042c0c04801034004940103651040c21000b1800740214030000030500ca6840981075038440303290000700740c1071400581c04071030070a00401980005903110b8088a00b2980050260f4001d60b800241c1211545112140b0b03136142c0d45072100788410301c9800901218130120440d10340e49a188107008200d808182c0c1402035401d540302c42008140d040320fa030081c642c0020a9040141851082d80029080d106101004e80c3c103a40801020b12410304042d4680303034400f12211007444555200000b03001002c10849407141000440070800454030418450b207160540c00004180404d521861043e000306600c1d40c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 570027778 1250 570026528 570026531
    0x2b092306061c03030c030e010507030b09060306010e040b0c040305030d020403230714030102090a03030f121a010302030403030f05040b060102160807062d0e04140402030a120e120c0103 81
    0x410300c0c80c2202c2c0d0890b411105107100b460003078299a040d006882414403034030070f05031070b00c1e500d0f0a803030401d105543c070428081d074001c50495841814440410406030425009801500c010f000c030140466640e60407a500c40b00f46503d50343c0c0c01e19400311178029a000180b8034080012403050004075034010703000781c82c060511040d41030001d255a01c1c11400e94031a201c1146c016401c00c000c1c400350300c0a9119203a5000e0009850700507003100285003400c098004401180e1955030100c1901d5100180e048009810354040000c030a0b40c40301c0e13020001c20409014105600000002c2c10948039801030303aa000803e9400b030149003440c0c41e20303c1d000d03a01141c01c5401486000321000410b80050341c000b04480a14006d08001420914110342c0b101c1182c0c580ba0300301c0f07401c9121280000815910381c050900680d0344801c1e03100100204016103c041e03590182d080c050000b4130015a5010030b82e009001ea05c2803401440303909908082e00c810203141d40030303076128612035001102c10310007040f80004003400b680c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 570029028 1250 570027778 570027781
    0x1407060c030b0a142d03030f0406030608030301030816061d010f0f090b1f0302150a122a1e090315140408030712020c160b2b092306 58
    0x3c2440030703444510b41c80c9900c00407488400c03203506030249007001c0b010600c1741c002205e4610b580210746107038003000708128000d000250411255a0510500307000c0e10141000d14515451a12001014042e040c80030240307000040c1442c08005640d0300c002d0800710300b03110301c1008605840c1d00a009040b500100302501c1d0908507216070560091041200c4250703c4130340400c654031000c012403890000d10142c088055003100011004d41e0350084003407104410404442d580d41c1006074020101443c92400004c1c903130038460441c80460364204c914040800074544a000d02404e8001280c6010416071a00d03c2c0c4810105110a015442030016058a000f603075061881948603039010f080728800070790049400760502c00300d8000f07170a9000541e048103040c90065205c6281c074038803004a900604501c02c0c26444140104a4441200001c8000b01401c0500311b09114120031800c9001480b0440e01034440c0d0303840b010800581e100d910403a01d5075000581044c10308481c605a009808000c0600f0040e4800c820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 570030278 1250 570029028 570029039
    0xa090e0c120609060a03060209060906030f040309051008070e01140a020d1704050307020616060f060312030903080a020903120f03040c0801110405010f1b08031603050c09011407060c030b0a 83
    0x1092401440301405000c19507181d47c49a10007500400e0055030b106408010241e66a96450f000c0c600840741c1c10703441c1019040c2b0340f501030031001c080e0b407025021f80c007070b900040d88494020702200d40c08040b41c1032202c00e00343c040380100c4040c42d480200e04030f0b4150204495404903170010b80c6004002083e1101c980d0072024203069241040b007110b00401c964001c1025000608268018000703800d1080f04841200d1901c0c0c0d42e90381654042e12f50060525030f102c0d020000e01c100124844622140c905003027010303820f182c40062018100030b001e0a005500000c06171100d4508001062003890400e141c15100c24070103440c180a40d1007036070306a0b6105480f802c0030170b01c1a018842d02c10503030807180c3c00d1884d06203003c006594008080742e220b005c0c0a910002e00d14100414032900025030721600025640785040e02d0b10b40010001c0340d1403501094901002c0005002c200001c4851000090812140103035403220481e100344203107080101090300b804400f202140d0950003240c0c0d440003c46003a90029106c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 570031528 1250 570030278 570030289
    0x14011b02030c03090f0a0e01080318060702030a1e1a070e1807031a0301020703090515121b04150810050f010c140309060406081f1a0a090e0c1206 64
    0x3501002c54104001c0e03000c1c1482c10880c10a440c81c40a00901c034070740e9582102038165134003640714000316040011003480c1000903460f003a164002c210342c2caa04201c0b6a030046541c035400d00c840145418070301aa0410fa0404065441078185e9010040e070407c004d000c840d81d0107443d01900d1400108860100003d50f500d8204031800c0407585203040003184d940c451608801402130001d0120b8040c0e150020300340d00351001c4c0014046203009440324210b20b860b050600010107168050050b14410a00c9180b842d1403a0400543c0c020420180701e00d5100c1021050302064070440e4049814010485d0b03200c2052a04101e905104188050a075128140d45e64103012400101b40c0200d80003560703111100b000150404400d8800d90700c03050807a81030500d4075020030030b180d0094000d18003095610b000c11102507664110707841c00c5520059851801c51508083d94000c415200c03620f1400500032900400e62841032200d44020448000d0f0804c1904010408640e0f650051100d20708000f13018002a00c03c1c01d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 570032778 1250 570031528 570031537
    0x90607020604060b04110406020102070c0e0105030d0503180601080d18030b010e09070503030d0207060510030305160303020717030106020d021204050d030201020d02180306012702030702010914011b0203 89
    0x110340140455a5590340c6260040404003055984103a58400741c11805600c500600054070103600016650481814840d0300c0d41269482650f1212800005003c2601c011507240034542c440d0625548a0300c400414000f60342522500c8143e5210b05000011007250004a0350380b01034180d00c1d40c90207200c0c44a0a010702d00c2300d42c040030741860310100c0104940902c143c2000d0348000401e094a281c1038407030740040c1c2560f101d542d60380715154010510006118075407240507000b0b050040c0b011849881c50340c01412500504880307442c0c661044444a09241c081e030100c075046d940c021550342c0c950f090f41c0030395030281e0000c2c081c98005100c0e092400e14294000642488100c50080700c1c9402c05107000c0800c12440308020044045540910800c100c1d030504d400a09080661115038030075110020741418504441640541c04004601860300001ea107081445401e50300002030241e40d941d04c0d400e0981c007410103002e004100e004880e440300325000c03040d400b0441c50403003003050207140b01d80d814049035079005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 570034028 1250 570032778 570032791
    0xc090c0715051510121b021b03070e06011e0801030b09030315060a020703050f0105010602010b10090905040c05030d0201050403120b1c110901030c060906030903080f0903040911120906 81
    0x40c80000d50070a1070305100141d407211992608100309105c001c0300728203581349070b00c0d042d11020106004500c0240c06204403a40200241605400a0f21400000340d4030005440ba035201c03c46200b0124609074480c0c030020142190202140c180482e0f1140b00a11004007480161603451000340412154000403045034041e0840c4c00381c10f555251b0f00010891580d000000c1c0005600c07540e440000040c00501c104115400e045000080ca585415406400d59079072664951203409402803c582032078010004100382c5000c0380740000d1079521840c0400000d40300b03810903545846070300f00780f000c403550541105100300d200b595500500440707540000207450a01501a9008900106516070a00d000d030f00180300170f0280003000416000c10340440c20440080c3c0060f1500c02c4680d10500180b900b15440d44020301061030308018401454900421503880944030031084030340c2c0d1010a0014108005032005030401007820400c0c481401000c407101d0740040c44ca03082e81d114075000940f090070085000d0b4815070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 570035278 1250 570034028 570034051
    0xb0c190510050601030216112701090f0603140d12020307020a0b0a02040e0f1006020303190b04090c0b0d06080f06071107031e0b1305070b0c0c090c071505 68
    0x300c000042000e000b000300391070304250f400e011050802c0044030145841034010a0211030601940c0240081d44060120f01c820304082d501204500200310340c0b4190445036040c20018100d40d032140200d0181c40c10f80d101070030b03200000840001120001c500f0601d81c219549070004250b501c00305040907404111030060144e006101a040400c03083d494a40e1302c407558610052905803607106048484409a90f541c294030300860030400c1080384409800301600f1180000c6003540b50400701c440d0f5010464070f9402156403240c4020886071a50380103c0e1040d58040804c0009585401e13441c0c44035003006150710322107410035030001850b0780d02240c24500504a0350181029039107414003038813407001411050b00140b00d100e80010100d64422075103849440c18111310070000307841d41410a42c43c0300150080600801c440800800513400041c03907011a01140040364581d10b8804036a41000442c080c040e40005118041040010568005082852140005050582c2c4100d008021104200c0e015081103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 570036528 1250 570035278 570035293
    0x4090c030b0d0206091c0c03030201020903100b030601030305071a010603020c010c0e0325170606010807030c0923062a0318090c0d0905010f0b011112031008070b0c1905 74
    0x207080440150388094100d06c86986d0f40a850b03510078811040d035034020780050751301040300c01451809200d842407581c51254288031050150000a0b111807061100a042c0076000621404000c030f80b004900c008075640d080d4034003669684001401950100741100542d500c4c01c0c42d1492524080c1040782c07060301d070141c024450141024101c0f820611003c189a03900074541c840041e21502c44140c0452048200707014040e00e01781540007420151018240c0000d144c10f00c00b0520182d40d02c11900000c6803024403502d003800300c929036403030444800c9860b4107401000c0002e003101950040c0c4a81d0251030850604035079170040c09181c0d41d451340901e034180351502c262014103505600d004d003055030b00082e40000c17180c60b1200c0c01075800111049000c0032901a511242030308601d02036442000d0082000b801c0c040044807a50b00150340b91000581a2100c00c403003c0041050550292021009410043d0454a20307030348ac0c3e0400100c54002c001c082200344035400c41c142074080d200c40181c40c003550040003440305 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 570037778 1250 570036528 570036547
    0x309051c05070b0c0d0615050d0908090a080c0306010b0a08070509031024140f04020d062d0603021c09051f0c080603011107020d050a0804090c030b0d0206 68
    0x141010341140c4010040c0511041000c0358680f08034602403009440c0a07130341d82001c1c0c6030030810358417180d00200014400718100c80c0b02541201c200d070001903001c1e1002851107030619150a05004580029420141100d008035248000103010654840c1c22800c460340790b13a80b120201c02611440402200142c45100407405182c00f035000f400000c00c009043d20301c18406c0700c45150440301800c0c900781e01030028560b842d024180100940303003e0513440d09062800315106001c2484440170341c0f021801142d000442000044440d88803030058409030b4070548400340608034003c203055030030401d41003080e8180c20000d03906000344201d503250141a01019107464a441020b8000d10ac40171090350503000716915208072000000296211001038140042c013a10030080003400300350020720302030190b17141c00300d2400f42202140503603594a50441d5045d044000c80d01d0f1050034030218550040c100300000c40c0c0410440510b4202e00c101c0c0040e581c4c1044885180da04200c0004941c0b40003942000c82007050501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 570039028 1250 570037778 570037813
    0xa0e120c1c02010609051018061505090312040b0304020a080604051207030e030706050d18020a0312140706091713091a130605040506150307051e0d1407030905 70
    0x10181d620380000648240c1d1840e004007529030071100c241042c0010300041c0004043c9154203c80706100c2e0908004003810040300040b4980f454848000f44031000c00e05e203041365001c100345081d40104007603540c0c50710340d07849484115400c2134508910414402c000420310903c00521188200d1b080002020000b80700e01864015034032003c016020040c0ba040c460003d91820003500005281659600d5074461f000344c120030071100e81c0c1d820310072030b19280c101c03070405030780c1e5000c6540550350840b02d6400450505082034524080d00307190040302c480003164110500c00e180e401410224050074181040c42c80607000d4560038451030021581c3c8804958051000e0285079000361040a402c1100380c482500c1d50b00000c40012580c0d0002110076100c010902c800d04042c040c8a800040903900780c410001952254400d03400024841405c20001082004c4040741955014642c1e10000303000603902c01e80c4892100141c6659400d9444441850002c503000910034498038000c96041005401e610442c04241c24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 570040278 1250 570039028 570039073
    0xa0204050c040518011503110706110418230c0726120406150302030a030503090705060711090c03070203041e091d0706090302090c210a0e120c 63
    0x1041030070a010108194a60800303040d4540a00c40c49011503600d841d00424145100101ea03900301030500a10751040c101314000da0fa0320641c46000030071100704682c0034400318011644500b021801101c4000501074469020003800140c55508c1c4101401407160030101c80019583e8010005003000000d0104410080c854401e0310b0072001c403404d84289903040e070706940090410b401c00c8004403080c042001003d120b11150711018049024143c0c0c59a00000d07203402180307a0207010311000000150b02040c0c03e102e81005000000e1629484003014207003622076000e403120f2580240740803004101c102c000101a00d1159070709034010351400b810070b0300310a44444940a140b01c0d8a40c540b0f00800c01c2016401080025201001c1c00681004d41d00201d5150240c150f00c05003e10400080500168466042456002d07034150040e80d0748140b0001c1990780e01414100081d13882040009220302107840341c00040005500c034046440c445420b0008203118454140800c085612021360180e07550200c1705200e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 570041528 1250 570040278 570040291
    0x2010b0a17010e07081b030c010221191101050a061a09040605030a030203070201090605040e04030e0f2107050603100e0402031e0105010302100503090606041a130504020117090a020405 81
    0x85007100c0e40400f10b500e00b800e40e40110107140c00044200112036601d00030000041c1084000b0f0920030a01400030f500d41800715640145240c800c0e0b6590007220711b0100700d84000203444c000c1c901c500824600104000d640c0d4108004035400c0a020400181e81406031900343d6006103892464441038009604081e4014000c491308151990000100e50781d0a00c01440c4550081d009544d40b00c0e020b00c001050344110340c00010a0150900c801d2066646c412059a40301e0341c1404c2030000300d0160800919042c0714401907940c07000345c154420642010400a64240d041c009049844444d04c40301044514002106c56603092120300c1d41c2004844070080308039810074000703003d5500b99606101c1c0100c00124050381881f80c2c0c0c2d101c80040046040150101c2c07881d40c49850241d045d41414140fa0751542d030080c00e0300b032065803074403070441060441e21f640580c5003800404031123000410688141c00380074215001c1e804691047d903c44080c0d4005250325115040207000741812210079801c00000b0003018100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 570042778 1250 570041528 570041531
    0x150a020c190317090307050a180903090302031e0c030d1d15040308181203071119090e0705040902090420040f02030412051611040f0501060c060c02010b0a1701 70
    0x200f80e14140d0344a02c0009041c10340d43c1c031864607040c50701d400d015034052030203030412440401c400d0000a90251011014940102d6018034909048490000542001c1d625020f00710459051144080301c14004074003035426075004140d03c9080607102c0220300e407007601041107908400030807800d04104601c014801885081050030b0f21030340e501143c019420880b50380c04005000100c0c0d480a5148515540c411640c030f21481c12200d01041e2207004900303009007404a5100d040c0406c0d5200b0300400b9081d004005002040c513914403d04028100c541c00d51030a9019003c3c0114441c140f40c0a180c26443d0040c180b00ba068a03123580d20303000d424040200704521050384a0300c01680d03a0790f0107200b00783d41c0e52402c00340c0c80341003a0500302c00840401d0034540c18080d00300f10f00c000504440650403011034004505440d624500f00105010303040380513030303d62102d182c40d0000c641d06d034103e991910240d000c0c0707038100302c6540b98003010ba080b1010700012503880084100c3c01c1044041c0c00c03a00c0030ba8104480700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 570044028 1250 570042778 570042829
    0x809191e03020d030b040207030c0f020a0e0907050f0d0c0e070c0f030903030e0901080d050904020c030703111e030409020d0207140303240d0f030c0b1302150a020c 72
    0x1010361040a04400480060300300c90202948242c0c1801184102e45040380c1c21881c0040361368001d080c20b02e803542e004001000150040b0309560b074105290703004049004820800c2d00c0c11000d0b4903280c01080c05594825034003001c1e80301040c184071580034400d5a001c1840f891250900304501c024850050072003040201d041c1c61000001c440c44001c10f01d040c8213480f44600e542c11884d02808882d0715200c400d0040001700d00400440c0310000c2d005a801141d403c01c075540300801c001003406480340700300340c46040c40001150300c1090b51002140c1b60800c1c460701a15000c1984014041100340e2403584400356030710a010500a11950394020261201d400c840185040602d948044500d03954030b049800c0758001000300841c1800307841440780c00c0d07030920a040d00031011080000780407511408020706041400380f4840c040600940141c42455040350004c1c00929203403043c250707003080c151005c0f03000d1000b180c01d061126000741c0540c4e070002e0694001d009030340801c030184680c54556200070f6008500c402c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 570045278 1250 570044028 570044063
    0x2090c041a12272e0c090b0309190c0e0601020f030306040b0619170105030703080706091a0a0507030b06161401230a15180506030102070c0e0402030c01080919 70
    0x55440e03088084a0b4809600308030342d0003481016900d01207680105c1c1855800c19000da4440311080075543e01d52441612520f40d004901c0c546413899441d0447c0b030b14400806401c0c084202401d108540c210200072140c0c0c2d485030012030b22600a001c102c581c42e030013480030840070300d0540c1043c1c1c0c8848001d441d140c14220103004c60480f0281c042d2000012802000070340303548400e051902405010700b900208141440c55403a02403e10400b1005880c0c1941cad55056420014051030b0700c41d42c5450441412030350f080c41c0036560010032003601c0304004246003050303888007428004161200700b401d01d0b030030905101a42e20380c059402030401c0100055562440440806103145915000402a5a90032940c03841c2c8900c05204032558201e9005417810080410001c2c0e900e101050301d130403200c20b103000c01c10b0f407103110100340603004034400141241d2000b60003040c2c200a01180314801d5008070111600c0b10807400c0103591812082c0c50409d0143c00501341440300002c1c480503030004c180b01c0d5410f0100c0c25042d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 570046528 1250 570045278 570045283
    0x1521020d0b07020105010e070212030c0706020a050a02011a0612040f0c0f0f0506030108030318030c03030408030a0f1a040c0e180f070e09060111030702090c041a1227 73
    0x144011558a507040c024448816424441c0c1405450002d13000d090300e042103200a503881c0c10008041003925400000154a5181881600ca107654030803070940d03c90441c5072014206821800000c0011340c42c12023a4044407030003508203490b401c4003174882c3c0d18100316519044041074000388252689a000c1d0001400500000d50707084c000c0c06a0340a0046c0e03a410540c42404011040d480581300c1d40c000d0005204d47c010100c1241d4206040a0310300301c140603295151030550082d41318041403070102108201c01d111484d40103501c11144404100242a582c00c29107049030741045100c2e0120341e1850071003005e800d065003e16000b008a0419609a103100400203001c2000399800c000200000d00c1800704c040c0b030302190281c210300141000b807a40403204011a207051802400d0074100304007603080c002140000d004031102560043c1080c1664600400300319505d500c184203246140c055202000c5400c00c0c56026118010001584180300c0e0701c480b0000c2c0110a02d01901014500080c40c0d8a00111002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 570047778 1250 570046528 570046549
    0x91502030714030d0c110709151e05100c0f031206050d0c060810140603061f1808010b0102060a0213080303040f020a15051638070201152102 62
    0x48000795aa200910309607020b0b181790320381503002d10040c156540c451140229981041d103604000000b082da51401900d4013040840d400b4920b888007001d542603202c12050010350560b00b0550741e071456006000c2c1c017155150820740300504104a40500000000e1280c42203005054480002096840c1c881000542c40c1c00342917400c0702c0d008190310b1b00b00481504441c1d0650700070280c0c1c0c0070102c101d10381403a002d502120916014400d02c40080094803a81d00c200320300349405d0001139002840c80e12018041c103140c4005404030700382c01d520040050300680500869400100681c0a020b142c0c80b81c0ca0206c019400810f8000e00407880c1410100307008400b003014500c1140551801c0d100da0f600741c014000005400d030440c02d4031414409803898039a4002045424124510000360b013840142d04180b020346c2c008602c2401e115001300c07002103540c4100c04140760918031174540c44806468240e016400c03507072442da0030301e40400000710800140c5048841c3d204821408040442c40c409641d00060301500d0b0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 570049028 1250 570047778 570047813
    0x110102120d0e0607050c120306060d0e15010816090e120a0206070e1e0d0c050a270615050a020115090207050c0d02130e210c0f010207030915020307 65
    0xe0b15414032030396aa0401080e90444010705049207085045003020f501e0301041c500508003010000003041c03680e00c40c2011200180c903e0396040000680301103001e500c400c40e019843c02c0704204500003103020500400e0150750a540301a851000d01d1030070310b600029000560746c2844a02540302d1070700ca1512100000c1c11520200c1d400740a442c0b0f0301002c0a42110030700c2014a001e826958201a45203040500103441900c0895000114606901d00550f581005800c01364020842c0742000400781c400c80c094800d14508190f001c9c00d1480442c0c1d0315401c80308588104640002a002600c2c1901d0041c1d004283c26090380c400030070010190710740421034401d03a40c084030031154005540028070000788001888100205c0c0e06162030b055980000b04050803c2d1080f00d00190359610403081c01008105403101c0001e101908051202624851441500900c0501155002e10000245192410300c00c5030b6800b07500d0f0705c1d401c01a6003450890542144c00c0c81d50304055100820100b00820844401d1440d5070b003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 570050278 1250 570049028 570049031
    0x14030708030a031b0e0102060705090d02030a060c0e1c11120706020a020109090515040203100f03050a030921060903050906130501120b210a0b13030f0c020d110102120d 74
    0x160082c88013105220018040c0c2c013004444284001c0c980e070b0101d40b0300c3d007045042c5095600d981224000031a0048a4400203500d40700b8030424404010706500544e80500080e04c0e50a2512500d00601c03403261280b40303082c40724040c1441ea4900140784900480042d082c00751492244038405409540303444100d80004000d40e004082d481e04560f40408200054000e000c01404941000782c01d1142810408584a10907500800000c01d0b08460f044003000a0100c0f5003052100390384da0600d15102e0441d0082074001610710f080104103c0011030344d1203031003051010000000113113500e07100f0082c4075040d012010000100000d441301d950300e101529000e42154881040c091510740054200002240e4072038a036420f0030090400c0d84c0c0c078845050810f14030200071614a03540c0b00c50850802141c400d000304050307840350500c00041185a10320910b91b1017178070750400050741010203a40284040d01c00075804440c4420140008810740846c0369202410b0040712003e40000d404100c9541085000c3c0e03840c50b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 570051528 1250 570050278 570050291
    0x60a05010e06061908070302220317040303091505190807030c09120201030e010b0612040606060c210c0b01170615010203120403230909070807080114030708030a03 72
    0x50703034440d580c1c1c0114003194264500001c101554040160520183d41400012000515441c2c040e40403207042c204010b0344084000c0e1034043d000c00030410740c0001d48140718046003105000c3c020340104c130260b03501511910303207103890701c50741d03521607501c00c0803101c00c000c7d05004003110b801500550003401c0101da2074120851030512030040c01c4404044100040050f03015042158480380051502c20319020701c3e01051011a0050280c09002c0b00796485400090004442492a82501c540c0d40254400c2c50700303101ca0f0340d80e884c084800e00882c04000d414040d0303091006070700d860b4030b2146550070380d07042c14454141c102d43e46402e43e00060036400001e01000114041034403100c24001958024111004800402d4089000039a05e010310140504200040c0740854245800f4003082c09820340e1800340c003110002c4600350390480b0b411079094030f0300603101100422310250003444001d2144240d80c2d0742c02e10b10303071804d10304e40c03000c00441d00d209400d8003034008040340d810f17403d10003000c00100c6528003007900c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 570052778 1250 570051528 570051539
    0x6090607060906061d0a1a1003110309010204050a1d0a0207050c09010311030d1b0602030405160602070f0503010b150f160c050f010f0f051b0316020f0d150507020c03060a0501 77
    0xc05c00b00034540041c03030b0301d003a4800c1281f440c010201d150442c0281c544000f00340551400f40c00405200007410101100401000403040317054004100381c6805a441c444266070b92080d001c011281e880c480140c1c580c803840040c00c2c3c00d83d580e0142000301d00400442e2040007450010905440d000e80095603c2042080501c095040412504c0e44209092070101e03100a48030000d03c0960381d0070b030b80003031031103030000081418000e003080562109080c1d40380d903904490399800701039901e2b000ca224004440740b140b10005610310341072044251804019082c420540040c00d0302d0001e5902c4403034a038000c12000e018802e04e140034000e400c0f030411320441840ba032160503d410880b00e04075000e000ca040046c81c848030205154449461000c428940c20f01648400c40c0803a8022040006400101944800300e04411407480f610000100740b40280c6000540300720001c10310041603107240014003002070130080b0701400000c3d81c1c0710079400b1041d44103480d01c80b400a80007a0400c041660a02c6103503032200010b000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 570054028 1250 570052778 570052829
    0x3040c050f12060a110c070602100c030b010e010e0112090b061309380f0a06061d090901140424020304030c020405130605100f08010b0609060706090606 67
    0x7070945086881c0d0071001021441a540c0e600010441c00d035a586030b40ca20458180b9a10550b401c0c501110165660390b030b00c0b80340003503541c00b0200702c158110307040240c0b440328180244030b61030b04101c040e9205502144500010b4461551310340442e4108072003410518003140c3c0781d100c3d01d20000e05c11f80c01c0b9480360074203000700150b0362081c07058200d44603c1d010307000000404400701d00241002d2500c40b052452007e42c039002003000409c0380003d2450907941041044044468a54892050030008000d015200c8808546801802d0703044c2130348010302e642c01c00b200e00e07040b911160320807043c80002c9000c5035203c100b082c0029017998111004644000c5210318502d07800340040501540b20000c40c01e610f8582c60050000c0f2400c01c0203805240e40f8408510a01c1c82051072610182d0402c4090120381803041c8070804400c118400c590f64412091000304000d070741801407015000b40101980c0c00c0c001078804000c0280e110060884007180d48007460380c0010441c1c091a001400446503110041050282050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 570055278 1250 570054028 570054049
    0x140d0207030314160c05010207050703030f12110a050705070504020f042904050409030c0605090705030c1c0b0921090f270702030c100504020a080f0601092003040c05 73
    0x40700f9034085810040601100942c0c0c04d5840041e1525602e034046a051a500911402c5006001401400400310134542c021711184e032082d40540e01e00411061508901089440e00e041c010110107007040121445441134001d032090324081e41c00e4030505503170707800090100e1744100602490018003087c100601140340b01030382c1da441018a1002c40d40d98241c0c40300d0003c2e00c01c40c0121445555071b2014101498417454582c1106540140204224241800005d641d96468820f0a10904c03641d60250000e00b00285255545c1802c0786240d00c080074159920819658000c214100501c58010311030011200216040703070150300038004c00d656104560030301000264160015000e0030039406c4404040c0004025804034440c040101291030310399020807401d6224444010000d0300c00c240714281c1207140355000343c4c00786100300e1700309030312968803080242c0b03c8100224481d0340350800401004001c00c0d940000080502c40d02d03000b158907171480541d003080c0e0401e6609a80d00c0030458005d00c8a42030601000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 570056528 1250 570055278 570055301
    0xb16050406020c0d060209130603050f010618090f120f0801050d111005090423060108070516170c0f1011040303140702030105190b040204051c0201140d02070303 71
    0x140d151078109040a581c0740d140d9084240a075000b140610203103c01c0382e05031041e260000300100745000c214403411002d481180000d071080e000e003d0300100341c1d40e814802c000403544044803103148030740c100860130b004160f8240c0584891000122010014070303142e07030003042c0034202e403140b0840800f50000140580d03816000280646114514031f008986039800940708070b10212110658501c2079441240d244c0a01d100540d0010f060180d8034079496030500e14440c481010750b09d0180c06560341001119250400e44020000c550104021b4581c2c803403160782400c3c1c0c2070043e060505102c9205010201c0355001c1401001c151304420034141b683c0700284038555068001c0c4c0070031300c40c0038501c0304e490146224920004041c4001c004054000a00c075000b07885025800030020081d078a44038046074928051340e4035001c142c500e000308100745494940300b554156240070340812200c40c05d86102c0040340001507402c0c2c1c10f0282620485607515129402020000c5505070050f031a0036081c9030280690b8500700e1036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 570057778 1250 570056528 570056537
    0x10e0a03050a08150f09190608240c071e05061905100b03010b0903010605040c03050f0106030203040b01150c0203010f0c020d020114131e030509011b03022a0a030b16 73
    0x101d0f9010f03500c5c2908500082c104449454031074a502103080d03641a000400d140866080540004162001140c03045a801e80100042500c940740c04030030318030ba801101c1d5044240390174030810300420403080c450001c000c200e60300002810071603214036181a008548140c1180800f9a40e0030141007580211038109240d4000d0404450400003488021301050140542d8450003007a0718031555400d4110100070600503004210342a080c03003006014003012a40c108680c0804000003c405210f842240d100d69085544d40b8116401c1240a0103a1100101e100080100b00283e03000540c1d07081c80b541e0380c6020302c0314000600c122049006402c00c002e1031080015a41f42c000b80004030703106a0704003030f40817110a01c0c0598460152a020007800f074801221442551444120030400d90014014020b409090300d9541d0b8103840e03140c41c1001c010110348010016044200001408802141b4284840d00b0890705900100c01170008118403134055801900c104007900140101d40c40629050109030b001c6140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 570059028 1250 570057778 570057811
    0x60e0a0c0201200a0905090405060906010506071e06021b0606031213030b04080403140f120a0c02010c020a080a210201020a02060f06030a150c09080712030e03010e0a03050a08 77
    0x441c00040050208610f1010000040c1031426500c180e40c00c40c0a0704000745034030000d0130310782003841c1c1da000102e8003410544990320010070545801410780b0b6080c0c2e403200c04024190340b8015240c0c01000c9940b012a425602030001ca04852184159081b0407503582000388101d2624104040c039010b014122450040c104200b110400c8100d610190280c9802016a06180d161460882d165100d0303a0b01c007814506aa41c45560f03290340214045182c030700d043c0101d50403840e40c40d403252014481c01860002040b242480d92006500402d40410201d000802e8440800ea980ca02142050601001100c030550075171440740c5003820b0308660070b900701c510344000c500301006000302941c1c540c00945440d0000302c071440020000d40d001c00c08000b005c1c0d8409290b607070202c06080034802070400d80c0c05010104440345004540391a000807a40708035600c0b2500341030341402680b0284c13a9040601000c6426540f9200702c103541000400191240302e220341e441a0782c1d51903802008203410f00c094400c0b0302c890041130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 570060278 1250 570059028 570059051
    0xf03031a060702040203060d020301110d0605090105010828060914010b2d0d092306160f050d05010303021e0601060504060818162603040902091201060e0a0c0201 71
    0xc0554014690644005075a6190000041e440c640052310007035140d800e0002d52001882030341c02415054101e2301382446aa41c4560070030920000034011a4002104030001614a000d1201c51001c0700000c0c0c041607003517803202c007502401d070740c0030344c10039070740540c0f5110403680c0c1419200c502401031000d4004c0906040585407000d042c1051480700320a2102d0540c0e045118203101411640c50080c41e0200b041100201d10f845110b000000d080d00425444804a0a149040208829104004448506d161180d01400649902021500ca481004070a200784102e00c00280f10382c031301841c000d030014041050803000042c5109034920000348150008401004820b0b0060140e42c1942d2041c00c0c85803166440d60078120300d99040e442c0e40105441081140403040d06010315110035109041c0400789031400b40304503055208416010350401c0e5004000030801c441e0141c0c058440c1070001026072008207a01280d5a09440c1c4c19005000901104418000502d0b042d2283c07850f46025070000340101d40001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 570061528 1250 570060278 570060289
    0x3060b040302010807120218012601091109030609280803040201081b0d0606180305070302090a06030b01080c1305010303021f0e0a03080a061a03071412040f03031a 72
    0x52100a040c00880c4d40030036560750260319070803405600e4200454035003002250321412100c00745849800f00301181083c0c000c288001c0310010320140a58000307600c43e40f030224120010010020713010b280c0001404081c4140d80c05009550007540ca6a00410780203203030710411241005996481034511841d00b00742000903480300705403988540c09081c810701c10340d11a010448400b41d030f290404140d00000a98038198803003a480403007030391680c1e5115401070b60068580d1292482c28000034010354007041d1f00b0001450030440c9683c0c0005001808148956a507031541031a0300280c00a031070035088890728420700d003414954051070001002080c441c5515644019440b00f1142c43c50710003961080580249040c40e81e008541401c2c0604200c4128401c1820003c14110701500c00445441c10302c900090a5002d2540a071200c448894840d440d64840c0c9078180c5110300d440700c40322007500c420f20880802043d40c01e061407046000d1030104808490f1072800400326454041704d240e400c0e040045416468a0760b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 570062778 1250 570061528 570061537
    0x5010f090303030c021c050d05010f0b0403082802150618010b07030e1017060916180312080402040e060c031f3602120403030f1e150603060b 62
    0x10f04000601160a031401c81c204a110001051016095908014407960000c0100138184000008000742e9884004a401094040c495207290038002e00c014800300346188010a80c3c4480f2540381e03180c001c10a0600c002030303907042c050a40541c007c80380c0914019540d00c6440d60041c000c0350a04d00f040c07208002c180b044281805041c807168030100d0260704150040c0002540a98000c2050241c2c1c880181c00034010f41c0d43c041c600c00121400004681e2a051202165000d005084400c00c8000c3c00c0c0101107980c800e0615602030681001c01d0f001021442c550b0b00c10044c01099034030002c4038541401440300303403120310f030b110400c513800b0030100020400c160064135041750481c0c142481c202046001200110415000b40b03400340040041d81001840904401208200c604447d40c4440708030700255080b400b600e4501d0000002d810005400a44641d0003051004002d25000070220724120350704611464840100e01c0c11542c840c1c2910400b201200c0c00c0703004211500c0c0030322840f81040c41020284c080d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 570064028 1250 570062778 570062783
    0xf0f03050c0915030919050a12170109050f0601020a030f050904090803101719020103090c080d020d030b0f0303040b0f0f07050d122a030b030a0b06040605010f0903 72
    0x648002081e450100315085a050300d1004180e600c100001c0b610711611a0300a0b80c03000c4c51171103458400c2205020400c48400c6554000018144166080e151055883e80d080e00c2242008204100140d2000340203800d070b8007800c00240009903a240c2801e12240700030018080358190360210030000700003944150b854008820034030b842c5448484407800310b4060f042c807201c01015060301104000c1d000d98030124007000c541259840c6407513140404c0540d070f1100601c3c1c15481d2111a00c3d030108015501a4004038001ea20a150040011303a60b10b41c2903041900603440a001030b0480c00044088580c1070080d0714040310201c91224070004c40c0030002e540c0344220300ca440070b000004101040c440044000381c030400740c40503200d941e50700300300c0c0b500c15211564a039225010680b00e003912201905140f10b0503100f4070f60440607010100315400050003c419580c4110105074450240b644c09440600000312030b6031050b521b00300542008000c12003903030300c50741140d810400c0c00c050340c040499104000c0e8003200d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 570065278 1250 570064028 570064031
    0x3020f06180f03011503060905060a090b010e0c070c06030b01090504110d090203030705070308121509150310060b1c020c1f060509010608090f0a0203030405191701020306100f0f03 79
    0xe02c0c1804a809003014441354990346030980400000c1c010190040780703103030344680c06599041e60346485035012100036140107010145400d0051007101d1030400701d55000074041c0c00d40e90034001690313600d441020080e003000c1c1c0041d4540348440810358110320014080c0000721002d0100440b041a0940103000d0040f40103046070300c0d021a002503450500840c0e00c841d4114094842d0b46481c1c0c202900c0587c85242505840040d0800264054041500007044070900130b2185145407520b00c2d00116a480e4030303045a40c0b40c02a45004401c60b030f0785114060050606100720764075110b0b80b01b00ba401802142520035100c60041100300c419060100c0c03910460403090426084d8034007001c3c0da84004000c0364100d10b80200e2210004100240c01080c170781d10a1102ca0200c900482c5214140e43d16503400681c001c0d0154001e11052002d0302c1c008070180440c4d04504007140009030703100703030300c2d1880120340710717509000e942c000103020f03903801c141401c1010346d502400c00b14400510341c500201b000300942111700c01c06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 570066528 1250 570065278 570065299
    0x10807020705091605160323090307030b071115072a06050c040801050109050f0115022d030403060c0206060607151e020703090602010507020f0303011a07050a080403020f0618 77
    0x30301039010785500140643c00c4c0f40d40b4151901d8080c190340608022300143d0780c948258941c0c0078680d40c00b2a054070714090041d20b052455030307850b1011028080c2c18201801b580300d0860300c80b030742d003040b00501c550000da400103040e042c6040040c0201d80022681c0300d2034200100301d00e4515284640480103e07500c200000707156590124240e5035030145800c0141503500f00750002a00141c180c00c9640034109411210803566618201503620400303a42601c0096004150403c000c2c40d8940d5160803000540d4041104000b410000c5900b540d0180d0002c603030555071040b5440469904200c0c19922031400c0d0303103151400b651900d40c0c070148041e00e2031301d404141d110700300e652100e81071001840440f01444815501d900c594034019103040c4641c0200ca006601c0d100004009510006100d000c55800307002451075a42008c14041e450108401807d0000100304280c6002450403c010000a0302988240340c0322801d6104005425000f5910303079104001c03d0000b1181003e00d03045110f11000c044950311400e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 570067778 1250 570066528 570066571
    0x15030c0d0914010b0a05040903020c01030e240a0c0302121302030a081c05071b02010e0a0b0f070c06030b130507030b1203040501030f0912231801080702070509 70
    0x6819030880c01003031900d40c004048868a0b054104440502d012203085843e1030312002071100b229440400500142c0c88540300c408a540664000a6150100c109850446020000d80743c40c05000302c1100d07480c40304c04010000c0b01c2c8020711420070303542850b04e8254909118404c2548400340098500790109220212410442d1390070020141c0385035019890944590210011204441d00f803d05140150b0a102c00220040d1040c0e090350310104140062271145002e517001107419240a1701446c1d00014101030100b07020400c40050100e0401034a80b03603a45c0d0141d4901201011902e0340900c0506080c0f400c1e10001e642c40c107071010f8468901c428001025a1100000c402401d010500160841c20701d6270b99200000011005006030703203003a02c0501c121130303407400008100e4170742450140148030400815151248035107d180328117100c400510742400d010031143c4030b242d0300c4040c80c1d8034010507038108420a560065000d95120704d0a001820507030749080040340d41081c0003400e80c1492400315a26014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 570069028 1250 570067778 570067781
    0x60b03030a090527010909121707030b031f0b210307021002100509030a090e10050d2415122d050111030901150308070b13020603042015030c0d 63
    0x280c038802c4101134000d550799074a904000f4614000c080c0c442c00c1d036414100e038201c0d0081c0042e10427680030504206855a800401328000c0c100c54221603032500a2058980e034580854850541d40100e00000080100c0da4030104541c1041c94048145203001c0090b250142e141c0c0407041c2c401d1140c043e1201c000441e1070710b20880c18205001000c0c1c110714503000c02c0c4030000301c000010705a000c003941c450704801503e507440c1c001081c10440e00600d024019170828051342c1001200103181034400c02424140c1580c80d4908110090090452140f1035910404108421900054040288040c414a404626aa446d6203414000706090032000f05811039140a518803100c06840ba666041030081001c022082e08040d81c0d94815502920340b582042c50340c1c0e6044a45214110840b80d0102c4d201d460800180c1d5000c0c0760b0400140080104180001c410002d620766034015072207540705020703d940d0810f64200b4a203540e4200c02005015800880000c2152088501100c0c1c1007244c1101098564090000b00b07030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 570070278 1250 570069028 570069079
    0x9010948180f0c090e010b121b0403020904030c0611070b070e270103050708060c1e0d021801030c0f020a020d051e1614010512040c0f060c060b03030a0905 68
    0x4040c140f8010381e200d012984000e41000340d94140c14032040c940d0365401d03a1005801255421180803243c00085038000300303000719201c500040c2411030b170304142da250001156882d080b04c0507808610a00700060400019100381c00603da01e48401506062554444a0508038014445003c1c0300c2c02c0115848180e031307240340250810b4031226400c4070401120018408800c030a03c012a0306205a070004503c0020200e003051040b08068400d82c1080e202201d154000680300e50125010001003117000402005400103204110b043e10b441c0000c06561030004080301c074107800c4501040404400c03100c000c2d5000c181c11000300d804440304044c100c6a4100941020f9a030200c0c5c5c0d035603100c3c1a5000d0a09400480c078100c88103da4414005202da9a07000e1201c1e6048007032000340055410800501910109400550458001c1000b120165181c07800386161a2107500a40e0105044181e4101001501d020b51854000190040d600b4020003040250029116014591107203c00ca280440701e0319100c0002c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 570071528 1250 570070278 570070301
    0x302060309070503190201080a0b0603060d11100504031b0303081803190816021f020a02010f110301150c02030c010522061706010f0806090901094818 66
    0x895454642c6030022005c1650800102d0204038002c00080391106a0310482001d030714094070701444c503941c2004100140300308040c211071105040c0740400c07881d1aa801c0104202c1520b0322031550350b904601348444940041d20507200343c44011641400060b60104410b41c200440b148a004100c0d0070b00112400d501404180110702c05041d9800d0496980c030042c1640600c030503000d8008c8144904070100e17102c801e044000c040340d01d40404c900420b0102c0d64000d003049411807000042201d0301c1c0008500b51100c0d528402940c0d81c000c001442020354409811084d40c29504207011500c2c0150b0220751110b40f880030040c140140850f15034040c02c41d000c3c460807400c40c40d2a6002e1030980320100a40303d001c2081c5c01c1030300300904800140040d406440c029140001b03648400b40b641c5e4825040089092008150507017554840c008140020300c00c44405c001c1c542c203524a81101c42c03034a42656840a0103801380303c1020500c50030000c001e0028000c600903206040e040552175608000c41001034180c0e0003c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 570072778 1250 570071528 570071533
    0x110706020f071205040b120717090d031803020705092e06121a12120408070806060f090a0f110c060406050c0a020c063a060801090c0302060309070503 66
    0x60000852144001e0124900c910410b2101404140302102d0a000b03030b0081e4003046c1001c0000601c0c41102001169102c103075480c000c10303800341c01100314510500c19500c1c050594005440c1c2c402c1c480d00750003000d640000d5002030700307003140c481d450080d1b4414003481814040c0c041000801c4d01d06c285050701c082181080703102c00c20030408014090031010768910503c1c0000705260b01000c0359071400d020341c030106201d584074a1607803180101081031255074103c0d0303181d0070703c603900c074002d07242d54080007802c02052164054400c1d07600e0084150b04006005002c18450712040314480342c1540d80000c0d00d600301c10340c400f0000d004191b07010050000c203030321041c0101d940d0010411405940000030700ca8461441980c06000c0364885841250040c0158048000540c120b011241c00604008002d400145041c2d150b07a1310a00720700c80c0022452645040d03440c803c2c00c0d80313403001036411407038001c2c0c50041c0902d900821503071860742c0701c0c01401c0c20140402481030000102180ca104000c001c0360300070301801000e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 570074028 1250 570072778 570072787
    0x1002101e05090a0507050604050d081c0c05090307051002060115090b070b0405150c1c0207061802010206010b25021807050a1404050a0303050f07060501030c031401180611070602 78
    0x2c1651000d082c1421903491196410100d550b04200741610122400641101d840c0002c0340d07902e05180e00403d0b00d00000030b1401c07881d0340c000c1c00c1501503440f081e0340c162a02e41c2d0350b07282c080030304d41070401d9500400d001c1e903208900000e40300e0340003c4035411100b448070900c0f000752030078100315840022030380407161029010501800b8004c10300318650081d03200303104a84a420a01c1060215806e0840f00050300c0c2c101131050714206130032070040070110029002e0051410305030740d448d01c003194107402d07600c0d00c00d040720030b4120700b1560100003650141030721111440c20107410480140c10f94440c085000000b04898032940c1c00c644400401d454012056800000e69150401000b000d940180164000252000c41c4181c1341420300000c0350301360703180a05180b070158103640b41564244e10414005900540421038600854400d100b03da01851040d1040300c0c400c0d01c2c42c14055580d030701c3d12204400a900d0410b403260328030710600050b11891361040c0c0106503043c160001440e54019458007401071800000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 570075278 1250 570074028 570074041
    0x160305060609010f111203010f060206040309061d09160f0212031f0503060f0a1506020606240406020303040605060103050601020c130e030d0219020105070c140a060f090c051002101e05 81
    0xb0714181c500c2109200d10480ea6a640bc80c0d8074035050706c0c0600881c00104d0140880c1e0f01c05c90f20080c0701410b5060401d51030840c1c10200741140c000316000603850030a4100c03403640950008104011711001c1c8000c1500440c21a100c1165200280207198103c081511082d5014000a05003008220040a503045440c0095410015410442e01a403005150074180c07032040010a41c170406039865540180396540d540b03014800001420740d2058440344c01100410340700d140070070040010b4071059020356103c1c18181b4007803007540d0014210b14141400d000400c14641d030300069a20030380100301c03030100c10428114142d00040c0507031750003120f0500000a6030080303181d62340c005100282e22502d0520390000d10070422422200c0c1500e2520008002c0744440d400f00301e510b000206c0c42c40d00781d0b0582d041c4000b00d68810086802302d83c0600d045039140c5001c3c4052190328561341c0c008020694040341040e002d814001c0d142c00c240840300b030070f480d92902c80d153382895080e141c001440c00390500b00610304084 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 570076528 1250 570075278 570075313
    0x4020a030914160e09030412030c03022b0318060e0a051509030328090303060302121204170708060108031210060c020114130905160305060609010f11 66
    0x2a04107a4085510b40c03808861920001140800c032525803220076506814039080005024014000c402c5038881480b021a032030110703800e41d5084a20980311105041c0c020325000c0c0c01c01c0e00303c40d4081400c029a0720120055a410510181e0720b88282c640043c1c481e02c0c030a00b88200720b082c268050089481c0900e09040d1980c0010210216800b44048807a015140003a1408298003200d0120340ca170401d00220703c02c0320460103142c00f030905507403034860100780f00e0720884201c407200c400903400a034880e1400c105504251000d40d40d000740c07080142000d10b07082200d402c224400e91149401442c81d40c1d521100c150014010000907102d01c00a80c1c074203594172140790303a69800400903000d00c0001d44000c15a110005154281125260f4540d48201c201715001520090305041050f44c0c244004c0022010712a90045e402000c1c4c800035000244504081c1070303082c410010500c1d1501454035040a20501c3e66940056404001091074040c2d500c00b40030204603030601a840401150f0b100d00011603030f800121 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 570077778 1250 570076528 570076541
    0x30c0314011e0e0c030a02060904270303020a09210b0a180c140105040f3609060b03030f040b070204020702030303250c0f0212010b12070510050307121a04020a03 71
    0x1400444013070140d444105038070352040f102c0096100c141008112014101600158215081403821704503910002c0c15044600c10039010840000307a0004001464680290340e00c4040c15000c0d100b4210f4910000012644540000c070140449100d140052400c003211740011565030420300e5142e03200906458152143d1580e40aa911200c80002c0f032041c00707510800c01d8030704851529018001c0c15140c48040f02d0b00c55070940d81d01c0b000c40f000340c0d00c8020006540154042d6070407007410028501c0028201a812030740d41c01e400c1032280d01304000f041e124000e40002c4d6000e4890504480e991161a0710004009114851009401d80004410002c604040201076018040c109000d000b641c6d4002c03904651894002c0310013001c10329650120400750500040380001c001c1d2030800019071010510000710303520700c601424007941e8420390041c099810b004444480304002418243e00b076040100015201c1075012480d02646503492600b814010229580650300702130142c000c40d5213210400008001e40071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 570079028 1250 570077778 570077801
    0x30506030c010e0607080705010f0207050609120a02030a12061d070e0a120602071b0f090e0106060206130618080306040c0206010501080a0902030a0203121b07030c0314011e 76
    0x107203185040007940601c405030107002c802003442e440c002007641c40b03039403e40104600341c0d40c642d61a02ca400d04414544014108240501c000f01450f14140d02c80d6480d00410080c21014550103201c604055a0008241d401001c114101031884020b501014802090640d00c0661b6482d24140707004607081c4424103841c090341c0760342e49044210010506104048505102d1400c2c00440c5904000c046003160b4080c1820610401586003e003110789444800790580b038100b5003c05080000400c10980640705038003252110100901c038451030140c0113520782030018802c0d40707102c807580c1030322003080b03410703480303a022002d00d4441001a041c01d07082072000b44d0000c8030058041e51511080710603040c00002c0450417036205944107200e070303568034080001078a00c403e42241c1500c84c0100400050f41c09001c07404207002100c0303580e520b64160303484e00f8034006100201c84845811540d418404940e80602035001e9a405c442994030501f200010030f8010503620b442e441c5900b4104025404c08042504600b45102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 570080278 1250 570079028 570079033
    0x1e030609011d01050f040e0d0509030c0d2d060c1809091101050c030903061302100903080f0f0f0d0e16061706061b01020304120c02060703080c1903050603 68
    0x280c030750100800300348030030748042c0708241010010400e51a00d45220803004102600200d0220000c030b06c1d1070303c1c11a5081840000c203030003007050111400c0402840171400740c111482c00703a0f00c4003074032421400c0000d0410b00f82040d120f800103040c135842c00d2012401181d03002c17101b0032407910f5074103006080180f56100c1c0b4140999a90000510740030500803d640c150b04458000e4501c0706840040d01c00b64410042c20300940410f00c281e00642d42c0c28407116103d800510600805424584100a54000f00d141100240b024542c800c0c408100c2c440c0c20745050300601d2441940d02c84075810b0403180b6018081c0309070700c017000010380804400c034590040a80e51040c0c504030b0b600301a00c00d01d181c4803010a170003507000240440c00c0c900040380e004020789422110250840d4039000c00005842880d07140c0650400c0e5580d000014002082030f0071a0202065459103400840c41101e80e000440b64450700c000942080180c80c0483d00410001c1c0484401e8030003d2003405010b0320442026000d400c00b210010311a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 570081528 1250 570080278 570080281
    0x30e10090213020301030b07032c060f09030415081509150406240c02060706091b0812120a0b10020703061d070302090a020f1c052410051e030609 64
    0x95843d0003500d050f69440003404500360790b007440c11401014000c01014260550b62083d205804101c01100c502c0042100a00914074110f42d032004c0c00030025004e801c40d5481080300700301407590007214524809642c94a583c1523144c1030381e509400300e005900c003a4400d01e100b05104072000700d142403010b41c1c0419034080c0251503603503001d41c102c9000d62160540f18030407490680c00d10340c4165a02e28010344001d04c51410454107448000071903000100c2180e000d0583e11036092072162030806070005050320b00c000d00c0380018a108a480c28012941242244880391003c01d801000c0d542005141d940d003d0080145e821007100000e584003114403080c1c0d58586441c412070290f00d250101e1180e03101100000b058503c1c59a801e0040c0f086c00100348040d4264244850409041010020300390301d4840d00350948003500c0c10400000302e0f60301404207551081e52107270b50100b0900054000311a510121211070644908060036212440f4485441c1c03200c0c542d080ca48c200306400c0c0005036005940640316203040f0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 570082778 1250 570081528 570081559
    0x15150405040b0115090e09061009020307120b0d060e030a03060906083d020703030e030a1d06121f1e15030f0905060403081b0910030e100902 62
    0x111031058402a144002001c010301245000c08019401c002051034000580c554825000c0c0d2240419540a9096080401030050804442150170090040d01104520314140b0b4200541218030720705421814a40b41c0035803144a5596446030000d85800c910180280c890744081c6544903400180100040b0b45403502c0440c00c0c0303180d4851750781540d003050010055428400190703140066441c000c690710000c0c1c8440403130014000001c2c1c4942c041d201d0f4016864414070300d0003a0540301158850645548148421038030b01fa8004041403c13100b006c114015140810f10200d0a54800c0c1c586410114101b00103011085d10b2085407900050342c0d00c02c06028107a1120041074917418015441c0c0c180c0383e240c12051050791100b140c0c50f054000341b8200014900341e008184410394851a0065450f60013030340401080c10b03000035009500140040d004820411080c100039094041d0100381070040080106115090340698000030400c0c0c1d554007210303034200c50200c0000141100c1c030000c81c020007103884640403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 570084028 1250 570082778 570082781
    0x503032a12161115030105010801240e010509030d05040e0906010501050d15050d03031a04060b0a0c020d0204050f01030302190c03060e070b030a0c02010e07050d030f11151504 77
    0x116910385180300780c9480540300251480c00116502950140348902850510f03a03640d541010700510440703201500ca6140900240030a20140e1041e6940192240040c202007a4224003d010303007031074100a4400320030350300100d03000e020340419a9054421122022aa00d42010141040302c0c40704218668a65804484036240c000c203101c0e035404200180081203208910760081ca090404c02c061006100c1d94a60008401d107440760410340200fa80d0b648050100350000c061520307030b69000e983c144026407402090300500d2084050b40020050048626411903690151034150307c0e400800c07d01c01403c0032403100020130820311086025128103030031203103203001903c0c219541c1c40d0019103003030310145980c03035010103065800320001c514004d0031030100344040580080c501a1004503000100004e0040e0042e0031915850020303a0558054581042580d4030940b64a50310740e81807800000c01006a0340c02c0d64004210001d007038150242100441100920300c80b59441082d002c3c100e103245100300f0081c4030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 570085278 1250 570084028 570084043
    0x405010f020c07180204080303130809031506010f0306050a0611070b0c0f0601140616051e1605030c03071a07083613020f1315020d0215060405060a0503032a 69
    0x2001c0d4100b07000199411b8041e80c5030b03c8ac1c090180c41c1e1079140164190019040c0351076041c1041c0701901903010f101e110b5921580007854681d1a08042141c10308020002d10039021502c81c900130080c1c1411100742120080c09a84010441c18400b652036111441c0540d44619905060301581d210351000080d004010b400400c0c280ba01c094016450014012a80c4980614002060b0350600c50705500a40010517a0b6154180f640484090404085500c803000c00858040e88540e20aa00c8104000c0450f94041981012250010041120924041c1110182e40501503001d03006040211700d00140415000491915141103490b02d0002186066074041c1142d05c1c580c12038019071440e640c01c50b2241a81c0c003d1402c14800702200d41401241d00c4602c00a28060308080546403104942c40c140c036030100107010024400340042e202da60110b5008031a400e4001b4442d601c51500d81001c5265501e440941001402c00501039030759a00829908125000c1020700814900610400070b13690200701180b180e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 570086528 1250 570085278 570085289
    0x23109140d09060c152309070909020102120a0e031002031506070f0b07091e0801050906240f0402030c0910020d17041b06020706030c0801030201080606030405010f020c07180204 78
    0x1100e2400e0a03850f410306040d00b522484071180e59803000c0d21030500c039002812486c15100c01c1c540080b07240c40380410341491607590000034110300380904640141c1c0c02090642e0481080c81400c0d403240000c840454102d050700c141543c050044110410411200342c0045110300c1d444080200d0810b0b40713000780585482604030103442c118031311443d800081e0254400d40e170030040c0c03403500c041090b80780e400d030341c000403404070a95010b00052082001002c50a000d00c41e44007556038081c00003894800c100a4481d5100d06c03c8001c2012104c03d440f015030741e000351404070100c01902c03c5481e450f02100300001640460007280c4110044800000d00601c0000d04c0202d00d403161765820140c3c00c0510120f0b21107030002d00300301e81203850034000e00d81c02e0001c5d94800000380001c0c1d00600502d49005400740841e80b13201c040d00104001c0000500160340c200d18066000401580d40a0756540c46051590040421001c83c599032800002c4006104100041c00c40940d0450248410510500b4040004910403442034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 570087778 1250 570086528 570086537
    0x80403080f0a060506030109060305101824180302010e0d0f11010906091a130f1101021e0c0a2913170604150207023109140d0906 57
    0x1c1d09154100c221241c0109803084081801e585440020302a40c000760402100142d468034100240300c4104141e072110314074050100544040103081078605010f640d0003514840056003820b445201c244600404e0602c03d4038100140400c50b0500ca1030391146c48001e50040d0300b0110000135208001c00e09005601c260380b101e030109918560281d402e000030002034000f5550319407441c404500c85000c4ea8225900c6030441001d07181040700940603003c03002c0c041100b002242e480210010721010041c80110b500403038440d080c0300c800d80040346403100070317880108402e08980e0554004900021580801401220310301807640d2a0084108a2503a6600b081c0c80508a003668010008a05000b403992680295260b111152a48103007008110102c041c00c460794014002c000502c6a0400d8207103642c05080d60561034054a44c0014403e0744200b00703211400300f518681e0304442c0200c003d54400e80300408100784611001403e20192907207084003100e219008018a0405051080366240c05440f0303243c0301c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 570089028 1250 570087778 570087781
    0x6150f09161107030c0b040f0b0a021f0b0619080603010207080d0b0f0604060512060a0302030c0103050a230a0c0905100c020607061a10080105010c110406050a032108040308 76
    0x484801240c482c40008900890001001140403100000041d00c00d207002070b079986281900448141d885684194081d0400780440b8a450354046150750110040d045410902e000351f913540d0300105034000550f6070001e070019400d40c0d1a09660712090903031f06251540d50444d135840007858240c0c42010070080c034071542000b045950400030380c00803170107c802074001e05407485604081005079015030040d10200e0400b04108924500140d030b581d60119040c5c4220001d00d10f1540070075034a031034102100d4145511200028180c400503481003100b066400301c07000109220300780138010b002e02030350a0003a25041408042038103004040e0b8408480c4003801c03020011035880000c940ea03010030b42040b079014408014400103c0d515028000701548454203082c000c00f4440300300480955085288424490107100400c200d03a00850020700d0307150016400860207800b40000350003030400d4ac0002e6404168548040280500801c4c140107001d85014080d26024010009440d08941120010000b410510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 570090278 1250 570089028 570089071
    0x423030d020c0f060c010f0c0801210f0308071404060e09010906080606060d0b03030d060e0604050417090406030f05010204050108010902043006050103050607030617210c06150f09 79
    0x10000c20000c00302000010700800481c7c00442a1000444a00002442000140100541c68003501011005048040c16030015955548030314185260058240111040019030081c000c000302090007c10840075070f9150703201d010140445a12001c80c5005d800c140c400464034203000d210301c030150750580f4014003069480c00200b0a091388582202c0c0c01585c2c81d5090b819054604201902a03030414010101e1b4483c01c0900d6580382500090146103c3d1781080d050101140e00301d1100d080b9501c031490482d9480c880100460091700c1e440d8030080001d200450400180078041d40508103485003643c41081d2a40d03541c0440c0c0c282d0060340104e2002c8102c00001101040b6400f812050800d01511020704c03036130080d1201404c4950980c425551a0008000c001100e94141f081781c01811000200f84101020034139800e554008526613016403041d4142c40308003103200d490543c0c01103441e410464041e440c06030a1180540d803441e04c518010201907a41400c01c0c90620046446001080005140c503440d18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 570091528 1250 570090278 570090289
    0x1e0c080f010b1c1217010f1d0f0402010807020a02180f01060f0e01030914060a0e25050907031d030a03060906030b0a150b1b101e0507050423030d020c0f 67
    0xc07221010b01214111700c0c104020324212080c020504540032109440c90458014006640d465001c06106040020042c509c81e1040030b464001d6020701c1d04400305d070390b011004d8cc1360840101000c3d512904941821070542035414200d0301c50414103400000c584d07030310801641c060102111403404585140302141503540f00754045810070b80911100340320184d05c564854244002030707502910300d548800501f001890204040c8041c4010504100f0301d01035041d0103078040308414010213116203804400700704500d100b5009001c0341d0034005414005040600306a40d80d07507004005420200e8201100080c100e8520710500084941180c282c0d0350554903604000018014900354a80c20305022001090401541c0b0290007107074980b5120000f0400f00c008894a0003211101414685081000381003800d110301c0050416031400b49404a9035403103400c815625802160800a800960064204141e1765440d030070504106080e010b50f00407004a51040fa104e001c2d0140c0650000e146508204041c20b10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 570092778 1250 570091528 570091553
    0xf02071a01060c060f1803030b0a140f150c010509060f07170a150f08011d032805071208180d0221070609060501031415041e0c080f010b1c 61
    0xa0400000700106c114103d01005840ca44081c1d001a40d500b0a01d682401d20b4000340c8050468490b41c0700f17114104000181c000001169079500070045c80c00360760b0b03524415406451000c41400c7c001d03c10b80c40c19610303069a40404947d413404200400c00400c5500c1d0050310301407124000303007241b40640e9658071100e0000e0203115050307800007840800c0c00505400314600d0786000c0c014940000ca428042018103040c0426411401c0356690010408039080114017540d03000b0304d0420401c441c0d1405a4101c041d641809034240107070590b0302e100740004105901440c074070702c02c1d1440d60611040e904000d2103d565150090003050160740a04400c01c5101d404428001611143e49100351a00d81c0c5681d50006441ca40304c3c085511503110b41c01402005140f003a0f6100d020362490051441d00440c0c2e802031792445003d4005025078510035000503640600c10124845290000ca00d44035079903445851369a00e410b504c0f1200500d5113051007040c450320340840c0d10b40007500708918100c1c1465140d1207501407180b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 570094028 1250 570092778 570092801
    0x3060a0b0304030c200405010e0106110313060309170a090905090c01021b0631060804050303130f0602072d020303030f151011060f0106171008010f02071a01060c06 72
    0x605c2140300e0030390340c450141d140130305203154000c445545072800182244194420104640d0414403105c2491102e8401030012240e00f850041003900384c03400d140101c036071641140b005170040040e01816141d04041407908a84600c03400308a2a9600f20243ea03ca81400004900503040142c104a2080d85203500c2040d04030001c211034986002070080d842c80e6403900e48011103100c00014500300a903100980c10f4020315850400c82c51520b0541d0f65513840e44001400700800e00b0108402d80288240125005c3c0c00d50390140742155164031a05140642005403600225205024410301500c10314114030010701d141d000c0d00442c111303181c0c19910400c4c20402400d081c0d0703420110340c450000344d64541ba060003c1101d5150040054143c440807402c3c003400400c410480c42d8100010090036070320071000304125526800e441e0064981d0702c00f0042d15031071039114441c65801c01d045205155130b1540207102862081000310844c2c10804241c4090607002d1150380301003441d40180c1004620903070444402d080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 570095278 1250 570094028 570094073
    0x3213020f040207030207030b160252140f011d150301030b150d0809030708061e1003030806061b1f1410060e1302040b03060a0b0304030c 60
    0x903018000ca4100d8200d0507003500141d00c07032141042801a000509600079800c0200321100b0400800080d5880484d17005000070490750801d5445e03007003a00155000404038005400006810520401c103103400f100f803400e40c00040c0395000103200c50001d2881e1080c0940034007803151200101005550200d00015000032120881c196041c0342e9960109803407804d06841100d648a50450800c00a0720790001c00d0120344101d00769040d5115580c003848040b101b540030b208d140e0717102c8032030b80460b081608550080485104207002d204d804030f1001e142a107030300307602c00001c00b0310359540d640208118924480078011465010100e442d80c01d040000301050200180c0304191f0740c024010355031900c1c8207944045074281c415a01212004000d00900040031803401001c46542000088171040b090107214000603c80240846c4809403500c40d011140300301064001c54869955a003484203541c003c940251240d00340180c0403450414031410f403400307550903586041d00d244481e0b0305c0e04091400181401c1004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 570096528 1250 570095278 570095299
    0xb01020721060207211106010e18150a0e070317030c040b03010602060f0603010504030e091f032001020a170d0b03060a0f0b310905030c01321302 64
    0x92510b00060515920458511440b40134500d1194507090050017403a040001005491002010004a81e810b4600c0c080343c0945c0e42d1111300c00301c0070503404032070134030140e001d00c802c803034149619200002e10654554500b40203c086001a4230388500c1c0380e01000b400000308400208007a010000a19409118291500d00d0161121340113006504240c0c401e00040e88040d041000c0e40340250401500700e001a00280050709159030090310018061021500400050001031405070741c0c8903403e0111581e542d2102c417165100d0814a03525501e80226100009410000141651000070b03910152600540e90780c1c18445035803030b40c440303543c04400004c641c6c0e503c0c0d105440c000d81d024031490380a048150390000e06400241c0309070085d901d101031214812038248031102e03a410401052459191518441d2505954100400340003e0a003c81c02405520000c03440d003055420542c0008613144814002c910138480d81ca031004800f41c00b1000364101c004620011407800f041804160355464030051405228 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 570097778 1250 570096528 570096533
    0x150409031e1b110f1002190305190503090d090e130804092c01020a0e01110a0f05060f090703020d03030902030106030624120807020d080c01050118050a0b01020721 72
    0x701c0309010000d586140245000d11880c4c03a103441a03c08110042d80c1014407001100000794036500c0d81407509011801c0b8255140c1050700c51822500040f00c0c00d81c56a00300d2a101000a082c0d8004842a250340d109040340e007070a40340100c1401044654400140300c141c3c1e11840304c804100f20155084494240038400070403400703c035015031100454840080800c00c00344030311443e035217040b00203030b0307403050744108100b400d00b075400ba0340c01e01e447d0350030f091001d00c101d404450b90345001c9020030043d204e0242c2440281c10031402140440c004e118044840d4a55150611a117881e00c94500c0000d50100888540780300103402a004011554001000010919542e403280c40c1680d000c483c80342446001070303e039083d484044607041c0b4040e00601030000540341c5541e46079040c03442042c802134803c0c0d8440301918208140c140071519000a007038000d101c5941e403600180ba1400008081030703030960a00e00000c00701c000d5031150801002c4141d0080040310700c0c24003030710710013071445881c84201c610b4020010701 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 570099028 1250 570097778 570097817
    0x21002030705030d02070201020d03054305070b010609080331031101090b160f0f080703080a05090a02030d0809071d010f050603090715050c15150409031e 68
    0x135542d0840c0016954121500c002418103420703a0000c0c041c50b1400c424007000a008410f42c88855004c0240303954000881c280401c000f080c68001d20102842810364440e55542c804050708a003442111101d45a90300c42505941c004218010013a41c0d50051211340f0301c00c20800c00115440c1e1030034a001c11554600040d15040c400305030401c0d5900a90090b0152aa5901640c01002490784500b2582042d260030091410480c5e0000701600151608080d4000d02c948410300c2122280d102603075030358410052601038060f04c0229030300d68040d4a000b00040786010041104602e50358020040c0042410305101502c3c0450040e00503603503031082140100700b28101c00300319002803c6007010800e40b0b601d01003501156030032a40020b07020314014010b1001a540000d9a84182d54080d0341c0e441d03e140005408460b940513410b007a8606220f44080054403660b81094140954200300c603291050341000c0a01c4183c0b00d80860003000140828900307120310740b050a2910f500402da20b0202881b05005c0c04058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 570100278 1250 570099028 570099037
    0x41a040c050102060108010b0d140c06030a0504420615080907090603170319020f0d050a0e15090c0306090d0305090a02010519030b03010c0201060914011202100203070503 75
    0xa800c0c4108050901103980c04008003030050400c139001340401c00c1c2403400725400503140c010090400504100300324800c0c10a003c2c00708196409015103850b440c0000c6401c000d0074098805072903420740d101900009041c000e03940d03040c1030001c207520100e480d401040134121555032030105200703561340c000c040799040c0049408078205c00982c0d00d01c00315080c4514885c2c1015015801a0542440c1550400c00683c101c64485428126920019103da407151480c0d00d0700c1d80f1100e000503440344006800c00311401050007504e1115101c04c820400381d03503401d03811000c55502413900603240c0c3c481c20381c80309042c0310384005540c8a024841070b41c0140040201007417a1101c103491425558200c0880c4042a960608c1450303402408480100740003003454001034800d00c1100c40e1400500d0095117040641400ba4200c05568840070b4020441800103007002402450700d800b484050a0811001e0320750440c00d00910b0741030340d14414103500c9030301c0c280c3c0c200181d04007410700148c00e5000510552001c91400d10207030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 570101528 1250 570100278 570100283
    0x7031d011d04140a0e100902010903030c1707080406121e0905031605211e220906062709051b0301090603030e0108071d0102030c010204080709150e0a05041a04 70
    0x482d141c5e50007680542070043c0b250307a88155910b070400c0f500260307034054100c2c421070341c0500700a24118024208507114500781c40b98401c100c900019104100440307080204104e0f04c40340e03601e13050810302c1c404900c00c0e10640840f02c6e05040502c241c0c507601801d0782d030041c4101da100d1403c80340351041d00058105034602d083d4040d02d40d80c00080c2801a840541460303083d0504611342d00d03034a4600c045120601c240101c2d000c040d054107011a130000405504914030f1292139484500f12140c95a500180c806401540541e60004030340c00c2584403402c0c4001c40c0130248880e01b4030726540050418501000901009112040101000500390341e00c1160300d0041d406404440004199541107040182a0388190003465040120035020070590560081a13420351000440d5186034000c51040102d00e1030103281c56880440d480050002880c070340c00520349007250341441081c41560b880308001001021284159280d118103400080c841c0c00160740801da201c0d103d1100490302803840ca154071200642240d04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 570102778 1250 570101528 570101531
    0x90806130c06050c060406050414062a180402090f0d06020409141905060f031b04061d04030509190b09010806091005130204081207031d011d04140a 65
    0xc0c0800d100c011a24200600898100b55160410360902c0740c2e41d031032004001410469035040400c040100c4c1d410414403400c41c160480f0640c0c1400840d1444201c15101c05004101201104060000e01103054401c801403600001720604050011b01019501440c0e00ad5400b86120512115941d00d440703a840303000c3e014000c016111800d1902c1082112a01c0782113865034280c240400400d1070701c98000c4424000c090a000c5040d8840b103003c111032180d240c480c2e95140c0106086c0c54490b082c191440075021004560501400c3e6403091b0821100022510042034800128006004280104020b02c08050b028008001c209091902400c940745030b034011000e00b8800041080300c0d5a40003004035003080307049640b680c1d2810300021102560460b441070f240506507031280d00d00201010b0b03041d01d0080081c10290ba031048000100e006441e8050042100031902441c4402081e13900c0c0036074104460340c11307152170300e84003451039440304a0303001c02c00310680c002e84070124080512030184503d40a006034050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 570104028 1250 570102778 570102811
    0x30209090111030c0c0115180e010b1f090b0310060809070308040902070b0a15051e030303181603030818210a030e0f060609060a0905090c120303091c090806 69
    0x303546c290340901070090130703204021005100c003841c00710f03c40e04901c10080300001e861040c60004c5001d0162003615990015045030341014001000c04104100350323040daa00411281ca96202ca2030a00065400313042c1c4070040720003440242e0052951980100b401030880c0d41b40ca6603581c4801103540150404400c2c0d47e00440d040003000404900301e42c1081104505001c3c0513640080308407800d00301d1207031500c681030412044c54a0170100384542d1803a4405029290f480c40c4c8440d040703500c0700102c40c81c8140c906c200a4803c4050750300a82d03150940754580d5a6040c41c1d00e4803120442c0621080019410b107000c0d268403080b0032154404401607114014810540706d90a11901408460305003508202603002086411000007010540d40c1d440754048980361132a843d5140854496400c0e41c03c210280e51905042c40900b480000b03000b070142204a420b900701034000d4050545902007980c1035030140e031100b9161320200074040c8120340005d0441c60440041c0395100341e51b600d080740c1518090001c185114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 570105278 1250 570104028 570104047
    0xd0c1707020307080f070f12110609010c0b1305060606030705040306110903011a091609050d0f0c0311090c04030506040f1b090f0b1012110f0c01020c160f030209090111030c 76
    0x9512002407c14090351001c0c0c03940ca0701d80007007000060701801c0c881c03e2b0000c0c0d0749000d81e025012603e619504101c91060b186002d102459505c0c402c22010f484e18464100010700a14000088074892121a0358a0f820300d855a40c400c8042c10141c1e010845008061011500f161802d10601c1100b489201d8030101c224064001e00c9081c038800703880350302000c00c109440c031091a00b125061040b150b084d2078003c0c610016060864110320241c4008000362108103000091001600d0300c40c60307141c0215041451601c91818900b554840e13840300906a41126000a000c00c1c960503044200314081c0c40c1c21420b0703002600300d292114596401c000b0f5280e9407a84024103c1c5101c0c400d02c0301c1904181d8185485168101d0301809500c2150520204181c07640840419003d40006a4a0700000d1101084e102d00c401490280030350001c028100b118499021411051141200c5010443e0702c000c2d558425203055809001d550700c401004580c5640d02c4d14046482c010f071203002544100c00104d1066102c10022 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 570106528 1250 570105278 570105299
    0x10c110621071d06251a150108010e010e06040f02130602150f0f040c08010507030603020909070f09090203190c030c0602010b0603071d04050106110d0c1707020307080f07 75
    0x1c00c0c400d401000454000220391620704c121a40403840d5a03441244044400009881d0751031000c00906140011004184e01d044010030f040c0660816441c4c040031914480046900040910680103c0e003c06c01c010000c0040c00d09c009604134a010300041040303141556504140c1e40b141603040d80301d4081481c204845503050104000380310f03038000342d00801c0c10706034001c400101c1d024007640f43c084001400b050400900c0c882210081c00321100a100c1860001409402450244002d9001e81da60200103032a040700410394000740c03a0721822403c0c00300e041108a1004000f0048202e030148107030703103090325841c0510042031402c6225080f5041407a041d841c00f8002d840072540a181507a050280b001c415684010940c1d030301000618181c420701d01d94003009008040074800b1785030450319010002c00c02ca039100c10b400000980300c00441d4020401050100c03094550103001a1020700b0054800720b141e00501c0c01032a40c107000904a40c4130a4640c2c44280c107001410201c0e820b594000c4008101c081d820 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 570107778 1250 570106528 570106547
    0x10050f150409200a080105040305031005060702030703080922051605030f01142b110a03030206010b090411030a0207110a05010e0103050702071a0414060702010c11062107 75
    0x603902800451810b07560040c036995501d902c440f0701d420311809000076480c0c2c1c034200070042040e0343c001c1c4507a00305810050421f5005848038583e0000d002804180c3c2d040140c21100302540c00b40040121602d1030720b65040607000030001c680c0c01015080201440e01e082c2d600e40d1450780120300000b4070384c00c2c00e80410180c1007086440c0e0061080c2481040b2801d032005411904450761032000c40a03006907080000c002000d2203040480485003142e6400309815000b404130581807003a0b5104040c00c80d590708000001c00d451200400691018005110400c1e11001411030040041c001050000c401800b010854000310303000c20342d81d640428900280b00300c4c0c07645550b151405a070489842800c000000301200980649503042c107460340085144944200640c1c001840819000282c445025035200d2580d4482c3c402c0100640300c2110882051900500f100d03612030f030584540c502804103668040c6031100d440d0031258010803c1c01842c000f44a68090807429485100c210307041c51516000107404280c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 570109028 1250 570107778 570107821
    0x20c06070e0d0609020616030f081f050d02060d0216060b0f010f0f022b1206080307020d0302070503060a0b030114160309110a06050307080a110f0c10050f 68
    0x20500520406502e40380342e0410380c0350300b1203004280346421340007041080c450200744007528481001c88600b8554458003040e181c61865032024025261074004010648403c648030344540942c50040105151400650807a41d1020b01001c0c2841400045e0000726040300b100201010380c0074419104114262090241c050001c031035000a1014406c00201040c0b000c1040c401800880f0309032094079802081058807048048038241800354000c01035131070340461141108003151600c10082040d840d01d000f0517080e00c0940c0e00450900c241e94080020b407403130f0400149d066020710308010586440510446114982d0304201050782d100c95001d240c211103074409400b02c0440d40100b4001c550b0383e054141202c0000d1403902240b0380219040c0b18100440402c0c2182d40024145000900590441c0141d84101510f03240d094659a44110030400e40b08640540506543c0401c4122400c0c25803802600d41811384408a4001900d10b1914a0488500760380030741d03030202240308200019952401d020171405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 570110278 1250 570109028 570109037
    0x80607080a0204081908070b0c180409052d060a060f1409011719110103050603060c041e08030307021c05041206050403030e15060102060c0c03120709090f020c0607 72
    0x207142480070740d180c01c81800e18030048402c00070301405002c40c0405947c01183c01040010560034414108040e5500c52190907004e800301440303c2c3c0851074a0310400007403c1d086006011080002c5803044204607d10080c510800b110b100d81860760b250400155114199804000421034103002003a00280d065901000044e0b4410089014607200da40c4141e04458a000300300c000301e0b8043c61428202a2088200420200030001c0101030101c85d10206864407000e0700c08010710380321748040c91f450f10030894403000040303403c210820006026400300702a0a019078200100d0741e03181c3c12418203551081e075050005903c240f0f10640c1e03100c55010400a6680203080251074240b41059240c00c10380d41e80307000f41c501c030781c0c07840040d041c54000d0304560010303000e28081d0380c0d40b40117500520540e00700581e25039006205040001da1401c840204079130003000345800441c10000c4c1d0540e401c401210050038038042121009000031030620724050f12208101080b805a181c640c00c961462502000030000c10810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 570111528 1250 570110278 570110287
    0xc060e0f06040b0a03051b070501050f0a05100e060402070209091c0822080904020f0d0606050406050f0d0b10051e03130f0303090f080703021b0102060a1a0604080607080a02 76
    0x83c4030b1104070341c00c240940c2070205169407054541400000399912180100c500015003004110065000078418165144000310350346662100204840b0704460380e01035003e80d468244244003c100c016a44083d0041c00545040d05c1903011480410064031404860b6212003400c2070300801031081d0000b400c1c20381c54803d84900c1c0c203445c000544400c80103440301440c660904141030000e20340807503109e1f0b90b01034401d560300d03c80f500c6402140e40c01070000c007107200d1034030310b010803410711807802ca40445403544d641c1030400c07480d043c0d424159840314400040c070541c0e80c6603200c495150110501c0100b0400d444240d01c508501c00303212400410080c3c0110380d4001001009168540c203100300320706030b8129103c101014214a001e0740289204e6101404010b024480d83c410000f992006105c403034800d60035104181460740704a1505511690301601607005540020000c08999100c1c07503a030b072080f91034034504807219000b0440c1c50f807164000c2c9140e500700604012000d0b403c000d0f556005540712200310b242 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 570112778 1250 570111528 570111539
    0x5130b070f301404091802030f0a0c06031109030f061509100312270513020909010302040b010e040f090204060f1220040f09061d030702090604090c060e0f0604 70
    0x5030079000e251000340000311000034503c4820f041901e0140640700402c00c080103000c0c0e01d00e1100300090008910a03c1009244407000d01e02040c1c071610180d214444500720303420440185c1c064544801300c9075103030000303101c14020341c0c0d02000580f0501032150003030701c1c031070401100802851055100c80e41c0510000c00a1040d042141205e400c1202e401200301680e044071111b0840b190500c41241d480c0c056407661000e066580607400c2203085420850f20b944148881440c80b000343d0061303561280d4002c0c4404010409400c198100044503401498006a02c21035030340098111072803250101d0032182d55030010b2086092070311480001e04040400d0303400340d602d845542c0611b6040b04400401036078801c0000a184100d41e5101c0200e007200400238041c20305903900000c010402d880e030681d110341c281443d51159110002042080d903044401841c0350260350303000d00c011031401401c074a030066540c08620001c29000760b00c1e04c000d050150707520140c00c4242802c000d4001076144c1001d22601007008200301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 570114028 1250 570112778 570112853
    0xf060608010905090c09040812010e070509150903101401061407080703030902090c070308070509031b0a030605041203060504110301150e03100e070b0f030705130b070f 74
    0x1128841100802d190351100049401c5c05c80c1135a8090308512000284000c101ca004003601548858443d00811030780e940724050126541035409030301190b0b0401005429081c00341c00411450200c21015240040300c1c00030916240104000746640341c0c0d9106072045407500250b09600422181c58021002c004000c0807161074454000c008140f070702c0010b404002c040c001d4110021507a0020008140c3d840c010117a03000d2603010081c11000900d0300000140505d018400361598120060300070144120021a444909458080300c160b1002d0000c0002001581c14000c1920a5100795001165013460803000f50a54145820851145040030303440c80e41513010405883c11101c82100f5580f00306412807055440d5801c0248050305070240d2a0f10241c1141e4a811011611141104032036105a54440d400c0840c09524400036078a00100b0115440310b10560240c103403609121004441180c1d901c00700074060340220411203010501a10070028800040700700102c0d00700c01c203a1303111041c1c80c1a902e080b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 570115278 1250 570114028 570114031
    0xf0c0b1e01091a0d020f13060510050d1d03030604270f0201020d031e020a0c0b04060e12030105060d0b15040e0105010f030b0a05090a09080d0b10020a15201c0f060608 73
    0x9000e0940d098030351f100d06015400c80402010090b042011002100300b004104c5d90100300801c050a040c440d01d072140c2174404c0030780d5101440d41d9000d1411a11a841004094210521030400035140c2e043c0080f056024801c00d000541d10031010414420036a1001a080910120006042c5464a82c41759840b900d15005c0301c190800b031020050303503030160500a856240d27800350003502c1e030352540c070400040001c00d0f446180000d444600320ba242002102c0c903200300303110900402c1d4001400303005600144945420100c84c0000041c4180f1100072040039000694001d60703c403a400e00d401d030740100982d507080f502c40012881540fa0a01040c3c0300300c5c0210340c20501c28402e00e0b000da02c1c0d810010b800c0c4c5040781d00081e2041d46c02180c0c0d41e0766004920004000c1c0c0001044584100031190040c22400d00000e010051a40d020340c0e48168205040400d02c006d16880c480e09000301048084241a52900c5008154584c4210400c0070040c1f1052000d800300c0381c180c120281154904202480040d41003041d06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 570116528 1250 570115278 570115309
    0x41d210301151e090906080a11090a0b030d08040606090621150608060402030105090c090403080712110a08061c0b0a0b100518010f0c0b1e01091a0d02 66
    0x1a0b076248100b06044491039407500601844103805007204000350381c400c40c03820444088180602c20f880e00c03807401c981c541c031886500504036100700d21131080c54280986800da0207000c61400103829040b130000f0074240b900c84030103c0d00151030841040104119440f4581c003404410404100150408860340400001c01075541d034460942203116041060500c1045440c90815005006140d907031131640350342c2d01d0207031402c0707200b942094000b42c040140080e0380d012007000285452200e0304c840e00c040d60b4031400076080a0030850b0503045400d02514034040c40c1c40505c0e034256690fa4641036448000c0c80100050b041c580310351121400302c0d004880f0464512906900a103010609889884c0d08070010402010702036040802c4d815000d4189401c0400f606051003490300401a14554800440c0c1cac1504000d00e07000031a070300c100c84801080102400980c400041103c840c4482030703007600744c5010034090b0710002c00941c070b491001d01190544ca50b40c2140700f4054658035403010117603000a51214016015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 570117778 1250 570116528 570116549
    0x7050108190b03010c02280c0506160b04080405090708011514040302120102040e0a0902310617070f030b15010203070b04030e010e0d150218041d210301 67
    0x1808100d032150b0388268040c40e0002c000304062901c0300e201035110014580501c900f004109291403aa0040c00340200720340364421400c5040c01d0810003088002e420014080003150004a200300000318907500c5103009030300404400351903524000820500890003081941000707010801000042c8044c1c010f0b0206141c41e050007039920301340020b14000d0340a1903001030340c804085c14440c3c0c4040344c10342c02031054030030f51241d03900d441c0d4901188a064441002c030003500071051510410514220319a2030088450325120024030f14400e460030403e45170385400580b0301d11000b104485101e50100b1001c0d00408020090700c0c076051039a21610310b0080d0003880d0f00c1405491104c0e60045a02c24030403924420341c0081480c00034246030800800b00e102c06406030b03010030268100c07076105140206c00300c05190340c03009200c50303200281e03491007010f5081000e96441985801a0150280e0781340c0c003c045034031100354148445030b8011071686262040c0d00100f0600781c15200c1140036555000c130216415210001803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 570119028 1250 570117778 570117811
    0xc010f0c0c0905150a06020316020d0f052b120b0d05120306130908070210030609110306130b0a03030804030504091a03100203010b04060c050c0a0305060403030e07050108 75
    0x265641810504010070006255001203003070303078107503000e940101540c954440a07948428180a03402100d40074410150348184014020a10070072212800f10780302034583c00a00006a031621666414840201c54a42080c01c580515104880025114288030b040c0360794a4440d0b41c4018114501860030310202c25141c0c00c0d4102c00d52503c00102030032550100840701320000c40c00703c824080c4c200359011403040c410b9607c20700f08403c0038080c4100700c40d009646d05243c120303030b9805c11489501c03021560b0181a100c12001520700f94522a0071307251400184a01d60700d1810804004400984013405403100b403401010091a844040016050303982c14148542561502d06080e200c601655105004007814003040c001400440211130504803400d50881e50340e0140b10708480300fa80001d00401400b41070500040002d03900c590700c0d0707038a864006d401303981c0c802d001c450100c0c0d00703d0042c0e04180c48603449101403208041d0f151040380c90f10a00080504003035800c00000810b9840b01800f046100c80b010034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 570120278 1250 570119028 570119057
    0x1509101803080c07051504030b1e1f0f060f080f090d0c03021203011211121902011101020c0102041703031005151201181416031e020a200f0c01 63
    0x484d8402078030380184401c4031044041c942d020150310030700003124400945008102c05107030130300d0461201403c0d8040310442c0d545955500520242c0110760384800b010000e030028107090800d070f000024080c0ca940e807101c400c2c41c0f000701038822000079140b0a5090404801c0003900d0381e000c50a4516881e0310302c2c00704640500f0f804d00720b02c0d2442110080e6400180040001480124410011410351007545884a08040d2008100c80000e40d50780720003040d00a2446282d1400700b0b0309940c501c0c28414102288600651002e040c22030700701c05c1208840e6980000d0612203840740d855081c0381100344500030b6203507203002c4034000c080005a1248a005014a521842c0013441001c00d45407541a080000109981d50729840000074480c0389000030f54901e881d01c0c40c07049000c0030000e248104802100d80e08890035140080f0000e04458409a00050001d580401c4d109114002080c1000c8181c0d1411507180780f245104204400000050403141d00c030950301100c011002c50082c0b54150242880f03050700043c070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 570121528 1250 570120278 570120283
    0x9090601090e09010507140c07030204331a0c100c0c0204051311010201021e1b07081f0204060c0321021606050a090f14010b1509101803080c 62
    0x3030b0040140900c12800b04035002c0360560295115940982d1814512041d0040e11105072054400300081900b10078411700c0541043d410600e00d040806c00000501d00004090b00620000026000031505a1440c10461540400405400f00d401101361700d04d04003058409981c0c52602582c1c0a09007074480b10705501007402102c1d00c001094001c0c0c018000d038500701d1802d42003204140070440e0b091110f605410041d520510030f0300c0700f00010281c1c8008801c80307191702c40181c0c3c0081c8415611510781980d2401a4082840301d2030060840600400b150031100c0030440c1c0320340c807050020280c03502c1031000b001202e40c01800d461404d50141028000080310f42c0c1c29149030000000d0000702c031400001c04003041c10b03c2c0008455580d00450f01003040b500c3c3c03103142da016129054409071014107402034481c00700d00498a0300001d40ca4840000034980d10240100b8400b054142464060b281c001c54180d1080c00d100c0c0209840c1c9800d450152241034046045d0b00842d102804080e1900c100403030a0030100008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 570122778 1250 570121528 570121547
    0xe070f050d0b280b01020601290c030c0a0b0f0c0708091e04020c07061107050904080d0f05010e0f09010b1e01020a0204090c030c0e040203100903021501091d030c0309090601 76
    0x1035400d01a1030f1010b5a0030007028000801c2114014854100001081c04030a01143c110b40100b040720041c885a10400503880e40020385111a02c0c0810044401d0076035040244500a901c900d81e151040d103044000c5112140005200c80c421a80c100f04840c00240413008860036060200c0c1d8500400a122260038102c4101042c0315412501c0001c1d80811207000141d40000c4404a0342d403600b060031101d203095140c49503445070301d820a0008001c07800150101000c1c0c5000a44840c0005240c01300d852558251142a409800c280c040d400a02010300e01f000b050552103403818009001e0340e01d0b00701c0854144003464030304c59184410304403810b100da0b10901c44e481500c0d80042040c80b08205504202c613035030359a8442180c2c1600c8020000500d040c1e548101841160010003500510750b4008010300603045902c0124214024102d04c840000d00d942ca800307019010520001446040c0c000c0c60200407007001d0181a2168401d01c2a58503100000044130f0f00486d040c0e84010407615a2401a1403001c00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 570124028 1250 570122778 570122821
    0x80a09120305070c0215091e0303090603040f0b07030b1503070c0b0703020f030f2e05090c0d0f09060f110d0c03110301090f060506030f1b09030a03030e070f050d0b 72
    0x40c6c00b03404220400c2c00d0f001030520410101e4030074010054160641d07541d16004040560190400c1c0601c40003032520802035030f0301c10701034031103e441283c3c0c540e5114100082140c6100100c0c1d51407051410501300042803140c4414480e550b02d01d503080c07015016108000c41c0100410307000c07139080003900391440303034043d11205660400c546440b030030840150b01c6001d004503000044488540304400344040804503000c014804078500c0b1004c13034109428040b4000b001000060006820003030213003540001d216201418820f41400503070031820f07181c440c05581c040100c44980c2414189441c00b0307041c0c03180840e0401e0550702000a5070340c0b0703204004d0300075010011855100346004000060300030000d4200110b66100c108007044032070344420800a81e0b00040d554040030302c0d4480c00040b4031140e44074640b40010120100a41800008000170b45400d0780c580c4100c5c0004d07215034081c02c1141041001401401d484036a00303804c9030400021403c104445c00c005000d80040e51b020404070001000f44104814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 570125278 1250 570124028 570124039
    0x5091c0219170607051318061502030703090b03010b0904020313050105010305031e03010b0418060f171501050f28030807030f090b040623120106080a09120305070c02 73
    0x5a89614154184000400a10b030601405002844c00c520130812120440600403000b00d01604100c0316060b40c2d582058134004050f0340d00710100f00b081c0003070641448050315500541d07036140580340050039010254001e1000304001d0005001494004083d180081c4040d180184c41e075171043c0121705d031040b01d030300c01400315440e0800100078080e020005210200d0035041d1070060480780160703401140f00c00d1043c40c40505085c801030100c1400d160480c001d0514143c004101e1503114900980c80750f0f103d03488032a03450781212b6100c0080300309200e208881010000c04c04c0301503151201007104940d400242c3d9210303020b580107038242c0b2828801d2001c032085403200d0310b240e440d842e86002d4099511100c000e034040707444c1580d507840e45440f60b4000d10035600c00000702420940361040030741d01042e4880c040701e40e140d945c0c04000c0c0d0041d00c204c060007910034a031f8a1074103a54502040508940340c09080ca110440c01e002c000c1d001304000c04109030341e201103458005034a5803005c1041f1100003940000a5115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 570126528 1250 570125278 570125329
    0x140103020f071a1e061513060f090909170f1903050a0b121203220807060e120403021302040b1204020f010e030a110d0f15060605091c02 60
    0x21900302c9403803030700f07440318205141c03d6290a410601e00c11041c1651051003802d50000418a09000e00500a125141000390f400d081c3c1c1c1410008040c0110741000303000401011341040c505500c000660010300d40290100201d62107522170713051684401c404116000d000081004004c02e9a43c111100400e4500c121560483c602e08000d003c0e02017501c40103241030819030758410030b1a1045105040e08414802840e18012000e007501081e003004111940c096203c84170329450130454217103000701030b100d01c100d0b9a4400300f074584901120741c4108000c1c4941e02064101c041203003010112400e50760100c801c8224403a40d00f2104010303214030f8010301c08130b80703020a0001d0704015407200507000718030032100289428244401102e0000c0344010850745507002218800110704074002e91007031400302800343c4d4003440c0c080e15013000142c26100c0468650460100b400022080ea00c00c0802400041c6401490003000c0340010392242001c44803d4081200c8c2c0400b14115076540f0003481c4040d840417a0300b03130b06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 570127778 1250 570126528 570126533
    0xc0a0e0603100603051b160203010204051203070212031306030e0c04022a010c0c03180b03040308010e01060203030c0409022238040320030307080a1d0307140103020f07 74
    0x161902c0e01c00d4401007070812020403000498580306880c2900310700043c0c0e0500748503042020b10720080e01c0c001d0741c25541c200000718041d1140e17243d800211a54400840c5d58030001d01c140422404526402c0d0f02c680c0003440013000325200303e0181d004948152030045070f240d40180680341000b400303043e0300303031312910000d4807615000f00000030401d0900101030b54680310032800c03031050a98643d4007504000542c01884500000e0080c554041c4003240c040682c1c10340360700da070b1901403140c0c000d031410360201d5540f00040060400d4038641c2c2c1d015000c03e201079410b43c00c14481c01e581900840c000d06c0c074030640104160055180400b04480401c1c940342c400d110301980d070b07444002c4200c002100c81c0701c02001c0c040410740026020449095100c900f0810070720b41071442d145e004c444004405030341d280d1028030912810300d640410103090712901801207c0d90701d071002e400c0900341044007411500d0007040c40c00701c020350341e03008220b42c0c1c1104c0d0313070310040d020303042c80f61004070001d10503050068181c04020600906 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 570129028 1250 570127778 570127801
    0x60706020c060112050c150f0d0b060307020309032503030507060e06070e040b060909010306180b0705031509090601060311040f03050c03010b060f031303032a0906170c0a0e0603 78
    0x24100e0280003074508086d1103d0a10000740032003900c0095800d0b0420020340c40e0802d13440208034840004000180c9124104002000e503441503030034a0041e8400300c0d441007a0b2800b13008201401d00000d50802d02c0280c40d8084a85002140c44040d003030010200b10f503000c0c45070035040804490440b80a50340a8030700040094a081d8070300300c01e540038525011106410303040500803980c1400c001454040303e84e10b5030761005d0240052851001c0c1441c414038030703200012078000e2000d004a900707444241e01c07071600208e601c00000c0e031b2040c060f2041090005121000e100031503041c0c1564424940030a0b14104541d042c0003910441c3d101401e424401c003000020f0080100d940d0b000810120000c0c0b003800741c0c10703040124a01800c21a0b803404103003007000ca08000340c28084040b025100742030108080103202c220000c0149480ca200f20f803040c0d170144030441c0944c890340200180106d403c22044003d48a840340c08c440341c0c0240844640680041e134083c00e5409070381c44620040d80200303015528034100800f000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 570130278 1250 570129028 570129059
    0xe090a090b0f01170d140f04080f0732040222180f0605130504170c0703110a08100207030905040e010207140f0a030311040b0415140a0c030e04090615031b03020906060706020c0601 79
    0x4c007400024000e040300102c0ccc10494608150001c01c2d1103085c0c220420403000b50701440c0e403c202340d420403c040700c0ca0420031030040000c040e241010740c084c1030601707500d5041e20319120000b421349141c00024400ba660344444104c08100c0c1d0800040e540e41c95140c24444071458281c010510301c4085024032540100041510a980c400c2407a41604804a424402101858020041203402240e4041c5900c903066024164139402450803038102652080400c00702ca29298445045035000101c410a2081002c4d807411241500c50003001e01c0e0342001810f54803112442001010140c94a4051640c50036100070345001e0510b4a200b03d544030354507543c100240c40c02d0320301036011540011101c2c8850071182c09443c480480c94407003248024160f5800c903145008001d00701c1e481561014180e0205000d4404d0181303500030381e94004102e60540c05e01c80341400c0300c0d4881e00d00703112003140b00f840162103003c3c3d001e03007000303040c1ea482f80c540c0402d00d0300001a014800380301d109032017100000242030b0116045039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 570131528 1250 570130278 570130289
    0xe0f04060825080309150f130e061e040b0409020402130f0803040b03070e060c120918060d0b130510060e0a0c0e090a090b0f01170d140f04080f07 64
    0x2000503001600380340e030b024014824050340e50400c0c0080c1004d400c086590320984100031042e42d1810b42618501051601301c80c48540d500710807680140400104007130110307001081111060140c0c61801d125904400f03030440c031303140140e403100001e40043c1c031103070813080d100d40d030060095442e8998424000c840c0315a41c030544a03103040600c40002c06000c040100c909440740003c1840ca140d85108003035030116000b2180340e400410400440050a000340007803100c41c0400b02c4000d03643c0b82c0150421000300c95049025800265039014001c5130b681e2030b0401c40c0301560100c00c015407a078403150304240c680128103016100340290344044404060390351091040c1d6003160141401c0b900c3e2554100c0c12145c10071030110200c0c4c0c250003880c43c00d14101ba0742950103e009840030030002c90b02e98034002c50410540b00510300c0005600140840700b1031300c2410301030b00960b90040134034010f044c80040c078411440c05044020080050030450442e00c0a08480c09800720604880b0350105200000b0364507009072040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 570132778 1250 570131528 570131563
    0xc0c0a1509120f020c0904020a0305030a020115050a0501020709090323130e0c030403081b040b1b0a1a13080c0a02120c03120f0d0615090e0103030f0e0f040608 70
    0x5410700d4070f0103408521a2462264002c11200c211a03080c01001c0070040c0042ea4040c000410020001d032042004080c003080c240d0011404980c628512010325006400c4580720301da010305c1c1844641d03400540030045441d03601020812003402e0a094500f050801043c603ca8004491000c0d03542c2c03060001800c80880880704000c8051791002e0000004801b6110450300b00b00070000b013000f1902c5010f4440d0031130442c0c2002e00c5c114203c4164881140c0c0540d0150760b2095001c42c500e03295402e5401640e11312000c0101030420100781e9581e090030503000710021ba5109400b200400c01034001c0b200003542050340090003d50704e00d400c0c0d00e595540e01000c80c0c12407140da0300300840c41c22506c0100f0700416040340900100007038000c003140c4400780d41201d1540d62003400184250041c03095a405803100901c0c0700d41c5e4400c1c03610400c000c028540d02c0f260700102c0d0022002001080001c3c3e1055003041980000e150404000010100045d8550040e51b41e8660050800c1000b0890346804182071201744a542d0340d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 570134028 1250 570132778 570132803
    0x703020606031f1a03030c0a0203011407090b0a050f07060207020f04150b18030a03090302030706020a0302030922090b0105040b0d02092d010305030703260c0c0a1509 73
    0x8250b03441c2c01100c2a581807442010f03141d140306800d508007036003220082280d0f82c0c400301030b000868a550810184107045a00942405095003801c0c4501001882c2c000207000e424a00214040d048500c0c3c0e201c0d4204003900044d0190403c2c0c451400da440d07200e0074078005940e80c1c02c00d0a220f400780d00292016441032043d40d04400d6136241a10801841c07400c4601c4841049180c078040d0801a04400607840d50075169400815659401380a04642d5074440d03200d64030117508500500d03140c02c0a0345c001e0f8007594042c0c442e41020035000030a0b1201100d04980002442d00c0e814940c0a000ca54146140c5203142000c0000041098058009058680580b001c00603040c004003008580d07581c501010303400c0300b00362021441c032802100c601c5d540d1141100f42c0d000380c1182d40c2c40507215007c09070306c180c0d0560030204862040560203c0005000f40c041d01140392280806540b240820310041c02c810301401700000c541007000301c107000820b1080d41000b40c2c40d5520300c90a0010300680519101250a80c44140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 570135278 1250 570134028 570134041
    0x50601050304020d0b13020d0b010603050708070c0609030915030c180617040212030705030301060f030603020913031e02071a03010f1e03120e0306060f010e062d07030206 75
    0x10350b807140d900140116444042038480103010741010308040c0b144d601c10401d10002da05c0710740710306112070b12070549644250315003071008084601c0980100e04001c041c005105102e40d0040c0c500f4003841d049030000811001c245001e4600c0041c5030710541944d24404858204260107a00803100c501c60790b00c0314400c1c08600312000a0442d40d5000302c4020030741c0d07162040038a1000c9400d06601c41d00c050310004401400d4400c030307803540d04581e604980c29480080103004081d071150003540c62031200e003010700036035040da8001106101c3c010402580030b0a241c00160600d40309184030300e4501d020b03014081c5070403085d04000b915207c490003400d000960f0030440002030100341040380c1c12120541640b4a190781060b0401c11008601444400114180360000c0086526601034884c0741e1070175244d0207454070414052604100700200084d100c0c40a210005550366082410348400540c21114155030301c040c40c0180c10364540e0504a12103003a54042590980f403004802005140d01a800301d940654400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 570136528 1250 570135278 570135287
    0x18021203090d0b09160b13090908040603020a021c17010f0803040509040c030611040603140601050a27121b06020705060a03090506070305060f010203190818070810050601 75
    0x41d10030340d42040600e49001c01290380d201c0340503081003c1e40f003502c000a051140e081c409860a400c1202c10b0000024400032080740030311283c008064143d010b01403c00c280d00da0a00c6030082d8440d41c020725400003180358449200748048505010180b55034100510070100040c17034283c141c100e000101120900209400141c9402d4408940e030700c0004616160a2609000380c4607000380c000c03100f08686940110004e1040d015050010307102d4503c0e40d4813146404401070594520156002c40d45140c3c0c014090b0b6a6805004c64040390761a05003540d00340e101d45d4410707039880a0300c0080c00c0050400e140c04160342d00d20344c402d205c10030702400095550050029011058245500c030304805031340584420099070070440c003d04054486070400103540d01d02620f0700c80c01c03e00300700d0307810700080da8810410146140802c40c1300c52100742840154209131004a50842403100060b0410500c248030000482001c0d642030002ca030240c09c03a090710340c002d80e92484240c5d120710003044c1310030113810800020011f5103c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 570137778 1250 570136528 570136537
    0x906051804020d060c1803110406050d0201020a06021312050307050f15040b0601050c01021207110a030503180a0507180606034208030403050d020304060909050c090418021203 77
    0x60010105007500d44d2500d004180203c0341006000015412000e410704168118009600586000c04824503002c2040125001600194411400c01c1d1360400540d83c0056a05074007580142e0059a41d161a8502e0500394170650008610508450300c039000c0001c040040d100d801c1c0308008550705074541800c450f0720b60b500801e1102e00c1006502c00100802c0c110401c07103030451418140180f414071036401440c00e9901111102e03001030800070074041c01c0d1360321164103052481414041e0a50458550b00104644806803510800084004610520b07074020305c669050541c3c03001c110744401d80d81d000c40b1443c03403a451807154051480c00328001011030003401840584200500e980096249000e0b4a0801d102404000304402070600015410300412800c40e5019004007001583c680b803540c94a94540100c10710001d046410500c01084481c4e0040e003500d050f10483c5038040b90640c0c031703a401d1200c0d5024030003a480d482400c25015880c04210b207118005413030300a03100c0a20746426602503640e240706 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 570139028 1250 570137778 570137783
    0x1204060b190326031e1f2408070f0507020f0402070c090f050705030105040c020a0b090307150c02031611030a030806030d0903051b010e10050a17090a080a180906051804 74
    0xc13417601400310882030004103a4004070007840f80441c2c030003150400c0d2500c1001c0d00800c1c0b4485c0c00f00b020764441400c140c5542007000191420540358909500000e088044110f0901c051080200d42c1c3c008655501c4610041000050021500c500c02e5042190b00d4204900c119409541791450784500070109004e0540f065850f81c403820303c1c1da482d041c00e01000704002d41d00312045024040c00f601c002000f1001044c007400c903a03002180c1f21911400d2032008034a2055042c0c180b5441c028042e01d00075000703c15911b00300c5d0400c0305900d41204600300782d10341c0b00c0d5054034030764940030304c0031100b08260b0000100f41c000c5505034211038150140c1441a107035201280000b400d0780d030140300214500c05214440110482041c540008040160004a9141c00d40034440c00d0102c0c90200d81114081e40c03042c00c040c030420011442c480c090a007648801c0e129201100c024124802c002120b44030940605480200046907007500030f580c4d0b5603101854010502c5000742485038900404d002c01919030690344a0040c0e8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 570140278 1250 570139028 570139051
    0x1509070c030509011d15090f0303070b0601081009050a1a041e2004080c33030414030309100501060f050423060304060b03121204060b19032603 63
    0x120b0300d41c01500c880e84180c3d40800d01c03030250076034817200340c50b9078031905d80c1c0c00400b202c5147c551140c81c00700240c090514031114020760050041e040424110040303103802c280203080401c41c0352901d824800c01c0400e150440710b0b003070b17090a05021001013150710000c0d841c0c2c042d0200d101501400c1c0100025200c0c0f1401004090b03026001903120700c00258440e0b60f8501409980c44914204458006496045588840c000350010f20b0342e045241048080c0101d1168951035100750808500d90110780b18008400664540c48040700140400c2008600c0990740c143c48006c580d22031805070b103250b81d101000544400072074145000020078500802411354141d0b000d88809060a003010342240031380344000301c1001821481c0c1400521a200c05000b0350003680604404160480c0e00818545040403030711000d04030000400040c1501c20350b204445421680c08200414014034038070004042c600049642126041d04a500008000095994000c02840702c1c0c480d404981d408030643e00d650004541803074840c0f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 570141528 1250 570140278 570140287
    0x15030708071409030d020c040e06070503010902070305090a180608030a120915182d03030b0d0b010b1201081903080a02040b19120515041a0301051509070c0305 70
    0x2038098042c1c5503401c0c1024950a08040790000000c1c0780042c2041c140000d41c0160200e0344d0a4207050040b10003a4220200410391414500b8008149103c14030031100095800324900b01010301c00d0085030080d260042c408400c654940d0014400c8010442580041d82d20b0803a00007280e040c0401a0754544500303807140d1100303030300314001c4d04050000c8940440c1c2d04010104100d420f40070b2441481072a0004803440464036840d8600203100b84484840401c00e1f10050103a886002e880811841c01c140d451f2801264101e04480455001c6101c2c0d440105900300000c00401d01c00d00c408042c109042075800c4005542c1da07203100d481e4881c2140c09021441c400710b40e6145020074054100b442d0002050240180750075510819118240c00c00880f50703a2a41a80f12038045055000008030b110030b034005010842070a001040c0b480b405200d001e568099a115940242c403594042c1c0540100c1601034001d0005291a8402e1220710b42060300c1d03940304a41d410b010404480c401c025110f0029450303182d59161 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 570142778 1250 570141528 570141541
    0x32b0306050a0b0a09080105090109050706050c07060c051005070806010912021c2a0501030605190302040e01090605130b0c0f180d060e01090506061503011802121515030708 76
    0x240c1c4000203040500002880000746c0d440d0034880c00e889403131001d00008440945280c03403810502c00b036001208001050280c000c00013808a942000c64981d8240001d02c4ca1b90361030301500303102007154501c20607484c000401c0161500310341d11a1140030241d071007041e0329844000b456030300e19801c44041d41044a0003041c1703030024107910b20640304d07500a48200d00701c54002c8903800c94010850082211082c07100c2400c02c02541c240c00341c01c3c0034007000c4071241044580d8080f03805a01205100c043d10a5496001ca055000402c0d030041c01a1500094180240c0c0b03080521405c1b800440c42040740c811854000240f072000039441520311050078944258900003016240c0001021061011580070103041a2180025a544207130035a405051001080c6c003149420f196007040300080c100c43c0a2510040c910340d00c0d901c0d120071a410341e01908408541c4428071083c1d00020300803281513070a11403002c1c0900100c005902906089018210743c40000c003040c28500c455240020344442e0301044504020407034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 570143884 1106 570142778 570142799
    0x3050d0504180c02061f1220120a030807031d010e0c030f1e0102040308030103150506040207110405040f0b0c0a0206090a020612070c02032b0306050a 66
    0x1007045400006519013600401b5486100f940c01e94030020801000707841c00140681c410390340500081403414200d9000c0a0500740c500d10058a0f0880907403030320700945c00002c0602406842c0c03044141d038059030082c1c0c002d001c6405064540b82700710081901e240703500007009804400480c0c5107180e412002e0806202d6035900b4029000026001a80d5000080445040071032a0680b9407440f441000310b8028002c07a040142166070000c000818003800325007035240519034000c00c0145032940307020001244510000100824142c8240c2022450039500055005000310300007447c0800d9990380c114a0a400c8543c0e0032103010204000c1603a590400c41254000021401060b0a45440e000101d05000c2c44039900c510100340c1001800f0b507449041f040c1c240e1035019044031400254101410030000900c9050001c068000c42c14944041c468018441222005424500e290f81051012413 = true := by decide +kernel

theorem cover : BRFrame.Cov 569964028 570143884 := by
  have h0 := BRFrame.cov_init 569964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 569964028 ≤ n) (h2 : n < 570143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
