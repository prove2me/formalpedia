-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4670
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:21:38.785978+00:00
-- url     : https://prove2.me/submissions/6a89c034-a657-4082-b9e7-1027553221be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 839748201 ≤ n < 839928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 839749451 1250 839748201 839748209
    0xd0608031b1506060a0908060f0a0e0303060a09050c090d140c01020d2c0d03120f06050105070b130f0803060406050108360d02010204030b070e1c0809130510 69
    0x24680052a2500c0c07805000b07000c0d240601a07280819510031150250300d2178405030a51800f101d20b245802c02c1e42c1443e581055030b100c1941c514107030300000d10788004022248a06000b41c9981016807400301303280018100101200070b00d030018041c5900035500c1441001d50140070700c03010340484894138046810b101c1544002410b55210300840d000940d080084020a01d482400307069000389001d6030300e400b80a004000341d070b01035448001e080416400c00340e418035140400d5030800c00102049400011200b0074050180031640038464040081d450703222190303000c1c4042a414201101d07640e0b40b001d080032188000c445420000c401c100c0b4504152160000506003403a04407994108000e18009041c8680c50b1500c2480807000104500d118800b240c040100d40340c001c0703a40b05418140028000c0d086800219080401503001c9503455204954034007401d5001400704ca070076400c000e49042d1410281400310b4486600307104d00e420f15903034442650300c40b80381c091000c500d519040d00301114803103850b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 839750701 1250 839749451 839749453
    0x9030e0a050907140901033903060807050d0c05090f090d05070305031317040b1e0f1b010f1503030f0c03050409150801020d02130b0922020d0608031b 66
    0x410240503413010300301007060414420035544910140040300035140e9101e0461031000010451134002c510314003200041500000c1550840003c85002c600307030758091260b40c425901402c014440340c6481e0000036111072190b03142e04e580d25652000f107080d0f0881103400807900100d6208009068a051145a20901452600510307150640d0b501030003074000900034a071901301c103119aa040040d02e41e64149907500301e03215241c45d00d507280818034180c0d004044400d500b05400c104510703025003181c217442894114145050034145c6440203c0300a00182c4182440c66485040c051002c20075845150080c008058500701031905508001d01f81c1c1c0e10080302c1808000c0040f20b0304010170b90002c15a01903500700e10000c162000705140c01445c920098010b01030a510015406817aa0801e0340140804102c01c0c42c02c0b0318980e0b4030400b0b02024012203a216400108c1040740b0350075403144481940ca500e449590041c200030300300b4145421034031550000c900300d03400001d07800da03003004403401d41801d440381e50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 839751951 1250 839750701 839750719
    0x90e0303160507121110050406020910030b030d0f1b03020c12060f0c090a031a0714032413090b07020c06090303070212010e03130311090405060f071209030e0a05 71
    0x15484c03a42211245840c0e004000e064240d407801100148917103070001c02c0c4c42c030b0288070030305040c01d1038002580028061841940000040071400e03019015460340000000c001e41113018002d030742038840102c0300f28490100b1040c004403c42c00c51003454040c54040c02035000302800b0701d80505001681108031240052035100c4010000c2c01c4540640c100c1e480401d20b214a500c950b2004085a505d00380d80e04010400000c4008841507175800c192802d00c145803658400d611744030102054030080c030081c0d40c14403080244070040100d22000d0b212082e078058000d00341c1141003003520500b000b100c00078002260b60755680707400d0100203035040201c00380b20a01210350501d0142d4610000b5602e10035080300034022011009400141003080d841036811241d804141c1c1e9480c003181420411082c12800121561048002141e40b1030a00850031807049030312000030f00c0e0030b4546d82c100e202416802440d410820104802e02c2a0814950007203a09891081e25107d22113016502081a00c2c0c807030340c016034092102c00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 839753201 1250 839751951 839751953
    0x403050909010f052409213013050a0303021f051909020415030c17010506091305070b1b010e0f060c0d232d07110106090e0303160507 59
    0x12000c40000302426117008400500030351503180c00e002d1041c0a650040f42211041e00c112000740e40d1328000c040700000d69003103c1d80e0615121020b42c8001c02004045000c0c0098501600214024400da5504142e42c00c6501e60710f00000e801040c190700300f00d005070001550040000b00600e41015080001030041c800751400c8403000100480901d4a10082030b11100803206640307403940403406107250360801d501171580705c0c2442c3c050b02810b4800c0c25403842908080101905041c0308050241382c00401010702e0384c880c1c0841c0d104240f0b040400752054000d51030300244510305540282000e0100161008440354039412081c21a504003000c440c2170b03040007214041510000c80d8803640f040000c40c85a1321103802d1903d20700103100348014140a52640c2c043e295803407a00c4220948510002e00782402c50826511182c000d02d285030015151101048001c503a40601641400312a0b40011000107107007683c90726403900742d03081c00030081ca850304000140658683e4030030611354003e00c01c0c20000e14113401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 839754451 1250 839753201 839753209
    0x14030a050c1507081303030209060a031e0204120b0601020f0a2009040503071202070f180c05070c060e0d060603120807090e0712020f030a1505100813050a05060403050909010f05 78
    0x3008140400c1445e249400c80704050103039041e00d80092024040c0380e2100b501c010041e0050a820b071000c488079145200d403071b0010f2403034000c413800d07203c150a41c261951425640d510b031070342e4040d10982c10b40c010031300d5a20150f8030401c000d040407409080e8020560700100080c00c803000c3c0b141e44407030050488004110200303c00200b104c2116500c40c42c00c0d40100040c0c4000c17401e040c0a50084140d14a502c4030000c5d0080345008005807042110200704410540780500351010300c41c0c1500100542c140007010400b45010300c07040d40384214090184210100b01c0d640e958115001d1340c2040b80c120a41035a403843c2ca0380e000408a61100b181d0616594450401d9905c402141004041c170041043d400d40a000c0806141c050b5401c550403204034a4480c202982d0081c060107489644403030881c0314a10000c1c462800c1105c124032006141c4800010345c03500c403070700b124090040000755100d102d5458aa40050001c21003039104a0081c2d03500340c0c961700c1e800100644210117078805180000805800e00007555 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 839755701 1250 839754451 839754467
    0x14040c050a080a151506020607080c03150112020f0705060108010e030c03070f030c0c030501020d0f0b15070f1b0e0f1e060307080106230a030309050d14030a050c1507 73
    0x1810030104c540281101400501400c568895400da014100704001079403a00010010b008003a00d803030303802e9a80e848501030182400103c0355202001c200c02403251565002e59014032445005500c09440d000e10070a0600480e48001800c0350141d0140c0d004014a41d800e03c90254041c075110040c514041c0c40a850179500d00480f100509400f900c02003800030540240310300581144d0004d880f0004a949080990003500120721400685092544c1203900b50708520171400c1c0e000b0028404080301828a05160158100d010300700c0b0210ba54090500106404844510345041c0e00f0441802c203a061003404d55082101912040c0c00d91901c4003440301220a010702441d40104100800c0c403a41c0d1001d001a01e4542240c0c000c0021354603000c40402d01158580d04c102e0b9110071105024205112336080c007204446c184000340006110541c10b1205150a0806400c1c640c015a48a42c0070ba03d42502070f800c591001100e140404e4000440c000305079804e11641441800040c8c42c060240741c1080003800000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 839756951 1250 839755701 839755703
    0x1701060605090603191d1b100e030a0609050313090b0604060f170403021b0109030c14012001020904060909050c10030f062d121106070614040c050a080a 67
    0x3d0780400020243e4141203610a503e00f01554280508402807804da001242848401442c1d401883e0494003080100100c0b040301d581c028000c0060000b82ea503040b5125560582d5095260240c0100e11f00425000e000d4415040d0241001e56615161102080403815999000005641c20425000c9650f601c1d03005460480d11641410b00543d074515600b240e01c2461190680302c0044903e06101c00d0580c0011180c03090825445240074a0003020010f440860051000800c5c24240e40818000b4003181d0003054285141030502007002401080d10f12101c2c40c10312442c40740340e9400300d00740b011b91400c0d0140300010040300c4010014030500d900c8451f21f40310344840450103030018840c84214039101c0d602c1002180d01400301006419114140101280303d164180812443e800c03440c4525003041d000f15100701e482a07a2a0001e101040d6500401c501c016840d03c1d601286c14000d02001c11020b0084166401c024a05120f443ca000e140c07031140a10103802260040d500003006100c2c401c00050120602 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 839758201 1250 839756951 839756959
    0x50106082208041d060114120a09020f0a14041109011b0c0906030c15030629040306390906110102071211071505030403030c02070e070207170106060509 67
    0x51040b801c0c4031409201eaa44600d00540088098020701010000b03064082c00d400d81c2c0303200104000f020380e00628052000e84011540610b40030a400340001e6024040b003910203040c07905041c154400150041e0481c1d440030885050158100d40d01d0319051050b284090b0142822608000000700000e0040c08010041c10015140345140001c0c031400c520110000d1114981c00d002d00e6440e40f400b20245d480a00c01c0c0214130204151f4481d03c54005c0c01240c0030303145030403100306e0715018001e11565960005030340c1c501c8560003044003101049060040d21070b0283d05649000d20b81c010440040500000c224040c0c0306500103142015000d90701070106c80841d004d903e84108031402e99895140240301c2d440c0020b000d00c030410b00390401c00382c1040b2080c0d1200c003a20181c400b025035400008400801310300c0e81c000011010400500043e0003540324050315822403044601650f01c070442107140410658282d8050b80c400e50080188071124010805118010b000900485250140281090041c0d2501d140703d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 839759451 1250 839758201 839758261
    0x10b091e090705151e070f080a030e030310030515190c02010f05070206041e0f0201030203070c232103011202030a0515011410020606040c0c08120a05010608 69
    0x3100c1e0003048001c0103004010b0042d100c2030800d21a03c0d2144d0f0183d40ba00b0191098030744841c40c0d102289013a214116048604040c80a640d80d41d15105a400140c10b1800e040d619950411011010400b65210700b500c664004003990950409500e81840ca22414485091b88001c01c800d403c19500510b0758810005000300310b480036a4004d9014000e03201e041b80303085281204015080c0c0d40080c030305e03004134010800301d00781040c0c0d004140c49120650744068541000001d8480055203e6401180d001903a480c010a255102e0b5407820140c0c8103154007010400c44a5542849042040c05090030007440d40444e0703200290080c5014003036000510541e6411030f2400381d28015501c050000c01540355001c829146100103820750810902028011290620200d20f054070540c1040784100990ba01c503600280b000350360303034000c01c000350200c070710709900300300d020b05660b800110464003801e091000c7c040c8075111440c01c010080308444050b4040410000f02d1400d204000040d0b0303ea00c40d88141e03600f0302d83c807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 839760701 1250 839759451 839759461
    0xc030c0801021309051b0d1a030d0e150c061021020a030f06020c0d02060703140c120a06090c0201020c010c143a150603020f0904150504090f05010b091e 67
    0x703140e81c0b040841740003841b00080c03e0241c0d00d151792080302a08041d0960000c01d0320b803081490b6840c09003d5090000c5810f00c040d0441600c6c14801c1d0507003904e00d07000c003140f8082d401d000140c20034400b030b28100010819144144640d05040300e001a01d42c411030051618001c0503000121182143e10010740003440d000321010a0092a8040741c1c1c124141c0780854202020301d42009594100c1100c0383d10020b49092084c10a82c90717402c108a00619545088034103080c41205100310f007810107802148569a0f514001074a04120300902007d42d055400058076004400c0302d090030350301c0309100c04080140a04084d00701c84a1401a039500c820501240010a410118000b001c1c02a40b03130003100c6603440401c0108601e40b00c0c0c10140d020400d80d040d543c0350555649060302a8051012194118034041c410000e150030540e101d261104058840071084a5980000c2000c45002e11000e4800e210421422070601c00300b4001c0500743c0d4030a0f01d82c540e00b0703d018840c82201d0510514910400041307100468 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 839761951 1250 839760701 839760721
    0x10e0f0a0314030910230a271a040509010e0603070b030c0702031501031b050a12020301090c06081f0303050d0c020a020306070f12021905071506030c030c080102130905 74
    0xa8901d5805000701c100380c4484003001d40311aa0080e071507071001110301b0310020306800f00419101c0601864884030f4080780c005e2083c10608501c03c28400d031810344c0943c00903455400d407207446401030380d128000750364900b010300303120107030070142c100d40c0e0201e01180034042d80d9180043c418007181d103003d103140e0b20390700c44c1612041e87d0f20850a01035407601c5240e04540d29441c1d4100c101741200d1040f4541d41001181c2481441040f11502c500d80e071040c0e8109040003040000f1070780d820740510040000510310a190780e8441000c090f030304030600140c40b8500b0060f003400d407403c0d030015041c00c0241e408642883c580c0d0052603407161103440f104003a282d01c2c0c0340240c0383c0204910740000c0d034020261803c614241c85c000f066001034000850009070500b454501210b0107108444c84850300f0030381d2144c4264108400d590320790220000311043d2134101c0800100c0185e5110f50380103113100c2c00c15640010319509102e4107015107a00168410b0f481001a0034104c0c2c1c04403404000c843d0a400b01050541d1004401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 839763201 1250 839761951 839761957
    0xc0c0909030509040b040e0c130e100501090c050c070506092b2604090e0f0d0e0f010e0d0f050c0d11040606050c07030602031003080a0e010e0f0a031403 67
    0x5800080c2409060000c042e0070002500d09414107443c100444481d500401c0107981145160f00007542007009801210b0800c007604482e1404441004200c02280d00e0840d40303015032490703420350040c0c0e940006000440d55400b0b0881c030003a0500d441414074034900c80c8161181042e10034079101e260001000c2215454689880b101200c401c0c160b000000145001203a81e10704e482c40031103010b5008000780c255600c108034486009a01c800c00d040c10711f4100f8400c0c000034000071084446074070546920b021404c80c201301d43d0101c20229a24660000e80440074001101112440241030144402850b0780a840b2481c0e0380404a401610115640d00c080c1842414040b082050541202410140744140120f00d2900900e15000391b50401103241ea60303004958900856000c11001e422004003080411680d80295400078080340c4d248141d182c0da5500c4c1462a07100b0044940401e0030707550707080c00d60368014500e090700e543d00b525485a800c00c0040090f18800701c60000405c00e0610031060b018540f402c00503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 839764451 1250 839763201 839763209
    0x10e060105071203020c282604030212031308030403051b091909060501060903050c041b1d10080a0e060114011b060e0a021c0503040323010524060f0a0c0c 68
    0x1c15003480181d401da0800d40741f40c410066403007048030f02140b03161060210352002040c81c810200360400b800c42e8204003101c0b114440c0c1e8851844140024011005041e202400518654000359135861442c50444c0c140528240c00500d01907106030303480c00c103444607484164030800c9009220700f500701601400004003035451010380304601e0000007041090b04040580300382e80c042c004032007001d8150820081600c25001030100d14222106101181174015a541040c5043e460008140321400c0c80205a12950101c034600c005a9118184a01100c0612170700c0d81104041001d40314660520144192034041170101d541004518002c0400d22500e03400c0c1c11f00b00b01e6001c0c1d0144920b00b0f188039100da45e0458031906a120f00c0001c2ca204c00e80d204000d51003e06507621401850405140d41c41d00c0741080b02141300611a0400c003d40b00e0000c1e4001e00c1582c0c41070340c680d040b04190314088408840303003603800d00916024410400400d420207903560305840581c116480e294506510f00d01d421075400e049580 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 839765701 1250 839764451 839764483
    0x609061a2d1309061703090303070605180a0f021c030915050d090812010b0310030818030d032a0527130207030f09030f02101b050105010e060105071203020c 69
    0x10440803d43e80000080325245c8407103540300300703c40048a4691149112040e85507004000160000d01d080e0005a44002c140c035101c86012744100c142410150f5140003201e4a03581030f1086421440c0c11150b4884440ca0604240d0801c0c44030796005d0040b400c18021074041d0790707002c80d10800c15842241190502c0b40c1e00c44050041c50360510f031520382c035040021410a81c2c4101d10000c200c0d10481026a4894103681c240d5403042840c50b181d4005541c03040b0340d54041c01300144040802d94600308040440d000301550002555404e81030015079025418080d18480009003400c141c205500c03c043d1410b903003091403400c60040264524103141a148030615403c04104074070405a80318a030b020780740d260b000e920b82542546482c44100c0b101d0469000c0109003c00c14002a009030811240b40300c101c1d5000d0501803602c0d10368606104080030342e0341041314a071b034407103006100398132a0b0415150408400c0c20140e04140d9155907800308564244000b0040541c049507111516508003e07032002c681e0450 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 839766951 1250 839765701 839765737
    0x120a05031e0307091206110f0c01050a0513060209030a1a0703050c030105131e051021030807080925080f0c09150f03010609061a2d 58
    0x4500240c681d040000385880c00c80307540e4400045651580222803080400399601c484560410620305440e1004080a4944594822003075480e160880300600c3c00418480300582c13224101306046080d520010301551466080105021050071404004003015900c0038026803903a1154011a00e0082c4415019100d8401c001c51459050b503c0840680900d000343d0b801e00069441c0da035403840611080c03207120f40000c41d0038000d0040c5c0485a000001d00200c09070194440207403280c1e040180c2d03c0542d038a402040c0c0c201c03020014861b180000400d04a40f2055620500c0c0c030a44016040c02e40c010314040500505500181c0c10481c28015195004540c6d4410b000550346284403d18440480c01418000c2c810b080140048402c00500d001700106c0c0204074407001d80d90344c645040c486a42551244d000345000d18189480d58080c01800c0c090b211042002821500d002428101910f40144070412854100002e14104030304101040903402c0c40070102c121040c07210004e041902c90000c09140f64034200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 839768201 1250 839766951 839766953
    0x23190b0c10052d070e0103051e07030605030f0106030b0126010c020a0209010512100c050705010603061a010513050607080706020a1106011e140a030c0303050307090b180f120a 77
    0x3d0600b681c4400107200070080060b00c4100a21010402a100d250129000c066104010b45c0300340c0026600041c1c1d540d441002036010103d10340c1102e01038854001027521440184400d00f420013544800964410090248502d503807a0351009031410b008101e0300082d01c400d501d20010019009007120328800008014001071403200940710502c1c448220302c601c80c2c2000004039898100c07011402c21441001030304d0020003402d0f402000744040158442404000d011050204000780b0a1030003e5002e40c401180106030b101e44080d201c08403800c5141072103030a102002c52200b1040302801a9141511030036611a4542403000e49406641d42c010119400000c581003001e47c0a4142c1e1101f9604100322921a46c0720440135a090070425011805050790782420130070b011a15451020100000d000140b00d1038890719070039420301c4141c100340c0105c1c50000c14044856406232494009000e80c100d00790a0002d60075904119560b010700c00c52107010012109072059035000d030700c40d0304000002c00310740011500d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 839769451 1250 839768201 839768221
    0x309091906050103020c0d030b0a080a050a0c08010203040f0f050a0807061509020307020a030e13020a17060607020d06050a0b060a0918060e04020105030703090c23190b0c1005 77
    0x49010000646424010300007429400b034006d803425500c4190140c01006503412041300100401c1442651109030400c0015200d032040c0031503400c3d00c3c0124050550041c0b00d04180c40305258542c888480ba038030402c1040302080061188680790356200c0212542072645081240c82d119070110094403400700050342104000322644100240b810482000e8882540c50f440c62080b80400c540c0032016030403090740040040d1040c013600905000050400e80c541c403070014408100e820007400c813004901d026080c040b0101c00f095446602010071250546021103c4e4041900242d000c04001c1c01c00c5d0b01c0d0b0001c40c5e18158140c014181a02c000b9143c2030300d403140c24600500e5000188648054040030311107800100740b44d809110241c5a03501e05402154542e58011583c50703000900010400d5540e424100009801da565000240260442c0c1c5a105016082110881c51643c100902c42d00308400c89400c1e522042c00d5500c00ca502c443c100c1603c4d2140081c00c24100228004012035481c5403504000c02400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 839770701 1250 839769451 839769481
    0x302070819110a0b04120204061703041d1e0702010b03011a0a060801030206030f0711061e0105030d02060a23090304030308090307080301210b070c1b210302030909 72
    0xc0a00c400e000180c801030b082c01014151401107072801c0400700000d019448800662011040c400741001403ca99039860241154164810034401303600000ac04210400002030000f002540c40100000207007001300d01304c50a503020300400148500704500054006000390721460600c071000e4000d01504080c0d4444403040d80300100c185201d95942138001c180030744181c0095059070b6000d4001071039910b510404600d40e100c020302003400c112041040d183c0849081c80310305c5c010120003131240300100300c4a06102e0800c6050700700c42d01039441141a11481ca50009010303400000000c03000034441c42c21109428000000c1180809440c10481130140b0b58a0000041003200e000390b991201c00c4e290401115140e110b0341d403001d0144c50b410700041c0b10781c43d0b124015000d110000000a4502c1095940b141055442185d010b0042908482d0240901c18a0389201e0021148104958140d41c141207041b15444680c00c1a09402d104101103c0704050007041101e028210007005140c5d10b1614156100c4442 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 839771951 1250 839770701 839770703
    0x309020607031107080f120c2103060906060c150912040f080c06120106050f1b0a031106060325091e0b06040605070b0a0912030f150617040302070819 66
    0x48a200400542060b001c10442200f07801a0040c14002210008009080d000b400d5829074a000d480c000038100303040070901c449c1001001c1200c2c0d071030f841c0010070801c3c046002812180a000c0801c103419085a020804541c6450a40085e1842d511455202460220f0a8001c02e9194500041c0481c500e1410074494045810002c21254030f00500418890303640150030040603254405070060003014042c001400c1800c8408600303508100c0e05000c240100d1001c01f6500c040c4d074200e0241581407560009004100580440003040f1030704112012998076003009120010620074080e0320300780001c1d00f0302c1000003442200000d2040201c01c43c2801c1c2c1c001d111100c40303e5140e00c0c0103815000350070000c0607501124800c2e2203007400d10690391612640104010601c40059030789040030030005102c5400440d4402c50303a0340000702d420b04100c00070304441c100f4101e1041060300390420406135600940c0906124925000c5041a4480d45000c1e45040303c660031806503030040c1100c80000e1241481415412 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 839773201 1250 839771951 839771953
    0x1e0903021e120a0c21020303041202010f0305060913060e03040305010e06010806070509100e030d03051005040e1c1e02030a2604020f060702041103040501050615120703090206070311 80
    0x216000b59000d507a98011000103090500d0a2010880d503856040d40080074818040c216410300e4840d80040c2c2168442d40002c0b1818401200b10010b41d44c3c46200e08142c0c61440c2000c00090500c100081d40f034402c01800004d088000302d0041c000c1001a400c00c2c0f4120031070000b1a606e5076100d10340303103001e48104884903401e8420840002030480700001c440380607031030b55120fd40c075040c40f000520083c04906800d40003230007882014001151809c2141008811007075400007581d0600380d213a40d241c00103950203280b14600740355107060310305000304045028a0b1800642000038054500c1130f00d0310341e8940c40130b01d80183ca440603001303025004070040240b42607547d50904100f03600502144403400c42010842416699000500181043c1070f410030341c104020102d0f030600c00a507001500761141e201044802080c003006000401109002e010f40044086071555031808103003000302558007401c03103400e10341c28085000c24821402503002c4d20116801030a002d0381c803005410041c1503242c8080a517042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 839774451 1250 839773201 839773219
    0x2040c030204030c0e18030a0c23100e070b07051209010c02090708040302120322080417100b030609030d0504061812080708100504110c0105160801090b011e0903021e 73
    0x10000011042300c03c2603d49440300b012460050719408012000c07114490204155024000c0950004202400e80b4010384480450b44840d8807240780c2c1080500d5102c0314611a0078060791002410100303c06c0c441c0d045e090b41c029216480200102c1d1110b080d040d01a4120b008401400200c903841402e49100c0c6009400b11010601250720014542c4401c991404102e11140002052008180040d00e019401360890030b00309900c40c2400089840c100b43c0c0350301070b81d0010342e080710140002e02400030343c120214060415440c204030000c0d120301c80c04200b82e131980c1d55000007070200041d651104051101c900113192a44100f4038000d142c1c14400100c100108605000140c05903200700745080c4030794940d1440e541500e00e003005210242501a0f420a5050070a0001c0c0aa0b0a82489010b11540c100314600004588180002d4503140341a080409607905000342800d5903608002080701e403803482c2c140e240071040e064404641c00c1200d504001e41c4800380c00024005880c84c42c80e42184020200da106c64 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 839775701 1250 839774451 839774491
    0x3030a060e0c0d0f1d0705010e06041401050f0c0a0606031a0403050d020c031b1e12090f011b06020301050a050d12031d03030127020304020d02040c030204030c0e 71
    0x300c6542140c61460160007008079036100e400301d801013140006000000b00341c1c01d00328985c01020690000c0300a603d0350010008210543e407041d000604501d05880d210320741400c0601c805884044d44c0300b1103061103400143d01d0042003070326040b124104101030603030318902410b01d0181d010301221311040c3c803000018131800d200e0a20000c5030502413035064a80d18506030050702140040d400036008131000b03000c18488444004110300112080d407000c0f41c003400200c1d030f0081c03908050300468038610f0129031008550440300c03c813100071244402000c035541d08101c4040001207a4001c96000e8103001e4541444051003000b140e07402541c162002200d410300115124000c0c40001c00fa0b500f4042c0210382107031203826a6601a07402506040507014042c419115000d1446185a00c203a004105c4441e00500e00303091604902003450b1105491030040d1b1942c04c1035000030360354140a40d8060311459480031000d001034000d034100e5004552014034031b4640340d60307285418003100040b55081c13041505081c8c008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 839776951 1250 839775701 839775719
    0x3100f0219033305040f09060c08041e060e0d030f1d030d05041a071119120311191206050406060c110f15030402010e120a0b060f0d0503030a06 63
    0x4080fa00348403007050071050460240031041503e1203424140d025459002280c03981720781c01405041600755074049071817003036807602c84111050b1003070003c01c1124050a0000185155280001c0001b440e05040c22040203403c1884c010988007000001ca481940c450402c1c0303507010740003000e00518000c420000071500803281520188001010704150b001040300c039010101e950b00407500180981090f0b150610030000658000e0415034110b00444c00302c0d1204001410300304a6400c44042d030038800c0d200d030f21190340c0d901c0c0c0c200c100300070541c03e25441d0500c84207491b910340c0aa40c9403000204c1d40701d1040302c1440001d82182d0207c0c04600d40142400d00106140c14070f030003481c0481e030445c0e44000348442c25448281c42c080b100e09103181e020b86101414512503907003000041640804a500c00c0e03030390a0910000d40420090340d10135010b03503442c800c4031000340b0700803800030980c4e0741099032107500e6503071200003590040081948035400080c0d4684601400300c004051441540901001c01c126a12004d0328 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 839778201 1250 839776951 839776961
    0x106050c0d0818030a02070f0b070b07050a2a0203120906030619050316051212032e030c210222021308030a0311190e03100f021903 58
    0x12040e030241d1a860035051150341d0495002804114070000250650206411548510315500050740002801d110320890030400710010908007c2d0a860600c465031543c0c0001c04c020000800c0c4070002c1241401c0a0050410241a8010000c004810084184c1074070030440381d1310090740a0312621140b176042e100c000c001c44450101c000d20850560f0f443c4400c001021000101d01805101c55400000d1a43c17010483d244d0041080944910b519091406100c0300c0280301848000c1d81d4412910040703060070784411650083c10171072110711000c140814111001d003000d000e10300d60045601d800020301c00082d00c0360003611104c0c03c02c00d800c540041046031680505102c0a5803182d007150300e2209c0602000b50300a400c04800d0307400750420340d040f65054240b07181036201c4150b40d000040c2d1150543e40c1031156103200c0400d00d40c1c250400911200c9407e285801003080b0050045029601e151540c0070440d010740714050110a00904051300c1114001c1e40020200181c0f007001d02003074840c0d0900902070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 839779451 1250 839778201 839778217
    0x11010e040c021b09131415070201050a24060e06070818030c0102160605131203020109050c101211070b1009060b0c06040b06041508030c06010905010503150910050103031106010605 79
    0x11703c0c0195254031002403000742007900203076501c07402e1045015a54a042110700c00e143c1a00002194a42640e0300c0c019610441c1101104035403203807108944a00c0c0c0c0350100140c03a00f505d4409412501c0402040240c0310b807041c003500103080425014041a002c1070080361140d401e80c107480d00f4400c014016a542c0040d411651290540d0900610280340300c0e5000c1e0460b401c4045d989494541d4900007480004038000c000c0d00140d440d01b0200080c00410006c04101c402d0940340300c2e0502070302c40002480d45080e59920044503807115242170b4a80040020b407400c0c550040309030b62650900d142080401c40700d921a05101ca0308043e00020210402000d481c4c07004000005005e043e81c40e95540c000080004110643c89035681c0413020a040c002c11500014000c43d10055603980340004085141c004140d0080c2803442c240f01c0140032540b0b01141c2d1042c070120a607591006521920702d80e50904075910038038040c00d803074240004141940900c0b0301101071303407040c283c8000d030f600e801044032240f141d204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 839780701 1250 839779451 839779471
    0x140a0507030609062a030e0c032802030313080f03030c030c13031502040e090d140a0507150c080906071d01120507051207050403020a0311010e040c021b09 68
    0x40c0c00c0021400e290404484644500030006a4041c00344221074280724071407031481d0141201c6614684207405110782a610020800200008600c190010356a019640f0310741d10900c2100e1404e03030607800002c2c2c007101e54607401016640c6902002c0500244a11a8451401623101b1103c0c0180c01460120440340620a40092649140c0e07440038002d03c143e000a4100b00b074000120000408520798001d19040070320305140142c4d03035514110040c2d9003080c010b00844006d0700800600107555810000a241c070464180700e0716250800d0400990f228000c4800250100807403000708000b08d00d140d400022620007030f0711100c1d215182c82d10203980d81c03001194040b020400d214600340c0d41204082c100e6241242c14501003101e080b00e22001c105075201607501101241010400c11034408602298039808092454030f542068503580009120240c54400079140d20459003488145911822000380b5840020700244040080e43c03030001e5885944441110300040c860b00130000c1481c002e88040d00a4440e92 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 839781951 1250 839780701 839780713
    0x60e03070c0f0e0a110c4303030c08300903090d150b0618030106080a031e0c0f050607090b07230c1e010e010804150906200403140a05 59
    0x451600c01403440f03441701175640005006580b0a0a0308120200c81e51030030140c204ca0103414402d07030f111045ca00026166690b0003400042103041d0800e0315440440390185040b00d040b100c03508018400744150801500c1c1c1040c085844068018610002c070404008070689110356a16088266200d005016009a110303c592101e034021a401e4401581d41c0100e03420300203000b041003800100d641e8041030049603110348440c03401da410318081c482c500003401c08402501384000960f40c0105a00304085c9140c80315008108850f88440c807407101103600d690b12400890000c509410641d0b960074080b65040005802d8620101c0d0f1071072035500b580c20240d801104c40c51402c0420340190343c0c0074450203400096100311300c21540300d070b42c85040307101501d0036990340c0003ca130040c8070006104404441c0d0036410300041300240400242c400040700d04a520001001444414a00d0180023400740040007110030305001d0201204180c41c400107000b16407080900d24140ae000440e41502c4803800d140191942d0004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 839783201 1250 839781951 839781961
    0xf020307021002160311041413031b0803090a0501051f0e091207081201050301290d0c08030a021605030c09250512130b01150903060e03070c0f0e 64
    0x195500503202e055500603244441e851107008007a100c0c05a0094600b007500b00c0c1c194134039040904c0ba80c012042d07040010181803070090140c1c8508140280028104150040c00ca8080c8111102d002c1040d54841c010a1f40d9040404103155078086104054855500c0e0902240c44c0305d01c0440a00c02c5407042c5050300190034540320120f0580030004012006600560080c0c410220100e402000b4280c8500d66058880d200c00d100f0352480c403816000b0a010340c0c0f4040601c041c0450007444420502050048081715a004001044040c044120010095042c00714081107291006c070240903000010360031034108064030f4900000000040c803c5070740607040a0342e105c034141030905070282d100301e18021160310440c6414840700d0000580004500084021580302d015011803036100b5007145500c0b0050340c0070b240a44801d008460180b0449811440403005410024001c40d075003401035411550410041090f40c02c000d48a070700c0600121518000d0210214424000560110a446035410506004e81d56 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 839784451 1250 839783201 839783209
    0x1090e041a151f0e011d13151d0105130209040e01020a0315182012010f1e1401020f161a190e040603080d1e0b06031b040e0c0a0f0f02030702 62
    0x1b00207a191200107140160300403601c41c40c1c0c82154400300010002094100d00c402072045107042c0d00000c01d407501a2001ca000c01c0c1841e5101c50540360112600c0ca14102e0400106c402071045d21890782d002400c01644820481040d0702918403a001c6440c140080c6125904416448646000f29130742000c110040c0301c50003100d54011444000b8004010300d400403116600b201c1c640002281e1216038901500501490301d00c0c081c2003004140d6401c4078012854120422842148103005900c400041c994405417568802c0280d0103048401c1c40c1500c0c50361860801000c0707a103600d8000c500240351254903c00e1145c0041c0121694140b50020943c5070910f40750040b2212008004170303650040d2034460102c003142c0210002c2800000445001800180306c0b00000d025503028540d081c00f10f460310280b014261110002c4907805001040d06025841071080004118012034010002100321a401c00051403a003400814041041c2c0d140c24448418060301120391000708280c000047c0c0041c0550302c01410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 839785701 1250 839784451 839784467
    0x71d060a0c08090a1a0406091410030c1b15231816060807020f071d0a14040b04030e1e0d061d0c0a0b0901090e041a151f0e01 55
    0x80c010f10402e8105d6031021010000051490024410480094200405e41d04882590300030301c00c0764070741106a140000042d404400d519000e00504d525402d4103040c580c410b1104842e034040403000224180300c170703061803a050080c00e009036003480e14214112300d50306c0032109565544540d440307202d0f04968176090399480098202940842c81d120764020301c00081038071084400508540d41e034803943c500e0300720002880c1c000b4108004040750000c90051068803000110b81d0820701c0d80c407040981903101c00c502c3c10004c01800d007808225010090a01c001c0004145000740110700075030b02c03000042c9000c0f0070007a03a840d002070000d1806136a80408042410040031030000301e4000d141c0090485208680100368441204003450b054002042c03030b61036440d29442c06c4024007040030510781001400c5002801446d0680210010008010001001c0101262101e50364012550382c410643c1001c40c200c140d88408101c90324818924400d400350100040c801d51404080300741d0f1201d200c00420001912074035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 839786951 1250 839785701 839785717
    0x4051003091e030e0109050a0b0f0c010c050901020d0e03060105090402030f0f0c030709050f0c070c08241e0a021c05010e040203010e030406080703150905071d060a0c08 74
    0x99194628000820010b50025119601d100b004490019840c07400418501001080354103100140300144080c0e154080300130140d07251514001d41d03e41c01410000a24019403000c00c0e20740d82490700c00350b00300c0d80c0507002c7e0a00d0f00c000e800721070344c2e10440901598480b2602009640540c404d4004026a140c004122500705002900b503820001ca0050090f0400003411a41003c0c0c9c0e000d00c014a1140c10108100c80090002c085c0c2000103041600c00f080c207503100903180904800020602000384a0700b107602d100103080d50411103003942d40d81e1340d082d80004544400d40c10b0225000000078090706840380c030b42d81031003452a98a2150f503121140300000f50480fa403100c00c0b080007030b540942102a944220b81c0170784500b003c0d21480d440e1610401d400d480720082d280c071175500180401c00040c1d8002d80314540014107810701281513071030282c800e011242c540d0300c0950701d241401300348902c498010b40e0030720741c141c0100c1082000c18648020b01c6070301c1c41041d141d24000741204c02c4070008a1144c00142c0548 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 839788201 1250 839786951 839786957
    0x705010801032f0415050907020f0606040b01050f030f06041b050a0c1704081b0109080a11061207033303030513050405070f0e01090b07150b1e0301060812040510 71
    0x488600404142100e40128050140000ca00010f010502d49010150f48c842017510060079080e0015400d81e80782c8a000d4411405642c0361140b0a01503800751003030b200c031003184040060b103920300001c03000c00c08001920300380c0c00760341f410b032403803641e000d00c075480d22322400654944501d00701407480300300c6107420510f030103640e54055044095090300b40c400040c4000d107800c0009040c041a4803440e80001d02c170400c00309042c81514281088403020111301c0b0030341c2c160006091045604444046102d0303105508414030202910300402541075099441f4422101501600c0c00880c46880308144c40c800341a000a074000f020b100d41000068800d0006040301140d4620304040700e40c1e2540403600341d450945091010482c0171050858141d0b03c2a941041d1800074a000c00109143c292013105604c02c0901c0540070a1040140f0031481e442a0041c90151101500c000700d0001c03202400b00080c1408003c003442035007084000642c018000580c0c000146000c41e05503d401d03e0641008500d001f0180b003030307044c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 839789451 1250 839788201 839788283
    0x50a14181f0201050604060f2106090b07020d0906050405060703030906060e060910030323070c03210306080c220501060c1202010218130b030307060c02070501080103 73
    0x25070746500201e22590600070300d25904440003298083c1c2942e80090041d40914a0400100b28207c411a10300c811558046c1e8603416900b0402600e020300700360300e41d010700b00d00d0822a04c482042180c00c1d84e00e11400340c1d5030076266252620041100e0030b6106215000016406100070300c01450400300070074180b0310034200025417490955405054540039841703035014009280030400b80d8104503a1030f42e40804250301c651211421658007030600081c04410050b0586504103e15400030203508031070480b504484080c031101d9a920340464049020201c225103d200178411007002030003401980161003008018003240003040302030241101012001d00700c1301881c11803455401c5000c0c8038246c040c0101e41c2e41c0c0c003c4c0c40c10318100000f2682102c5440d80c01c581c41004114a5a000b10a916601c4481110303507a0101c103900650380c0260010078481c661602000440c0c90420442e6441000e080034030f41c00360703010300b6030311001501c4989091001030440f022140c0004d03010181c100780340d541460001521b0f40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 839790701 1250 839789451 839789497
    0x30f0203120f060312070f060504060b18011a09150a05040b040906140a0e1503120a200c061c021b01020a08090610030204020f0c01050c1207050a14 65
    0x2078400010b6455008909204050100302e09007448180381290302c41c0b20881c0f40c0489540c400142c2c0b07200c040b0260207503a40318041820404d0700e41080048030700060001d42012138548a0111100c42807040340c07142c0d600c440104c40040880016102d503020003e00300a14060002c1d00b850865110110b01e02c1003250030403000c65000001006000038024110002803458240711034001051a02e01d859480303020500010002d00300554695a0301c082d100075411240041c21020030300d8482c106081c010401d90202d84080401e50221280364181c0d4002980c1581e1041786c8031454586241007146a0084003c11100420082c08288018007200c2811b00500e010031000480c3d02c0420740114116040e500024512941a0f0080c00c0da03400c160030034040c0c00a803d04804c810800e450600c030090189401241d50100308040c0780c00d640040300001c1c000d11280c58030500300d0115611012218010b003007444045404e982c855029100030365042c2c0c8502a103804e444641d103605401162803c00540e9442040b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 839791951 1250 839790701 839790727
    0x2d1b030106020601080d0503010323160b1201090605030d0f020c030a0f200303090d05010b090a061a0414010c050a15050a0b120d0f1413030c05041404030f0203 70
    0x50003841d069014114079410314030b04038207080ca00610b03141001400c3c401800440c04119407442e2040e0741c9100200310003803a0b412507003017140c00d251a007907030107a4040003e0243c054800515a211140c040a0240c0e030703e5a8220044640c02e00030590540c1c450200c20030b085024017210f43d02c0038801c1c012518002e070300e0800246000c06034041180c0303900228140000300f03d42e800c1d41082002c628101d012443d500140465a01d02504580900c02c20640029000707100081d4446c14494001410603035840c50f0190b90340d00a8025445150441740d00c00491058124101c3c0684041e00c102001014400c50a01c004540c98580c03200181c030580a180b83d10000a00c440394040001c0031521004162441c00020031070440d402048424095648400541c03a00100881c13a11000c02d50fa04003070080c21602e404c1110000f260083c0702580010008407003d03080c1002c103a0408072441420720401498480b03080c0402c0c0c0e408400200008178010020400003130061007600304011071841140d00300a0032003400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 839793201 1250 839791951 839791957
    0x10090909080702012d1b060f02070c050a03050c1504120501090203060a060e1311060c0a11040b090f1b0d0f14040f1e060f050604052d1b 60
    0x4551140c000a0b4000071540c02c003c1d084e41c1c41e00c0303c1100c000000c118000c0029910801500c410804c01c1ea00018001102c2e4955035624450300282c08200c150303c00c0d04038200940c814902a5612961000e0010342458480281c0040e01d5010000d0003503076450700c052100204080a8006411200744400300f65154142401c8150324003074000401c01840074014981814800f410390208941812405d1000441c6280f0068108840e511020403480c0b00d41040311652040c144d10f81c0c1d100740d0028003403210714030004164801c01d000e0410302080322034100800045603501d50b8043d4100b81c54100103541d460210201591050607600442c1040c02d00346041c441a50140c240c05010039515038a50044d0f206500c030301c10b07046200d00f0018000d410700da00c0700000c8020621000b80010240c400364003d0b11410040000740b181c1c03000e0140b04120815960f00c01809003141c1e028060303031814000643d050000301d132410207001c40c84031824107081d6041d14406018401030100c5550340b22640c50040e046282401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 839794451 1250 839793201 839793203
    0x11040905010f0b0303090102120705030702031603121b03180b04090e0f031e180306010e071b0309151403040807260a08041529060f030610090909 64
    0x4502515200b032204468100020600960050094011990300050b160b0910361014092503110102c0780b40441c170b18414050004e405009511502800d000d051a103841982c1c412441c1a4107200341c42c400b00ea0701540d52100d01c1355940f050100501207402a405405840015460f807091203458080a00b0242e00c5903025100d41d0380c6d59120001e48680500c40142d240040401840c03500c09000d40c507555144550300040100c040004420200940f12002218039000113400d48109680d148c1c0364408200301100d10703001140f40e00c1d419000f04c00b90500079600c29949901d60b4020141060000745504070089516001d2107007000c2e101c002c035449a80a5886135201d81c40150742d901091408031030120304240c2400d048005417101d29401d240740400e98500c5070251800c3d05040d030b200d0030100c44204178a04c998078a04d00e4400e6200e81d000781e2000c43c030a100440c401200c1c459401e07006100062060142892858130f081c40401c185103000300c80350031100304030302d4a2102182c842c0c442ea07080700c8031114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 839795701 1250 839794451 839794453
    0xb010803030910110f09120f10181203020d20040603060812030c0921010902040608120403110102120c01090b0c0301120f080c010c020c0906090c0d020711040905 71
    0x1c00c0002005080080c80070030a80100140142c080b104100320300d42c050f640400d1400b080108683c140e548580b038400d20705410000c11900280941c0100d1038a555100344007000642c24507c0e1246071201c08000d801070702d58498010700c0300003902003040f0000d40201551001d0980c41d109034200d00d2820f4200c10391011251104650b03a0341c60500e000d81100c0c0507a208541a4104920017243c0040700001d40768006080450542e8400300c400000e107661014428030003190212600c0000100c10550004580c2d501c00c5d1001c0103510348841030766503503505141d100085c032082040b0500003c0e010180d20480304106004655018004408880307103500000f40e0341c070301a9917600e0030780705011540b00f0054106c011140c2451555040060200317206060081c040c01c0c59400801c10410003c05108446000f03107100c000b0401c00b00e56941c002d4940590b992241c1c4180750001c04500140340c1924000e00418101645500e068424230f5104080e401c18102070740d07160360351001c0501940f5540682c07030b1410700c100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 839796951 1250 839795701 839795707
    0x8070308091305070903111f120b0f06072009010b071709060706020c120301090905070e13030f091505030a18080d180204020403240504030801050f010c0b010803 71
    0x241c20302508003030300500d003001c0d075062005110031550803c0048059a03044500c6941d61350b210700114481d003140842c4080d81152905144010640c403107224400c042a020052128076078071401c0019400358400184e030b20800800044000840c2e503640c100380c42108036139600c00c600d4000c00041400b4401d0b4000c0c41c00b00c2000804c1d01c10440c0380c00d946140e007109d20038410304111540c1c000c80d80170b024014004140b5075002880241080c4200102c000c05000241403036520340c1c4515140000e8400800b04640c0e62160f00782c08a040a00c0c030503524410060304c1003444807840d0316181210071071b410a0307512007071007840500803915a00307110b5151544c01f002d8035a140d8905089a0300412521740c0342c5c0c15012551004010000502c1000c00c40d42c01b4845090003007002a10026447c06400d0f080c02c009602605c002800420013030203111880c00c14007041c0807441071140c0b07010003009031402220000c0c001040c080040c003452601507500246c0c1101032401c0f0743d204a01e50ba84c030b0311070304080c1c000d800558008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 839798201 1250 839796951 839796967
    0x6081002030711010e0303040b25050a02152203140d0b0f030610090b22050403090b040f03030309110402030a050103020f010906020601120615030b100902030c090409020a08070308 79
    0x48024200c541e43da200081142119840b00c664a0b80400382000309140c607800701085945d181c0d1036489103501c10003800020410010000900603510206400d409402282d1100024641d1245454071407000003084080360254800140803c91281204400b806280040413203030a0844d0083c0c00b451000d00800180303c04082c04100781a1204603c0700d00c20383c0600104100e5224480000c03085440c04000032410380034003c00100311303464044c030714840b032681c000a482110009400690055000b526000700341a01c40c0d8401c40c0502c00c3e4052209003d802c0c107020400a88a07600c021015402240708031007402c80300c0001030070f0b640281c5600c1c0180b502d4800610540c80c0c10022031000304024203091541915180c03020392036550501c07880c240559441c4c02343c024411030750400c0f0203171000035600c02c0b01c10340c8038600f10a80103400d42d8100840340c4685800f00d45401a842124000c0e02c1d1000700505060020301044047c0c004c020301203800103441040051501401c0000320702640c400d2000989408039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 839799451 1250 839798201 839798207
    0x100b010207030b2a04051806030c0d03030212090307050a201c03090801150603090c0b220b160f0f060501260627120d0e0f0615040f060810020307 64
    0x201d9130b010800520030007041046641f604001e071404440310010410664640700020304141003c00d000c0d41140c0080008801c0582c10380c02000507001022030304d60301e51103c0000b10b6403801100d100a155600281907100400c0483c90803203000c103241c0c5005521a19003401007400c002c0c0c12501c4080000c45120303082c04242d00301040301d010303000c400d00070000c4002d40148031040900c581301c0d200505a4400080003845424030244018040b15158140d95040104240b44c81c0075000741541618404a00b01094a080500c200c40031003c2201c1100c510305103e855823018890384441c11070300005130702407810005009000c0c05000300b084c0c400d510801090f21a20030002c90070380070300460f5078000d8400c004128941e0130390940d11550b4101c08008007e0b00110f1645409000039051400b9200800c85440c2c2c1031a58000c4d80b0705401c0a410b540c04c400100410556502c000d568240e80b0f84e08001c1c83d54601d00340780d8060050f00e1007000300454a80e550341c0320582021a12038408407019000000c00002c150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 839800701 1250 839799451 839799511
    0xf04090903030f05061f1b1a070503070807080c07020a06020c0f1c030c0f060e010525120b061209011a1e0d020607020306070c050d0f02100b010207030b 67
    0x400c0f050205140140c0001c0c0c18581e4004812070211414065038800342c0300f8020802000c000c040d640e0701e070300010f0a0604007650500c1402803903040c50000545894860025a4000c0f036890711076881340e440713160302580e17090001403404a001e00306008100150b038a0310780a030010011030300a030001160220030f100b011303c1842e04c0d10b4000c00e4036404004070700d443e80c40343c4030459406207031014a5065600d841091200c80c00400342031681008006101355a0640c042d1340501c40e0b4000c03444003000700400300b00300f54518400710008184800b0a905006945030048024031030010103c0e8580211042c4609140e14144e440d000d00c2da5441e100d18000b050b01106404801c5d03c22509100140b40284044070b510307403600f880a00030301d0410000021500c841c400d45076803c0d40101a2641442d000c00300500402d207a00c415107980c440e40b121400400d0103402d4400011a02d0790107880e4a511440d420400b034000760203154114070580d20b0006c0400e800186407801403100400f81100e0407405009803460358 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 839801951 1250 839800701 839800721
    0x191e030e1c0903140111030f060102060123040c090801060308120c0c07120602040b0d0c080c090a050603041407061d063c39060606030406020f0409090303 68
    0x4240181a18055604032044008503503000c0d0b000040200900041e1740540500040540600004401e0043d0380d40c403050745620890080c1d00f242c1d51680d8440c01659406040c2c000e401815140711840f1070542025003280b9404c60f0715041100313106076a1941682141d20a9005941000002c5001701090b1803411915420030030000700d490610080801554030703014284100e0001d45030140000042110a4060700d0040048548076a10749214541c40d1000d04a515403030700c0010b040b00c000407204402d40003560804400a0301031070300c103804c01007402180d92001d407090310b818498540304119903904020080c00b03807402e40e031000c003070703401d2101c00c5c007031340c06109054138400c0106000c0d84a030068052a4544032030000a00c2d40440707200100c000348601a81c0c8001c03401c0b11300004054440394071029858000600c03241e034002e00d004503429414003040c03040041b4040350300400c010440c81d14001001c2c503001070181900501e0000548207910a03540980c5c09207920070b443d03140501c20f068042c13158480070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 839803201 1250 839801951 839801983
    0x30702160b190f0c021e03012307050901020a051b09130506150d050706022a06030f070909090b070809010c270503070e0619030305191e030e 62
    0xca00811060600e403402c42c076001c000c0010400c0700c3d00c002c5104412460000d81c015109081908000104103d600104d017400c07400396081c042d83d6030708920350841701075003c00b40914040c003940318800c0407a110381c170081d42103046100380c1e942000030801c20300c5000d90042c41c0c991744140c148a25014050b908000402c02c101c040c18420405000c6080440c100d503018550840084e140040b500014400440c0d48001519500c0f691101140303440d000501000410800c17031401101d104040850f1000c24045068183c1200d02071010456110803440400d800c00769500b032025500351200002000c840810100365002203010080c00031140d00040940e801401c50b400a008424980c0700280c8510503e240e100000c454405040307070400c0b00001e20f8006400001e090700d100e5503560359a00400d02c004e03200759114a0081d1118000ca4060711a544101d030303030549038181031644803c16040c40c1d0f44900c5500e024410909030302c144045a00403800214991600d00050855007010300c2c91412207004505040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 839804451 1250 839803201 839803207
    0x30e0c09100302150a08060d0819030b190f09090f02120d080a05240604170c100305090a0803060402090d05150105010219140304080106030507080c091e090a08030702160b 75
    0x10716a20905003540050251010b00d084403403442d208116114004064102243c2001c9040b0210781c9a08254ce5910007150384202c0000c2c42a05040c0c0b0540605c906100a007000c0402c110015003034220046440c0140005d00d0350310025000b0448100702c0507041000e5402103803485a00c0c90300300c0d030155000340400300100454605010300000034028038922014a803c0c2081c807069035941c02c803c440c050011a07204580070052003041c5903480003d48440c610980001c02010720452292054a11411400000706400c240c15110150b4a41c009030006810030340070030108403603880c0c440072801d08070b105000400452240b51000e000c0340506820540c110741004590a00b0b1a806e0303515134003265004800c19005501d00c6000034603500c6598072040b003950030000b001050000200b0040301712511070080d1450b09141e042000035010382282e151035007407507403803486080300718802606602a20500c02c4849a440549401100750000c8030100010f0b0302441c01c6204034040300000302c0007451440042c5003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 839805701 1250 839804451 839804467
    0xf0309080f07020d0c090603210f08150411090f1f0f02070509090c03060a27020d02030a1407061103180312040308040905061906030e0c0910030215 65
    0x8420301c20304401044041c80880c9040c150b685013070000905641c440716009055a0790150390000d05214072054464a010a202d06d002e1100400c0d885107800603541c80e2800d403002e9000aa0300180d029040d13400315041031150a10640301d1340304603114000515010340d00c819400c2d0030000d29414000c201c2d0700980090340d4403219a409000023400c0390442e42000d07220155a010100d252208650086a01940c58002e018840c00301040e251054074041d8282c030443d0303894000600a0725507181100009240600030201c40303a24004030310448038402030070071002000075000280f8050072124160f40d503614080745a20124000c200e0600245064148889040300710024280c581c01801440354a03840c41804481159a0503c5a00c50382013100c411151115180c3c184456550018091841c1c4c02d45010b010403010b00e0421105904841c40b507400c0d042141c2096411000380461640f0480c19100307182001c002951100f41451140145e10318001d03400d80745004010b4411a003011a5840c8101040411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 839806951 1250 839805701 839805713
    0x6010f080d090302090601031e0501090507090f030b0a021207090609080c06090d020d0c090f0605040501080a0f0c0801020703260103020a0e090a170a020c0a050607060b0402160f030f0309 82
    0x82d08498045418100f2580d9680040e0068a641c0f4038156000c92801c20064580803d40d02c000d05072010b01c40c0801c510394601900b6141c002140c040e401107181441c00c00c20015030724001b45076000c041c0c40c0c40942015261a140d051000040e90410003080d8204000e114040d84040c016005007181801840700c11440004903003148a00380304503015100380340489055445100758807141c29441941d402603550344403c1d0200408142c650707a46003900f40f45002900d45403901071141a01e101c07a000d00381800f0950348055166005040495943d040c2450000d0308240170710280088901946030860b800b400661500c28101c546510101c075a02c6080040c030150b00e4098016060b65152501d8200c545c64541c1140c0c40c10500b4078000f403403082400b01c00c41c5500c4011001d01720895840c0c08881c801d44800041001c0003c207030050700e4200c0d0007030124901092403070b0000c800e450380282c4018170b07040e4851154100411281025280824205104000c050b40602c1c10314241c103452904004503401942c8039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 839808201 1250 839806951 839806967
    0x90a090b1f0512250e1003020f091302120c0108100f0b0a1e09050319151d150906070302030c0f03091906050117160302090c160506010f080d 62
    0x3800707580c12400d00e5600300070130001041007081e191410291038200d000311a100d5441401402c80e080d030300c8000b140381d03120000c14130070569500514420540b1903120500904e100000d20f02001030f8103295000002da00c1d50040c001140c0100005001c0b420901000540f444e1406880704d50104644103007000500892141201620300c03180402c1d90b03034070a20008542100402402c500c0c1c0400c0000480c92881c1c208254808031403068041d10b4481c0d100c0c1c8040c10701083d2050000d480450004d05001d2895030350340c041e030301d90f01ca8840b04441c0c4240d40640940f4000510341646030742500c1d00c0502c40204810001554029400c0c43d081d441c6291015045441d4040c0d0418a0007a00001c40852101d00007844060101501c18102039040c2000d410000007910080c881d080f0322440580182c20901c602240c1100b0a0b01c0660500c50403a01d1a030a20007040b4008002c010a401c052190000311f40030900b407901c2031402100200840d50501c0b000100b0025140d00903201c0303038003601c04103c400d82c104600e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 839809451 1250 839808201 839808209
    0xc0503040521130f0609120c090e01091a0a1b0c0201030908090904110108060f06030f06030304051201020706060f050d1101030b100804060b180f15090a090b1f 70
    0x510700075110001c503500c21038060341200806410744410045265040520240202c0e031860380c415208690f100e040e019041d0380303410040e01c00e01000320b09009504807600012b0041030700c50000074070b0107056254480111a002501e0b41404030090900ca00c1c207409000301c4c60104480f84156800401844001c1c0100d8403040000303060549072041c0c41c092240041c196401b054026028010501e007500c1c01c86601041101414045074103000803070440c2c00c049070300000c12100948043c2c42c0d0b0702c0341c0304404541c0c030008204039854030082101040c9520381d5081e40030182c804c00c001680324101d03468000240c5146400040d000b9120b80c030100099550300c400c032080b1341c3d00241204410b01c0c01c0302c012405000c800c1002c5070030402031440c8002440e80079040a00ca14090401000840c0d401001c12144021801400c0300b0604044082600c500d00180d601e0780040300081010034601884e000720341088412554004217a50380c080400a2044001903150700120545505602c0521401c1d0b40c5d00054032809 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 839810701 1250 839809451 839809483
    0x403080709030f03110d0206010609120c0b0a0521160302070302010b0a0b0d0e061006051303020d060b010318050327031006150c0b01051c0b16030c05030405 69
    0x114420314001d11030903000d143c0108156042c0600d03400d02a008541d203001051031842003007111559640301248103816201c0c556100700042d07151412000d03002850200c103846210f5444000242c0e03d04002c0203120803015916010740740d54190000415104407016441446086c007010440090340c0c01113000907244850500607183d448a0404900408081c1e0000d81c10404401010803042e9900b0702806107680d0180050000440400500c0d840e000d05890303056403d072810906010503401750016141c1e40700b02ca0314403400d860341c940001c0c00464550405070703041d5907106036441c01941d0500858020304860a0308040030003003a65a1543c0b44603080407061070030030320b580c4c43c000f018a0743c002c0354170010700604541854941140550050540b84241c030384500c4242e0032500094010200714070029003004040009031f1a110510441c4010451074240341d4120f50702940001c1c140d02c0009011318807844550100416488010702210b00e01c4a0110038054280104400030381c002450010091541e9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 839811951 1250 839810701 839810717
    0x5100509011806020c190c05270a090b0609250201020909040c17070e0f150301021902060c130302060a05090307060e130204080c010c0c0b0c06041b06080403 69
    0x1034459004091148940740030140c052481420701000d81c01070034110140380e055a2000b2030580382d0301e1000c0c90106000740a0b0400d903404004510300601c041001130415020a003074010000c2152903000c90071070792862290350307406a4500b40001c2900c11940f0000c1601c1d520228200000000c1d500110300c548040d07010450700c2121000c0d4801c0d015103101402c080d00c000a85d042514040c030900042d4040c0040382e1215162a280c030550004440c01101c000103903511040c0c803100c1e203400a049004082c051030703100000800b21151024401010f010000c0300c0401001400800c009052410280264510700d805001001070029680e200f0801c40c0d80c115449541d90f81c2110084d0f84600444000aa241c011100005115038004a0301da464510407100c804019083c200850101d00860003212955070220f120754405500665200f0b4003980134014545043d940c505031011154000500e20406801c80024001080b0a100d100d50000c10300745108a40309003003240003041c610000700086c1c2040540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 839813201 1250 839811951 839811961
    0xb09012d15090908030f0603031e09010903172205060405060d091e0303060b0310060e310e0307020f090406021e090909012f0f0406020105011502010504051005 70
    0x280310100014001a00240503d180d6410800343c107030800c48602c0d00aa14100020b01d0303520300031084036058042c03020000c10300c540c828080c42d00c98000c90241814444054000300108045101142440764240000b60740c4a042e012105401c00b000c4682000300391003240c050119030744850990f01a942c050742d489850322a80d409140203020b22140180c900d410030480540301c140c001000041c903500984061240b15910368814442c0e1004039403040e481e51142c04144100c9100700d01040c554800100300d0489961507407290401c020240c4120104006107e007070381c20405c12401011640a807a101440c2400b11302e03001f01b81d018170b9042d00c3e0b030f103e5a607090001d02000701e140e05850407294402c407012144400e01c800960030390b11003182c0c10310490601c400160401e40500801c4044050002c0814403a14004080403042d80c039503541088450b024840a50101c04031341c00760000b030000354008220f03549007003c1d46442040c1800608216410602000003003280007840310006480340c08002070039565 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 839814451 1250 839813201 839813231
    0x7030b0d11300f070605040e180a0615060225060302031f1413020705120c12030a1d0f070506070c05060705061008010b1806010306120b09012d 63
    0x70582c0212035041062070445400c0c0c030000700c81160b48004021210340580b1802c042c0d80038015485440341e094000d8001606144011010804040300d150807900f03408103556513903040c1e498148001580b070504003420044a9410009107010090f104900142030b01c0e00074450b040c01c01076000f10802d0540000114000c6503940f00c031b160141040700d9800c84026244c0b05606880c3d54a0f20f580f510a60303400d0000c000c1d480c118800c50750900d074440010009403a44840c04130154101817000b200386d00030500261424520a80114882c1c03100b940d0000d20600d190740300d141c41e034110b4010060304d80e104e00c8005400040002c7d1074815103008540d8140c86440341e14026140158a0304401c3d008a40030a01408001d07000070424000d854124200c6152921008610b003207440e0140442d510040b1810030480141da00c40215400880601d004103003251200c41c0041611003403042190101129001c02c0a103000038821100c64401d070464000e818810310b0b12040419241300480300a6641c0e40082c0849485 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 839815701 1250 839814451 839814499
    0x60b030c2809080114090c0f040b180118021921090308070906020f1b060c0d0807031406150306040e010c180f0e01210c03080307030b0d11 61
    0x9400704150103a4207030201e004004080a106009244d8281222003000c0c520481525109000b40306c0200000d0701c02804100b0314540380400150402d541e2001003d180d20380401c11040207200440d1980c1c40d500d48420008210b0004001139101d40c8140b145100e850150860140955102d180c11100e1500300200d00c003110344140c4580224178a0510424201500114000d21500700342c0c48690982d45d4584081e40c56854400e820002030b00194000ba130b01007610174816030400c0001d040242003528101200d80341014025a210204601c1c10400c0440e5505000340003c80001040c214180e06200e00030841002003001c4c541c0c0300c0400880010503d45680d440742d80c010800b81d0081c0503014078a20701805403000044400c902c90f290b034402044001c0000194003c031141d4600c2c24409a00e4803046101e48045240340a21140c50100c1c0c80c03010962001807040a1400f440c0050b80d281030080004d03003212000301e0340314002c4107440c5a40380410541841c0142c5007100f03880e958800070030501c0101c0d05c04c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 839816951 1250 839815701 839815747
    0x3010317040b031311010c02030304170705040204030c030c06110c0d0f0c1514120105061e0a05030106080906240a2105070602060f0601030b010c120e09060103060b030c 74
    0x58404400c022925000800513030006026150069100420700c00440f82086040c03c06905944200003c0007404007901d1003104802c40310055560682e10391000800b031703900c03541c030a0f070303401004c1c01d000e00a114110490000800003800c007100c2c410400e8140603281e195144400d0711806000d0022030a103c0c0d0503c8100a15034008181340f101034580c902d07075201c0c0c13140c00b80d00e50004450440000d9014440c104541e0356900038003240556a10300000c00c04980e0044880481681c03003011a02c407102c851002400c424030058075501e841e581403030001405201e00500c41410781c0c5c080011302108280c040d0b00050700d030140000801c11003641c01c0210307860740080c0d07002842d02c1e041f111444ca032012241ca0190402d6100c3c10a48040e01ea80b110100c2c0da078041650b00400da1082c80000c00c02c998080d9200381c0f001030042c100041c0c40d15180c1c0f10040081807034000240400d1070304841c140c2c18588114495808602420100022410241d0030411800000d000742144000042c100c6080400501064000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 839818201 1250 839816951 839816969
    0x603041a10051306061b050a110d08120a150303082a041706160f081b0a050706060b0f0703080c040e0c1c140f0a06050a060302130f03080301031704 65
    0x1159100d6109000300020f20811300011380c46e01c002ea01009046c08682c0303444d60000000c261900107911110541000003100700c0d40801c01d0710303a010014502030081c0450401c000e04412103440c0052003082a181e10400c0b040640c01191012300009422030105508170a46447d4800b80f582c0001140200350a103809003045600085400074209900343c404240c1c03031100c04d0a0f80c01548541c0d101100d04138015811001003a11405c0c041c016038031401e22168803a82c100101c05c02050340c000c6103c02030740440300300800240b0010741c0ba0188040c81c01400e00030150140703814502004030412229901990780000c04100525021400c03010524041e1805404200f448690b60b091105444219038071403440110b08410904c01d40c2c4c040c651a01c52100c038250440d43d443d9042d6207600c034507246010014030801d211551580e020500d51502c4e82a140070300901d03140140e40c0c1e800e40082c022100340c9544008140081000d09000184004003540e0459a1000307940f0040b040003040b031250b074000c2d0b070090214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 839819451 1250 839818201 839818219
    0x3020a0e19031a0c0f0a020a0b010905040b1b04060e0d1703010314120f0a021e0c0316140d030c1e0b010914040816020a030804060207050603041a1005 66
    0x1032070081444000c22607200b0042c10342003030160124050b1555007110018041c1e0824440005a5005480141148a224810340e05040c095955030001d00703000f81c04ca18003281c0d07908100300c200140c0c2c02100390000c510307140180182c0303a02100e05019214501035030741000001480c40c3c1d03c2d600e82c0c1c0800c00c0c246038000400001060a980c141c06036400c24131050781e00c0007449031103510850000c03810103250218035a0040c0b40c002440c103402a99401644500708501c141884800e500c0300c01014103507071201c0c800180507440c0d10001094a40040000c40f90180d0404100411444090001552070240281ca1800d091200780c20155800300f030210300507200442c0345000d00c104606402103011090710929100e90183d8841c0b540408403442ca900c0c14407100c0d00f0784c011801044080020b0b0401e603015a01968800c0c2041e0b000c1101001c466204440b0150081000e104803901130042a0187c001600c640f815883d02d51a49500a040c807101000500e000b08003103440c0000c5826407001429010307289d800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 839820701 1250 839819451 839819479
    0x1b03020a03050f061803190c0807031e11070e270f0d03050c09011202040f08011413030c080d0209090702030a02070f140f0604120f050f06010b040603020a0e 69
    0x1495000c0d0f211241e1081c0a11030001d0b00c3c404c410a0400d0b50f1100000041d07061a4400c0d250385402d6a80d0710300c0d1414410740321803c0c03001030401c100a00c01c86100b0f5540e0380358001c3c46e01410510400c6100380c08103100c0d400a614200c5000080c400c000c95401c41e00c1401d40da103606030342c0ba80c498003c5064200140e0100c0840c40f0040b0005200244103100c18100c1c0c01b050003c100450172601d059412029801c1c040021540c250700c03503480d5010805401c1c40052400c0e5844c5000034241c01f0781d038400700b40e03a5101c0c0c02041070401100c0700641d1000d10010821004071055900408190847c00300405409011580c07030b01c104110b6050f41c26100f400703010180141003c1d0f00195030727a000200101c00512506102182402001708000121907002d50f02d108040500410801d40e80c0d59000c0040d0042c0040c000011180410b01800201500815001d803010f400c0381000ca041085a10040307185a100318010015001d43c1c10464046906502c2e005884183c0302c0c50441c2d00c0b884408048c1c1d48000103d800346 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 839821951 1250 839820701 839820703
    0xb0d060b1203070b22030906110c0405070903060b030c010906051c050103141e0304090f02070b0f010503060106210506030c0a0e0a150b04030201050c030d230108060f041b03020a0305 80
    0x390042020507004031800380800b0140710705d0307003001800400142420100704400e500070b1101555a01d48074017034852481d0786201150480d40101d0b030f50400501c1251040040c40414072030550040410b60180558882e4200060880e250520441d410032400207065140071564407002944002d51000a103c1c40d40d413800c044101040a50707001e12280a591410010300141d440c0c5030f02c0f0104404084d50415103482e000710f004000c0040c90802640c0c007040450f00050f200d05007075104c1c000101071100b0550504040c580341c240705810400c1400b80c03001580700e01c500e4420000d1a10080210301050740d6035900c020130304185041400982014081c600412200740ba440e51038801d0407054800c011800803201200c0d1100c1c4070f440f07030b41f1220708200010b0015502c240f005180d1385410201320380c80c14040b01c0b0000c085681302c408030708061a21564000140c41c184828900426a2034003c110034103080c0a11102804041d20040203810200040c7c24034800c08100c0000035900280300e07524203680c81c1001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 839823201 1250 839821951 839821973
    0x70507060e031204020f030f030301090608240408090d08070f05060601180e0a111c0b011d0d02010905061201080c240c0307060c1101050a0b0d060b120307 68
    0x32141541001d01c1144006000001d03203042840e030303101c42150f03500c9039024410015200c004e6240c0500420520404003402040110f0003407550140004d0380520b4030041e81d0410724100c030b00c850b50714895040049a00544d950903a042500070071400d44c0c40c410b22000a00310215188010420b00c4082080d00610041c03c100911a0b405101942c0c0c0658039080110391000d4040d40d2205103010403001030084400211125030b01285042c00001c517580242507030011a00300c0304450340b00b954a004403001e83e200901070803211183c05c0c20494154400803501c0400d44086d0f0781c0250041c030324a007000d415a845029102d000f041f01600d161b83e0b17114500000900c000003401105564030841d601c8244070300304603c940c01400c010580714090011000164420713a03000c04141107541c4014884280422814483c0c0e900550541c1ca506540801601c0402e00b0f50f8801011056481e150546090454640f20b049140c4103600640020300e408040000451403207003140d000d4200c3c80042184010030000740c0d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 839824451 1250 839823201 839823203
    0xa0e0d060603080d0f1b123c140109090f120504030606080a03021f2a02060907080c011206090204030c0e152b12030c1b05030301031b0e070507 63
    0x1050005c8210101c800c1e003a1409140140c0f0800c104c2c1d800640501d2260310100d41103003070400003190032840d00c050300b40c04a20328450780c0c0310070400c030f80700400340c1c158251100c10141668030103105400340503142c1041001c051042c101c3d020744504140c410490002061265030741c1c01403600501c4003030500f0040454216010880300b042c5800c1012403607400007d00e03420300b1a070550041c80c5003460320b035405003d09007014034030141ca038641c0d002503894030702c210480004410911411100c0010644000e15001014009e9050b581003c41b040c8820400810280320800003801c0c00c0920861254089005086550042c1c0200c2c0c400319021041001c0c214600c42116041d00a01d0310035200c0d6607415040c582101d0031a1340c000d80715001903a480b421103441b0401c0707944c109147c08031503409440c2c0e04012840740701c0980000380e032900308056042e0131140352030200700c10300381400b448082c9c2d42e42d283da04e10042c0800b500169068050446810080003c5000342141c900801c2c92828139045c098120307004618 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 839825701 1250 839824451 839824477
    0x3010501090506031308070c170307350a0512091c05040617060a180f110937060201060617063001180b1b0a0e0d06060308 54
    0x2002d1070010140d034060440e40310071000e01005e03076548019030380c025003007152821a000d6002a06c94444400502e0f40c203190000313503981d95103a180c007020070f4002d1446003000500502115050000d009560228505122640c5584d858007407070613103807405401401d4103040f114804000d85154086000d180752000c00020003010191490140c40780d00843c0910b80c002001e020044103d82e0400c4a0f003600590041c00401450f5250182c8007080c010100d0210501501c4084590810b0024032a402c000c1071200291810030f42e0580c00140e0104c01d030200501200000c0d0950b04c2128144032400503041403041c0000c1503155680b6019000e070090b8400c01000c10b40d801c5511100f5188141400e00c40c0360020519021007208084603480c40c1d8041d8191800c41182607440042c03500d09115170b038035000308040e101c614080140341c0040500002010485001c0c520310180c8201090035098236220f00090402d04001410100426045260b034400a44805d0030a40b000091045200c020182100014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 839826951 1250 839825701 839825717
    0x131b09090c080c07060c0905130509280b0402150a020d121e0905121305090603012304080f040b0307030e0f0319051902012403021509031c0503010501 66
    0x3200507030b10800119410302200504000d0b0a00141040d400700603141c905082ca0140d481e1500c02103030465003003200d0a00d03030a42c0c420500040c0e0004000300c009582d18610391151501000034010050840c602d07004140f182074801143c01c656803641350400452100c2412a2103900da00c0c0001e40d100314100104010030f43e09001c2c000743e6645070150100241c440c000c0b04006035622203083c0024100d110060303601d0300a0380b410703108000426008003140c20404c0e0480300350500300301c100075240e080070749070901c00e1b031408200c2080c2c007001c807075028000b811302c0c20071042d140d58a0600348110b00c500034140003000c40008000c17600401103006140581c2e1355503410040e11070440300c2e40b0359503100302052803000da0041c40038003000e412001c0b5800660019140103030034214541107104e041c0c03001c240802c0142c2d45460403030b1400d00400040c000d04104034811490010300d550013082e40e4801c0480800b2924000007020041c94904100d100000c00d01140256250b51540e10000e1480d0428010309000030317110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 839828201 1250 839826951 839826971
    0x50d060603080c01051608010b04060c030302130b04061218111f0507030915141e0f0301051c111e060313050f010c0e090601020c030a0b041a0114131b0909 68
    0x1c0ca80440c1600d08018215251a0400006840c40c0c0c013301801c408058007000044e1200c0c4011409000404c80c2c1c41100f07807103e080c92800740410074500000c1d030401d85031250407544000e9061b1070b0384680390002d10950b6258148030118508544148190188240b120100221164004000e142040c080da03112008a51625804502c005203200d80c00001512007140765048001c403001081405500806000c00701d48450810503503404c141c01d10444500080010405424603024401c2040040c5410041c0703503503150b0381d2007802d00640d80d5040c000c0000400290980d08081004008960010706442c0c9074070f840d07484085c80c904200c1044a060040824020300024140a40c01314811941c541201030301300142480b51400c03000702441c0c118800d14101207000c0e01d0500c030800480d4010a06001c040c44c190400403404048014205448521000100401d50380c42c40a18003515084504410704152a559500980b03181c051490211040b4849640e0300d6400816880440b140c0d40340921100c895 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 839829451 1250 839828201 839828207
    0x3031c05010b09100806040e1002220b120601200a030207150e0d0c1508070e0f0105251709041508070522151706070504050d060603080c010516 63
    0x10f01820140c12510502c0302c404400c0c0280780e0640d02510152000078801d01e1210410b14003440c0c0010443c0c15940012422003051102c41701c0c0b0001d1420400400403140341c0012081544201400344000030020804586981c0c8903108a500d200f42d5621040000a041003019840e0071500d0700440141c031441c100000c0030903568060381041c91194031440c030500d071a9000c0c8018001700400456800201f100082800b05009c000c40640680903943c007203851400c1c01c80034151458810380580700e403005185c03006c0c0c5680e0120484a01035983d4482e8440d070001071030080c5104804400050288002004003080318032050007818a58408039000d100500b0b02c600c9031156402103005414440c2c000c40414455802c02c10b00804d180ca8075a0988001c00920f05400f0f81102d2032108129103d0080d618104013032117071492a0303010140c00802614050902907070240c00d138412842840c3c0a50311020000c001c0c4045640048000c580101400ba0340344050f0b8001340c001d007000c540444002007005085a50288 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 839830701 1250 839829451 839829457
    0x80a180819090f05060d1112180303012402031b011b170a020a1b062019031a130b090c03130305180d1410020f070611040503031c05010b 60
    0x1000140e0b820050a0030140301c8982d12804410f541651500b03001000c403440e280c010500c130b09040c840c0c0456403e10b020600310181d0080127010a643c02440140806a84605803052203000192034110600280c4e0003a821402640c641450b028407404803800445010740041e807815142081401903c2c8001500381d40c0500754001c0a040e811100c8001000598194010020075900c0d0500314140e031440c88807101d4041d04588125141c1d40c0b80c051005815002e019020385803c00c00850030700b00340c3c41e5010b000f01080c0501600d001c06d500c88035140c00e1034014181040c00100042c0ca00c5038102c4017900544050010031300c80b907009600c4100018100071000d82500d001d0705400030000e101425a8034100c03404e8101c900c006076000d146c5101c60080f0354841c2d031000140c0d80300b10860013001048140c102c2c01d28012400039401c0600401c64101d403443d0440031100e14581c0000000b41609040302c41112900031030308015050303c07000680b11101c500051030802001e191310f00900071750381c07118845a0240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 839831951 1250 839830701 839830709
    0x31e0c02070f0b090904050106120503120f09030a08070909020a03051b0406270e070e0f0102060106090509190203070519090b040501030207050a05011a19080607080a18081909 77
    0x703c0e0038002c400c202d182c450505034000f4011400440c0d52621000500801102c0038400c0350554000100a00c500c075440c4440c50f403004100c0c0407216186804043c480c0c891040045400c10841c9070000695020300901600d400307400d030070308119120f0200641c05002008140d070b41c1d4a1010122081d40d09180055044074150741705966041440401801c03d46241c0c21012421241100641804148075050409013441440e10355900e0750384051450500a5079640c4150315030454116600603c903040d00f04003000200ca100783c802084a941d042d1443d00c0d90141c0b401050790090001080c0152254000054024200c00710011602d069010b20b0a507840b4051b442500c100900c01c0c0303c10012903002c1c1d4003921241340210306440b0401166960300c0e00316501903450060000e400c441c00551400c0040d0003001284005842c402c031103007040240c1ea6180c200070400b00411840300e0002e0919421074110400c0e018510010204000741482c100d1041d820026408451509501030151018031514050f0704032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 839833201 1250 839831951 839831969
    0x3160e0d020619091809060b0108010e0601050901050c010204080a0b09070312110c1002010f060509041e0212060903040608091c12060302180f0106052107031e0c02070f 74
    0x400010350260a042d565100307060240040d080c00010301001c05c840100301c2000381e10300001d200b403483c6000300484e00b04840c4941000300c0c10005000341c40c0e1240000750004000d090160f01c4085480048030300c1d20036141040a60750000c41c00140800c40010384050140c428030590306944c1e5400100395440409100240242030144442d211550050039402e6401843d5030581c0c40b4400194041407981c56004040030050390f50310740c085070344200e601c5114007401c0100c0e00304070641050f0300c0e440c1013080c030b030b01004941940b20041041107544282010b104001400d00307560791441d004903c0b548a803c103200d08008540e51350300040c1c40d40e00104842e4005c414140642080c022482c10407510040c2498a00a42950303900c004000b50741e07401080002ca101c20040d0704000e144c8610302195141040c3d2000040c0101071084140b1b4032403c0c00d0348900c0c0b0046d903074401901d960311501240505403104003142c102e4008816a031041006400c40d000c440f04036000c4800380c40d83c400e8000c0703801c070761807050200c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 839834451 1250 839833201 839833207
    0x50d0f140d05070c0503121006111c0507050d03020d180f110604090f05150a03081c0b100507030806120703080d0b0a24030515220203160e0d0206 64
    0x50000c2d40c42180c00400e24079010508200e2599000d1035540812044000041100700b00111888681c1c0c03010090501803070b0000400000c908543c0c1da0300d0078100c0030a0000b0144002c000000d1048043d83c031000d03040000c950041c441d54101400960004401306042428502950001c0e4010210740c1c0c4c09a5100c1d000751080600c0e80c4518519210140300a60700c1501004001020000ca0146101c0030340f6405c00090a8200110056074024141100c94001e002042003040811310100c02d84034400710b07d4940c88a0811040b2002d80200303681641036034442e40d103e115403011580316010b06515407281d250700c62a51280c80030481c4891210743d4444256001d604180b00060403038003c1e080717045540d10003048414102c000a6050306007a04601555a503c1d426000e45148001c4805142502d5045c1000241000d4151041d082c0300910303aa4025505000794844e141050b21820800c0c105440e000c54032401e144c0140c021140030071000f1800122801914001440c20000c04034049a0041400345 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 839835701 1250 839834451 839834467
    0x1306060b0d06090221180609070e0a05090d05030705040308030703092310020901020f01050106051e1206010509010c02090408090f01030b06180a120302011b050901122403050d0f14 79
    0x400e05900905c100054000c0c46c10003103080c2d008014090040d041750014001c21424091480f5420a0090643c10200d04010501c0541d071408154a8001d01003440e0041d52540c8078602902c561081c0d03032008080000000070840e0860b8144d10a02006201e200c003a4182d900002881c800c02d00410441c48480e08400580d401c9140385600818800c201801501e950643c0c400c1c45508603602607006c0c1d0049040010042d00d950800c1e0070800c00882d1410704c0c02e0030141c81000c40c1081c1c0c00f0060070b00d4107210b800035015000303078010384090b400303260300501400301880e140c681031b00240c1103000c0d2a40509040100e1500c030b5070290140208880010348240e00700407260075401c059031281039080360001036100000c900c080240076000340c882d010381c0020540d030b4080d88602c00b1034009070000c0802c000341401515880c1e0713400385440b0086481000c1c046041c08421000700c0008010400480150a07200d42c00400c10038082641c0d0080f1400e6111041d01040c0a801603c040341d440c503a02c2c80040f03040008007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 839836951 1250 839835701 839835757
    0x90b010b03150a03060c08070804030c08130e1302010216030f11041e020a0815010e1318061a0102011806020c07030209090606030c12030a081306060b0d060902 70
    0x190b00400c144501d5001c0ca62036000300e2082c80650304250341c0c03d900c50010f140042e8000801c10780009075031600f1000b6240a0b24001c0c000d050380d0800906400d000030704480d514101510300005094040c4e0407200c60b003841c0d90f1600d945680940120301501540010a001c6240c03400c000c3d080320f412100703001520701199074240d50380e159450043c2d849a501c800e0502800036031151104602006200142c0e60300c0c007141e0103000008002d283c400201d1848907000042c3c3d074090126140301a05407500340e00709070501081005009074200032000181a15408028411680c01c07072000481d107261010402c0794940c00490a84074000d2104145842c28000d0a0000740d9a0f03005001c003040f00c205440c46507071aa40040c0340000181c60b05217855000c0c0061000910703080c480703010f0707600048031030400040e2203121254a0740214180d030030502a200f000965400090400c01c0070107a4400700801c0407a440e19403030300440d04949260340541e40380683c0071410941074800c0300e089050603480541d610b03170b8110001d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 839838201 1250 839836951 839836957
    0x601211d031801050c2e0605060a2a2001090b0306090718180504060506010f08070c030e1804050f010207050a062f09010e030102090901150215190e01090b010b 70
    0x11000e07500c105000210940b6a40c07082d550303000905074160035904442c1840381c080c0c6003680c010700d00c1040704004ac241100e811181c1c84110b421000b2904581708040184015403c0d1107102c060702c3c401068044060040c65505104050032090700c4020600362510743e50380342030008440300ca420040b40740104544174001c8083e06d00d0b844101302168035540d262048c04600c25404099400f0068a0700140001c10aa0707000d065030115080c40c100040f00311051004041c8070015114800b40070410300504145031140c0c0c0258444400500300940442c4450145e400c03000080350165810b025071421415a101c040c0204c81850390480020607141c3d02503200c403002803019180c0d80d400600003100c101817000072256032104090750101600d4440803090005000c01340b42c00d40d0300703101e41d2040115003202d9660040d0039054650681e0307016104001b9560030b034507069580c982d80284000c218100581044c88000c6c0c070002e81c1c52030f1002d000d5420b841542310f00360b079100b6100800c3c5480c10704c018000c800002c03001d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 839839451 1250 839838201 839838217
    0xb03150c0706020c0705040c1d04050a0609020309030a0e010809151503100608070f0b030c1617040911090306040b0a180b2d0109050601211d03180105 66
    0x500c80c03400d019030ba40d1030704a0340300f0410005242c100903404c12440c60f040c41010183c901500342007450042c031400405c420200c0c6182c4600c500d6a8a000c60000c2030164401c4020b007609400440d80e9041441e40f5941e640c02c0031141000044919220781c0b044d5100d035103402d002e43d08890040c4550b140c41d60b051107110500078003030300c004002003444504d60341d0304004c401e1202040381800254181000c16560501269401800c00c205403041c00b00301d003410700380840c0d42c400f03418040a5142d078400c3c6422580c40c0300b003602c0600710007403d8500314200e0b0481e000900464003c0300b000c201c1244102c40d441c0d164003c0c208000c0c1c0c55080400003c02041ea02c502084e40708004c05030000e191403111350000440b0500074000d9421200d007078200f180301c0384040180c803092910100c0c48400c000100030361030808081409101d8059840b034021811a0b405036084207180d03941c01c074100440c12461610800103022941a00d0880603a151040c4501c2401008807107480038586a050354500c0800c00540e625480512 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 839840701 1250 839839451 839839471
    0x1d06061204030e01110102090109120f020405070801150801050117090f1603030315030507060c0f06021c2009300d020609030c030304020d03050c07060206190b0315 72
    0xd8004900380d11407095100e030311840010501c03d40014040c5003480b8044409038410081d04026030703008046403040300d44060180c0500c94140c40e020f1048101200f00070b400c142008248018242c10590031410f940080d54036407600e4080080803a000348003885400d0114042080c4c040e40c106c140905036501c4002041100d5542440c20640c626200000007490716004108500b48101a41400f40e0f041c0c2140800c4507103092415916642c1e00c0314014403815051182d0700c00802c0800ca2807079200030031103810140440d02c81401084036103129120140d210902d615180f803111200c1d122188a001070341c240300442c0c2c01d00c1240c20234404d00d00b810319880f801c0c8814003c45040510100c004411808144002034070082009210207807801c10013811002207a08284020b025490b0000103481e800780e01101d482d039468040b82415209481401c0201c0305e58081c603140440c0c015000510140101d850038100000a480880d40f0b60882d001501d81603419004421412010307440010110342211442c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 839841951 1250 839840701 839840707
    0x80421020d060c030e0a080409090c1703210f061509040509030d0c02070b030a1806020c2503110904020f1003090b01050108011409070201020412111302041d0606 71
    0x90009541c669081400710341c1161101411500e4640c1400364800c203155400c0100031503800d0f5070f2503413810300403801141c8006988416403018015034040f0f41c401004014600700300003005402b840d071298813841841d200c010043d00400185140107005620035504040b8140c0607403145020400c08810204600500c1e4100f4012507015039a03c1c0b00f141d01440169005542e2810125a5442524101c0a400d4159004140c0400c40201040210383c0c2c0040400e0740060560a000d901c00c00c40e10303c80704007400e0300c0c3c4040b038600b00801002a0012140b0009000d0f445044402a1007600350b0380d546c0801844035142c3c0c150b140e064203040803007a0b0042c0c03000b0b21010356002420045542d0b540c0c01658440003c0c1c0342c052540c00d01c1b016518040c00744c242032802110075810003083c054540b4410b84600e014030b25280000e10702901c04e60544000c0c040b0051010180121400c1490003221425200b070f104848186d0715000d0710055101b1202101d0000d0740c15290402051002c02100710003c181e030b60081410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 839843201 1250 839841951 839841953
    0x1104051f2903190921260106120b0a0e04030c0c091a04200f070c0509040b010608091203070207091a03070e190c11100501060801290415120504080421 66
    0x3e1048240c5d40c00c240e440c800d006d0b120102d101d06044100b003601d40010300407030040c00029030001c0448503454101d100030039401c0c0303618003080c8107010b15400303000000386140078402015407003010400c046001d80d01120946440e040d1807001c4170310003070781d03484c3c0b07051101e0301c480d40c604007500182001c3e000c00c08105144000040081d800b5808074446605840c00000c00d80304000030b1001d500b0241c00c050303070280d25a15103503031a4242440107008000510094000046568000b003202900041c024400c554480c20400b2001e91340f443d0074024000d4aa003000200740c2e40c2c180880060f440280c00a00600d20380b480d090301c3c050007401c0509402203000004529040f08021400307507070074164141d80c03840034100c0d04050b1142082e840c0d0103c92740541c00e140040015580c010302c940d056a15810742040000c41d41d103060040d60308000e084904081000c01d001854900c031041f001a0095142c4a00002020b160700360381c1140d40c215030080c074501b001d1000340b06415040700d0406916080340a14400403082d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 839844451 1250 839843201 839843243
    0xe010f0905010219020105060108040b15030a0b0a060e040503040b0901051324080603100506010210091b06022a040e1501050f0d1104051f29031909 65
    0x5028415a442c0e0b4000840c202d0480008005440d5442c0510082000e400c04000003054014042d202505414904010074448a915548902c0c10540101151000c8040307181075032142c01c088a04c0002c2c01c2c41d04600059015107640a41e2260b64400081d62070542040e001590780d0b04110381080c10060103000641407402e081844030054110b2034229010181e11200c80c44200f03e601c041c0c0010003012030f0501095403000502504400c42d1100c01245541d540030040f450a1929900103034940d04081d644001e002d6003007000305540305a01c0c031a401c81c070785625050b40d884610386010030b0001c1a01c0c1742d10300055014114082c54045c001c00200c0d0f0401d00213000b914200450140034400306626004102038544404455078258042d100002c5007011030f03c42080c0d80c2419241140602e813280005880d6034100c01c1169994828029031441854032201d89681c000074003088800003081f406400030110911400ba80c1c46000d22690301d010546e643c641d1b0501820030302c40100c540c0380b5860301c8180f600348 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 839845701 1250 839844451 839844461
    0xa0902030c061321060605040c12050c0d022b0b0303030a0c09050405011706011502120d090c150f020c0904031107030804150207090504020a06110a170a120506130e010f 74
    0x100b104c41e180455007410011964a80e2091f03105520744140d098090b41c1059107428a070f23404110015a66450403500612482400c0b4410f15243c400126205062451040700c0254203e2040804552042c6107800b021182103a01c0154540d00910026800c110f094100c0420b1041a1900840f1245c0d2440454180c0743c0a802c0079420000c22414458041010450203004000c8a00f0700d400315095090080c0d10740c40050512003080c1e40004641d6286402e60300310110a540c0840b581c2c17402036072034802e90088201304d01800006200440e00180c1c03d4800201d0480e541c2005040340507544890b1b900303480320038403000141c1060141c4540000400c03600d9000c0c00003030002e900130100362041c2c00b40003404e00322039801030b41074503251070184009a201c412003003081e1841410249003a0860580741440e0024032038000344000003100a040103d100d80c40506050702c40c41e203c0d1000049154004416207004407481da4005000c115128003000b1690000c191500340c0b1400002c0e40c01d031018030081070710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 839846951 1250 839845701 839845739
    0x8010212010302011701320310140f04080d02070203012903070602010e070e09120403050c1320031003050a080c07240f0905030a060506090a0902030c0613 68
    0x1100c0010019560483c02c500c6110200d8001c000e429130500081400c0792084110655660032180c1e00c000e11200c61002070010792000030101d40e204502411010082c108000640d11207441d03020204412a200400140c011070f070002e440d40c2481c2e0f120341440020341200100b40e03490364823224005c0d910b41c2ca5411b000005004d045481d1101190502810315020490303000c2021a0f141150f0700079031090103d550b000b580c03007080302e555a544400280901c1c03e074032410152315148001500200b00b24000134031030b6520005407550b0003003550240d050303001c90300580c406003c0c4420354000300032100b01e4017005581c441000c00704c440c0038039126150725180140e101812104040300240b80c003400d901c2005414028603c61240400c2c0d8407480421000060309620000240016008800001d901500c860005800e0107003c4030802c0f442418510043c010a0318070070300070340200300401c199500a00030080c410b5005001800b1201c0518140300c01640701507a4100a81c0c0980004070356000c142020303400c48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 839848201 1250 839846951 839846977
    0xd0918090b1e061c170702090903040e013003031e050117030316050a02011b120b120c01110c0603010305250f030204020a0e0907030c090e0408160804080102 69
    0x1001c1d107002c1e0400040a0303c0184a0b00d01d410654a15200c07116008481640c4215240c01702a130350703c503081c8940074600d4025401482c075000c0002803403001000d0070484944101000301642d0315070381d03a04130104042100e03240d00000d000302841807601c1d1744200041d911a2500040500c000c042e2180d82126141107280c01c0d43d102c2004004480d00036103018150a96500a10700d5801c15110703801441e040d20000c682803240c0070500c818103d00030b601460000c02c000c10031107044140c4201c024002d09032954504441403908114080606203c2d4034403141d80d450000401c0d8007003104005545486002c0e61119007441000c04860301921183c015600a62184e80204810303200c8a024031091001e041c81045010b0425100704004000c1140719411030b82c0681d0f00603500d0158400032902c41d04e40b0350001d500114007105011a460781544030019160165999810483e1500c03103901e6408800d4401405411042c05020020007004a40c10003080c0318822070b0f40b6156588001d24207903000988280b0389 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 839849451 1250 839848201 839848231
    0xc03151f090e010b090f0907020f0118050f1b0402090d020301141b0703090b07140a08030714040b0a110709050103061a01110d1224090c020d0918090b 66
    0x149003501d050a805094144c00d0941060710f50800300e1500b0001c011414802c00451002c40c003564000c2c80034000e5a98244020300600c400309250710b1505003a030408440c2c91043e451380e1403400341c2c0821032008403134000000070380e5940c1d80000c10020f50021000194030010140c610001030354244942d1300410818840312034a8585829071180c1070300403d003807000940f000c121000010f9446103010040d6544030311041e496039454108040d0340c1c0302c1001e40b0b400c03900c2407040351418041101d004e14800c80880e0744100042d00d00000c024850301540c41040c40c0c1040030f0040c2396005004108481c011820309003103542d01560b41d01c015060321800c1c9c0c0b00b981c03110303602c1218841d03080d181c07002a821001c007824000c80c988099504d031aa603802903c5802c00b0003141d180841c0c07280c69550060001d00d0300d1241219a410104900c08030f46410500c10f500d181d500e02062014003a00124142015840c03603150710030f03118a450100d070494030703440d1203607249030b81e440051030009140080c0b483d000b00740d14034010301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 839850701 1250 839849451 839849459
    0x1110303040606240f0c060e0a0f12021504080a051c02040503010f05070e0d11060d05060915090703052a120f1306090218090f150c03151f09 62
    0x201014400284504d810210f42d07002c403400e03401261484110752036141014980042c2d04016000b06810381d40204a8040e00110348240266200d80c4544a07000f543d503020315610419080c0d80d61034064050402107007000c0005000f040124000c2e10280c0200d06001f0315101028044a0381c0b218a40711030050268003050601103800e09100d07154030090070307000400042c1132401000c0c09500303406548a11540c2c0558509040084c0d6080b601c0c1450340c094250b60312440302c440030743c020b45402c030b03042c5000d581110700148038070141c0c602001311400003030010740366620b50700c41c2100640303c01000c40803004801410564500124204980045600c8103096103a0120601d1115415030280800220384440d505001d007035000039440d10a410340c40a0006400c04551010030b418040b45441e0010800c075540811070003c4002c90540c0110803920213036800112004003986c41d092094442420402d42400041d0440345006030004514400070310112019071074241600603c4030268589000843c0154104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 839851951 1250 839850701 839850719
    0xa1a070909050c0d0902010e090a02040302010e030304030b010506030c0c0d090305010516120e1903110d03090305091314010902130f181e0501030602180303030f1501110303040606 79
    0x14001d000308003010b2009050800408059001d004d1804000c2550b400105046a0081952082c152006400c034106894092390020082d0020710090b4082000d108032007083d45408000c4406503548030281040ba6400c00c020301915030030051848424178004c0041031034145080003112244145aa6420142402d510b4254207582c405011a0b6515003400d03a0394820542250040c0940340324200b0000e030440c03142100303900d4072101c20200300c26590ba654104041c1640489110384141c2d16104403036100034824011000c41c1c4c2500c40190002d10b09200700f413000e1401c041d42e03013a0000010300104084802090b045100d11080e880103504580c009640075200b0401042c08005100c0e071070041302942d01c0c12004442e0189040c48042c0e585903614108040c04200b103191145600c1001402c0009603124981540294403440540907090070b61154dc4250b8a800011a44076021f01400741269031150450145104800080ca505001d0f500800440c0880c0400285100f10701941000ca001450002a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 839853201 1250 839851951 839851967
    0x51002091318152f2106010f051602190815040b06040902150714030304060b0319210e0d030206060a0506040e181219030f020301260a1a07 61
    0xc10303003090034200d13803a42d20380100c1c070100000b50440b03022441c0000440e640c0c09072885401c4801151869901c0301c2010521701c264103522a40080c0c07944421042840000d455034028222800c1c2c030030710780d24180070060400c602041840020000702108441d02e0304030f058200340e904030018005080031002c00040c4400c0c0e200c020741202d0b00743d904010482080c0c0108200c52001d1102c980000400502e0000300f00c600d020483d00d1001c0c070700c152030f124103162902d000a8503004010f11303c2840b410b442d14164045a5001443d0b0035884000f44500c10113080010602442d040d50342c806001c0b15100955881e225000d8074203c841c840d0b80603004600d0710508011003000c4036001540990410b020134001d0080e40d42806400070061204060040310b414007561a18481a4030349503020750104449101c100311610300b1480003107584051101420045901c0304a010911501a031032040ca003040030901c16210030300701015000c030155114044903407031300e00104015044c4000a0700e860402c020701303075030b100283c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 839854451 1250 839853201 839853233
    0xc080a0e0406150f1e09050f030307020325090612030e03010f060906080709091a131b0905090109051009020a0504020301120221060106141306090602070909051002091318 75
    0xa035003408103204400800300b446c1c5004a60054800d89400d000c1640c1c01c10603950901c0e4010304441c04c0da01e4940400600c00301d07403503000075a00c2d483c0e00f0120b11880300f03008201c20345007511204203c0030b00a0302d0845020b40050071194042d582c440c0180c600c10114010070000d006402d03800308401b45021440c505d00743c100d03400b10340c03c9440d2090342d031f0001d03000c080c4d00c40054900703000c0300003503848080480b149100c5d0364900400303507050b04602d4030889443d503808404540b24507030300301b00301c1e41d508100354281ca40340d2800400b41d400459103803c0140955106200c41d03400905402491178803440414102e80c821b80103035500c01c1c5604400c00862400106580b4900038500301c209800b2010070289582d104180a488148400e0344901d0320490710500c150351027034028040449401c1d548000c080c050054602443d00107000d00d90001c0b5000d030241c0109544203a0004c028400c0c8500111128001c0d00410605584a0041e030103d840c00210b41c00b82210300150341c03841130041d00d19460000c10b4100c6081d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 839855701 1250 839854451 839854487
    0x7050703050d0f2f03070c0212010c2c010c0b070e0603130b130c030209071b06090b0612030715020c150604140c0316110d0305060a060c080a0e0406150f 67
    0x18131581d5541107502525044451414000c20681040c4002600d01c020360b03030b00041d190f1034000100951a40315603070240e140d000c5580079490648407a1031611490280000a021603643d503520b000003020300140300c2d4401c00c549001012916074400103222036000307586058100d0740da44000030500a010b40f0075034004d40300c03803002d41d6007011590700d2051000e0305201c06482100720360000382d011070041001881c1602ca20180c11000070070340c50040300034040130740181c48141c0780e80e00182080c10900b920920130a010310085042041907515442081c0c084e808810717415400b445041284031040140e40003450b01d0f81e030703219a149044402c1c0804c507002c0c0c804e042e801c1e030403200501421700078503822a504100f540002c10071004581230159011030480300100024422500521070341e41d4951700c00350107500c0468242c1405592004100c17480d5170320280242c10310b941007002030401d0b40550000419507070050800b0a03ca81d460500e0104a41081100004525209014003e05e13500c450703155840101a8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 839856951 1250 839855701 839855771
    0x121e0616030b0d060b06040308030c031501030209060f090d020d1511040308180f13091a06011e09030f200121090c1a04032907050703050d0f 62
    0x90001407440c100503c0c0a00300540e580d5000d00103403100c50888024503001501540d903070420884178400d6600441e6180c500d810480307905c0c08550302c28001c80d051500020965070401c915240043d1042d0700c918080765200003044020001601c841c4080b410040c0202e14400209640580a109a403a024040c000185e400c020500002e2200d8041c0c0b00c4005000c484483c0c030302840700c0030842007032606445650106101032030040c01209600a0a03c5521410240702030100a03143c2540c105420b80e50f03030780814182202d1a180a684500350800c956191911003502a505c1d11036051042c1c0541c425104055803503c0c9201e61804505c0300c1d21800020310340240b03035250b010801001d140940074400100c0740c07102c03400800d0000c915144000b40021a14144e01503148a4600040d5840345c803044450664034041486403802c082103114510890a01170101035a88910441f1941d01045048042c04014407480391029000d00c0b407480f1404c1c40140000f2204008140c00c000008121008030010840c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 839858201 1250 839856951 839856971
    0x30f0a0203120c010209030604120f0503060d06020c150a2003060d080a180b180111030d0b010c0f0b041403070c0b090a051504050109090c0806121e061603 68
    0x10032511a04041440c01d0712605103c06440c06407050702041e9526110304802c1c4800c2c0103200450071030750701140c1c6482100010000040d05d843c0000c0f40c5c032a40c0700f0b00d60118140882d4283c0c0007810300801c00d20a0301c0000720300750002041c1d0074066805004040e035855600103030a100746035020150000480305410341c503107400090a0b0725146003009181d0382c00801d106040d503010f030622080840d807200080350541d07211010300826400c148030418808224941c0e1803100c0d40123000c403600c41400e550286140185008118001d030020340003141c10446140756480209030403404000f8024030940c81c04c165800d29080030139402c0000300c600a00c9030410000900055021800d0504441404c408240c50308650000180804441d50049400c9025002503e00c460030001c010310988000340c071510402511800507504458000c420070000c100450007003541071805030307501c040c050940b1080303035036104803040c14100101145250900990041c800d220441305807002002d03a40030b00c0d00d4100518168 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 839859451 1250 839858201 839858203
    0x40303110c120a0615081005040b06040c050d020a090e010b180f03070501030e0703021005030a0e0102160b060f031204081c02120a03090506190f1a04020903030d0f0209030f0a0203 79
    0x1c20380000303084c0396940000c8074031098028070350f500a040c080c0c2034a0407081c1b00a07984024000807241112110b40980000d055072510303104804042946640b100d00300b00b43d5a90040007980045412010b11005007000108940c11b8500305000e00844030119403500c404004e51003100c10301c99141d61107841508214055a20300081c41e4080390424a0081800742858190324140b0301d0940002e90481000d8400036461a0400c000318044c20003c0c808000650825072068203d002c1d04405c3e103c2e440d0056014001710300c100c00101d400280003040008015000e50000b072401c440c08001d0311400002080070400b011084c803ea80c440c4c9c100201030892002c450a00944608100d480481500c502054012146101760700c00c203219a07000d4102d0f0000c0c10b113410f00d0007180700c81e8401160380074100710500044807994003400b0031542d08102c13501c98140d919400c1001941003480d50b90b4040c0301c00e021211105481e4010144010605100183d407008602c040c50304142c103c003c6446282e104201080051318 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 839860701 1250 839859451 839859463
    0xf2a140d031218120c0c080d0203040306050a0e010c021f02040509040f1b030b0115020115050909100203130b1605070807290619141e06040303110c12 66
    0x88201c00007070610010400c0c020300e100d011401a0403046040500c4107040c1c0c01c00410300c901801003d0745a40d16947d840c1e50b507510141d0100d0440107030000d000400c0058070340e030000d07030300154812800b20f40141a0340c0e00600f140c018541a01c0103070721200980d56007003008000c5084c010010780c025442c0504140118508040280c0300525040c4907060710814440711910b00d02c695040010400c80c020381e01e080c6511800c5081c0619441c101407541c2d0200014014481c1783c0061400844040089203442c0801084800003007500d5110b0003085a2106011004e20086109004040031800202e406040900340400300910103201da904c0b140611036010740003400d03035030505d6104009030b0ba075001c0c9180c040e040e910704204040d8100d2150006402030011240300b98032440e419511024a0901400f1800c8114030b075119200d01c0d08401c41c000801414000312820a10f030030340f0307001d8008445850124065502c25441940040c0050b081c100c44100240a0818805001c5842c8003a1b0601b0941582d1904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 839861951 1250 839860701 839860727
    0xf061b0809150313020901090c1b03020c131b020f060a021e0304030509030f06070c0807050a390308040603090c030605070c060b04050c070f2a140d03 66
    0x301080c000c00c15680c030380707403240062002d95985490b801c084808035006500000100e1042030703403d00202c1e00c500c60340b207180790894003030365480309005c4003c10b10080400000b5042c2c00310301410030000d841e912803810303812034600c0303c5200041d030140002d80f1008000030155103804541001c0c2030100312000c00100d039500714103000001661031242034415481440c00440f904171010022007044203154000d40600070381e020582c261080c20060310034264440c0d030119a002c010a01428020b40402e640d800500a1103210704101d40131381c880f0b0340b160000f41a0040c0030f40701d180b1039240581480b04c000d52041c0c02c0307125061010300c1c80c0350031036685905a0049020304420181d0302c1c0d42d90000c5c071400301c42c56001075070400410001401c01003c001d040e0110004143c40e1b8500700408030405040c54400d1130f00c11040a4510750074807015a684002c001c1d4130b0b65080e5101200164403403c3c0203482210640c0100040d03140c01c600c1458442501c0d4200940000c3e41c0c0700721805100c1c9000300790802400c0c0f01174 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 839863201 1250 839861951 839861963
    0x3060916021c090303020114040206030a240915090203190b040f240b04050306130212010509101d070314010f021809010e011802090a1206060f061b 65
    0xa030a0340004a25012140c9101d01c004500600c106801a03000f218150580f8003d5009104114640307405451950007907600079000801080000e41e00c00540e80040100111188151340400e00e200000700140c01c41d401060019903502c0da8100d82c40d40740c014120081040b0071041d41103203401d1081c1d42ca200004280c02140d00d840d0a2031840759625540400407a00d091201048043c03105601d80d400c4060401d400c1c40c08800704000403506120310801d4030202d8000a000701a95a20382d010b010001c0803410b822604214925030851381c1200038041c0900c201c3d600c0d00204106a45075401c00d0544401070305907c030b6a02815048080414003007012815690803125000401c03c400c82d01c02c0c010040d0005148901e440402e50607000701e020b15403c504a0310455032110036076210804000c55034400c1c4200c003408240e0305940e980005468001e86440480103003800302c0190341d090000e0102500d50003c480060340c1d01c0d001d115100d40251108040c0440d8501030039002d041c40b554515950a020001d051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 839864451 1250 839863201 839863231
    0x3060f0406050c07020904050105060a050105040509011517090109022b11152b060e04110f0a0e06190605220909030c050708030702220f02180114030609 67
    0x1080e0f010045401181c0d015100895078542818072600900b000c0c0e8196200d10322100d00043c2c1036120380c059600340c80006080100c5c0d0b03460503600c0308a144041d144082480120034100f1042007030014658454200100049048151031042162440c90080549001c1004d105501095107419203901d0001e0b9111928586000c44503000030201d442c0c20442988510001555000c50405910f000c1030307080340928031000c2031846c904ca81040da2580d0290b03070384400039800010081044102901c1c0c4250026015540003840b1401040d201c00c02c036041504071381c59080921825007407442448003143c1c0550540749e641410074400a26500c90300c032002041203100e240301c41882504506c04801014643c0d0200008085860041d2001410190544090003800f0002480c500c000c400c0320034040c0d00a0a10000e51418032103566540c0340c00d0b08014080755100e40066000c0000e02c01842c0768447d60301c0d0b21500010070070005140c241048a0290602404e000b4800d01da1280c4d180290020341c50100022 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 839865701 1250 839864451 839864461
    0xb1e130303050919080109030908060f06061e040632041403010e010501080a0c1410030f020d0504030809010b0307030807230d08160c0f080f0417071403060f040605 72
    0x58034030642c00310403003131100c2601c000490f208150300100e0414400e444503500180d44150064988900325110340f001d040f0500054000c0c582140248101c550070008050080b0211030f0000150f0420381100012031074034001018440c0d0050002246180301c00c2d4400c805584c0c030400a0002c0c00741b4800c015185100054541e0039580a41101c40d0400010000704515a0340700c0c3c0155585100200a4884440e034480200342c603641c40340030300e0201901800107161a900608101d0080c0341d842d001002c0c0039401d110407a4042d103540502e0340102d00955551102c1e003801101142141c1c11440c80c14131030b9006040400000c0c9482c0240c506c8035401809920500115202d00c0c0300c003c1e01818443c00c80c0c012040d21f0150310741c0003418580540b8140540c1c020f1410003601c25611380441400107408110b51f8050340e000100b03450300405011075507100d141d0a081d5106800c2c40102000c01c13014072940c00c041024440c1e001c1e04040311712031201c201c0c0100201e04000e036001d00c404801038400750079251900e002803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 839866951 1250 839865701 839865709
    0x8090d0c08180d080307031b08011203140a021605010c0203150603010905060f0a06120203062e060302041d060a031b0e040b100f0b0f130306060b1e1303030509 70
    0x3001103006043c80c10104614a0501c8017540115010000f207032600c82c2a0340540082100c0440f4007038a915003e1003039081c0001d2000e0040c60300c0e0100c080040e08a4a401100c0c4c0c2100a0301e650f00e00303500103018035024501da00c44204803c2d00310604000b4424142d50141c3e40020303045440c11000500550b054a841000c00d026000070304010300a4850002817001c1e96881d8001188514032841c001c111440d12001114000502140081d5150b4020740100e10f064030002c18503016020100074500d9108103511003011151196445240803aa02103020070a58421503840c0c1107a070480500d90b203562038214002584080140800f4180110014401103051056050007001d8900100c0c5510249410b2801620402d01240c5007000f0f41810b181c0012607444003a8404140d0321242440b5080010100c160342c21908050500b440880302c454000010810701e124403006812114181c0d5510140d01140c0e55084000170342d5013981c030700c0c2002008d20004100c0318440540c0d51600e80160f565400034002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 839868201 1250 839866951 839866987
    0x20a0e060322031d0603060a050103020c0124080601081914010603080f03150406081216080c210a0c030f0302070c08011b0c020a060e151908090d0c08 66
    0x281480341c0d030b415010780030705800c541e48000510340002229205800d500600213107000c151038481d04008034900600c03056009402500070307100741c5c00002510907440e4592004503488400da048040070041014056150144425805002d0f0b50000340154404181803528050754854007605042c240019111004001e4000310001e5420001854480a48544c503416541c01920305400300681c00d14140741d213081174094a402ca4142c1c6002d40000c03204100303d06190707400291004c0e41c441d40d4904080004151801400401030034400600100c007100c68074072090320800f008260020f409001242d00e40b0307805181652402c0d814507241c4107072950700c90190068051520000d150103007943c0301242a0383c056000004405420712403008894400c10250750a12110b0006500301c1c02140090205c240200401650007102400012001e507009507400e0a0381c0100c840c0e07072444003200080c9a050b80d4482c0780590000c10200242640c1d4000a20142900d004028001d001c410b000c41c0d07021030340b0060052 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 839869451 1250 839868201 839868241
    0x300114240a09051006120c0215180718051803041e050306070f1218170408100b01021c0c26070c031a010b07140a060e06040c09020a0e0603 61
    0xe01407400c056070f0302031303105040b0300409000400ca034000d03042041e03441c00381e18841011900a007845068003620b50030103181c010b16241c3c1c0c07080e46018020b102c04081150304014000d50300c180b051100300860782d9090303541c05071518401c6050b21030a0710119a0200071501120039114918030301c41ea4804410502d88040d07882140e160003940c04002001d504000f082030303410400c0d42e4840382c4210312110042141c00d4003a080b40002030140f1003000144140340c04030041c41402e43c1c501d0600350380f0500680350032407142803914010b031103202402c1c1550301040031804030a42e01c1d4007450240310300280100203140100000e0070483e03081c84000001c080c01501d0011611090800590f181d41c641020344403400b45e44003c071884402d41c501003500c402c0caa902107043e500c0700400c07180761117080c4d21689800851881d1107140c501508500b800040c0f0b035031250003216241013000d89a1440d00707007851440312903d80d01103c40d5070300400c0410b8036180c1c000b038031401005048030015101d0701daa052071140340d650421 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 839870701 1250 839869451 839869469
    0x3060f0601030b18040c0e070228060c0504090605030304181508070b0c07170a0212070b04030b04020f09310b1008100c020604030e300114240a 63
    0x289481c900d0008142178030650081c902c00401c070b03941d81c0e076a8503001c03011124175005800500d4a101d1990001007001d001841030304010400740c42680786c240c00c0b540412022004a0400a820403000201e8013030500140411006181840d18207608805043c4124244043d290790f40c200c031031120b04070100d103100900011422070305603d4481c074400e841ca900542c1000124812440002002c0313642ca903030380d062984c50b840034102d801901c0c1e09010b509500f0075400c170964001e20708081420f00a0501504c0114050340c07020095043c85d00600c00c4e51900c4000c5503000c4c0480c84200054440559401c15007005c40b500d0140000089104003284400007c10040601d01c0c07200510010380c151171240c0c004c0d51a03540664000310120b4503024211a04002c407880560446070005000c207001e58204a88001c0203410804c41d03414010401c0812070030680d250320001000c0b2000c1692070000d101e0000280c0102c00180d80c81d003085248002203424a48482540e20302d141c4a080c070607101d424042000b046102 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 839871951 1250 839870701 839870719
    0x10b0a27020921160f0b07060c090e130b13030e09090a152423011b0f03081b07060207020607020316080c150a030504140a05030d0f0b03060f0601030b 66
    0xb0f0030703081d120310f44000200d5001c01810404110044190302507000c50f10400c04c02881c0040d07640d100409405540c0440091101c000300000d641468044694454240c1558001c0e254403d498402c3c8100c001500b40c0c180b10300e0912141c400a038000b00c2c00012100d04854101c082d07510060800e281801c0d4800062603030406103a50702044039190010440030300e12100302d002e4034941d9080c0c00d41701c0340c0034420000d03000d20a184c075421600194901650440c0b041c54000e507903144403181e003217035030040303460886002120b012040c0a041d40a100184c00115201c0e41d42d101400c040000c0c0d00764091400301900c44c907400262030045548034001c9644959024055a05a01021a0042604181d40300700f0003d4002c105a61120b4641034000340c1c604c0303120711516410003243c0c44d0120000d14000700101c0e00c2003680c44803580020010010110f605200344000c503514080741d844201035801d0000703c24000d40c00c0c010008180e82d008640c140e070101b05655081d0706641d5140c012005480c65601e401d400100e10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 839873201 1250 839871951 839872009
    0xd02061e090406171209190611060f0723041d010303020d020606010903030804051516110c0609010f03020d060b03010303080702070503060705070f08030702010b0a270209 75
    0x1040070348200001110300700040c1e99101d500f4150403245800203001c0380c002c008075029480b5448007405448001030011014410700c698a9840c80415420074030110300d00d0400b90104078420480e6542c42041826a660a800c2416001d840d182115a83c84040826600c48031078082c280e405072402002c5c8003804035803400381c400c40d081c0c0d03858080c041500180101c010340b5070002d00018200d401840c041e9106062180746433011280000b010b40102c585000b241481000c40c0040b048440c0200d001d0524400c000142e85400382080060b40c0541e40c9541000c030460400c1e98428064440c03822003030805004001050314114004d03c030f5103003011101458030101207840807841c0c010714103991007038685c0e81c525140c0d040b00381c1e501d1400744900395246d4054000909554421000b030410340e07205007012070058400382c1d03c50002d600b0803160100141c0d0350702c030074090500d48202582d0050210284601d90029a00200c501a8185104880001c0d400080c40603490b00c0e0b03144014800303000310200325024094 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 839874451 1250 839873201 839873257
    0xf030403030e190501080408030603101d160305100b0d1a0402150c060106031d0303150f1e01050f120921090a0911040305072d05010507020d0206 64
    0xb410441c0780280c5a0120000fa9401d020b0f03582c40c1030300c005031214409036407640e9458000744e10003407040350903000d5103400a000d606540510b0343c101c1440c50031013466210b0035030850700c4c0c514014020101c00c2d070116000c10102e10081004074148520400202d05070b0300c0d403c042102c040c07d00320000e280300340782180e107400c000c2c0d0a0075140c022071003144c82000740409102c035944280030318081910f668101c5001080030f0743c025400041e07400010344195410207120381c0c010707003180c0084071510041031041c8200000c51603c0641c04480b041c0c110f81c41801440002d03498030300980a1b05286052040006040e0740120100095034141803a0b4010007409140075141d080c2c84600028061010b141144d04650003140000d064a07215200540081912480e110301c01000d00918146078240c140100070201c0810800c0c07203201c1c064240c088103064079180c851000301195401d0b0039581942200e88000384441d0b0b0b4450f08880488e901210f82107100314440c00020003a1060348200b0342c000c0c00c0004042d24100e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 839875701 1250 839874451 839874467
    0x60a1406070302190f150c0e011107050402070b06040b0409030c1103100603060e2b031509060b040303020c0d170a1206090902011211030414010608010903030920130e0f03040303 78
    0x481017040482401c0184003101c00d940e55040e50341d01260030306e1482341c01944941c10441080c40c1c1681110b144a50b200c0100d001c0b03a04c2980e09440744410b403002c010060410380201c4c040e20f117003640c2c10400345140751002061060243c03801000811400c802465541e010404031484662a42c0e040019968a00c0d0200c02040000005130f414000d81c030b030980740d0310000f44003000d82c60300d007140701d0403016070303c0104800510011124100d089000280800c0d20702c028030814000c1c0880790360b0142d4550175424061b00c0e03d0300803d5054800e110340c5c601c50001896140000e6911009150f8058480d80022800c1e1482d885076a10080c0303c6242280000300452940c00c0070020034001e0b2500b500c2e0b9244d40151005840c03041001500c2c402e410008030340094002c211a4403e10120030002540f1a03d545844e829621245070903000aa191030840c800c4c4845c02c00c070050590164a07900304804803e001040c4d11404021201c0c01003940c400800d0300804060100600750070006082d80d66542d20703882c015141803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 839876951 1250 839875701 839875703
    0x917030d1d0607090f090b010c05030a08072007030f02040b03010e070f1a0a1b05150402010e060309060a150e011d010e15061c0c0e09060a1406070302190f 68
    0xb1040502080c0c02900036030504c2c0648104507001d2044030300b066a074402810400300c86ea41003000c144169008a602400507202605039550340c5852801c007107034028030041b180c02e2184403181c041504e0400c0d1850025401003240c0d8032900d000c035190803900001d0300034101001640e130954202002002840000b04102082d00c040509201115450700d20070741c0701590040380344401c02820040005290701030a1040349680210410b0740c4907034501e5840d603041c80c49500250030760a200302c050004560300950119480c1606036141421880c216045039583c100c0900342ca80919a20158082c0e41d0b080c02a21b0fa01801170800403011959445200ca4242d142da00311100303000d60a00300215502000d4241c0350b0103002107141030546d90750301a04100d116804900303020300e0b400040a0303604d80030a80340243c1c5c440c034807103450b04140c0b062000d05018182000624003486128070800900814400015420792403400381c55064070b960040c41c040c1d02c0e200c074100142c000c101c084ca0601c03041150740001100c0c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 839878201 1250 839876951 839876953
    0x5100b0711040609090b0f09030f041811070203060f06010e061b0c060301060903290705090f01050f160807050102030408031812071b0e0108030403210917030d1d 71
    0x981c1d550725002045451100d0001c04021110012501441d8000d81c801d030400001400d40c0e01c0d040c81e815114ad00e0b40d026602c281058800d0044141c090380052042910840c07001d68600d00e414803a90000740c5031080100000c0040d4800c8000c103803c1d9110720381c80d03001c60602421711640c03003442c41c0811508080303144c0d20142900c00e02c80c039030700e860038150149c074102c41d081e454540700caa05695402c0f00d601140081d003004e140703000c442e0345122540304a038180100c1094403540e03900d001100910804100030303600d40b0b041c1700c41000b900f400c47c41c0d008100c07158242c150f6400d1160205514000c0740e24454403002800a40c000b1040c0020312620b00001c5000b14181281c84480c490741490450301d4600d81c1da860207403100c09201c01e0010420003014040903401d0039440030380040d104c0c0c8030850302a01c00e03007040b6030035400401c0a208000c40f400c007224103001c117401c0540001c012400e000305961428021001d0780c09810034419140103080040d2402100c11200c1400703058040c003500110a64020904541 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 839879451 1250 839878201 839878211
    0x8010f0b0405100f05210d0305070219200d0203030a05030708010e01030803010b0a0c0f24050c030103060905120d0b0f120c090702070e0f16140d05100b071104 70
    0x1020720b50300314100071281d0040c9102151441c0030b08110345041c40743c0101040e481c8598003c0a4202c6c01e03c030030901e0064544001443d400c210200924044035421109440300c0510b02c1c2c00003044242e4881004080800b803084600280b01005c07403905404c899000390103120101d03008002680003805181700359025610b0040b01da0784c43e00d41e50710b00c0c80e007844080d00b9200c080005104500904005080c03294003414040c0780d80d840c5540300310b41481015030070f8546040301d00140c401025449003120180b40701310300c00e025609091000350b0084c403041c4401000c00740e5407005a02000410f114510355450007032501d40d111811880854050454509a43d03c44d10a0080d09845841c00d910000d41c6007000350004c0a203121820240411107402504001c20361298100000e062024503804620510b0700180020003400c02c0303c9003064980d1f100307000d242400101110f201e0711464400079541d01d40300301c00021402da2104001148544083e81082040e4000011404284840820110082d010950b02000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 839880701 1250 839879451 839879461
    0x120614100203070b010306021b16060809010903021902041e050109060b07050a0b2208070b01060801080a0611120a0c020f240c09061c06060203070f030807020708010f0b0405 76
    0xb8403407051481c02049410100f0060010071141c5c0d01401d10801140405a8a1410000014600810a641a50080c4d0034100500c001c0e45e205100c2500030100c00024001100156006900d610054645152502c1502465825907403a5004114105003040d1b44405895900381d00034040c0009000350300c0f251f81407800004050000d01c0491300e2054000000e0051030740c280c3d440b07000d019006400031815024151b6045880043c100820500030310401a8642e1001381c1d15020641080c1640644148040040104051500480c502c00035a0784210300040c1c0040c00d950311303031050041280e102040c076031910400290440f55486282006e50303503000c442c14400d900175136540c0c1d080c521100c2860a602545202006003442500a802c854030405c0c817828030340c82c400495a990401c010a0001a400451010b210f9640e4800c100c041c10743d62000e50715101c0035440709002c3c00815074005042100c0300c4001200c0502c00d005031070140202e0320082c0300703040101c00c0032006001300c2c59580c2c3c800e6140801042d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 839881951 1250 839880701 839880703
    0xa080907270c14040b040f0906060903170d1401330e1201091b06020304120f02120f0706090501031e092303030f0a18060c1206141002 59
    0x75003051002032800c01201d054454a001030301c61140034406010039141e120003420042c102400c0545000850262910300c1c0807401c40300341110383c0c4101d512a29250b8240a03030307a8014420000d0320342004a54181c98880c0070b03252294420422180d0740039290100096650000c1c10440d81207a080c034041041c0e40d402d0012000000301c1170411169440f000200720071a55024008110904c48020b201c2d2007911b005e41c0015003500c068003011203054180c114203000340d03009000c80d01e000d0001440214201420400c0440000c1d51203240900007002000700a0210342e505498001c4100b4400b0a940c40604040042590740081e07003c0c500c041280490701048651083c410340d0504044034212000410300900084000d0044000648041c100d0380010b4100710a401c06204441003407800555403850903c000224034680070303002c8440380b4181003111004c421a62503103030200d81c00450001d103566080a040d03030099034207050700e13103480e0030900000f94030044503120000d800c9c0c01703407014241e17041d50020803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 839883201 1250 839881951 839881979
    0x702010b030d0810090609150e090606040906110c0105240105120907080f07182c07090e06150d2d0807050d03111e0f0f0a080907 57
    0x49405502c445001508644645407503504240701d0510506507503101c000902c1541c0c1180c000c1c002c010380b82c0d040204100c0c003080d420320040c8036002e913600b21810800c3c0c0c1c058603150041c004621075a00d4040308024040079500590141c81d103803a2080c1d40c1e100c1130300346901030902100d041d0040302602031504107116a12110744a0081c059440700d1401884039505480c1d00000340400d10a480355800104180c0740400901900640711001002038900d00101090300718410007040d00c4403810b080c81210303945d030078000030440701c403036400380507140c0104403012450440c0e141e008407c0740707040400c01c0d80100d4020800d039000d4000004e00324290284402480000100e2401c01840103100b50f030080301d400102e05d00c1e003989404400002000c1d07401500e42c40e00a0300000400d88042d04003c454100c1c10f5094441c40900054120034141008600484c00507074030540005510084000a050303040c0c41050021031340b9031a59204040c1e2140d041c68001005100c003203542180354811404081031920104d000c2c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 839884451 1250 839883201 839883221
    0x31a030a020103181703010e090304060516051f0e01150b19090302030d030f050601020c1003020c1609060e09010e0714180106020105090706031a04050c2101030605070201 75
    0xa2605600c50341c011002841001900c80408207080c051000140c0b244c0034440c40c59040c60009a213075411f107072040c80c42d00c101404210050b0b004000070015180c00809a9000102092000350242c0071420f2141c280b4030307080072040c040c2c04146c01d810000e20003903019400602000e4001c020b00001c1ca941d0000b0480c45005144801c0001d0044a802c0c0d240001c814400c61441e2030007440040e1b403a0b01003490b24000c8102c0030003003030f140c3c00304504041052040d10341c0190244000c185e0340c0f4492001c03d0f41010310240d908101500028100440e040400c0b02d14002400300e40d0402590b551200300e03000030034250088032041400f0034049090f03103105008122130409031101408206183c0316004a40e03280c0302c1c01c181e8201e08045c0c41ca0080c0b080f0403008a0003800141c00100d03061610076903050512010390040c070181841c100e10b0000039090600f81c18032006040d5400101c513260800305500c0c0b4011030007000200c07103101d41568003a058500c4e039141203910694043c0300d10344600740c05a00b43d44510711 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 839885701 1250 839884451 839884453
    0x90e01020c06270d021b09101505041a0d180b01181103040501050901050108070303021f1803020a03090605120604050604020906040f15030e06010b0705011b0c03031a03 74
    0x2003070024100210707582e645110f00f802c80b103600f407110950a0400c51054000d20141c0c10107058120707800e08190b4041c20707400c030460b070360b4500d8a000282c1c505034410600501413501080b54518100501440c2202c02138220101a401e090f601c034080020281c2c0f00745603501104c0c0c00c000c2111248540d040782066070550000600c00c590b03080c249084011010401c41100c501e844042c03140015019100560166018000101740c9140001003e820343e07074103a10100c0f00d0b0b401984d040000c81d034049000ca0f52904146c0300c501d00c03086428181d201510030b01c1c00c01507100d449950b1010805400007054000176202c2c1e00ca0117003050303403084c0079940c60240045d401003104003400003c909151542c80180d00401c0203200500381101d100100380c16030000d4202c800d0b40c03070350f520b018803079500b0f4000950502c662a280c01d100aa052040707140d01d41c18180729207203e031400070904000300030083d00100008001c0e0303804403e85100e000b100501000c4120307801e50101c1c3c54103043d00c4600b01e024038203084104000e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 839886951 1250 839885701 839885713
    0x61a03010303391b050f0d02040b10050301140603060d030e2407051b06070b040c0302040f0203180703030912210305040201020f060610050f071209090e01020c 70
    0x2840039a52001001505584040011031801a01c0a2810b5080825458030065a4200850302d40301c941e1001e100c11320b0602d0b0070000300400281e990783c0404a24018190b4040894582ca8070105d000343c90b84862640c1d00140300898148550343c001c01860403142d6024050560781c04010034072106210a441e00d907000300c42e0303155090102e405000c007284039540140042c5000d42000c0b80e0204101040041d101d0341c04000100c0341c0a002041000c0800d514460f030b51110060314420010300244101d1800030034411000300080c041c0940ba00403030000b540c000e04107000c2d50b070304442c07544000e40c012590b01f8544010103c41440310400010b240042d00ea2640790184421300b4105060400150b84404070ba2806040c418007404030018022080489042d440105050900c6c2c4006070030040d40070300c4101d05a10043c00c01100d5a18420f20480040007810081da1303d0310680b0413021144994200689035803540641312143e80e40c000004011219660403c201001d403c9864030b0070303413203894030200b15a4081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 839888201 1250 839886951 839886953
    0x220611060112050c03060114180c07020d0311060f0103120c03210f0204090c02070501080f1506071e0210020106031109090102040f090603020f1c060b04180c0801061a030103 76
    0xa148030b0354020800c80305003210300800a890000300b60044050f10810a8141d2442c4c100082010882a16000084058500180031004600402002034070802e40307654440309150043e013015116034034040c199212494401030304083e9141c288000c55a802c040ca580d0360285100b5052498001e91503a13610b81d254207001d0000444194242480005598505058144048600c0104000c0400d014007088040314810043e091030410381c00281401071042c03c018000c4415200725500c054885008444410810b01040440c0600c0000030008000d442524540e40c0091041a00041c4210740c0062941d000e18003c0f401c0e102c1e188401080210300d018804010325155100e117034000a44800182003da032491451a54056036010302400341c0c2d100790600075810084c1c48180a06002c2e01d400c214040e20340041d0780b90158184000c0c084940d1640e010403150344a0300504003582405820107101d099a0900d200c070415548246401c035840e14800090415920001d810000f004040032804c0d0b84c65 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 839889451 1250 839888201 839888219
    0x100b030a06200a0903050f010e0a1e06020301090902121c0804110a0303080f010609060801231306170616200303160f14270301022206110601 62
    0x1142e0072414640300030791402c014014200060100e40c0001d9841d54105407450400c107003018907840d103003801c5906200241185140c0020034034111a800b00c9900c5100b5812604800074150001c0020070356400040000f80031035440d041f058000d8000c8039005035920b1214040b90b0f80381d4045165111080b80311a050340168001d2421a030b000d401045505041c40078000003034450704140e00204c1c00300c0d03941d2007401640c1280d00e00d41805000c050518406440c203100c0701501100341482030a000411031002c200404983e074403180540e0b540500801441c40c01d07800080b024116600412074030340d590a50141c1d6010000603071038000d205003421109500c21280782150540b5010407203140f0902e07062024401000101300844c0300c0c84501c0c43c035443e41c960501008140d8800b250100081103d0b440c4080d10f014000d000b00c40c854000002c1d41c9180403801035440e40c090110741e07015a81544040787c0041e41825105d2001000500341400700031030303a100e0300140d03583d0500319821070b15540b20f1401401007060b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 839890701 1250 839889451 839889461
    0x2070f052512060b090f1b0304152414030d05090d02060304290f07020f0d0503061c0b04030908070e0c0a0e042c0111070f0804080d0e03100b030a06 65
    0x10250360085014008080856010402510496540c4080c1b10400c998000c41c00ea41c480d0303045602c00c0c1d0a2541c246500c0300c9808140540e903401a059881016801806814a110341c0703d0300a668030060032617035071281c0e000c4000c1a80c441d50280c014440350042d4103100d40c08031050800002c000c10860f614580a21800d604010000c94a942d030041101c4e41034100300030600c0d01e40583c01441201881c025450208100700a07042c80c041d58411410380e26007a00210716058002501c0c607000762203588100c0000c5e18040010810542c800c00800d062003403200082c1c01d140b2076030082c2c9494007816500c003103d9035154224440d1400507480d160119480c40300040040041c1c248515100d84040e00300000a0210740740c4605a0190b004a0807a4041901020070400004845213008015001d485c01c03121300075125480000344000603400608080000c28020ba80241600360201c1342d07403c2e5602d202a01d95041c50700481d110703100f000c50140d403011140c024400c413500041c000e051030120720703561240501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 839891951 1250 839890701 839890703
    0x1806070f0206015406050a06030b060a0315051011010507020a2001030f020408031804020a020706050f0705070e1504060b0d0905010605090a020711090405030307050705030c0102070f052512 83
    0x4800704c82c62403401d2107181400d0061a5a48400241252900c2d0030090384000b01c0d407002c0c00785810040d40e000d0070740d54001a45d541180a003004100601d6607803134503130413040d0303608a180d101e241140300901d480d51200b2044080d4100d14002c00c51500c1302503090303941c1c62141c00c1c010442007000e4940d12000c0800584240c0c4c00106040108403e102600c0d801d0aa03041600202641d17072000c604076010400110b480340840c50181d504500d070401c41c81000b52292207038003901050020000c0c0341d103000c0c1c1c2d0440071910b8487c3c01c201966142602d81300503840b00d85054490083c0c4080c0c240080300b00d442c1a04c10041180e29400c603040c90300c82034220350000340001c10b82c140d030039550ba180002660317240c0d480c40c01c0c4070b0750750303c080140e842e8040c0c07034101e81020056150314018400b090802001030f0000044a8001c20242007a03602c5401503d480c3c0e00d503110b4158a01c009500100d00a400c0181500a14039170724855130030380b4071009903006140440c40b80581c400080c040c030724904004000b96902c00820711 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 839893201 1250 839891951 839892059
    0x21909113106110307020d080304030206071107091a1002010903180e060f030f01090303050601090e0121020a1518170c011b05070b030f09060702030f031806070f020601 74
    0x422406e4002441c1819201c00039220010000204801c06505001580c0c0c009464100000c10f500b402c40d00e241e58003828045c01507420ba6a210b4611400c11011032201c400c07000034007404038814090070003400b910305000c0444c08125107032841891038070701d41d81c51400c1da0128400304140390341d407004101e0162104401e06401d80500740041000d0034081c010910858080d4070702107401e084c900001083c5501c254840c040501c0d400f40103110b400d00044052958564643e4420240c51b070a00001e040502c090707001410b01106140d41c007031129044004110b1001c52000500412541d03102d41c2c582c000c1840070004800e401c40c0c40ca00c04650f008845ca040c0d1000402c0101d14400a5662524034201c680d400001c65604044208809203035020041c5a100702c011014001c581894500030b582c9003e100118001c050000c00040d096070204a08101c07105516811103c260500000140c000f00c010604100103020381d50001c101c040c581d0408241b00c0081d440f6094a0140c420500043c2070b408012134494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 839894451 1250 839893201 839893207
    0x606011422240e01030c0c15060b04031a0601050c1906020c07090905070b070302122803090b0f0601020d0309080c0616030b0f09040219091131061103 66
    0x7948a024242c100041150708680c0c05511039201511009565035a941014200074000d1203040d4082c2c402003035140d02204000c117403060703035856001a0a881e08050306c410008100001445541c03003814802c0c184851120500351540c02c0115510f100f110345542c003950007000d507013111040c4900604402402050014282641140b181c0c0c10112103511001c8016281c014841c00d108084c0611001003140c02001072518203584d030b000e5100e01c0c00385a0003030504000301d400a081d054051002652419507042038810f600c0d0010042c000301240b2070256890a8180c0025010107046c6500d1070040405070000d1040848148045002d08454202203c40101c2480140c2c1d61580412240f40520b00c8440406044c00c1d00140090440d04400b08980c4201b020300f940080c42d40b1550511504a6015120000c00ba2404528030403841c50f681d11051101c0e01d000c1440160700b480300c000e04940d0100f81941c012580b0000d00c800c8000004070202460341800301c60802c562409024892000ca42d00016641 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 839895701 1250 839894451 839894459
    0x1d010b07022713020108090f060f07121811040902010e19050d03021507080105010804060c05122a040b03060103091b0602010c0306090e0c121e010b01020606011422 72
    0x55264020b07180b00f45040c2d21003d08504542c1c20001d41c9a122069000a1001c09080c00c0306a42c0c44002801d00c000a00d100c50100c2e101c03620840c0b0b5000075807071101041c410100c00229154001c410342109450710002c1d50381500f0145410300542a2040d01651045e58190f41d00003002505159007140c110030200e80e000c0000c0d070703841d0040d2040c2654001c1e0041d11198180b0110404034403402802c0c0c0c82086a80001070000342c1c0c02c0140310350002d402c40380c009032021500f2810f9819204400c1d80d00a031002e54010803414118461054000c0000c200c1c46c20308080d00c44a05032030600403802800700011052001560652090b4814880799008100600394001170b40e41004c4a0507240e048880140d4480c0d1590b82100c0d0103000391701c02040345907410040d081c1c1000c07a07161261490080544035501000c15203d503481b08101d0084541c0e04031a02e4004881d0f181c2c0c0d079900030102c07040038501501444000032a03960080f40014003d180c00481d284c80c0408030f047c2d500480030108002c03c40300e005504082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 839896951 1250 839895701 839895769
    0x606030604061d090c01020a1709010c140a03020c010c0c09050a15060c0606240f021c0c0c05030a02061b03042304150503030706180515011d010b0702 66
    0x106201c440c02d4040740e14249030b40402c0c1400220017081d41550700110034400003a83c03500030084039540c55024283c8034400319004803000a040800601003510b0035400404920340441e031114914032a0b021561812074040c0159208515540050105140c45100300003682854010301d0780a500c024001a5103034485800c13440205050f08040002384151990104200341446030a0151044696402c101c105280103003c4044840001000700b089542103902418000c04c500703400e47c090350100c8920182807810007421500403c10683e034070303640401c000a85080204020705c90a4016261918103d0826188681080b8540b00e6507001d1004003c0040e0441c401011005035601080b0f0855010a04004000981d03541010182605501c424104034599000048070412a44104081500d401d4171602d60102e401107000a0914021003100f60240e01418007007506982c05080d40c0e070f911118162045036814024096010f85103010050940036180007400d0000c2e603005000040c0a5507002000c031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 839898201 1250 839896951 839896979
    0xf050418050f1605032b020f0d0c0c0b0910050f0408060103061d010506010f2601090606140313170d0f0219050c150402030f06040503030105120114060603060406 71
    0x240c0300350003520800c2d000e000c500c40340900411302140180181034400681c14400500d14500d0038800350702c20408903003d4020700c02084202d6148081c0c07a078642c042c290140c080192101d04a03401c00d8007030300100d6481c003400d050f10b803246005003045501e4034801038245c0e036561226580c200e00060a000c0020070010400500b0b0107544560310100750034030200c03202405000300c0002014281d04050810900380d900658140300c0e02918544400c0c1e1400022145006040440c0c03401160803034040041400e803629048041121055a0796402000800c1903480e918041030f00d031000c4c200c00c842154000b01e5420007103000400741072408603141c481840403000403100b0b03442d13003a5a00c54011a03021000c081007807200501c0304503410942d10b054a0988020b85807050444c4003000660076a000c2019034808001c02c5a0201100c011510b83c1c2c00e2030300b0315079941d400921a0381e100342594003040c00054810701402c01d03503c2e00e00040441540b2102d0400501d03400c01003596400039960388000592040c400c940c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 839899451 1250 839898201 839898223
    0x12120908030409150e070c02240705012a090504151e0311150f0f0910020615060f1911011a040b0a0503061603020f2a070f05041805 58
    0x1000403070513490b160842240070303954004d51624070140c00b00300a040c0c00c04021011140c3c112041c44031082103000305603000c4088162000c4c07100010580d441001815804010b0010700201c800310b034603090103030700084c080d040d1807a50700044c61140e0030015030800d50000700300300c0990100400c4158940080c0c10a883c1c05843e0100c2c02d980c040e0041052286924101c4091941500c0c03111080f000f008580420744156084040c81c82d0000a40000b00700c07108068455007a0003c2140103c00b106a80081d40c3d42c1096a04180964154030006001e203003400440c4d24929011620300d090244554441d1500f00308100b540040c49280c0302107035103000080c414101d0201c003e00d1100403408842c002e110898952070501130040c100301c01c09228542e0300103170581e444106094003411449082c0c504030003a0080807225035543c88007140e0741c07012016207004141011031740a444c2421040d40d849040c0d540300e152049a90207581c80000388618185601716070b805402c00c407000c10100801c0d58509141180c0044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 839900701 1250 839899451 839899469
    0x7020303190203120901020a0c020d050708010207080706050a05040b06121c1215060905150f04030c08010c030b0915010c0503030a05190603030f260109061e121209080304 75
    0x15031104c1c64280c07005094101101100841c24100140c0000d03040d4900c00102905c00c0c04028400800c021080080704081c105140080d500c8280929042c40c407600700c074008a50a900713240c00140c95150510807144103a403c84021104c41c0c4441050010311210454498020702802ca0380c1d000d0070700401480d0058940c00c0d40c500302c0c1201011801d000f1030700741101c00f4030415142941040718550107044e0b40d007075980c01c6420b510440c409844420030351203072040348440a48046400001d00400011a03c12103000030002d102407205031104a00f12060050b110b58044102800300340030a41c0150a02d903002018100040c486013070b900c0b9145180c20851f001c08940303440b0707801c0104142e00644000a0041401030502c0304d14115500509200c06043e00c280400c0044422101c100503c4444011940341c0d041c441c00311940c442c01701001402d9103014025800364a010515903011454100034200c8100c28035030090143c4546e02c0e030100284c6101d420081001c83c520115290809000620051010344 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 839901951 1250 839900701 839900707
    0x91305070f02150606030115020f0a060c030f051b0d0e010e010603140d051903020f1605010c0c08180f0a1508070c0519140a111e011407020303190203 66
    0x1100074509000d503042c0250741d9543c030052090baa1180000e690550b680a03101401403a00d07034034201d1500e02c03441c1d010211880740c02c2182c1e040c8911607204040900f955035060100c191585c80c001c05540094800d2000a543c4076040080b0400301c0c0c002e8080300c40762000c041100c03400304a4507429a144011f00282c56503480004104018407100455400c0b0410700160541494041014005008dc43c101449c00e0000c29500f5010302e10a504070b42c0001c4848120640306c41c01c03483c0a503415071180b9411501076103802481240c05000b484442180e070b40c06203105250802404540c2e164046100620f500800c148207000c10030355501050b0005400800c410500c20122420005c004001c041c20840c00d203d900341d00c42c80401c0001c282d05403452402d00007101c1012913841e0080102004400c041034500860f4009401c0140448081c0441081260309130112991290204150030245000d2070101d21302200365041081d010700070303105441c0001c0030385e401c00600c0b2503180000301e2898001c90050b0000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 839903201 1250 839901951 839901977
    0xa030e1005010305060a020703090f0905090d2a0c030804180c030b090a051503100b1914010c03030e0303010b0901020d022a03030c2509020903060a0209130507 70
    0x8004a00140e88900001c0c8465407440e22204e80f1190f01402c4000c28a800066504c18140940444001400702100c004000760381c1c2c0d40c2c13180007450207a0702c0c03040707a018608004a030b5511076849141e2002c4909151a45003075002d60080c2075414800c400c8800d600003000010115541d40040c000901750703000e600c0700f0b891101804030f01321404026080c3c01d0528040400e00c180d290b140c6119441100858005060348540000c89a030315104084280d1511401016075a640c60b035400140c581c0fa001d95140d040e00c41c2d940486800204c07280900748803003d2a603243d003030a40c86410100c0065000781000281ca1000f0341ca0a0705551090700044c0801e040000d0340400c0c0d5a040003013003841c0310319102415844e220303c020628124410030400c085450380d015580c1c5c4540d4184115001c156150044aa0f06556280340542400442080750385140110600241c0741280d8000c0380e182500007809464140e94100800c4001c1d0000d40c1e01c60340100705520902c58035a0948106030107200b494a60862142031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 839904451 1250 839903201 839903203
    0x2090901060207030b0406050a091407050114190503070c050f0d090b03160305070e19080d0c081c060e0702010501170d08040b0a0e060403170109060b0702190b0a030e 73
    0x603800901154400282013020070440080d154005074001d00102e5a900c400954802a051041c0081c00300c10131040040c010078000100c61040344d03400c3e02c80e10211070210b6140400341c003401c244200040004411007141900c60401580e10844c28146a9042c0c000358441c0b610702500031260101035841816842d03540c40e001100b1500800d00750410302e19518140d4041c0100060034800c03141415215008946440c4c0503d88000c482c00018029030203c0c80d2541d2080e01c6002d00f88103201441c09001095400309110b8140180d00700e410082c0240340413061840110300341440740c4604070403583e9103004614070104003106c0380104640d50010416505025800d4a020207942031012168001802000c0c12504002c086910981005001429135103400e07600003e450708182c03000d06030003540c2c104010107410650914400e4050303498181140c1e02c40345044e0448106000d01922a902804187c0c01841c202c1c00b84c000d8209403c01c0e4200c1d8965881e0070741c0d070030b40110b031000c0003198a40341d90b902c10b088 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 839905701 1250 839904451 839904469
    0x10050103060501090204060519030b060c160b0313030f05040314010b01141e03060f150c0d05250302070f090f1b050f13031a0f1005151e07060209 64
    0x1084e10862429180c5080949288520003866038103ca202c8818500076000e50700581c03540d00050402d17507071600d415098544032080409040c00200d4505030100d010110802035a2048441701449403a00041c0e4a05407007800c0c0403000300302002800c00c004000150400900d01c040030391040041120003100c000509400342850358606040b8061041e1422004030310140e99440308a0603180750350f41c032030a000c10141d0401c2d515aa800c004005d0403090340d402c81000400444c000241a200310f103180e041c0840700d501c11403e1b204c40c40b00d0801d40720340348110714038012100103220340111100165039040c055058141503000c50303209603481c500400d0204042c003c806400f051100e1840c4120311440340900b1500851132240003038400030520f0701c41c41800080420155400440841d400028010540c00300402241e08100850000c000f003800c2d0107101450600703681008245481c038902031564402641c00034800d202c40c1c42c0718051010401d00d0380d8002070041c030340a40c0d800760759001c05c1d20500c03440130 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 839906951 1250 839905701 839905709
    0x15010e0708060306070f11070e0912031006050d091a071701210309090212041e200f120706031b080c160503130302130c020303040f050a0510050103060501 68
    0x40002000c210156402040d00350b40111142018000040d1003101181e42804450200040c0d200720800409c1204a000341c45120b81d081e50121240301c2c0c070802c00c4403ca40020783d041c0b02e80502610007070280b1806417002c0e00e101c14409000161484032a1120850000c0c1040501881421103081c412555400b000020701241c801c42200895498500d203110803074481c840000c114a180c0000f241094440d44001d4000c0c10038400954481c07c403a017841c0d920a1085d01c0880c2d1200c9001c8030201d141c10f08191914019130005020744102d4a00c0804c0243c00c000151070303a6011941c0d8221010603a211440341129041100c018466242489005001c0714449155034086c3c0d0300d504085140b007940100902d40c0320303a079149403c0d100c1440455500c0ca100d40180700515500010031b801c1e4040500e6240c0a08481c0215107107103d03c001c220400b030444003003045580042c0c01c100000740100c4c0745800080a50313441001121360b00e50070740d1144d0b17003409000885c0c0003032503444000400501c0b026009150240c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 839908201 1250 839906951 839906957
    0x20040e0d091511030a090801060f03050a0f060e120403060b090f040f020307031719030507020307030c0c03020d141b06071401060e07030b011413030b0a090515010e07 73
    0x102851406070501c0e085100748800402c15510000496209505241e100d01c40c100449440341400300018260300224050b4000a40c603060000406001720030b10b41084035046000b402c03000103240c0341d121090007840016104180c5840785601d0501e42044110105040468030a884904501d0008140d4000c02c850078400ea00c00303018003110340403100100e03811503409015020610301c01e1010070308286d86540054100a1140500126044000010304a00458280f50706001c240030f0310039030440e4801d0b01e22000582c030038401c000000c1e0064400c01407260092900d0284203999034001800c81e11103c0c42103902c4040c08154030002541080201c0080740040c0c034840c021000341e03003c5401c9000d045409802140c00c0c245800e400c0c4002c0d0f21400c05000c00c03019241c21803800c0b90340507003c2d2508c007000c0b0b030002e1003581e400c10176000f416040e00c01c42c1c48107401420f0041d181d0b80781c104194a02500c3c54950700e42c2c402241000600810100000741407911000107258500320009000346802001c031800c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 839909451 1250 839908201 839908213
    0x504020306060f16021f12061422020c01090c0803070305180d38100909031e0309020916020d03150308031f08030f09041820040e 57
    0x46542d03400151001090358214160302d03081d85502c04041018040c202071740001c811078021849095481d0445d400c42d4840e200c240c0790000c1150f04804580c10b511072030b405c0d800d03a074804070b00324a820811f0301d0408144a08094541445003441350499110300300f081000da43d04d881407800c21a110001c00c004284100c007550400b052502c0203481d522822103840d00454482003044015960203400328503454100400c9004103030810011202d800343c45101203440f040811000422450a013100e0b4483c841c41902040210300c0c211010002d00f1000384101c040c00824600075041e03d06101b144610040d8566000c520801d5600610101082c080d09a0299030351a443c0800840e4002030310f032025050a140c0000c2c51105080c2e074410200e11030b0001850362790004280050390700d070a401c0b104d0400844001d2580c003956486125941c0c49a8581800ca50740180100704003031a0642c0800b07081000000c09040c8110550f481c580c3c00d04080c582ca400d01c43c1c21508541003400e06224900300100300a0042070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 839910701 1250 839909451 839909461
    0x110a030c0f0801060503150601030b040f05072a0f11012303041101140711030f070915080a020901180f0513140c151b030c030c210406030c030e030f040f05040203 71
    0x1407c0c4000410040c18140c84401c81c0071280c6690303100000004500d54104054284588010030081031103501c54a2002413865050950711581100e6100540c400d0382160142c00e80d503580c0c0720f00c00079a40c00c6418040a0020165190901c00740d0110003030000b40710076aa80b4262818516007128062040d04001c03401410102014214048840c40c40c0c000040840c03003480390303000910b0000b5024080c481c0740103460000406509903045005100280d0001e40d903540d03221908907940e45d0034100c02039030040d45100100325004859510701a00d41400c0740c04074860b1005405d66080d40e40581e881d03400d48030610b048000340308400d072801c0d01c9a1f0000b0060911429440000350a41c2d20381038500f809004000751281c0702c0c4040340d04069102c207024058030303120b400301740030345842c3d40221a0000315030107150b11030390f600351104141c50002200c03000600d05090030f140c0c2c00c8004200480d900c005040d40d07140804450a41040a0442d15003540c010b640d466007070240c80034510065034091405039005200f80a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 839911951 1250 839910701 839910733
    0x1e02030601080a1e1709042007060b0d120c0510110406081014100302070209010902031f1203030f1503140f031305150424031802030a110a030c0f0801060503 69
    0x480c030034520a4179103440e00340d1407001900a00000c030030305030284000c106040b0445c90101c0940340180c01280f04000006a00f01444590300c902c110040400203550f64801c40716000d59603103080c0e68010400c44079116400307c1c00504481c2622400040500040b4082041c0d9070304c03a003602c0d0b100b00d0500e00340d070500d4546071602c3c81f45140504214483c0c69610304103000c0920a5050703880044c0c00804540c03495a6804403c402503000741d803080924020207456207403e240c2a901e08048507580314a42e044c2d820151002c6006040300d50148030703490385518402a403000c0d2760300c1d106c01441c00303101d000014079818048285400d00343ca82e408a1a001440543d05140015082c00100c81c000d840e40340058148248010403482940c00034121862101c0d094400301c264081200202842500e00b00030000c00e80c5d943e04245d9100d000003c0d07243c0e210840043c00940090144603034040060012059542c6079940c11050f0031a6401c4035150f141c0e403000070000140c09029007001000103402800040c40d40c04580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 839913201 1250 839911951 839911973
    0x80406030519090203060c0f2106030d17060f0409051507110a080d021b0d1e210b06040801110712050301080703060c020a02060703051207090b071e02030601080a1e 72
    0x100c40711040104000710300103080e0b02195100c01c1c00c040c030011801c04114809c0d0300d440040c0e50079400b82c810303044100800ca00511a5046003800641080c20300d40d95842001001d541803215550055196001400043e8080010920880440c2c0241c400c1d0b18003008000d0200c40340b9060304160f070303208200340804100f088040f2401c1c00300c1c01d680907a032000e80b0485150442d040e12600c4a052043e00d03080d044a940c000c80070381e440488041e0081e50f00188140c125400307030281540c3d182d0721220400700300304008103030b21114032140c0c00f40c42182403a603984940340c2154400f03503a850384040001a1841040045c804681c42117545091090a6504201c002035070341c08a808001c0c000c0390f40e008039100207070007040b28554290703000305120b540e00840d00c1c00404542008100440c00d242d2078002c50851070044400006507452200380b64101420340c0c0302e0700c0c4140c1c0706d03003001c0e5400b07241c1450041c0541c50920449000c0c091300001401107540030310742000302103000413501802042c40c011642c0040c07032070010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 839914451 1250 839913201 839913211
    0x2040b070206031f0b0403030809030406200a060617070504140c0d061a0c060604050115030b0d0602030a0c020f06090a020d02011209030e010906170a090f08040603051909020306 78
    0x4a483c1e580e20824001c141c60549810980c95a0503280001d03604480001402034900c40d548102e95910381c074602070b0b41c9016a01900d000b15a84d1241d40560f040070900e0b0b00d085558020403262100b0690f140e0a0445120350003211038140c204025503401c0c0c200700010801004151010050a149022628451031010300325407214400015a4085c08442d03400c080c01414225075004258043c40c03200132a181c1c8243d82c00000c03400f610002420902c3d0038440e45048036803941c980c0260301a002807c030002d0800c0020207070300006100030000880c22600c0030354400d0f481c680002401d4880038501a00e410120780c1c0940044e4040401c100380004d01068221455a05417800501d00e1028030040c4c551070240c0f5940e1300c0007890500540140366201303040c061740a100782c0b900d10596480d00070031a4440c00d940c0e0b03002c10303101101020542c0b101d1503611a0748132500420b00420140d0b080c1c2d44141e940d91080d400700c0002629001400004900c07241d6812680c6940340e070800c0b009886078046600c0700c2000784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 839915701 1250 839914451 839914459
    0x21042f01180e0a020c03040f0e0604060504090f02132408070506030c040b0901050c010e0105010603390c02100302220e040b180106030b15040509060a1a1c110402040b0702 75
    0x45d95400501e42007098501074900210081489900d960200d4041074040300c41c940704130f0800300e00007524207292003210f00594010b003400840c21380b42e0702884528907101d1303440c55280e55200c0d16911141641c0a8045290550342140c2d9005840c10324280c0c0380c40c50706e4124601c41c15040003403041c1001d07242c08550861300d43d0700010752600780220042e12940503095021a184d400c3c10301d4048001c006500c00303070503622030b52402c0000807600c13110500000c181201e1405140c00d04001e500d42180e1107501042c03110098502108060110380c003140380b144030148100d02090b00401d6689a0b42c0343c20080074243c802031071880103803500d070a080840c0702101600c042c2c54040c02d040803688a076095045205030340414002405010781d130703260503003850f030048807030301c542c1842140216172510707043c0603060003407002400074010b03910340301c944000402c0300c6042d840302c20140c1c501048158666408821030302d615042074118501442c1083c40b8141c0c15210401c1c81588100b00c144440d82c0040d0541d41c0c0c0c203405036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 839916951 1250 839915701 839915707
    0x12120e0a150e13020d0e0309011709012012010506071a090c0429030a02033d1a03010c05190e0306040b190221042f01180e0a02 56
    0x1032420b03503051404080b16a00301d1a90300f10411000c20b43e4004015500503030307400f00000d84c8a1081140c80340034a91065001840c1c8620300c5e0300078441525080d400401e40070001800c0d0035152071004503402c8000e5603400513800071070030701118150780600c54018802521010310701b00d01562003108074183d542141c0a02c1100d0004180320107400c0100112440014100300642d8810400d84215210a10419200c100c01800180200c0c10003150387c0c50800d60160050880041c41c100c440e0341c040d14903a460b0440d080040d0000d050480b4007492104000c0c4604000404050800c01c06461180081c21103000741c2c1401007501d03520340e00c501110101c2c100c02001b13034003104600d00100c584141000e1056070600c100ca0602040c8801d802e0124029801d0700f034041c0c031800342d112440c0140d0003480f94950200700180c0140040399403590a0360703800f51051050351140e0384130400c44006016045c1d03c1103a6580c112911f0a05940c01030908420803031175540307a21410340741601da40c1d051600100407021080d008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 839918201 1250 839916951 839916989
    0x50106021218150d0f18020d05100207200d0201020a0308060a0f09270b040818030109060e1e100c180824010b160c090612120e0a 57
    0x2c000b4180c0e2400700102103200340c04950b0083d031003540103074503504445480e140741e002c44201c0303e1241070010180030900d60700071099902001501e0307031907000c292102d00400210031304504043c4005d2151a01c0340b03406052001c1012059034056500c038404d58000d18086004101503038001a800c0325407503051a10341099610b480105200b00d526a001c1c00e03820990340703804141d01800383c0014160100042064100b0003000841d2041000309820141000101e140450081005040108084080b800c015901c0c480c02c2d6000c0790841c0c043c104161020b40c3e4505000842403001d101d80701310000410007030303109107080b481d0301c036168030003c902c1c0c6000c207a541c403111210030f01603c0c01c800c0000201642d0b90902e035568440076200c003420038071703001c1da840c42c03402c072080040721054441d0585207000d5046007018500981003106801721001900d00c40d51f406800a4042c01234040e0101a082c40c1c0c64200301c4d0402460891940e40780140d041c010300444010030442600c0d001610412146031180140c018101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 839919451 1250 839918201 839918227
    0x60305030316140d1a030610060e04090b0a050405010b0907090e180303040c0807080a030903080d110309010c030e0c0108040213090501050f012103050306010c020310020c0d0809010501060212 84
    0x31003829000014010031011600c8030582c0c0031003196282d100c180c299000e0317150101a04d5400868028919030344180007070011921035407018010700c00152001540943e19150031140f20806c5508003004ca0f107a604110800c0801c2c007441080c0c1a0a81e81040702c0e05100c1000b0b0660141c0d0700402600c52a181e00142200c3c071903000baa00c009602d501130769034a05060a01900000840c02506824860b00380000b80e209000502d2403102d94040c1d0740c0c0450103040d950b800b0003941c40450703888441a169024440000101c0d0011070183c0b001c1400000e0040c0c04610140c192058802c8204198000d0089a0143d0340c0000c086648694119062400d000180e02420010248002d02a01c0c56107414104464510340040841c144c2c0c091940c04541d46250700741840250b45000f40080000b80144081945135020b01188050a4070042c207858021005082800498100c02150821948404042541c154004848d030380c001c95014000d10041d030400700080d42d02e0007900032a102170800000c4c000c081c0c1c88 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 839920701 1250 839919451 839919467
    0x1908011413110703030e190503120c0712020708010c030b1f0203300105060307020c04051806040804062307080901031b110d0e0f0411090d1b0603060305030316 70
    0x19140da40b40d03407202103a00b4014000c00541c5050b940602c14424100038260461a40d0b00c1d100c1d074000020742c03031314051100703c00007031201401c0c500c1d5440092280b040050803d0209040451065000b444464130306040c2600707442009480000381454024070303402e2030700c80d010183c00798044201e02012800007000120701d944100c030961602041e269400c3c001e084500d000401186402580d80c0c01e407030740c0301c01c2001420703c025110a800b591007052f00b0281c1d0700741600480d41c0b10300000130000c01001020006400d02ca41103a0441c0c00440016041c002d00b500714030360400f110146581401e030080704803081c03003c0d4841d032403010700740c07520201b00160940e120740c01c48a50098821a09808000c6001c00900548c0c4001d000d40446d001d50640c8040581c8940840d4a1a84001344040100c00c0d504007400700400c3c24182c00802e80b0420040d00b910340d00c5150b04101000c0c46261911003a280055804111050b5038002c8010107041060805c0810b07030010959800035004203846403070440103101078030400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 839921951 1250 839920701 839920721
    0x204230a03240b04020316030902130c020c031002070b0703090602040b0c0105060102100b010207030b061314160f05040b09040b0913201c060609111908011413 70
    0x1c01c50a40c00c2000b1074028940d401c02500d0320b40203100061412040105a0000b141d400d0201c4802d41026a8854400d4000301451170002d84165200710340a4007410554910014050160340918640c0c02d00d401c08200012042258040460030710384a0b0707651011001014000c8010113856907145410300c01c103541220000c2001c0e0700403580d40d440e288112400b03460111750080c058069150144110708050264102d0158160f01a11500d81599039403914036501030f01943e044402c5408030318951207144560062070301404000122840c2c403c0d0406400c01e00641c01404200300d135010204100e8100d025101070b501c0c00c80c0710603202c454030360204d00204214007050798049031070300c01d00c0703c840100e40c044801240600030307904149820510380c941854000082a8004950307000c2d0341d44842203003485c1d0f981e09214030780224806640c0d0100c0400e139040d00142c00843c0d2400580d00701000c2605486070b00051380307801c01d413420790301d04004440400008062940100301340302403840550f4003036101102003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 839923201 1250 839921951 839921963
    0x2011803090303080f010b0a03091a0117060c0f0d050a09020901180e030c060f0402010c050d0503010e012103030b13110c0f060411100c0f20040204230a03 68
    0x58540c2401011200684800d6022890780300115140d405c00a103454140c400b6924824604800010110f0050600d034005070380e52401c28682607620b803032142c27071140204041d10400300d204400540d103500f00b0101034099003010200308040200e4811007410307074a40103907105001a1036590403118102400044400070340c4540c08030000b050300c1c15500b5540086240f5070400700001c1070701d044090b0b1b482c42007020201d800c4d8402d20000c0d2100002003100c41d8840c0c81850302d0843d010560b5103280c40c2c1050200301c1000300704040014045100311240050050030301034814002503441800c012034101182e44040c040645825015030b0985031041e200c1442015120100890b0b10354100b80302e0b42d604002c016035441d000308220414071a000203041c42c081d5400c0f640b9045090100310070494014005210501400300f00c40705000480d5280003d0740d82180076229a6004a0707503d42440c003c410301007446849036105000511030140440d00f03110192103080f010040c00c03200100022400c3d907150781300520b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 839924451 1250 839923201 839923241
    0x8040f080919090f02040503031c09022706040627060b040f031202010204030503030f0a09020a060e03100c1b1109040503070b0f0408071104061a2d040e070201 70
    0x1c425848100c0b0440302c0304141041030a249071030380720a0b4401d07171080e158190b105026141100c0000b1700000b8045100400010300000c3c55030104281d45540390b08000f00c64960340e000b08019030b600484592040e0215010810681404404001018a1100b0080588a1042610220710103038031800c0900504161562103a80e903520701842d80301680800c44400c060b075105181e409005000790780681c1d43c804090341c19561041880003040d14001e24221403591106405005030b11965401e0f070142c4005c0c1d44888a1a1002044c1840e151800d0712400c0807a24080c3d20303c52903035104030a0b03d1600740c0200c908000641d0350400507012030118440e2a40490404140002c01800200420a051140d008084250380360b01c10010f00c0c0340b04807001303010f80c1400c0248c00f00290b4151079140d0341860050001030801d803110041c8014500c801040c5448500014800811210300c034401484412581c0c00d01000d0241d0003142d8601e8003852003140f80201c8980049000c0358000e4000c031111203a03a0806d128 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 839925701 1250 839924451 839924479
    0x2040801060302010e1905100e0a0b032721070209150118080303010501110115262a0d0f0803070e01080402010e060c150916051008040f0809 62
    0x4001e10061008078041a410181140a818000b001c28100c2c550010500082e03413600040c041c0121940300410100b042c43d10256201d80c0d40d03200d285018106189000303071a46002805605544400000006100c1409121201148000030185081c0410120494040903400000c80b210b001d1203000952000c030b41c03420040148050540d11203904000d03629130b1080043c1503200c0c04440c1c45401525840c5d0410001884070b540154000b09a1620503c00012448101440903094280c250810351a50000011a480410041c101c098108001c82c0c0580404003000d460745c0d89060302d44158141c60025001c09060541e82c10501c195682c0d001071900702012054074007000320368022144400804e1210610400d50b5109030195886242d068440c5464807180d20104040c85d004200c20f0740e03203072250318608034400608504050042000344014a0414030180d8044a0051307660001d078003480418807091b91a590004515800c07a80065603140112014205500c6505c5154081c9170000b0800b10060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 839926951 1250 839925701 839925703
    0x19150c02210d05280c140d0201061e0905060d120c03080709050603040308180703110906030a0b0112020d080703050306040e061e0c0c01140901050606211306020408 72
    0x281c6054245026244180c030001819074035401002d0141080c40060700112a002802a41402000c240ca0814925410441c0e640c1203034400601034504140e0042d03651030403050f409004000c040d0845410140c170901c000c8803840c250750383c10701c03032524181e41b07a50120300261690701d00c6040309a00300d104010124186403028180c2c0b944001c085000980a20000e03502c0d1b8411a201c0c400d0703801c0100728510316103e0707450449042c00c0c00744c1a001d200841d00d03038441104508015041c000c40c8910400481c600340f16080202c0c20070700500c503601a8100401d1800040c04026a06064649501185084100a00100d03100f1400d403500205881000076950301407607000710140d4410b440c2250141b10003070005a00030744035641500c142a0a00300301400b03881641c0c11103075550b8003110000340542000003422803e030a4502403410036562588550601c0a000800e024070340c0c4c00701f0151001c610744140140304000c0b018501d4084400100c0800105100c80d04014905048942110042d9202c2c3d440d41001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 839928057 1106 839926951 839926999
    0xa0605040303032301060e131b05160210030b030c030a020f0d021c03050703020d08070e130209190906081c08090304090510050f19150c02 61
    0x240c2c80e5800303202d00c040e001b01466601c25480702942ca0511140340b44a0209100716401c03c245106a40041d0f2040f107810004c07450002d9032110584842c00700c0c0221040003d501c0070074120034003034281d8140c000c18421081141607520b4440791600b050340e20b503498040250046a0075042070b0844c07900b601050b0809002510349840800345010301108010010f00c110080788011429105043d810072903020244040e0608401a04080c2400703004081560702944c8603c500414000c40040b190701607460040d03001e4000c1c40d2110b00c401c861079800d5528001c10b00094a44440002d0182002604540c2415407151032400c401400d1401c0310400740052010b41e961004000014004580748942c2c1e200e40025a000c1001c50f0910b4104640300d142502480d106007003011881010b0441500008101c0308480c00610303060207480070941705000100c8001e580840580100c0c0c50341d501349041 = true := by decide +kernel

theorem cover : BRFrame.Cov 839748201 839928057 := by
  have h0 := BRFrame.cov_init 839748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 839748201 ≤ n) (h2 : n < 839928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
